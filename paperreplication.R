library(ggplot2)
library(dplyr)
library(numDeriv)
library(dfoptim)

beta <- 0.0925
v <- 0.1826
rho <- 1 - (95/100)^(1/365)
optimal.c <- 5
infected.people.really.hate.this.number <- 2
horizon <- 500 ## horizon value for agent's optimization.
grahor <- 150 ## horizon value when plotting/charting trajectory
rho.vec <- (1 - rho)^(0:(grahor-1))  ## note this is 1 - discounting.
delta <- 0.2
digamma <- 1/optimal.c

## -------------------------------------------------------
##
## Tuning
##
## -------------------------------------------------------

## We need to make sure that our values are as accurate as possible, so that
## the algorithms can find a value with high enough precision. R's bad enough
## in being limited by 64-bit floating point, and unfortunately by the time
## I noticed how devastating this limitation is I've already coded everything
## in floating point. These fine-tuning should hopefully help a bit, by
## making everything a bit more symbolic.

gamma <- -2/3
b <- 24

## To extract an accurate value for alpha...

alpha <- -(optimal.c)/(-optimal.c - b*exp(-gamma * (log(b - optimal.c) - log(optimal.c)))
                       + optimal.c * exp(-gamma * (log(b - optimal.c) - log(optimal.c))))

## To extract an accurate value for u-bar...

ubar <- (alpha*(optimal.c)^gamma + (1-alpha)*(b-optimal.c)^gamma)^(1/gamma)

## To calculate mi... (default: 2 * ubar)

mi <- ubar*2

## To calculate vz (long run)

vz.lr <- (1/rho)*ubar

## To calculate vi (long run)

vi.lr <- (v*vz.lr + ubar-mi)/(rho + v)

## -------------------------------------------------------
##
## Basic Components
##
## -------------------------------------------------------

## Basic component functions for calculating stuff:

## h: 0 = susceptible, 1 = infected, 2 = recovered

utility <- function(c, h){
  m <- mi
  if(h == 0) m <- 0
  if(h == 2) m <- 0
  return((alpha*(c)^gamma + (1-alpha)*(b-c)^gamma)^(1/gamma)-m)
}

## note that infected and recovered individuals will always choose
## to initiate 5 contacts per time period.

## calculate C^{si}

c.si <- function(c.s, c.i = 5, c.z = 5, s, i, z){
  return((c.s*c.i)/(s*c.s + i*c.i + z*c.z))
}

## calculate S_{t+1}

s.t1 <- function(c.s, c.i = 5, c.z = 5, s, i, z){
  return(s-c.si(c.s, c.i, c.z, s, i, z)*beta*s*i)
}

## calculate I_{t+1}

i.t1 <- function(c.s, c.i = 5, c.z = 5, s, i, z){
  return(i + c.si(c.s, c.i, c.z, s, i, z)*beta*s*i - v*i)
}

## calculate Z_{t+1}

z.t1 <- function(z, i){
  return(z + v*i)
}

## calculate P{s, i}(.)

prob.si <- function(cs, ci = 5, cz = 5, s, i, z){
  return((cs*ci*beta*i)/(s*cs + i*ci + z*cz))
}

## -------------------------------------------------------
##
## Decentralized decision making
##
## -------------------------------------------------------

## --------------------
## What is the trajectory of the pandemic for a vector of
## contacts from t = 0 to t = T?

ddm.trajectory <- function(contacts.vector, init.s, init.i, init.z, c.i=5, c.z=5){
  
  ## define temporary variables
  s <- init.s
  i <- init.i
  z <- init.z
  utotal <- 0
  
  ## define susceptible individual's expected medical state
  
  sus <- 1
  inf <- 0
  rec <- 0
  
  for(j in 1:length(contacts.vector)){
    
    discount <- (1-rho)^(j-1)
    
    ## compute next period pandemic trajectory
    
    s1 <- s.t1(contacts.vector[j], c.i=c.i, c.z=c.z, s=s, i=i, z=z)
    i1 <- i.t1(contacts.vector[j], c.i=c.i, c.z=c.z, s=s, i=i, z=z)
    z1 <- z.t1(z=z, i=i)
    
    ## compute current period utility
    
    ## first compute expected utility in each possible medical state, weighted
    ## by the probability
    
    usus <- sus*utility(c = contacts.vector[j], h = 0)
    uinf <- inf*utility(c = contacts.vector[j], h = 1)
    urec <- rec*utility(c = contacts.vector[j], h = 2)
    
    ## then calculate the probability of the individual of being in each medical state
    ## in the next period. Note we use v*inf instead of v*i
    
    sus <- sus - prob.si(contacts.vector[j], s=s, i=i, z=z)
    inf <- inf + prob.si(contacts.vector[j], s=s, i=i, z=z) - v*inf
    rec <- rec + v*inf
    
    ## compute discounted current period utility
    
    u <- discount*(usus + uinf + urec)
    utotal <- utotal + u
    
    ## update next period infection state
    
    s <- s1
    i <- i1
    z <- z1
    
  }
  
  ## return total utility
  
  return(utotal)
  
}

ddm.optim <- function(init.s, init.i, init.z, init.guess){
  
  ## horizon is a global parameter that can be changed for
  ## robustness, or to speed up the optimization.
  ## BFGS is chosen because of robustness, and because we believe
  ## that the optimal level of contacts should follow some smooth (differentiable perhaps)
  ## intertemporal relationship (BFGS works best on smooth
  ## hypersurfaces)
  x <- optim(par = rep(init.guess, horizon),
             fn = ddm.trajectory,
             init.s = init.s, init.i = init.i, init.z = init.z,
             method = "BFGS",
             control = list(fnscale = -1, maxit = 100),
             hessian = FALSE)
  
  return (x)
  
}

## --------------------
## 150-day horizon

## Create a class to encapsulate information

setClass(Class="DecentralizedTracker",
         representation(
           s="numeric",
           i="numeric",
           z="numeric",
           cs="numeric",
           ci="numeric",
           cz="numeric",
           us="numeric",
           ui="numeric",
           uz="numeric"
         )
)

## Now let the economy work out itself based on the optimized
## values of contacts and see what happens.

ddm <- function(init.s = 0.999, init.i = 0.001, init.z = 0,
                          c.i = 5, c.z = 5, graph.horizon = 150){
  
  s.vec <- vector(mode = "numeric", length = graph.horizon)
  i.vec <- vector(mode = "numeric", length = graph.horizon)
  z.vec <- vector(mode = "numeric", length = graph.horizon)
  
  cs.vec <- vector(mode = "numeric", length = graph.horizon) ## contacts of susceptible
  ci.vec <- rep(c.i, graph.horizon) ## contacts of infected
  cz.vec <- rep(c.z, graph.horizon) ## contacts of recovered
  
  us.vec <- vector(mode = "numeric", length = graph.horizon) ## utility of susceptible
  ui.vec <- rep(utility(c.i, 1), graph.horizon) ## utility of infected
  uz.vec <- rep(utility(c.z, 2), graph.horizon) ## utility of recovered
  
  ## temp vars
  
  s0 <- init.s
  i0 <- init.i
  z0 <- init.z
  
  ## run the optimization and retrieve the optimal contacts per time period:
  
  x <- ddm.optim(init.s = init.s, init.i = init.i, init.z = init.z,
                 init.guess = 4)
  cs.vec <- head(x$par, n = graph.horizon)
  
  for(j in 1:graph.horizon){
    
    ## retrieve the optimal contacts in the j-th period
    contact.s <- cs.vec[j]
    
    ## Store current period information in the vectors.
    
    s.vec[j] <- s0
    i.vec[j] <- i0
    z.vec[j] <- z0
    cs.vec[j] <- contact.s
    us.vec[j] <- utility(contact.s, 0)
    
    ## Then move the period forward
    
    s1 <- s.t1(c.s = contact.s, s = s0, i = i0, z = z0)
    i1 <- i.t1(c.s = contact.s, s = s0, i = i0, z = z0)
    z1 <- z.t1(z = z0, i = i0)
    
    s0 <- s1
    i0 <- i1
    z0 <- z1
    
  }
  
  return(new("DecentralizedTracker",
             s=s.vec, i=i.vec, z=z.vec,
             cs = cs.vec, ci = ci.vec, cz = cz.vec,
             us = us.vec, ui = ui.vec, uz = uz.vec))
  
}

## Store results for initial values that we put in the paper...

decentralizedresults <- ddm(init.s = 0.999, init.i = 0.001, init.z = 0)

## Plot some graphs

t <- c(1:150)
data.decentralized <- data.frame(t, decentralizedresults@s, decentralizedresults@i,
                                 decentralizedresults@z, decentralizedresults@cs,
                                 decentralizedresults@ci,
                                 decentralizedresults@cz, decentralizedresults@us,
                                 decentralizedresults@ui, decentralizedresults@uz)

## calculate weighted utility levels in each time period

data.decentralized <- data.decentralized %>%
  mutate(wus = decentralizedresults.s * decentralizedresults.us) %>%
  mutate(wui = decentralizedresults.i * decentralizedresults.ui) %>%
  mutate(wuz = decentralizedresults.z * decentralizedresults.uz)

## add discounting factor

data.decentralized <- data.decentralized %>%
  mutate(rho = rho.vec)

## calculated total discounted + weighted utility levels

data.decentralized <- data.decentralized %>%
  mutate(tu = rho * (wus + wui + wuz))

## sum it up

tutil.decentralized <- sum(data.decentralized$tu)

ggplot(data.decentralized, aes(x = t, y = decentralizedresults.s)) +
  geom_line(color = "#69b3a2", size = 2, alpha = 0.9) +
  theme_dark()+
  ggtitle("Trajectory of Disease Prevalence under decentralized decision making") +
  xlab("Time (days)") +
  ylab("Disease Prevalence (%)")

plot(data.decentralized)

## -------------------------------------------------------
##
## Social Planner
##
## -------------------------------------------------------

## --------------------
## What is the trajectory of the pandemic for a vector of
## contacts from t = 0 to t = T?

soc.trajectory <- function(contacts.vector, init.s, init.i, init.z){
  
  ## contacts.vector consists of: c.s[1], c.s[2], ..., c.i[1], c.i[2], ..., c.z[1], ...
  
  ## check if it is divisible by 3
  if(length(contacts.vector) %% 3 != 0) stop("contacts vector is not div by 3")
  
  rl <- length(contacts.vector)/3
  
  ## define temporary variables
  s <- init.s
  i <- init.i
  z <- init.z
  utotal <- 0
  
  ## (we don't have to track the utility level of each individual now
  ## the social planner only cares about aggregate utility)
  
  for(j in 1:rl){
    
    discount <- (1-rho)^(j-1)
    
    ## retrieve contact values
    
    cs <- contacts.vector[j]
    ci <- contacts.vector[j+rl]
    cz <- contacts.vector[j+(2*rl)]
    
    ## compute next period pandemic trajectory
    
    s1 <- s.t1(c.s = cs, c.i = ci, c.z = cz, s=s, i=i, z=z)
    i1 <- i.t1(c.s = cs, c.i = ci, c.z = cz, s=s, i=i, z=z)
    z1 <- z.t1(z=z, i=i)
    
    ## compute current period utility
    
    us <- s*utility(c = cs, h = 0)
    ui <- i*utility(c = ci, h = 1)
    uz <- z*utility(c = cz, h = 2)
    
    ## compute discounted current period utility
    
    u <- discount*(us + ui + uz)
    utotal <- utotal + u
    
    ## update next period infection state
    
    s <- s1
    i <- i1
    z <- z1
    
  }
  
  ## return total utility
  
  return(utotal)
  
}

soc.optim <- function(init.s, init.i, init.z, init.guess.cs, init.guess.ci, init.guess.cz){
  
  x <- optim(par = c(rep(init.guess.cs, horizon),
                     rep(init.guess.ci, horizon),
                     rep(init.guess.cz, horizon)),
             fn = soc.trajectory,
             init.s = init.s, init.i = init.i, init.z = init.z,
             method = "BFGS",
             control = list(fnscale = -1, maxit = 100),
             hessian = FALSE)
  
  return (x)
  
}

## --------------------
## 150-day horizon

## Now let the economy work out itself based on the optimized
## values of contacts and see what happens.

setClass(Class="SocTracker",
         representation(
           s="numeric",
           i="numeric",
           z="numeric",
           cs="numeric",
           ci="numeric",
           cz="numeric",
           us="numeric",
           ui="numeric",
           uz="numeric"
         )
)

soc <- function(init.s = 0.999, init.i = 0.001, init.z = 0, graph.horizon = 150){
  
  s.vec <- vector(mode = "numeric", length = graph.horizon)
  i.vec <- vector(mode = "numeric", length = graph.horizon)
  z.vec <- vector(mode = "numeric", length = graph.horizon)
  
  cs.vec <- vector(mode = "numeric", length = graph.horizon) ## contacts of susceptible
  ci.vec <- vector(mode = "numeric", length = graph.horizon) ## contacts of infected
  cz.vec <- vector(mode = "numeric", length = graph.horizon) ## contacts of recovered
  
  us.vec <- vector(mode = "numeric", length = graph.horizon) ## utility of susceptible
  ui.vec <- vector(mode = "numeric", length = graph.horizon) ## utility of infected
  uz.vec <- vector(mode = "numeric", length = graph.horizon) ## utility of recovered
  
  ## temp vars
  
  s0 <- init.s
  i0 <- init.i
  z0 <- init.z
  
  ## run the optimization and retrieve the optimal contacts per time period:
  
  x <- soc.optim(init.s = init.s, init.i = init.i, init.z = init.z,
                 init.guess.cs = 5, init.guess.ci = 0.01, init.guess.cz = 5)
  c.vec <- head(x$par, n = 3*horizon)
  
  for(j in 1:graph.horizon){
    
    ## retrieve the optimal contacts in the j-th period
    contact.s <- c.vec[j]
    contact.i <- c.vec[j+horizon]
    contact.z <- c.vec[j+2*horizon]
    
    ## Store current period information in the vectors.
    
    s.vec[j] <- s0
    i.vec[j] <- i0
    z.vec[j] <- z0
    cs.vec[j] <- contact.s
    ci.vec[j] <- contact.i
    cz.vec[j] <- contact.z
    us.vec[j] <- utility(contact.s, 0)
    ui.vec[j] <- utility(contact.i, 1)
    uz.vec[j] <- utility(contact.z, 2)
    
    ## Then move the period forward
    
    s1 <- s.t1(c.s = contact.s, c.i = contact.i, c.z = contact.z,
               s = s0, i = i0, z = z0)
    i1 <- i.t1(c.s = contact.s, c.i = contact.i, c.z = contact.z,
               s = s0, i = i0, z = z0)
    z1 <- z.t1(z = z0, i = i0)
    
    s0 <- s1
    i0 <- i1
    z0 <- z1
    
  }
  
  return(new("SocTracker",
             s=s.vec, i=i.vec, z=z.vec,
             cs = cs.vec, ci = ci.vec, cz = cz.vec,
             us = us.vec, ui = ui.vec, uz = uz.vec))
  
}

## Store results for initial values that we put in the paper...

socresults <- soc(init.s = 0.999, init.i = 0.001, init.z = 0)

## Plot some graphs

t <- c(1:150)
data.soc <- data.frame(t, socresults@s, socresults@i,
                                 socresults@z, socresults@cs,
                                 socresults@ci,
                                 socresults@cz, socresults@us,
                                 socresults@ui, socresults@uz)

## calculate weighted utility levels in each time period

data.soc <- data.soc %>%
  mutate(wus = socresults.s * socresults.us) %>%
  mutate(wui = socresults.i * socresults.ui) %>%
  mutate(wuz = socresults.z * socresults.uz)

## add discounting factor

data.soc <- data.soc %>%
  mutate(rho = head(rho.vec, 150))

## calculated total discounted + weighted utility levels

data.soc <- data.soc %>%
  mutate(tu = rho * (wus + wui + wuz))

## sum it up

tutil.soc <- sum(data.soc$tu)

## what about the trajectory when the social planner perfectly quarantines all infected individuals?

soc.perfect <- function(init.s = 0.999, init.i = 0.001, init.z = 0, graph.horizon = 150){
  
  s.vec <- vector(mode = "numeric", length = graph.horizon)
  i.vec <- vector(mode = "numeric", length = graph.horizon)
  z.vec <- vector(mode = "numeric", length = graph.horizon)
  
  cs.vec <- vector(mode = "numeric", length = graph.horizon) ## contacts of susceptible
  ci.vec <- vector(mode = "numeric", length = graph.horizon) ## contacts of infected
  cz.vec <- vector(mode = "numeric", length = graph.horizon) ## contacts of recovered
  
  us.vec <- vector(mode = "numeric", length = graph.horizon) ## utility of susceptible
  ui.vec <- vector(mode = "numeric", length = graph.horizon) ## utility of infected
  uz.vec <- vector(mode = "numeric", length = graph.horizon) ## utility of recovered
  
  ## temp vars
  
  s0 <- init.s
  i0 <- init.i
  z0 <- init.z
  
  c.vec <- c(rep(5, graph.horizon), rep(0, graph.horizon), rep(5, graph.horizon))
  
  for(j in 1:graph.horizon){
    
    ## retrieve the optimal contacts in the j-th period
    contact.s <- c.vec[j]
    contact.i <- c.vec[j+graph.horizon]
    contact.z <- c.vec[j+2*graph.horizon]
    
    ## Store current period information in the vectors.
    
    s.vec[j] <- s0
    i.vec[j] <- i0
    z.vec[j] <- z0
    cs.vec[j] <- contact.s
    ci.vec[j] <- contact.i
    cz.vec[j] <- contact.z
    us.vec[j] <- utility(contact.s, 0)
    ui.vec[j] <- utility(contact.i, 1)
    uz.vec[j] <- utility(contact.z, 2)
    
    ## Then move the period forward
    
    s1 <- s.t1(c.s = contact.s, c.i = contact.i, c.z = contact.z,
               s = s0, i = i0, z = z0)
    i1 <- i.t1(c.s = contact.s, c.i = contact.i, c.z = contact.z,
               s = s0, i = i0, z = z0)
    z1 <- z.t1(z = z0, i = i0)
    
    s0 <- s1
    i0 <- i1
    z0 <- z1
    
  }
  
  return(new("SocTracker",
             s=s.vec, i=i.vec, z=z.vec,
             cs = cs.vec, ci = ci.vec, cz = cz.vec,
             us = us.vec, ui = ui.vec, uz = uz.vec))
  
}

socperfresults <- soc.perfect(init.s = 0.999, init.i = 0.001, init.z = 0)

## Plot some graphs

t <- c(1:150)
data.socp <- data.frame(t, socperfresults@s, socperfresults@i,
                        socperfresults@z, socperfresults@cs,
                        socperfresults@ci,
                        socperfresults@cz, socperfresults@us,
                        socperfresults@ui, socperfresults@uz)

## calculate weighted utility levels in each time period

data.socp <- data.socp %>%
  mutate(wus = socperfresults.s * socperfresults.us) %>%
  mutate(wui = socperfresults.i * socperfresults.ui) %>%
  mutate(wuz = socperfresults.z * socperfresults.uz)

## add discounting factor

data.socp <- data.socp %>%
  mutate(rho = head(rho.vec, 150))

## calculated total discounted + weighted utility levels

data.socp <- data.socp %>%
  mutate(tu = rho * (wus + wui + wuz))

## sum it up

tutil.socp <- sum(data.socp$tu)

ggplot(data.socp, aes(x = t, y = socperfectresults.i)) +
  geom_line(color = "#69b3a2", size = 2, alpha = 0.9) +
  theme_dark()+
  ggtitle("Trajectory of Disease Prevalence under decentralized decision making") +
  xlab("Time (days)") +
  ylab("Disease Prevalence (%)")

plot(data.soc)

## -------------------------------------------------------
##
## Government with imperfect information
##
## -------------------------------------------------------

## --------------------
## What is the trajectory of the pandemic for a vector of
## contacts from t = 0 to t = T?

gov.trajectory <- function(contacts.vector, init.s, init.i, init.z){
  
  ## contacts.vector equally applies to all individuals in the economy
  
  ## define temporary variables
  s <- init.s
  i <- init.i
  z <- init.z
  utotal <- 0
  
  ## (we don't have to track the utility level of each individual now
  ## the social planner only cares about aggregate utility)
  
  for(j in 1:length(contacts.vector)){
    
    discount <- (1-rho)^(j-1)
    
    ## retrieve contact values
    
    cs <- contacts.vector[j]
    ci <- contacts.vector[j]
    cz <- contacts.vector[j]
    
    ## compute next period pandemic trajectory
    
    s1 <- s.t1(c.s = cs, c.i = ci, c.z = cz, s=s, i=i, z=z)
    i1 <- i.t1(c.s = cs, c.i = ci, c.z = cz, s=s, i=i, z=z)
    z1 <- z.t1(z=z, i=i)
    
    ## compute current period utility
    
    us <- s*utility(c = cs, h = 0)
    ui <- i*utility(c = ci, h = 1)
    uz <- z*utility(c = cz, h = 2)
    
    ## compute discounted current period utility
    
    u <- discount*(us + ui + uz)
    utotal <- utotal + u
    
    ## update next period infection state
    
    s <- s1
    i <- i1
    z <- z1
    
  }
  
  ## return total utility
  
  return(utotal)
  
}

gov.optim <- function(init.s, init.i, init.z, init.guess){
  
  ## horizon is a global parameter that can be changed for
  ## robustness, or to speed up the optimization.
  ## BFGS is chosen because of robustness, and because we believe
  ## that the optimal level of contacts should follow some smooth (differentiable perhaps)
  ## intertemporal relationship (BFGS works best on smooth
  ## hypersurfaces)
  x <- optim(par = rep(init.guess, horizon),
             fn = gov.trajectory,
             init.s = init.s, init.i = init.i, init.z = init.z,
             method = "BFGS",
             control = list(fnscale = -1, maxit = 100),
             hessian = FALSE)
  
  return (x)
  
}

## --------------------
## 150-day horizon

## Now let the economy work out itself based on the optimized
## values of contacts and see what happens.

setClass(Class="GovTracker",
         representation(
           s="numeric",
           i="numeric",
           z="numeric",
           cs="numeric",
           ci="numeric",
           cz="numeric",
           us="numeric",
           ui="numeric",
           uz="numeric"
         )
)

gov <- function(init.s = 0.999, init.i = 0.001, init.z = 0, graph.horizon = 150){
  
  s.vec <- vector(mode = "numeric", length = graph.horizon)
  i.vec <- vector(mode = "numeric", length = graph.horizon)
  z.vec <- vector(mode = "numeric", length = graph.horizon)
  
  cs.vec <- vector(mode = "numeric", length = graph.horizon) ## contacts of susceptible
  ci.vec <- vector(mode = "numeric", length = graph.horizon) ## contacts of infected
  cz.vec <- vector(mode = "numeric", length = graph.horizon) ## contacts of recovered
  
  us.vec <- vector(mode = "numeric", length = graph.horizon) ## utility of susceptible
  ui.vec <- vector(mode = "numeric", length = graph.horizon) ## utility of infected
  uz.vec <- vector(mode = "numeric", length = graph.horizon) ## utility of recovered
  
  ## temp vars
  
  s0 <- init.s
  i0 <- init.i
  z0 <- init.z
  
  ## run the optimization and retrieve the optimal contacts per time period:
  
  x <- gov.optim(init.s = init.s, init.i = init.i, init.z = init.z,
                 init.guess = 4)
  c.vec <- head(x$par, n = horizon)
  
  for(j in 1:graph.horizon){
    
    ## retrieve the optimal contacts in the j-th period
    contact.s <- c.vec[j]
    contact.i <- c.vec[j]
    contact.z <- c.vec[j]
    
    ## Store current period information in the vectors.
    
    s.vec[j] <- s0
    i.vec[j] <- i0
    z.vec[j] <- z0
    cs.vec[j] <- contact.s
    ci.vec[j] <- contact.i
    cz.vec[j] <- contact.z
    us.vec[j] <- utility(contact.s, 0)
    ui.vec[j] <- utility(contact.i, 1)
    uz.vec[j] <- utility(contact.z, 2)
    
    ## Then move the period forward
    
    s1 <- s.t1(c.s = contact.s, c.i = contact.i, c.z = contact.z,
               s = s0, i = i0, z = z0)
    i1 <- i.t1(c.s = contact.s, c.i = contact.i, c.z = contact.z,
               s = s0, i = i0, z = z0)
    z1 <- z.t1(z = z0, i = i0)
    
    s0 <- s1
    i0 <- i1
    z0 <- z1
    
  }
  
  return(new("SocTracker",
             s=s.vec, i=i.vec, z=z.vec,
             cs = cs.vec, ci = ci.vec, cz = cz.vec,
             us = us.vec, ui = ui.vec, uz = uz.vec))
  
}

## Store results for initial values that we put in the paper...

govresults <- gov(init.s = 0.999, init.i = 0.001, init.z = 0)

## Plot some graphs

t <- c(1:150)
data.gov <- data.frame(t, govresults@s, govresults@i,
                       govresults@z, govresults@cs,
                       govresults@ci,
                       govresults@cz, govresults@us,
                       govresults@ui, govresults@uz)

## calculate weighted utility levels in each time period

data.gov <- data.gov %>%
  mutate(wus = govresults.s * govresults.us) %>%
  mutate(wui = govresults.i * govresults.ui) %>%
  mutate(wuz = govresults.z * govresults.uz)

## add discounting factor

data.gov <- data.gov %>%
  mutate(rho = head(rho.vec, 150))

## calculated total discounted + weighted utility levels

data.gov <- data.gov %>%
  mutate(tu = rho * (wus + wui + wuz))

## sum it up

tutil.gov <- sum(data.gov$tu)

ggplot(data.gov, aes(x = t, y = govresults.i)) +
  geom_line(color = "#69b3a2", size = 2, alpha = 0.9) +
  theme_dark()+
  ggtitle("Trajectory of Disease Prevalence under decentralized decision making") +
  xlab("Time (days)") +
  ylab("Disease Prevalence (%)")

plot(data.gov)

## -------------------------------------------------------
##
## Social Planner with Minimum Contact constraint
##
## -------------------------------------------------------

## --------------------
## What is the trajectory of the pandemic for a vector of
## contacts from t = 0 to t = T?

soc3.trajectory <- function(contacts.vector, init.s, init.i, init.z){
  
  ## contacts.vector consists of: c.s[1], c.s[2], ..., c.i[1], c.i[2], ..., c.z[1], ...
  
  ## check if it is divisible by 3
  if(length(contacts.vector) %% 3 != 0) stop("contacts vector is not div by 3")
  
  rl <- length(contacts.vector)/3
  
  ## define temporary variables
  s <- init.s
  i <- init.i
  z <- init.z
  utotal <- 0
  
  ## (we don't have to track the utility level of each individual now
  ## the social planner only cares about aggregate utility)
  
  for(j in 1:rl){
    
    discount <- (1-rho)^(j-1)
    
    ## retrieve contact values
    
    cs <- contacts.vector[j]
    ci <- contacts.vector[j+rl]
    cz <- contacts.vector[j+(2*rl)]
    
    ## compute next period pandemic trajectory
    
    s1 <- s.t1(c.s = cs, c.i = ci, c.z = cz, s=s, i=i, z=z)
    i1 <- i.t1(c.s = cs, c.i = ci, c.z = cz, s=s, i=i, z=z)
    z1 <- z.t1(z=z, i=i)
    
    ## compute current period utility
    
    us <- s*utility(c = cs, h = 0)
    ui <- i*utility(c = ci, h = 1)
    uz <- z*utility(c = cz, h = 2)
    
    ## compute discounted current period utility
    
    u <- discount*(us + ui + uz)
    utotal <- utotal + u
    
    ## update next period infection state
    
    s <- s1
    i <- i1
    z <- z1
    
  }
  
  ## return total utility
  
  return(utotal)
  
}

soc3.optim <- function(init.s, init.i, init.z, init.guess.cs, init.guess.ci, init.guess.cz){
  
  ## horizon is a global parameter that can be changed for
  ## robustness, or to speed up the optimization.
  ## BFGS is chosen because of robustness, and because we believe
  ## that the optimal level of contacts should follow some smooth (differentiable perhaps)
  ## intertemporal relationship (BFGS works best on smooth
  ## hypersurfaces)
  x <- optim(par = c(rep(init.guess.cs, horizon),
                     rep(init.guess.ci, horizon),
                     rep(init.guess.cz, horizon)),
             fn = soc3.trajectory,
             init.s = init.s, init.i = init.i, init.z = init.z,
             method = "L-BFGS-B",
             control = list(fnscale = -1, maxit = 100),
             lower = rep(3, horizon),
             upper = rep(Inf, horizon),
             hessian = FALSE)
  
  return (x)
  
}

## --------------------
## 150-day horizon

## Now let the economy work out itself based on the optimized
## values of contacts and see what happens.

setClass(Class="Soc3Tracker",
         representation(
           s="numeric",
           i="numeric",
           z="numeric",
           cs="numeric",
           ci="numeric",
           cz="numeric",
           us="numeric",
           ui="numeric",
           uz="numeric"
         )
)

soc3 <- function(init.s = 0.999, init.i = 0.001, init.z = 0, graph.horizon = 150){
  
  s.vec <- vector(mode = "numeric", length = graph.horizon)
  i.vec <- vector(mode = "numeric", length = graph.horizon)
  z.vec <- vector(mode = "numeric", length = graph.horizon)
  
  cs.vec <- vector(mode = "numeric", length = graph.horizon) ## contacts of susceptible
  ci.vec <- vector(mode = "numeric", length = graph.horizon) ## contacts of infected
  cz.vec <- vector(mode = "numeric", length = graph.horizon) ## contacts of recovered
  
  us.vec <- vector(mode = "numeric", length = graph.horizon) ## utility of susceptible
  ui.vec <- vector(mode = "numeric", length = graph.horizon) ## utility of infected
  uz.vec <- vector(mode = "numeric", length = graph.horizon) ## utility of recovered
  
  ## temp vars
  
  s0 <- init.s
  i0 <- init.i
  z0 <- init.z
  
  ## run the optimization and retrieve the optimal contacts per time period:
  
  x <- soc3.optim(init.s = init.s, init.i = init.i, init.z = init.z,
                 init.guess.cs = 5, init.guess.ci = 0.01, init.guess.cz = 5)
  c.vec <- head(x$par, n = 3*horizon)
  
  for(j in 1:graph.horizon){
    
    ## retrieve the optimal contacts in the j-th period
    contact.s <- c.vec[j]
    contact.i <- c.vec[j+horizon]
    contact.z <- c.vec[j+2*horizon]
    
    ## Store current period information in the vectors.
    
    s.vec[j] <- s0
    i.vec[j] <- i0
    z.vec[j] <- z0
    cs.vec[j] <- contact.s
    ci.vec[j] <- contact.i
    cz.vec[j] <- contact.z
    us.vec[j] <- utility(contact.s, 0)
    ui.vec[j] <- utility(contact.i, 1)
    uz.vec[j] <- utility(contact.z, 2)
    
    ## Then move the period forward
    
    s1 <- s.t1(c.s = contact.s, c.i = contact.i, c.z = contact.z,
               s = s0, i = i0, z = z0)
    i1 <- i.t1(c.s = contact.s, c.i = contact.i, c.z = contact.z,
               s = s0, i = i0, z = z0)
    z1 <- z.t1(z = z0, i = i0)
    
    s0 <- s1
    i0 <- i1
    z0 <- z1
    
  }
  
  return(new("Soc3Tracker",
             s=s.vec, i=i.vec, z=z.vec,
             cs = cs.vec, ci = ci.vec, cz = cz.vec,
             us = us.vec, ui = ui.vec, uz = uz.vec))
  
}

## Store results for initial values that we put in the paper...

soc3results <- soc3(init.s = 0.999, init.i = 0.001, init.z = 0)

## Plot some graphs

t <- c(1:150)
data.soc3 <- data.frame(t, soc3results@s, soc3results@i,
                       soc3results@z, soc3results@cs,
                       soc3results@ci,
                       soc3results@cz, soc3results@us,
                       soc3results@ui, soc3results@uz)

## calculate weighted utility levels in each time period

data.soc3 <- data.soc3 %>%
  mutate(wus = soc3results.s * soc3results.us) %>%
  mutate(wui = soc3results.i * soc3results.ui) %>%
  mutate(wuz = soc3results.z * soc3results.uz)

## add discounting factor

data.soc3 <- data.soc3 %>%
  mutate(rho = head(rho.vec, 150))

## calculated total discounted + weighted utility levels

data.soc3 <- data.soc3 %>%
  mutate(tu = rho * (wus + wui + wuz))

## sum it up

tutil.soc3 <- sum(data.soc3$tu)

ggplot(data.soc3, aes(x = t, y = soc3results.uz)) +
  geom_line(color = "#69b3a2", size = 2, alpha = 0.9) +
  theme_dark()+
  ggtitle("Trajectory of Disease Prevalence under decentralized decision making") +
  xlab("Time (days)") +
  ylab("Disease Prevalence (%)")

## -------------------------------------------------------
##
## Changing the Contact Function
##
## -------------------------------------------------------

## All we need to do is to change the contact function and rerun the code.

c.si <- function(c.s, c.i = 5, c.z = 5, s, i, z){
  return(delta*c.s*c.i)
}
prob.si <- function(cs, ci = 5, cz = 5, s, i, z){
  return(delta*cs*ci*beta*i)
}
horizon <- 500

## -----------------------------
## ddm

## slightly alter the optimization function for robustness

ddm.optim <- function(init.s, init.i, init.z, init.guess){
  
  x <- hjkb(par = rep(init.guess, horizon),
           fn = ddm.trajectory,
           lower = 0,
           upper = 5,
           control = list(tol = 10^(-8),
                          maximize = TRUE,
                          maxfeval = 10^10),
           init.s = init.s,
           init.i = init.i,
           init.z = init.z)
  
  return (x)
  
}

d.c1 <- ddm(init.s = 0.999, init.i = 0.001, init.z = 0)

## Plot some graphs

t <- c(1:150)
data.dc1 <- data.frame(t, d.c1@s, d.c1@i,
                                 d.c1@z, d.c1@cs,
                                 d.c1@ci,
                                 d.c1@cz, d.c1@us,
                                 d.c1@ui, d.c1@uz)

## calculate weighted utility levels in each time period

data.dc1 <- data.dc1 %>%
  mutate(wus = d.c1.s * d.c1.us) %>%
  mutate(wui = d.c1.i * d.c1.ui) %>%
  mutate(wuz = d.c1.z * d.c1.uz)

## add discounting factor

data.dc1 <- data.dc1 %>%
  mutate(rho = rho.vec)

## calculated total discounted + weighted utility levels

data.dc1 <- data.dc1 %>%
  mutate(tu = rho * (wus + wui + wuz))

## sum it up

tutil.dc1 <- sum(data.dc1$tu)

ggplot(data.dc1, aes(x = t, y = d.c1.s)) +
  geom_line(color = "#69b3a2", size = 2, alpha = 0.9) +
  theme_dark()+
  ggtitle("Trajectory of Disease Prevalence under decentralized decision making") +
  xlab("Time (days)") +
  ylab("Disease Prevalence (%)")

plot(data.dc1)

## -----------------------------
## social planner

## slightly alter the optimization function for robustness

soc.optim <- function(init.s, init.i, init.z, init.guess.cs, init.guess.ci, init.guess.cz){
  
  x <- hjkb(par = c(rep(init.guess.cs, horizon),
                     rep(init.guess.ci, horizon),
                     rep(init.guess.cz, horizon)),
             fn = soc.trajectory,
             lower = 0,
             upper = 5,
            control = list(tol = 10^(-8),
                           maximize = TRUE,
                           maxfeval = 10^10),
            init.s = init.s,
            init.i = init.i,
            init.z = init.z)
  
  return (x)
  
}

s.c1 <- soc(init.s = 0.999, init.i = 0.001, init.z = 0)

## Plot some graphs

t <- c(1:150)
data.sc1 <- data.frame(t, s.c1@s, s.c1@i,
                       s.c1@z, s.c1@cs,
                       s.c1@ci,
                       s.c1@cz, s.c1@us,
                       s.c1@ui, s.c1@uz)

## calculate weighted utility levels in each time period

data.sc1 <- data.sc1 %>%
  mutate(wus = s.c1.s * s.c1.us) %>%
  mutate(wui = s.c1.i * s.c1.ui) %>%
  mutate(wuz = s.c1.z * s.c1.uz)

## add discounting factor

data.sc1 <- data.sc1 %>%
  mutate(rho = rho.vec)

## calculated total discounted + weighted utility levels

data.sc1 <- data.sc1 %>%
  mutate(tu = rho * (wus + wui + wuz))

## sum it up

tutil.sc1 <- sum(data.sc1$tu)

ggplot(data.sc1, aes(x = t, y = s.c1.i)) +
  geom_line(color = "#69b3a2", size = 2, alpha = 0.9) +
  theme_dark()+
  ggtitle("Trajectory of Disease Prevalence under decentralized decision making") +
  xlab("Time (days)") +
  ylab("Disease Prevalence (%)")

plot(data.sc1)

## -----------------------------
## gov with info constraint

## slightly alter the optimization function for robustness

gov.optim <- function(init.s, init.i, init.z, init.guess.cs, init.guess.ci, init.guess.cz){
  
  x <- hjkb(par = rep(init.guess, horizon),
            fn = gov.trajectory,
            lower = 0,
            upper = 5,
            control = list(tol = 10^(-8),
                           maximize = TRUE,
                           maxfeval = 10^10),
            init.s = init.s,
            init.i = init.i,
            init.z = init.z)
  
  return (x)
  
}

gov.c1 <- gov(init.s = 0.999, init.i = 0.001, init.z = 0)

## Plot some graphs

t <- c(1:150)
data.govc1 <- data.frame(t, gov.c1@s, gov.c1@i,
                       gov.c1@z, gov.c1@cs,
                       gov.c1@ci,
                       gov.c1@cz, gov.c1@us,
                       gov.c1@ui, gov.c1@uz)

## calculate weighted utility levels in each time period

data.govc1 <- data.govc1 %>%
  mutate(wus = gov.c1.s * gov.c1.us) %>%
  mutate(wui = gov.c1.i * gov.c1.ui) %>%
  mutate(wuz = gov.c1.z * gov.c1.uz)

## add discounting factor

data.govc1 <- data.govc1 %>%
  mutate(rho = rho.vec)

## calculated total discounted + weighted utility levels

data.govc1 <- data.govc1 %>%
  mutate(tu = rho * (wus + wui + wuz))

## sum it up

tutil.govc1 <- sum(data.govc1$tu)

ggplot(data.govc1, aes(x = t, y = gov.c1.cs)) +
  geom_line(color = "#69b3a2", size = 2, alpha = 0.9) +
  theme_dark()+
  ggtitle("Trajectory of Disease Prevalence under decentralized decision making") +
  xlab("Time (days)") +
  ylab("Disease Prevalence (%)")

plot(data.govc1)

## -----------------------------
## soc planner with 3 contact constraint

## slightly alter the optimization function for robustness

soc3.optim <- function(init.s, init.i, init.z, init.guess.cs, init.guess.ci, init.guess.cz){
  
  x <- hjkb(par = c(rep(init.guess.cs, horizon),
                    rep(init.guess.ci, horizon),
                    rep(init.guess.cz, horizon)),
            fn = soc3.trajectory,
            lower = 3,
            upper = 10,
            control = list(tol = 10^(-8),
                           maximize = TRUE,
                           maxfeval = 10^10),
            init.s = init.s,
            init.i = init.i,
            init.z = init.z)
  
  return (x)
  
}

soc3.c1 <- soc3(init.s = 0.999, init.i = 0.001, init.z = 0)

## Plot some graphs

t <- c(1:150)
data.soc3c1 <- data.frame(t, soc3.c1@s, soc3.c1@i,
                         soc3.c1@z, soc3.c1@cs,
                         soc3.c1@ci,
                         soc3.c1@cz, soc3.c1@us,
                         soc3.c1@ui, soc3.c1@uz)

## calculate weighted utility levels in each time period

data.soc3c1 <- data.soc3c1 %>%
  mutate(wus = soc3.c1.s * soc3.c1.us) %>%
  mutate(wui = soc3.c1.i * soc3.c1.ui) %>%
  mutate(wuz = soc3.c1.z * soc3.c1.uz)

## add discounting factor

data.soc3c1 <- data.soc3c1 %>%
  mutate(rho = rho.vec)

## calculated total discounted + weighted utility levels

data.soc3c1 <- data.soc3c1 %>%
  mutate(tu = rho * (wus + wui + wuz))

## sum it up

tutil.soc3c1 <- sum(data.soc3c1$tu)

ggplot(data.soc3c1, aes(x = t, y = soc3.c1.z)) +
  geom_line(color = "#69b3a2", size = 2, alpha = 0.9) +
  theme_dark()+
  ggtitle("Trajectory of Disease Prevalence under decentralized decision making") +
  xlab("Time (days)") +
  ylab("Disease Prevalence (%)")

plot(data.soc3c1)

## -------------------------------------------------------
##
## Changing the Contact Function: Part 2
##
## -------------------------------------------------------

## Define phi as discussed in the paper:

phi <- delta

## All we need to do is to change the contact function and rerun the code.

c.si <- function(c.s, c.i = 5, c.z = 5, s, i, z){
  return(phi*((c.s*c.i)/(s+i+digamma*z*c.z)))
}
prob.si <- function(cs, ci = 5, cz = 5, s, i, z){
  return(phi*beta*i*((cs*ci)/(s+i+digamma*z*cz)))
}
horizon <- 500

## -----------------------------
## ddm (digamma = 1/C^z)

d.c2 <- ddm(init.s = 0.999, init.i = 0.001, init.z = 0)

## Plot some graphs

t <- c(1:150)
data.dc2 <- data.frame(t, d.c2@s, d.c2@i,
                       d.c2@z, d.c2@cs,
                       d.c2@ci,
                       d.c2@cz, d.c2@us,
                       d.c2@ui, d.c2@uz)

## calculate weighted utility levels in each time period

data.dc2 <- data.dc2 %>%
  mutate(wus = d.c2.s * d.c2.us) %>%
  mutate(wui = d.c2.i * d.c2.ui) %>%
  mutate(wuz = d.c2.z * d.c2.uz)

## add discounting factor

data.dc2 <- data.dc2 %>%
  mutate(rho = rho.vec)

## calculated total discounted + weighted utility levels

data.dc2 <- data.dc2 %>%
  mutate(tu = rho * (wus + wui + wuz))

## sum it up

tutil.dc2 <- sum(data.dc2$tu)

ggplot(data.dc2, aes(x = t, y = d.c2.cs)) +
  geom_line(color = "#69b3a2", size = 2, alpha = 0.9) +
  theme_dark()+
  ggtitle("Trajectory of Disease Prevalence under decentralized decision making") +
  xlab("Time (days)") +
  ylab("Disease Prevalence (%)")

plot(data.dc2)

## -----------------------------
## ddm (digamma = 1.5/C^z)

digamma <- 1.5/optimal.c

d.c3 <- ddm(init.s = 0.999, init.i = 0.001, init.z = 0)

## Plot some graphs

t <- c(1:150)
data.dc3 <- data.frame(t, d.c3@s, d.c3@i,
                       d.c3@z, d.c3@cs,
                       d.c3@ci,
                       d.c3@cz, d.c3@us,
                       d.c3@ui, d.c3@uz)

## calculate weighted utility levels in each time period

data.dc3 <- data.dc3 %>%
  mutate(wus = d.c3.s * d.c3.us) %>%
  mutate(wui = d.c3.i * d.c3.ui) %>%
  mutate(wuz = d.c3.z * d.c3.uz)

## add discounting factor

data.dc3 <- data.dc3 %>%
  mutate(rho = rho.vec)

## calculated total discounted + weighted utility levels

data.dc3 <- data.dc3 %>%
  mutate(tu = rho * (wus + wui + wuz))

## sum it up

tutil.dc3 <- sum(data.dc3$tu)

ggplot(data.dc3, aes(x = t, y = d.c3.z)) +
  geom_line(color = "#69b3a2", size = 2, alpha = 0.9) +
  theme_dark()+
  ggtitle("Trajectory of Disease Prevalence under decentralized decision making") +
  xlab("Time (days)") +
  ylab("Disease Prevalence (%)")

plot(data.dc3)

## -----------------------------
## ddm (digamma = 2/C^z)

digamma <- 2/optimal.c

d.c4 <- ddm(init.s = 0.999, init.i = 0.001, init.z = 0)

## Plot some graphs

t <- c(1:150)
data.dc4 <- data.frame(t, d.c4@s, d.c4@i,
                       d.c4@z, d.c4@cs,
                       d.c4@ci,
                       d.c4@cz, d.c4@us,
                       d.c4@ui, d.c4@uz)

## calculate weighted utility levels in each time period

data.dc4 <- data.dc4 %>%
  mutate(wus = d.c4.s * d.c4.us) %>%
  mutate(wui = d.c4.i * d.c4.ui) %>%
  mutate(wuz = d.c4.z * d.c4.uz)

## add discounting factor

data.dc4 <- data.dc4 %>%
  mutate(rho = rho.vec)

## calculated total discounted + weighted utility levels

data.dc4 <- data.dc4 %>%
  mutate(tu = rho * (wus + wui + wuz))

## sum it up

tutil.dc4 <- sum(data.dc4$tu)

ggplot(data.dc4, aes(x = t, y = d.c4.z)) +
  geom_line(color = "#69b3a2", size = 2, alpha = 0.9) +
  theme_dark()+
  ggtitle("Trajectory of Disease Prevalence under decentralized decision making") +
  xlab("Time (days)") +
  ylab("Disease Prevalence (%)")

plot(data.dc4)

## -----------------------------
## social planner (digamma = 1/C^z)

digamma <- 1/optimal.c

## slightly alter the optimization function for robustness

s.c2 <- soc(init.s = 0.999, init.i = 0.001, init.z = 0)

## Plot some graphs

t <- c(1:150)
data.sc2 <- data.frame(t, s.c2@s, s.c2@i,
                       s.c2@z, s.c2@cs,
                       s.c2@ci,
                       s.c2@cz, s.c2@us,
                       s.c2@ui, s.c2@uz)

## calculate weighted utility levels in each time period

data.sc2 <- data.sc2 %>%
  mutate(wus = s.c2.s * s.c2.us) %>%
  mutate(wui = s.c2.i * s.c2.ui) %>%
  mutate(wuz = s.c2.z * s.c2.uz)

## add discounting factor

data.sc2 <- data.sc2 %>%
  mutate(rho = rho.vec)

## calculated total discounted + weighted utility levels

data.sc2 <- data.sc2 %>%
  mutate(tu = rho * (wus + wui + wuz))

## sum it up

tutil.sc2 <- sum(data.sc2$tu)

ggplot(data.sc2, aes(x = t, y = s.c2.i)) +
  geom_line(color = "#69b3a2", size = 2, alpha = 0.9) +
  theme_dark()+
  ggtitle("Trajectory of Disease Prevalence under decentralized decision making") +
  xlab("Time (days)") +
  ylab("Disease Prevalence (%)")

plot(data.sc2)

## -----------------------------
## social planner (digamma = 1.5/C^z)

digamma <- 1.5/optimal.c

## slightly alter the optimization function for robustness

s.c3 <- soc(init.s = 0.999, init.i = 0.001, init.z = 0)

## Plot some graphs

t <- c(1:150)
data.sc3 <- data.frame(t, s.c3@s, s.c3@i,
                       s.c3@z, s.c3@cs,
                       s.c3@ci,
                       s.c3@cz, s.c3@us,
                       s.c3@ui, s.c3@uz)

## calculate weighted utility levels in each time period

data.sc3 <- data.sc3 %>%
  mutate(wus = s.c3.s * s.c3.us) %>%
  mutate(wui = s.c3.i * s.c3.ui) %>%
  mutate(wuz = s.c3.z * s.c3.uz)

## add discounting factor

data.sc3 <- data.sc3 %>%
  mutate(rho = rho.vec)

## calculated total discounted + weighted utility levels

data.sc3 <- data.sc3 %>%
  mutate(tu = rho * (wus + wui + wuz))

## sum it up

tutil.sc3 <- sum(data.sc3$tu)

ggplot(data.sc3, aes(x = t, y = s.c3.i)) +
  geom_line(color = "#69b3a2", size = 2, alpha = 0.9) +
  theme_dark()+
  ggtitle("Trajectory of Disease Prevalence under decentralized decision making") +
  xlab("Time (days)") +
  ylab("Disease Prevalence (%)")

plot(data.sc3)

## -----------------------------
## social planner (digamma = 2/C^z)

digamma <- 2/optimal.c

## slightly alter the optimization function for robustness

s.c4 <- soc(init.s = 0.999, init.i = 0.001, init.z = 0)

## Plot some graphs

t <- c(1:150)
data.sc4 <- data.frame(t, s.c4@s, s.c4@i,
                       s.c4@z, s.c4@cs,
                       s.c4@ci,
                       s.c4@cz, s.c4@us,
                       s.c4@ui, s.c4@uz)

## calculate weighted utility levels in each time period

data.sc4 <- data.sc4 %>%
  mutate(wus = s.c4.s * s.c4.us) %>%
  mutate(wui = s.c4.i * s.c4.ui) %>%
  mutate(wuz = s.c4.z * s.c4.uz)

## add discounting factor

data.sc4 <- data.sc4 %>%
  mutate(rho = rho.vec)

## calculated total discounted + weighted utility levels

data.sc4 <- data.sc4 %>%
  mutate(tu = rho * (wus + wui + wuz))

## sum it up

tutil.sc4 <- sum(data.sc4$tu)

ggplot(data.sc4, aes(x = t, y = s.c4.i)) +
  geom_line(color = "#69b3a2", size = 2, alpha = 0.9) +
  theme_dark()+
  ggtitle("Trajectory of Disease Prevalence under decentralized decision making") +
  xlab("Time (days)") +
  ylab("Disease Prevalence (%)")

plot(data.sc4)


## -----------------------------
## gov with info constraint (digamma = 1/C^z)

digamma <- 1/optimal.c

gov.c2 <- gov(init.s = 0.999, init.i = 0.001, init.z = 0)

## Plot some graphs

t <- c(1:150)
data.govc2 <- data.frame(t, gov.c2@s, gov.c2@i,
                         gov.c2@z, gov.c2@cs,
                         gov.c2@ci,
                         gov.c2@cz, gov.c2@us,
                         gov.c2@ui, gov.c2@uz)

## calculate weighted utility levels in each time period

data.govc2 <- data.govc2 %>%
  mutate(wus = gov.c2.s * gov.c2.us) %>%
  mutate(wui = gov.c2.i * gov.c2.ui) %>%
  mutate(wuz = gov.c2.z * gov.c2.uz)

## add discounting factor

data.govc2 <- data.govc2 %>%
  mutate(rho = rho.vec)

## calculated total discounted + weighted utility levels

data.govc2 <- data.govc2 %>%
  mutate(tu = rho * (wus + wui + wuz))

## sum it up

tutil.govc2 <- sum(data.govc2$tu)

ggplot(data.govc2, aes(x = t, y = gov.c2.cz)) +
  geom_line(color = "#69b3a2", size = 2, alpha = 0.9) +
  theme_dark()+
  ggtitle("Trajectory of Disease Prevalence under decentralized decision making") +
  xlab("Time (days)") +
  ylab("Disease Prevalence (%)")

plot(data.govc2)

## -----------------------------
## gov with info constraint (digamma = 1.5/C^z)

digamma <- 1.5/optimal.c

gov.c3 <- gov(init.s = 0.999, init.i = 0.001, init.z = 0)

## Plot some graphs

t <- c(1:150)
data.govc3 <- data.frame(t, gov.c3@s, gov.c3@i,
                         gov.c3@z, gov.c3@cs,
                         gov.c3@ci,
                         gov.c3@cz, gov.c3@us,
                         gov.c3@ui, gov.c3@uz)

## calculate weighted utility levels in each time period

data.govc3 <- data.govc3 %>%
  mutate(wus = gov.c3.s * gov.c3.us) %>%
  mutate(wui = gov.c3.i * gov.c3.ui) %>%
  mutate(wuz = gov.c3.z * gov.c3.uz)

## add discounting factor

data.govc3 <- data.govc3 %>%
  mutate(rho = rho.vec)

## calculated total discounted + weighted utility levels

data.govc3 <- data.govc3 %>%
  mutate(tu = rho * (wus + wui + wuz))

## sum it up

tutil.govc3 <- sum(data.govc3$tu)

ggplot(data.govc3, aes(x = t, y = gov.c3.cs)) +
  geom_line(color = "#69b3a2", size = 2, alpha = 0.9) +
  theme_dark()+
  ggtitle("Trajectory of Disease Prevalence under decentralized decision making") +
  xlab("Time (days)") +
  ylab("Disease Prevalence (%)")

plot(data.govc3)

## -----------------------------
## gov with info constraint (digamma = 2/C^z)

digamma <- 2/optimal.c

gov.c4 <- gov(init.s = 0.999, init.i = 0.001, init.z = 0)

## Plot some graphs

t <- c(1:150)
data.govc4 <- data.frame(t, gov.c4@s, gov.c4@i,
                         gov.c4@z, gov.c4@cs,
                         gov.c4@ci,
                         gov.c4@cz, gov.c4@us,
                         gov.c4@ui, gov.c4@uz)

## calculate weighted utility levels in each time period

data.govc4 <- data.govc4 %>%
  mutate(wus = gov.c4.s * gov.c4.us) %>%
  mutate(wui = gov.c4.i * gov.c4.ui) %>%
  mutate(wuz = gov.c4.z * gov.c4.uz)

## add discounting factor

data.govc4 <- data.govc4 %>%
  mutate(rho = rho.vec)

## calculated total discounted + weighted utility levels

data.govc4 <- data.govc4 %>%
  mutate(tu = rho * (wus + wui + wuz))

## sum it up

tutil.govc4 <- sum(data.govc4$tu)

ggplot(data.govc4, aes(x = t, y = gov.c4.cs)) +
  geom_line(color = "#69b3a2", size = 2, alpha = 0.9) +
  theme_dark()+
  ggtitle("Trajectory of Disease Prevalence under decentralized decision making") +
  xlab("Time (days)") +
  ylab("Disease Prevalence (%)")

plot(data.govc4)

## -----------------------------
## soc planner with min 3 contacts (digamma = 1/C^z)

digamma <- 1/optimal.c

soc3.c2 <- soc3(init.s = 0.999, init.i = 0.001, init.z = 0)

## Plot some graphs

t <- c(1:150)
data.soc3c2 <- data.frame(t, soc3.c2@s, soc3.c2@i,
                          soc3.c2@z, soc3.c2@cs,
                          soc3.c2@ci,
                          soc3.c2@cz, soc3.c2@us,
                          soc3.c2@ui, soc3.c2@uz)

## calculate weighted utility levels in each time period

data.soc3c2 <- data.soc3c2 %>%
  mutate(wus = soc3.c2.s * soc3.c2.us) %>%
  mutate(wui = soc3.c2.i * soc3.c2.ui) %>%
  mutate(wuz = soc3.c2.z * soc3.c2.uz)

## add discounting factor

data.soc3c2 <- data.soc3c2 %>%
  mutate(rho = rho.vec)

## calculated total discounted + weighted utility levels

data.soc3c2 <- data.soc3c2 %>%
  mutate(tu = rho * (wus + wui + wuz))

## sum it up

tutil.soc3c2 <- sum(data.soc3c2$tu)

ggplot(data.soc3c2, aes(x = t, y = soc3.c2.s)) +
  geom_line(color = "#69b3a2", size = 2, alpha = 0.9) +
  theme_dark()+
  ggtitle("Trajectory of Disease Prevalence under decentralized decision making") +
  xlab("Time (days)") +
  ylab("Disease Prevalence (%)")

plot(data.soc3c2)

## -----------------------------
## soc planner with min 3 contacts (digamma = 1.5/C^z)

digamma <- 1.5/optimal.c

soc3.c3 <- soc3(init.s = 0.999, init.i = 0.001, init.z = 0)

## Plot some graphs

t <- c(1:150)
data.soc3c3 <- data.frame(t, soc3.c3@s, soc3.c3@i,
                          soc3.c3@z, soc3.c3@cs,
                          soc3.c3@ci,
                          soc3.c3@cz, soc3.c3@us,
                          soc3.c3@ui, soc3.c3@uz)

## calculate weighted utility levels in each time period

data.soc3c3 <- data.soc3c3 %>%
  mutate(wus = soc3.c3.s * soc3.c3.us) %>%
  mutate(wui = soc3.c3.i * soc3.c3.ui) %>%
  mutate(wuz = soc3.c3.z * soc3.c3.uz)

## add discounting factor

data.soc3c3 <- data.soc3c3 %>%
  mutate(rho = rho.vec)

## calculated total discounted + weighted utility levels

data.soc3c3 <- data.soc3c3 %>%
  mutate(tu = rho * (wus + wui + wuz))

## sum it up

tutil.soc3c3 <- sum(data.soc3c3$tu)

ggplot(data.soc3c3, aes(x = t, y = soc3.c3.s)) +
  geom_line(color = "#69b3a2", size = 2, alpha = 0.9) +
  theme_dark()+
  ggtitle("Trajectory of Disease Prevalence under decentralized decision making") +
  xlab("Time (days)") +
  ylab("Disease Prevalence (%)")

plot(data.soc3c3)

## -----------------------------
## soc planner with min 3 contacts (digamma = 2/C^z)

digamma <- 2/optimal.c

soc3.c4 <- soc3(init.s = 0.999, init.i = 0.001, init.z = 0)

## Plot some graphs

t <- c(1:150)
data.soc3c4 <- data.frame(t, soc3.c4@s, soc3.c4@i,
                          soc3.c4@z, soc3.c4@cs,
                          soc3.c4@ci,
                          soc3.c4@cz, soc3.c4@us,
                          soc3.c4@ui, soc3.c4@uz)

## calculate weighted utility levels in each time period

data.soc3c4 <- data.soc3c4 %>%
  mutate(wus = soc3.c4.s * soc3.c4.us) %>%
  mutate(wui = soc3.c4.i * soc3.c4.ui) %>%
  mutate(wuz = soc3.c4.z * soc3.c4.uz)

## add discounting factor

data.soc3c4 <- data.soc3c4 %>%
  mutate(rho = rho.vec)

## calculated total discounted + weighted utility levels

data.soc3c4 <- data.soc3c4 %>%
  mutate(tu = rho * (wus + wui + wuz))

## sum it up

tutil.soc3c4 <- sum(data.soc3c4$tu)

ggplot(data.soc3c4, aes(x = t, y = soc3.c4.cz)) +
  geom_line(color = "#69b3a2", size = 2, alpha = 0.9) +
  theme_dark()+
  ggtitle("Trajectory of Disease Prevalence under decentralized decision making") +
  xlab("Time (days)") +
  ylab("Disease Prevalence (%)")

plot(data.soc3c4)

## -------------------------------------------------------
##
## COVID-19 tuning
##
## -------------------------------------------------------

## retune everything for COVID-19

beta <- 0.025
v <- 0.05
rho <- 1 - (95/100)^(1/365)
optimal.c <- 5
infected.people.really.hate.this.number <- 2
dead.people.really.hate.this.number <- 12
horizon <- 800 ## horizon value for agent's optimization.
grahor <- 300 ## horizon value when plotting/charting trajectory
rho.vec <- (1 - rho)^(0:(grahor-1))  ## note this is 1 - discounting.
delta <- 0.2
digamma <- 1/optimal.c
theta <- 0.0002
gamma <- -2/3
b <- 24
alpha <- -(optimal.c)/(-optimal.c - b*exp(-gamma * (log(b - optimal.c) - log(optimal.c)))
                       + optimal.c * exp(-gamma * (log(b - optimal.c) - log(optimal.c))))
ubar <- (alpha*(optimal.c)^gamma + (1-alpha)*(b-optimal.c)^gamma)^(1/gamma)
mi <- ubar*infected.people.really.hate.this.number
md <- ubar*dead.people.really.hate.this.number

## -------------------------------------------------------
##
## COVID-19 basic components
##
## -------------------------------------------------------

## h = 3 means they're dead
utility <- function(c, h){
  m <- 0
  if(h == 1){ m <- mi }
  else if(h == 3){ m <- md }
  return((alpha*(c)^gamma + (1-alpha)*(b-c)^gamma)^(1/gamma)-m)
}

## utility of death
ud <- utility(optimal.c, 3)

## note that infected and recovered individuals will always choose
## to initiate 5 contacts per time period.

c.si <- function(c.s, c.i = 5, c.z = 5, s, i, z){
  return((c.s*c.i)/(s*c.s + i*c.i + z*c.z))
}
s.t1 <- function(c.s, c.i = 5, c.z = 5, s, i, z){
  return(s-c.si(c.s, c.i, c.z, s, i, z)*beta*s*i)
}
i.t1 <- function(c.s, c.i = 5, c.z = 5, s, i, z){
  return(i + c.si(c.s, c.i, c.z, s, i, z)*beta*s*i - v*i - theta*i)
}
z.t1 <- function(z, i){
  return(z + v*i)
}
d.t1 <- function(d, i){
  return(d + theta*i)
}

## calculate P{s, i}(.)

prob.si <- function(cs, ci = 5, cz = 5, s, i, z){
  return((cs*ci*beta*i)/(s*cs + i*ci + z*cz))
}

## -------------------------------------------------------
##
## COVID-19 trajectory simulation
##
## -------------------------------------------------------

## -------------------------------------------
## decentralized

ddm.trajectory <- function(contacts.vector, init.s, init.i, init.z, c.i=5, c.z=5){
  
  ## define temporary variables
  s <- init.s
  i <- init.i
  z <- init.z
  d <- 0
  utotal <- 0
  
  ## define susceptible individual's expected medical state
  
  sus <- 1
  inf <- 0
  rec <- 0
  ded <- 0
  
  for(j in 1:length(contacts.vector)){
    
    discount <- (1-rho)^(j-1)
    
    ## compute next period pandemic trajectory
    
    s1 <- s.t1(contacts.vector[j], c.i=c.i, c.z=c.z, s=s, i=i, z=z)
    i1 <- i.t1(contacts.vector[j], c.i=c.i, c.z=c.z, s=s, i=i, z=z)
    z1 <- z.t1(z=z, i=i)
    d1 <- d.t1(d=d, i=i)
    
    ## compute current period utility
    
    ## first compute expected utility in each possible medical state, weighted
    ## by the probability
    
    usus <- sus*utility(c = contacts.vector[j], h = 0)
    uinf <- inf*utility(c = contacts.vector[j], h = 1)
    urec <- rec*utility(c = contacts.vector[j], h = 2)
    uded <- ded*ud
    
    ## then calculate the probability of the individual of being in each medical state
    ## in the next period. Note we use v*inf instead of v*i
    
    sus <- sus - prob.si(contacts.vector[j], s=s, i=i, z=z)
    inf <- inf + prob.si(contacts.vector[j], s=s, i=i, z=z) - v*inf - theta*inf
    rec <- rec + v*inf
    ded <- ded + theta*inf
    
    ## compute discounted current period utility
    
    u <- discount*(usus + uinf + urec + uded)
    utotal <- utotal + u
    
    ## update next period infection state
    
    s <- s1
    i <- i1
    z <- z1
    d <- d1
    
  }
  
  ## return total utility
  
  return(utotal)
  
}

ddm.optim <- function(init.s, init.i, init.z, init.guess){
  
  x <- optim(par = rep(init.guess, horizon),
             fn = ddm.trajectory,
             init.s = init.s, init.i = init.i, init.z = init.z,
             method = "BFGS",
             control = list(fnscale = -1, maxit = 100),
             hessian = FALSE)
  
  return (x)
  
}

setClass(Class="DecentralizedTracker",
         representation(
           s="numeric",
           i="numeric",
           z="numeric",
           d="numeric",
           cs="numeric",
           ci="numeric",
           cz="numeric",
           us="numeric",
           ui="numeric",
           uz="numeric",
           ud="numeric"
         )
)

## Now let the economy work out itself based on the optimized
## values of contacts and see what happens.

ddm <- function(init.s = 0.999, init.i = 0.001, init.z = 0,
                c.i = 5, c.z = 5, graph.horizon = 250){
  
  s.vec <- vector(mode = "numeric", length = graph.horizon)
  i.vec <- vector(mode = "numeric", length = graph.horizon)
  z.vec <- vector(mode = "numeric", length = graph.horizon)
  d.vec <- vector(mode = "numeric", length = graph.horizon)
  
  cs.vec <- vector(mode = "numeric", length = graph.horizon) ## contacts of susceptible
  ci.vec <- rep(c.i, graph.horizon) ## contacts of infected
  cz.vec <- rep(c.z, graph.horizon) ## contacts of recovered
  
  us.vec <- vector(mode = "numeric", length = graph.horizon) ## utility of susceptible
  ui.vec <- rep(utility(c.i, 1), graph.horizon) ## utility of infected
  uz.vec <- rep(utility(c.z, 2), graph.horizon) ## utility of recovered
  ud.vec <- rep(ud, graph.horizon) ## utility of recovered
  
  ## temp vars
  
  s0 <- init.s
  i0 <- init.i
  z0 <- init.z
  d0 <- 0
  
  ## run the optimization and retrieve the optimal contacts per time period:
  
  x <- ddm.optim(init.s = init.s, init.i = init.i, init.z = init.z,
                 init.guess = 4)
  cs.vec <- head(x$par, n = graph.horizon)
  
  for(j in 1:graph.horizon){
    
    ## retrieve the optimal contacts in the j-th period
    contact.s <- cs.vec[j]
    
    ## Store current period information in the vectors.
    
    s.vec[j] <- s0
    i.vec[j] <- i0
    z.vec[j] <- z0
    d.vec[j] <- d0
    cs.vec[j] <- contact.s
    us.vec[j] <- utility(contact.s, 0)
    
    ## Then move the period forward
    
    s1 <- s.t1(c.s = contact.s, s = s0, i = i0, z = z0)
    i1 <- i.t1(c.s = contact.s, s = s0, i = i0, z = z0)
    z1 <- z.t1(z = z0, i = i0)
    d1 <- d.t1(d = d0, i = i0)
    
    s0 <- s1
    i0 <- i1
    z0 <- z1
    d0 <- d1
    
  }
  
  return(new("DecentralizedTracker",
             s=s.vec, i=i.vec, z=z.vec, d=d.vec,
             cs = cs.vec, ci = ci.vec, cz = cz.vec,
             us = us.vec, ui = ui.vec, uz = uz.vec,
             ud = ud.vec))
  
}

## Store results for initial values that we put in the paper...

dcovid1 <- ddm(init.s = 0.999, init.i = 0.001, init.z = 0)
rho.vec <- (1 - rho)^(0:(250-1))
t <- c(1:250)
data.dcovid1 <- data.frame(t, dcovid1@s, dcovid1@i,
                                 dcovid1@z, dcovid1@d,
                           dcovid1@cs,
                                 dcovid1@ci, 
                                 dcovid1@cz, dcovid1@us,
                                 dcovid1@ui, dcovid1@uz, dcovid1@ud)
data.dcovid1 <- data.dcovid1 %>%
  mutate(wus = dcovid1.s * dcovid1.us) %>%
  mutate(wui = dcovid1.i * dcovid1.ui) %>%
  mutate(wuz = dcovid1.z * dcovid1.uz) %>%
  mutate(wud = dcovid1.d * dcovid1.ud)
data.dcovid1 <- data.dcovid1 %>%
  mutate(rho = rho.vec)
data.dcovid1 <- data.dcovid1 %>%
  mutate(tu = rho * (wus + wui + wuz + wud))
tutil.dcovid1 <- sum(data.dcovid1$tu)

ggplot(data.dcovid1, aes(x = t, y = dcovid1.i)) +
  geom_line(color = "#69b3a2", size = 2, alpha = 0.9) +
  theme_dark()+
  ggtitle("Trajectory of Disease Prevalence under dcovid1 decision making") +
  xlab("Time (days)") +
  ylab("Disease Prevalence (%)")

plot(data.dcovid1)

## -------------------------------------------------------
##
## Social Planner
##
## -------------------------------------------------------

## --------------------
## What is the trajectory of the pandemic for a vector of
## contacts from t = 0 to t = T?

soc.trajectory <- function(contacts.vector, init.s, init.i, init.z){
  
  ## contacts.vector consists of: c.s[1], c.s[2], ..., c.i[1], c.i[2], ..., c.z[1], ...
  
  ## check if it is divisible by 3
  if(length(contacts.vector) %% 3 != 0) stop("contacts vector is not div by 3")
  
  rl <- length(contacts.vector)/3
  
  ## define temporary variables
  s <- init.s
  i <- init.i
  z <- init.z
  d <- 0
  utotal <- 0
  
  ## (we don't have to track the utility level of each individual now
  ## the social planner only cares about aggregate utility)
  
  for(j in 1:rl){
    
    discount <- (1-rho)^(j-1)
    
    ## retrieve contact values
    
    cs <- contacts.vector[j]
    ci <- contacts.vector[j+rl]
    cz <- contacts.vector[j+(2*rl)]
    
    ## compute next period pandemic trajectory
    
    s1 <- s.t1(c.s = cs, c.i = ci, c.z = cz, s=s, i=i, z=z)
    i1 <- i.t1(c.s = cs, c.i = ci, c.z = cz, s=s, i=i, z=z)
    z1 <- z.t1(z=z, i=i)
    d1 <- d.t1(d=d, i=i)
    
    ## compute current period utility
    
    us <- s*utility(c = cs, h = 0)
    ui <- i*utility(c = ci, h = 1)
    uz <- z*utility(c = cz, h = 2)
    uded <- d*ud
    
    ## compute discounted current period utility
    
    u <- discount*(us + ui + uz + uded)
    utotal <- utotal + u
    
    ## update next period infection state
    
    s <- s1
    i <- i1
    z <- z1
    d <- d1
    
  }
  
  ## return total utility
  
  return(utotal)
  
}

soc.optim <- function(init.s, init.i, init.z, init.guess.cs, init.guess.ci, init.guess.cz){
  
  x <- optim(par = c(rep(init.guess.cs, horizon),
                     rep(init.guess.ci, horizon),
                     rep(init.guess.cz, horizon)),
             fn = soc.trajectory,
             init.s = init.s, init.i = init.i, init.z = init.z,
             method = "BFGS",
             control = list(fnscale = -1, maxit = 100),
             hessian = FALSE)
  
  return (x)
  
}

setClass(Class="SocTracker",
         representation(
           s="numeric",
           i="numeric",
           z="numeric",
           d="numeric",
           cs="numeric",
           ci="numeric",
           cz="numeric",
           us="numeric",
           ui="numeric",
           uz="numeric",
           ud="numeric"
         )
)

soc <- function(init.s = 0.999, init.i = 0.001, init.z = 0, graph.horizon = 250){
  
  s.vec <- vector(mode = "numeric", length = graph.horizon)
  i.vec <- vector(mode = "numeric", length = graph.horizon)
  z.vec <- vector(mode = "numeric", length = graph.horizon)
  d.vec <- vector(mode = "numeric", length = graph.horizon)
  
  cs.vec <- vector(mode = "numeric", length = graph.horizon) ## contacts of susceptible
  ci.vec <- vector(mode = "numeric", length = graph.horizon) ## contacts of infected
  cz.vec <- vector(mode = "numeric", length = graph.horizon) ## contacts of recovered
  
  us.vec <- vector(mode = "numeric", length = graph.horizon) ## utility of susceptible
  ui.vec <- vector(mode = "numeric", length = graph.horizon) ## utility of infected
  uz.vec <- vector(mode = "numeric", length = graph.horizon) ## utility of recovered
  ud.vec <- rep(ud, n = graph.horizon)
  
  ## temp vars
  
  s0 <- init.s
  i0 <- init.i
  z0 <- init.z
  d0 <- 0
  
  ## run the optimization and retrieve the optimal contacts per time period:
  
  x <- soc.optim(init.s = init.s, init.i = init.i, init.z = init.z,
                 init.guess.cs = 5, init.guess.ci = 0.01, init.guess.cz = 5)
  c.vec <- head(x$par, n = 3*horizon)
  
  for(j in 1:graph.horizon){
    
    ## retrieve the optimal contacts in the j-th period
    contact.s <- c.vec[j]
    contact.i <- c.vec[j+horizon]
    contact.z <- c.vec[j+2*horizon]
    
    ## Store current period information in the vectors.
    
    s.vec[j] <- s0
    i.vec[j] <- i0
    z.vec[j] <- z0
    d.vec[j] <- d0
    cs.vec[j] <- contact.s
    ci.vec[j] <- contact.i
    cz.vec[j] <- contact.z
    us.vec[j] <- utility(contact.s, 0)
    ui.vec[j] <- utility(contact.i, 1)
    uz.vec[j] <- utility(contact.z, 2)
    
    ## Then move the period forward
    
    s1 <- s.t1(c.s = contact.s, c.i = contact.i, c.z = contact.z,
               s = s0, i = i0, z = z0)
    i1 <- i.t1(c.s = contact.s, c.i = contact.i, c.z = contact.z,
               s = s0, i = i0, z = z0)
    z1 <- z.t1(z = z0, i = i0)
    d1 <- d.t1(d = d0, i = i0)
    
    s0 <- s1
    i0 <- i1
    z0 <- z1
    d0 <- d1
    
  }
  
  return(new("SocTracker",
             s=s.vec, i=i.vec, z=z.vec, d=d.vec,
             cs = cs.vec, ci = ci.vec, cz = cz.vec,
             us = us.vec, ui = ui.vec, uz = uz.vec,
             ud = ud.vec))
  
}

## Store results for initial values that we put in the paper...

s.cov1 <- soc(init.s = 0.999, init.i = 0.001, init.z = 0)

## Plot some graphs

t <- c(1:250)
data.scovid1 <- data.frame(t, s.cov1@s, s.cov1@i,
                       s.cov1@z, s.cov1@d, s.cov1@cs,
                       s.cov1@ci,
                       s.cov1@cz, s.cov1@us,
                       s.cov1@ui, s.cov1@uz, s.cov1@ud)
data.scovid1 <- data.scovid1 %>%
  mutate(wus = s.cov1.s * s.cov1.us) %>%
  mutate(wui = s.cov1.i * s.cov1.ui) %>%
  mutate(wuz = s.cov1.z * s.cov1.uz) %>%
  mutate(wud = s.cov1.d * s.cov1.ud)
data.scovid1 <- data.scovid1 %>%
  mutate(rho = head(rho.vec, 250))
data.scovid1 <- data.scovid1 %>%
  mutate(tu = rho * (wus + wui + wuz + wud))
tutil.scovid1 <- sum(data.scovid1$tu)

ggplot(data.scovid1, aes(x = t, y = s.cov1.d)) +
  geom_line(color = "#69b3a2", size = 2, alpha = 0.9) +
  theme_dark()+
  ggtitle("Trajectory of Disease Prevalence under decentralized decision making") +
  xlab("Time (days)") +
  ylab("Disease Prevalence (%)")

plot(data.scovid1)

## -------------------------------------------------------
##
## Government with imperfect information: COVID
##
## -------------------------------------------------------

gov.trajectory <- function(contacts.vector, init.s, init.i, init.z){
  
  s <- init.s
  i <- init.i
  z <- init.z
  d <- 0
  utotal <- 0
  
  ## (we don't have to track the utility level of each individual now
  ## the social planner only cares about aggregate utility)
  
  for(j in 1:length(contacts.vector)){
    
    discount <- (1-rho)^(j-1)
    
    ## retrieve contact values
    
    cs <- contacts.vector[j]
    ci <- contacts.vector[j]
    cz <- contacts.vector[j]
    
    ## compute next period pandemic trajectory
    
    s1 <- s.t1(c.s = cs, c.i = ci, c.z = cz, s=s, i=i, z=z)
    i1 <- i.t1(c.s = cs, c.i = ci, c.z = cz, s=s, i=i, z=z)
    z1 <- z.t1(z=z, i=i)
    d1 <- d.t1(d=d, i=i)
    
    ## compute current period utility
    
    us <- s*utility(c = cs, h = 0)
    ui <- i*utility(c = ci, h = 1)
    uz <- z*utility(c = cz, h = 2)
    uded <- d*ud
    
    ## compute discounted current period utility
    
    u <- discount*(us + ui + uz + uded)
    utotal <- utotal + u
    
    ## update next period infection state
    
    s <- s1
    i <- i1
    z <- z1
    d <- d1
    
  }
  
  ## return total utility
  
  return(utotal)
  
}

gov.optim <- function(init.s, init.i, init.z, init.guess){
  
  x <- optim(par = rep(init.guess, horizon),
             fn = gov.trajectory,
             init.s = init.s, init.i = init.i, init.z = init.z,
             method = "BFGS",
             control = list(fnscale = -1, maxit = 100),
             hessian = FALSE)
  
  return (x)
  
}

## --------------------
## 150-day horizon

## Now let the economy work out itself based on the optimized
## values of contacts and see what happens.

setClass(Class="GovTracker",
         representation(
           s="numeric",
           i="numeric",
           z="numeric",
           d="numeric",
           cs="numeric",
           ci="numeric",
           cz="numeric",
           us="numeric",
           ui="numeric",
           uz="numeric",
           ud="numeric"
         )
)

gov <- function(init.s = 0.999, init.i = 0.001, init.z = 0, graph.horizon = 250){
  
  s.vec <- vector(mode = "numeric", length = graph.horizon)
  i.vec <- vector(mode = "numeric", length = graph.horizon)
  z.vec <- vector(mode = "numeric", length = graph.horizon)
  d.vec <- vector(mode = "numeric", length = graph.horizon)
  
  cs.vec <- vector(mode = "numeric", length = graph.horizon) ## contacts of susceptible
  ci.vec <- vector(mode = "numeric", length = graph.horizon) ## contacts of infected
  cz.vec <- vector(mode = "numeric", length = graph.horizon) ## contacts of recovered
  
  us.vec <- vector(mode = "numeric", length = graph.horizon) ## utility of susceptible
  ui.vec <- vector(mode = "numeric", length = graph.horizon) ## utility of infected
  uz.vec <- vector(mode = "numeric", length = graph.horizon) ## utility of recovered
  ud.vec <- rep(ud, graph.horizon)
  
  ## temp vars
  
  s0 <- init.s
  i0 <- init.i
  z0 <- init.z
  d0 <- 0
  
  ## run the optimization and retrieve the optimal contacts per time period:
  
  x <- gov.optim(init.s = init.s, init.i = init.i, init.z = init.z,
                 init.guess = 4)
  c.vec <- head(x$par, n = horizon)
  
  for(j in 1:graph.horizon){
    
    ## retrieve the optimal contacts in the j-th period
    contact.s <- c.vec[j]
    contact.i <- c.vec[j]
    contact.z <- c.vec[j]
    
    ## Store current period information in the vectors.
    
    s.vec[j] <- s0
    i.vec[j] <- i0
    z.vec[j] <- z0
    d.vec[j] <- d0
    cs.vec[j] <- contact.s
    ci.vec[j] <- contact.i
    cz.vec[j] <- contact.z
    us.vec[j] <- utility(contact.s, 0)
    ui.vec[j] <- utility(contact.i, 1)
    uz.vec[j] <- utility(contact.z, 2)
    
    ## Then move the period forward
    
    s1 <- s.t1(c.s = contact.s, c.i = contact.i, c.z = contact.z,
               s = s0, i = i0, z = z0)
    i1 <- i.t1(c.s = contact.s, c.i = contact.i, c.z = contact.z,
               s = s0, i = i0, z = z0)
    z1 <- z.t1(z = z0, i = i0)
    d1 <- d.t1(d = d0, i = i0)
    
    s0 <- s1
    i0 <- i1
    z0 <- z1
    d0 <- d1
    
  }
  
  return(new("GovTracker",
             s=s.vec, i=i.vec, z=z.vec, d=d.vec,
             cs = cs.vec, ci = ci.vec, cz = cz.vec,
             us = us.vec, ui = ui.vec, uz = uz.vec,
             ud = ud.vec))
  
}

## Store results for initial values that we put in the paper...

gov.cov1 <- gov(init.s = 0.999, init.i = 0.001, init.z = 0)

## Plot some graphs

t <- c(1:250)
data.govcovid1 <- data.frame(t, gov.cov1@s, gov.cov1@i,
                       gov.cov1@z, gov.cov1@d,
                       gov.cov1@cs,
                       gov.cov1@ci,
                       gov.cov1@cz, gov.cov1@us,
                       gov.cov1@ui, gov.cov1@uz,
                       gov.cov1@ud)

## calculate weighted utility levels in each time period

data.govcovid1 <- data.govcovid1 %>%
  mutate(wus = gov.cov1.s * gov.cov1.us) %>%
  mutate(wui = gov.cov1.i * gov.cov1.ui) %>%
  mutate(wuz = gov.cov1.z * gov.cov1.uz) %>%
  mutate(wud = gov.cov1.d * gov.cov1.ud)

## add discounting factor

data.govcovid1 <- data.govcovid1 %>%
  mutate(rho = head(rho.vec, 250))

## calculated total discounted + weighted utility levels

data.govcovid1 <- data.govcovid1 %>%
  mutate(tu = rho * (wus + wui + wuz + wud))

## sum it up

tutil.govcov1 <- sum(data.govcovid1$tu)

ggplot(data.govcovid1, aes(x = t, y = gov.cov1.d)) +
  geom_line(color = "#69b3a2", size = 2, alpha = 0.9) +
  theme_dark()+
  ggtitle("Trajectory of Disease Prevalence under decentralized decision making") +
  xlab("Time (days)") +
  ylab("Disease Prevalence (%)")

plot(data.govcovid1)

## -------------------------------------------------------
##
## Social Planner with Minimum Contact constraint: COVID
##
## -------------------------------------------------------

soc3.trajectory <- function(contacts.vector, init.s, init.i, init.z){
  
  ## contacts.vector consists of: c.s[1], c.s[2], ..., c.i[1], c.i[2], ..., c.z[1], ...
  
  ## check if it is divisible by 3
  if(length(contacts.vector) %% 3 != 0) stop("contacts vector is not div by 3")
  
  rl <- length(contacts.vector)/3
  
  ## define temporary variables
  s <- init.s
  i <- init.i
  z <- init.z
  d <- 0
  utotal <- 0
  
  ## (we don't have to track the utility level of each individual now
  ## the social planner only cares about aggregate utility)
  
  for(j in 1:rl){
    
    discount <- (1-rho)^(j-1)
    
    ## retrieve contact values
    
    cs <- contacts.vector[j]
    ci <- contacts.vector[j+rl]
    cz <- contacts.vector[j+(2*rl)]
    
    ## compute next period pandemic trajectory
    
    s1 <- s.t1(c.s = cs, c.i = ci, c.z = cz, s=s, i=i, z=z)
    i1 <- i.t1(c.s = cs, c.i = ci, c.z = cz, s=s, i=i, z=z)
    z1 <- z.t1(z=z, i=i)
    d1 <- d.t1(d=d, i=i)
    
    ## compute current period utility
    
    us <- s*utility(c = cs, h = 0)
    ui <- i*utility(c = ci, h = 1)
    uz <- z*utility(c = cz, h = 2)
    uded <- d*ud
    
    ## compute discounted current period utility
    
    u <- discount*(us + ui + uz + uded)
    utotal <- utotal + u
    
    ## update next period infection state
    
    s <- s1
    i <- i1
    z <- z1
    d <- d1
    
  }
  
  ## return total utility
  
  return(utotal)
  
}

soc3.optim <- function(init.s, init.i, init.z, init.guess.cs, init.guess.ci, init.guess.cz){
  
  x <- optim(par = c(rep(init.guess.cs, horizon),
                     rep(init.guess.ci, horizon),
                     rep(init.guess.cz, horizon)),
             fn = soc3.trajectory,
             init.s = init.s, init.i = init.i, init.z = init.z,
             method = "L-BFGS-B",
             control = list(fnscale = -1, maxit = 100),
             lower = rep(3, horizon),
             upper = rep(15, horizon),
             hessian = FALSE)
  
  return (x)
  
}

## --------------------
## 150-day horizon

## Now let the economy work out itself based on the optimized
## values of contacts and see what happens.

setClass(Class="Soc3Tracker",
         representation(
           s="numeric",
           i="numeric",
           z="numeric",
           d="numeric",
           cs="numeric",
           ci="numeric",
           cz="numeric",
           us="numeric",
           ui="numeric",
           uz="numeric",
           ud="numeric"
         )
)

soc3 <- function(init.s = 0.999, init.i = 0.001, init.z = 0, graph.horizon = 250){
  
  s.vec <- vector(mode = "numeric", length = graph.horizon)
  i.vec <- vector(mode = "numeric", length = graph.horizon)
  z.vec <- vector(mode = "numeric", length = graph.horizon)
  d.vec <- vector(mode = "numeric", length = graph.horizon)
  
  cs.vec <- vector(mode = "numeric", length = graph.horizon) ## contacts of susceptible
  ci.vec <- vector(mode = "numeric", length = graph.horizon) ## contacts of infected
  cz.vec <- vector(mode = "numeric", length = graph.horizon) ## contacts of recovered
  
  us.vec <- vector(mode = "numeric", length = graph.horizon) ## utility of susceptible
  ui.vec <- vector(mode = "numeric", length = graph.horizon) ## utility of infected
  uz.vec <- vector(mode = "numeric", length = graph.horizon) ## utility of recovered
  ud.vec <- rep(ud, graph.horizon)
  
  ## temp vars
  
  s0 <- init.s
  i0 <- init.i
  z0 <- init.z
  d0 <- 0
  
  ## run the optimization and retrieve the optimal contacts per time period:
  
  x <- soc3.optim(init.s = init.s, init.i = init.i, init.z = init.z,
                  init.guess.cs = 4, init.guess.ci = 3, init.guess.cz = 6)
  c.vec <- head(x$par, n = 3*horizon)
  
  for(j in 1:graph.horizon){
    
    ## retrieve the optimal contacts in the j-th period
    contact.s <- c.vec[j]
    contact.i <- c.vec[j+horizon]
    contact.z <- c.vec[j+2*horizon]
    
    ## Store current period information in the vectors.
    
    s.vec[j] <- s0
    i.vec[j] <- i0
    z.vec[j] <- z0
    d.vec[j] <- d0
    cs.vec[j] <- contact.s
    ci.vec[j] <- contact.i
    cz.vec[j] <- contact.z
    us.vec[j] <- utility(contact.s, 0)
    ui.vec[j] <- utility(contact.i, 1)
    uz.vec[j] <- utility(contact.z, 2)
    
    ## Then move the period forward
    
    s1 <- s.t1(c.s = contact.s, c.i = contact.i, c.z = contact.z,
               s = s0, i = i0, z = z0)
    i1 <- i.t1(c.s = contact.s, c.i = contact.i, c.z = contact.z,
               s = s0, i = i0, z = z0)
    z1 <- z.t1(z = z0, i = i0)
    d1 <- d.t1(d = d0, i = i0)
    
    s0 <- s1
    i0 <- i1
    z0 <- z1
    d0 <- d1
    
  }
  
  return(new("Soc3Tracker",
             s=s.vec, i=i.vec, z=z.vec, d=d.vec,
             cs = cs.vec, ci = ci.vec, cz = cz.vec,
             us = us.vec, ui = ui.vec, uz = uz.vec,
             ud = ud.vec))
  
}

## Store results for initial values that we put in the paper...

soc3covid1 <- soc3(init.s = 0.999, init.i = 0.001, init.z = 0)

## Plot some graphs

t <- c(1:150)
data.soc3cov1 <- data.frame(t, soc3covid1@s, soc3covid1@i,
                        soc3covid1@z, soc3covid1@d, soc3covid1@cs,
                        soc3covid1@ci,
                        soc3covid1@cz, soc3covid1@us,
                        soc3covid1@ui, soc3covid1@uz, soc3covid1@ud)

## calculate weighted utility levels in each time period

data.soc3cov1 <- data.soc3cov1 %>%
  mutate(wus = soc3covid1.s * soc3covid1.us) %>%
  mutate(wui = soc3covid1.i * soc3covid1.ui) %>%
  mutate(wuz = soc3covid1.z * soc3covid1.uz) %>%
  mutate(wud = soc3covid1.d * soc3covid1.ud)

## add discounting factor

data.soc3cov1 <- data.soc3cov1 %>%
  mutate(rho = head(rho.vec, 250))

## calculated total discounted + weighted utility levels

data.soc3cov1 <- data.soc3cov1 %>%
  mutate(tu = rho * (wus + wui + wuz + wud))

## sum it up

tutil.soc3cov1 <- sum(data.soc3cov1$tu)

ggplot(data.soc3cov1, aes(x = t, y = soc3covid1.s)) +
  geom_line(color = "#69b3a2", size = 2, alpha = 0.9) +
  theme_dark()+
  ggtitle("Trajectory of Disease Prevalence under decentralized decision making") +
  xlab("Time (days)") +
  ylab("Disease Prevalence (%)")
