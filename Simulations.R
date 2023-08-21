##########
#### Dissertation Simulations - Neyman Allocation Version
##########

### Author: Jasper Yang

#####
## Load packages
#####
library(dplyr)
library(tidyr)
library(optimall)
library(MASS)
library(survey)

######
## Set n
######
n <- 1004

#####
### Functions
#####

# 1. Influence function logistic regression (with help from Tong Chen)
inf_fun_logit <- function(fit){
  dm <- model.matrix(fit)
  Ihat <- (t(dm) %*% (dm * fit$fitted.values * (1 - fit$fitted.values))) /nrow(dm)
  infl <- (dm * resid(fit, type = "response")) %*% solve(Ihat)
}


# 2. A-optimality
###
### A-optimality function - same output as optimum_allocation. Given 2 inputs
a_optimum_allocation <- function(data, strata = "strata", 
                                 nsample, vars, weights,
                                 method){
  P <- length(vars)
  N_k <- table(data[,strata]) # before removing NAs
  data <- data[!is.na(data[,vars[1]]),]
  var_list <- list()
  a_var_list <- list()
  for (i in seq_along(vars)){
    variances <- tapply(data[,vars[i]], data[,strata], var)
    var_list[[i]] <- variances
    a_var_list[[i]] <- weights[i]*variances
  }
  sums <- rowSums(t(dplyr::bind_rows(a_var_list))) # Gives sum per stratum
  df <- data.frame("strata" = names(N_k), "N_k" = as.vector(N_k),
                   "sqrt_a_var_sum" = sqrt(sums))
  
  # Now run Neyman on this df
  output <- optimum_allocation(df, strata = "strata", sd_h = "sqrt_a_var_sum",
                               N_h = "N_k", nsample = nsample, 
                               method = method)
  
  return(output)
}

# 3. allocate_wave() with Neyman solution rather than Wright for speed (adapted
# from 'optimal' function)
allocate_wave_Neyman <- function(data,
                                 strata,
                                 y, already_sampled,
                                 nsample,
                                 method = c("iterative","simple"),
                                 detailed = FALSE,
                                 allocation_method = "Neyman") {
  key <- stratum_size <- wave1_size <- npop <- difference <-
    nsample_prior <- n_to_sample <- nsample_actual <-
    nsample_optimal <- sd <- NULL # bind global vars as necessary
  if (is.matrix(data)) {
    data <- data.frame(data)
  }
  if (is.data.frame(data) == FALSE) {
    stop("Input data must be a dataframe or matrix with named columns.")
  }
  if (all(strata %in% names(data)) == FALSE) {
    stop("'strata' must be a character string or vector of
    strings matching column names of data.")
  }
  if (y %in% names(data) == FALSE) {
    stop("'y' must be a character string matching a column name of data.")
  }
  if (already_sampled %in% names(data) == FALSE) {
    stop("'already_sampled' must be a character string matching a column name of
           data.")
  }
  if (inherits(detailed, "logical") == FALSE) {
    stop("'detailed' must be a logical value.")
  }
  if (length(table(data[, already_sampled])) != 2) {
    stop("'already_sampled' must be a character string matching a column in
         'data' that has a binary indicator for whether each unit
         was already sampled. If no units have been sampled yet,
         use 'optimum_allocation'.")
  }
  if (("Y" %in% data[, already_sampled] == FALSE & 1 %in%
       data[, already_sampled] == FALSE) | anyNA(data[, already_sampled])) {
    stop("'already_sampled' column must contain '1' (numeric) or 'Y'
         (character) as indicators that a unit was sampled in a
         previous wave and cannot contain NAs. If no units have
         been sample, use 'optimum_allocation.")
  }
  if (nsample + sum(data[, already_sampled] == "Y") +
      sum(data[, already_sampled] == 1) > length(data[, y])) {
    stop("Total sample size across waves, taken as nsampled in
         already_sampled + nsample, is larger than the population size.")
  }
  method <- match.arg(method)
  # Find the total sample size and optimally allocate that
  nsampled <- sum(data[, already_sampled] == "Y" | data[, already_sampled] == 1)
  output1 <- optimall::optimum_allocation(
    data = data,
    strata = strata,
    y = y,
    nsample = nsample + nsampled,
    allow.na = TRUE,
    method = allocation_method
  )
  # Optimal for total sample size
  
  # Create groups from strata argument and determine the prior
  # sample size for each
  y <- enquo(y)
  strata <- enquo(strata)
  key_q <- enquo(already_sampled)
  wave1_df <- data %>%
    dplyr::select(!!strata, !!y, !!key_q)
  group <- interaction(dplyr::select(wave1_df, !!strata))
  wave1_df <- cbind(group, wave1_df)
  wave1_df <- dplyr::select(wave1_df, 1, !!y, !!key_q)
  # Only columns of interest
  names(wave1_df) <- c("group", "y", "key")
  wave1_summary <- wave1_df %>%
    dplyr::group_by(group) %>%
    dplyr::summarize(wave1_size = sum(key == 1 | key == "Y"))
  
  names(output1)[1] <- "group"
  comp_df <- dplyr::inner_join(output1, wave1_summary, by = "group")
  comp_df <- dplyr::mutate(comp_df,
                           difference = stratum_size - wave1_size,
                           n_avail = npop - wave1_size
  )
  
  # For the simple case in which no strata have been oversampled
  if (all(comp_df$difference >= 0)) {
    comp_df <- comp_df %>%
      dplyr::rename(
        nsample_optimal = stratum_size,
        nsample_prior = wave1_size,
        n_to_sample = difference
      ) %>%
      dplyr::mutate(nsample_actual = nsample_prior + n_to_sample)
    if (detailed == FALSE) {
      comp_df <- comp_df %>%
        dplyr::select(
          "strata" = group, npop, nsample_actual,
          nsample_prior, n_to_sample
        )
    } else if (detailed == TRUE) {
      comp_df <- comp_df %>%
        dplyr::select(
          "strata" = group, npop, nsample_optimal,
          nsample_actual, nsample_prior,
          n_to_sample, sd
        )
    }
    return(comp_df)
  }
  
  # If some Strata have been oversampled. Basic, non-iterative method.
  if (any(comp_df$difference < 0) & method == "simple") {
    temp <- dplyr::filter(comp_df, difference <= 0)
    n_oversampled <- -sum(temp$difference)
    closed_groups <- (temp$group)
    nsampled_in_closed_groups <- sum(temp$wave1_size)
    
    open_groups <- dplyr::filter(comp_df, difference > 0)$group
    open_df <- wave1_df %>%
      dplyr::filter(group %in% open_groups)
    open_output <- optimall::optimum_allocation(
      data = open_df,
      strata = "group",
      y = "y",
      nsample = nsample + nsampled - nsampled_in_closed_groups,
      allow.na = TRUE,
      method = allocation_method
    )
    names(open_output)[1] <- "group"
    open_output <- dplyr::inner_join(open_output, wave1_summary, by = "group")
    open_output <- dplyr::mutate(
      open_output,
      difference = stratum_size - wave1_size,
      n_avail = npop - wave1_size
    )
    
    open_output <- open_output %>%
      dplyr::rename(
        nsample_optimal = stratum_size,
        nsample_prior = wave1_size
      ) %>%
      dplyr::mutate(
        n_to_sample = difference,
        nsample_actual = nsample_prior + n_to_sample
      ) %>%
      dplyr::select(
        "strata" = group,
        npop,
        nsample_actual,
        nsample_prior,
        n_to_sample
      )
    
    closed_output <- temp %>%
      dplyr::rename(
        nsample_optimal = stratum_size,
        nsample_prior = wave1_size
      ) %>%
      dplyr::mutate(
        n_to_sample = 0,
        nsample_actual = nsample_prior
      ) %>%
      dplyr::select(
        "strata" = group,
        npop,
        nsample_actual,
        nsample_prior,
        n_to_sample
      )
    
    output_df <- rbind(closed_output, open_output)
    if (detailed == TRUE) {
      output_df <- dplyr::inner_join(
        output_df,
        dplyr::select(output1,
                      "nsample_optimal" = stratum_size,
                      sd,
                      "strata" = group
        ),
        by = "strata"
      )
      output_df <- dplyr::select(
        output_df, strata, npop, nsample_optimal,
        nsample_actual, nsample_prior, n_to_sample, sd
      )
    }
    output_df <- dplyr::arrange(output_df, strata)
    if (any(output_df$n_to_sample < 0)) {
      warning("The simple method yielded strata with negative
              n_to_sample values due to many groups being
              oversampled in prior waves. Switching to
              method = 'iterative'.")
      did_simple_work <- FALSE
      method <- "iterative"
      rm(output_df, closed_output, open_output, closed_groups, open_groups)
    } else {
      return(output_df)
    }
  }
  # Now, iterative method
  
  if (any(comp_df$difference < 0) & method == "iterative") {
    closed_groups_df <- data.frame()
    
    while (any(comp_df$difference < 0)) {
      # Find most oversampled group. Add that group to the closed strata.
      closed_groups_df <- rbind(
        closed_groups_df,
        dplyr::filter(
          comp_df,
          difference ==
            min(difference)
        )
      )
      nsampled_in_closed_groups <- sum(closed_groups_df$wave1_size)
      closed_groups <- (closed_groups_df$group)
      
      # Filter comp_df, remove the smallest group
      open_groups_names <- dplyr::filter(
        comp_df,
        difference !=
          min(difference)
      )$group
      open_df <- wave1_df %>%
        dplyr::filter(group %in% open_groups_names)
      
      # Run optimal allocation on this filtered df of open groups
      outputn <- optimall::optimum_allocation(
        data = open_df, strata = "group", y = "y",
        nsample = nsample + nsampled - nsampled_in_closed_groups,
        allow.na = TRUE, method = allocation_method
      )
      
      # Re-join with (cleaned) input data to  get new differences
      names(outputn)[1] <- "group"
      comp_df <- dplyr::inner_join(outputn, wave1_summary, by = "group")
      comp_df <- dplyr::mutate(comp_df,
                               difference = stratum_size - wave1_size,
                               n_avail = npop - wave1_size
      )
    }
    open_output <- comp_df %>%
      dplyr::rename(
        nsample_optimal = stratum_size,
        nsample_prior = wave1_size
      ) %>%
      dplyr::mutate(
        n_to_sample = difference,
        nsample_actual = nsample_prior + n_to_sample
      ) %>%
      dplyr::select(
        "strata" = group, npop, nsample_actual, nsample_prior,
        n_to_sample
      )
    
    closed_output <- closed_groups_df %>%
      dplyr::rename(
        nsample_optimal = stratum_size,
        nsample_prior = wave1_size
      ) %>%
      dplyr::mutate(
        n_to_sample = 0,
        nsample_actual = nsample_prior
      ) %>%
      dplyr::select(
        "strata" = group, npop, nsample_actual, nsample_prior,
        n_to_sample
      )
    output_df <- rbind(closed_output, open_output)
    if (detailed == TRUE) {
      output_df <- dplyr::inner_join(
        output_df,
        dplyr::select(output1,
                      "nsample_optimal" = stratum_size,
                      sd,
                      "strata" = group
        ),
        by = "strata"
      )
      output_df <- dplyr::select(
        output_df, strata, npop, nsample_optimal,
        nsample_actual, nsample_prior, n_to_sample, sd
      )
    }
    output_df <- dplyr::arrange(output_df, strata)
    return(output_df)
  }
}

# 4. allocate_wave() with a-optimality (adapted from 'optimall' function)
a_optimal_allocate_wave <- function(data,
                                    strata, vars, weights,
                                    already_sampled,
                                    nsample, 
                                    method = c("iterative","simple"),
                                    detailed = FALSE,
                                    allocation_method = "Neyman") {
  key <- stratum_size <- wave1_size <- npop <- difference <-
    nsample_prior <- n_to_sample <- nsample_actual <-
    nsample_optimal <- sd <- NULL # bind global vars as necessary
  if (is.matrix(data)) {
    data <- data.frame(data)
  }
  if (is.data.frame(data) == FALSE) {
    stop("Input data must be a dataframe or matrix with named columns.")
  }
  if (all(strata %in% names(data)) == FALSE) {
    stop("'strata' must be a character string or vector of
    strings matching column names of data.")
  }
  if (any(vars %in% names(data) == FALSE)) {
    stop("'y' must be a character string matching a column name of data.")
  }
  if (already_sampled %in% names(data) == FALSE) {
    stop("'already_sampled' must be a character string matching a column name of
           data.")
  }
  if (inherits(detailed, "logical") == FALSE) {
    stop("'detailed' must be a logical value.")
  }
  if (length(table(data[, already_sampled])) != 2) {
    stop("'already_sampled' must be a character string matching a column in
         'data' that has a binary indicator for whether each unit
         was already sampled. If no units have been sampled yet,
         use 'optimum_allocation'.")
  }
  if (("Y" %in% data[, already_sampled] == FALSE & 1 %in%
       data[, already_sampled] == FALSE) | anyNA(data[, already_sampled])) {
    stop("'already_sampled' column must contain '1' (numeric) or 'Y'
         (character) as indicators that a unit was sampled in a
         previous wave and cannot contain NAs. If no units have
         been sample, use 'optimum_allocation.")
  }
  if (nsample + sum(data[, already_sampled] == "Y") +
      sum(data[, already_sampled] == 1) > length(data[, vars[1]])) {
    stop("Total sample size across waves, taken as nsampled in
         already_sampled + nsample, is larger than the population size.")
  }
  method <- match.arg(method)
  # Find the total sample size and optimally allocate that
  nsampled <- sum(data[, already_sampled] == "Y" | data[, already_sampled] == 1)
  output1 <- a_optimum_allocation(
    data = data,
    strata = strata,
    vars = vars,
    weights = weights,
    nsample = nsample + nsampled,
    method = allocation_method
  )
  # Optimal for total sample size
  
  # Create groups from strata argument and determine the prior
  # sample size for each
  raw_vars <- vars
  vars <- enquo(vars)
  strata <- enquo(strata)
  key_q <- enquo(already_sampled)
  wave1_df <- data %>%
    dplyr::select(!!strata, !!vars, !!key_q)
  group <- interaction(dplyr::select(wave1_df, !!strata))
  wave1_df <- cbind(group, wave1_df)
  wave1_df <- dplyr::select(wave1_df, 1, !!vars, !!key_q)
  # Only columns of interest
  names(wave1_df) <- c("group", raw_vars, "key")
  wave1_summary <- wave1_df %>%
    dplyr::group_by(group) %>%
    dplyr::summarize(wave1_size = sum(key == 1 | key == "Y"))
  
  names(output1)[1] <- "group"
  comp_df <- dplyr::inner_join(output1, wave1_summary, by = "group")
  comp_df <- dplyr::mutate(comp_df,
                           difference = stratum_size - wave1_size,
                           n_avail = npop - wave1_size
  )
  
  # For the simple case in which no strata have been oversampled
  if (all(comp_df$difference >= 0)) {
    comp_df <- comp_df %>%
      dplyr::rename(
        nsample_optimal = stratum_size,
        nsample_prior = wave1_size,
        n_to_sample = difference
      ) %>%
      dplyr::mutate(nsample_actual = nsample_prior + n_to_sample)
    if (detailed == FALSE) {
      comp_df <- comp_df %>%
        dplyr::select(
          "strata" = group, npop, nsample_actual,
          nsample_prior, n_to_sample
        )
    } else if (detailed == TRUE) {
      comp_df <- comp_df %>%
        dplyr::select(
          "strata" = group, npop, nsample_optimal,
          nsample_actual, nsample_prior,
          n_to_sample, sd
        )
    }
    return(comp_df)
  }
  
  # If some Strata have been oversampled. Basic, non-iterative method.
  if (any(comp_df$difference < 0) & method == "simple") {
    temp <- dplyr::filter(comp_df, difference <= 0)
    n_oversampled <- -sum(temp$difference)
    closed_groups <- (temp$group)
    nsampled_in_closed_groups <- sum(temp$wave1_size)
    
    open_groups <- dplyr::filter(comp_df, difference > 0)$group
    open_df <- wave1_df %>%
      dplyr::filter(group %in% open_groups)
    
    open_df$group <- factor(open_df$group, levels = open_groups) # remove closed
    # groups as factors
    
    open_output <- a_optimum_allocation(
      data = open_df,
      strata = "group",
      vars = raw_vars,
      weights = weights,
      nsample = nsample + nsampled - nsampled_in_closed_groups,
      method = allocation_method
    )
    names(open_output)[1] <- "group"
    open_output <- dplyr::inner_join(open_output, wave1_summary, by = "group")
    open_output <- dplyr::mutate(
      open_output,
      difference = stratum_size - wave1_size,
      n_avail = npop - wave1_size
    )
    
    open_output <- open_output %>%
      dplyr::rename(
        nsample_optimal = stratum_size,
        nsample_prior = wave1_size
      ) %>%
      dplyr::mutate(
        n_to_sample = difference,
        nsample_actual = nsample_prior + n_to_sample
      ) %>%
      dplyr::select(
        "strata" = group,
        npop,
        nsample_actual,
        nsample_prior,
        n_to_sample
      )
    
    closed_output <- temp %>%
      dplyr::rename(
        nsample_optimal = stratum_size,
        nsample_prior = wave1_size
      ) %>%
      dplyr::mutate(
        n_to_sample = 0,
        nsample_actual = nsample_prior
      ) %>%
      dplyr::select(
        "strata" = group,
        npop,
        nsample_actual,
        nsample_prior,
        n_to_sample
      )
    
    output_df <- rbind(closed_output, open_output)
    if (detailed == TRUE) {
      output_df <- dplyr::inner_join(
        output_df,
        dplyr::select(output1,
                      "nsample_optimal" = stratum_size,
                      sd,
                      "strata" = group
        ),
        by = "strata"
      )
      output_df <- dplyr::select(
        output_df, strata, npop, nsample_optimal,
        nsample_actual, nsample_prior, n_to_sample, sd
      )
    }
    output_df <- dplyr::arrange(output_df, strata)
    if (any(output_df$n_to_sample < 0)) {
      warning("The simple method yielded strata with negative
              n_to_sample values due to many groups being
              oversampled in prior waves. Switching to
              method = 'iterative'.")
      did_simple_work <- FALSE
      method <- "iterative"
      rm(output_df, closed_output, open_output, closed_groups, open_groups)
    } else {
      return(output_df)
    }
  }
  # Now, iterative method
  
  if (any(comp_df$difference < 0) & method == "iterative") {
    closed_groups_df <- data.frame()
    
    while (any(comp_df$difference < 0)) {
      # Find most oversampled group. Add that group to the closed strata.
      closed_groups_df <- rbind(
        closed_groups_df,
        dplyr::filter(
          comp_df,
          difference ==
            min(difference)
        )
      )
      nsampled_in_closed_groups <- sum(closed_groups_df$wave1_size)
      closed_groups <- (closed_groups_df$group)
      
      # Filter comp_df, remove the smallest group
      open_groups_names <- dplyr::filter(
        comp_df,
        difference !=
          min(difference)
      )$group
      open_df <- wave1_df %>%
        dplyr::filter(group %in% open_groups_names)
      
      
      open_df$group <- factor(open_df$group, levels = open_groups_names) # remove closed
      # groups as factors
      
      # Run optimal allocation on this filtered df of open groups
      outputn <-  a_optimum_allocation(
        data = open_df,
        strata = "group",
        vars = raw_vars,
        weights = weights,
        nsample = nsample + nsampled - nsampled_in_closed_groups,
        method = allocation_method
      )
      
      # Re-join with (cleaned) input data to  get new differences
      names(outputn)[1] <- "group"
      comp_df <- dplyr::inner_join(outputn, wave1_summary, by = "group")
      comp_df <- dplyr::mutate(comp_df,
                               difference = stratum_size - wave1_size,
                               n_avail = npop - wave1_size
      )
    }
    open_output <- comp_df %>%
      dplyr::rename(
        nsample_optimal = stratum_size,
        nsample_prior = wave1_size
      ) %>%
      dplyr::mutate(
        n_to_sample = difference,
        nsample_actual = nsample_prior + n_to_sample
      ) %>%
      dplyr::select(
        "strata" = group, npop, nsample_actual, nsample_prior,
        n_to_sample
      )
    
    closed_output <- closed_groups_df %>%
      dplyr::rename(
        nsample_optimal = stratum_size,
        nsample_prior = wave1_size
      ) %>%
      dplyr::mutate(
        n_to_sample = 0,
        nsample_actual = nsample_prior
      ) %>%
      dplyr::select(
        "strata" = group, npop, nsample_actual, nsample_prior,
        n_to_sample
      )
    output_df <- rbind(closed_output, open_output)
    if (detailed == TRUE) {
      output_df <- dplyr::inner_join(
        output_df,
        dplyr::select(output1,
                      "nsample_optimal" = stratum_size,
                      sd,
                      "strata" = group
        ),
        by = "strata"
      )
      output_df <- dplyr::select(
        output_df, strata, npop, nsample_optimal,
        nsample_actual, nsample_prior, n_to_sample, sd
      )
    }
    output_df <- dplyr::arrange(output_df, strata)
    return(output_df)
  }
}


#####
## Set Parameters and seeds, which will differ across scenarios
#####

## Nine scenarios overall. They differ by betas and measurement error
# I set two seeds because I want true data to be same for each beta scenario,
# but then measurement error generation has unique seed
simulations_df <- data.frame(row.names = c("B01", "B11", "B21", "B31", "B41",
                                           "B02", "B12", "B22", "B32",
                                           "sensY", "specY", "error_varX",
                                           "sensZ1", "specZ1","error_varZ2",
                                           "data_seed", "error_seed"),
                             "Scenario1A" = c(-1.5, 0.4, 0, 0.3, 0, 
                                              -0.5, 0.2, 0.5, 0, 
                                              0.9, 0.95, 0.25, 0.9, 0.95, 0.1,
                                              123, 1001),
                             "Scenario1B" = c(-1.5, 0.4, 0, 0.3, 0,
                                              -0.5, 0.2, 0.5, 0, 
                                              0.75, 0.8, 0.5, 0.9, 0.95, 0.1,
                                              123, 1002),
                             "Scenario1C" = c(-1.5, 0.4, 0, 0.3, 0, 
                                              -0.5, 0.2, 0.5, 0,
                                              0.6, 0.7, 1, 0.9, 0.95, 0.1,
                                              123, 1003),
                             "Scenario2A" = c(-2.3, 0.7, 2.4, 0.3, 0, 
                                              -0.8, 0.5, 1.9, 0.9, 
                                              0.9, 0.95, 0.25, 0.9, 0.95, 0.1, 
                                              234, 1004),
                             "Scenario2B" = c(-2.3, 0.7, 2.4, 0.3, 0, 
                                              -0.8, 0.5, 1.9, 0.9, 
                                              0.75, 0.8, 0.5, 0.9, 0.95, 0.1, 
                                              234, 1005),
                             "Scenario2C" = c(-2.3, 0.7, 2.4, 0.3, 0,
                                              -0.8, 0.5, 1.9, 0.9, 
                                              0.6, 0.7, 1, 0.9, 0.95, 0.1, 
                                              234, 1006),
                             "Scenario3A" = c(-3.1, 0.8, 1.0, 0.7, 1.9, 
                                              -0.8, 0.6, 1.3, 0.8, 
                                              0.9, 0.95, 0.25, 0.9, 0.95, 0.1,
                                              345, 1007),
                             "Scenario3B" = c(-3.1, 0.8, 1.0, 0.7, 1.9, 
                                              -0.8, 0.6, 1.3, 0.8,
                                              0.75, 0.8, 0.5, 0.9, 0.95, 0.1,
                                              345, 1008),
                             "Scenario3C" = c(-3.1, 0.8, 1.0, 0.7, 1.9, 
                                              -0.8, 0.6, 1.3, 0.8,
                                              0.6, 0.7, 1, 0.9, 0.95, 0.1,
                                              345, 1009))


print("checkpoint1")

####
## Start simulations - Each scenario
####
for (scenario in 1:9){
  # set first seed, for data
  set.seed(simulations_df["data_seed", scenario])
  
  # Set up betas for scenario
  B01 <- simulations_df["B01", scenario]
  B11 <- simulations_df["B11", scenario]
  B21 <- simulations_df["B21", scenario]
  B31 <- simulations_df["B31", scenario]
  B41 <- simulations_df["B41", scenario]
  B02 <- simulations_df["B02", scenario]
  B12 <- simulations_df["B12", scenario]
  B22 <- simulations_df["B22", scenario]
  B32 <- simulations_df["B32", scenario]
  
  # Measurement error
  sensY <- simulations_df["sensY", scenario]
  specY <- simulations_df["specY", scenario]
  error_varX <- simulations_df["error_varX", scenario]
  
  # These stay across sims for now
  sensZ1 <- simulations_df["sensZ1", scenario]
  specZ1 <- simulations_df["specZ1", scenario]
  error_varZ2 <- simulations_df["error_varZ2", scenario]
  
  
  #####
  ## Generate True Data
  #####
  
  N <- 10000 # Phase 1 sample size 
  id <- 1:N
  
  # Generate correlated covariates
  sigma <- matrix(c(1, 0.15, 0.1, 0.15, 1,  0.25, 0.1, 0.25, 1), nrow = 3)
  covs <- mvrnorm(N, mu = c(0,0,0), Sigma = sigma)
  X <- (covs[,1] - mean(covs[,1]))/sd(covs[,1])
  #X <- covs[,1]
  Z1 <- ifelse(covs[,2] >= quantile(covs[,2], 0.8), 1, 0)
  Z2 <- (covs[,3] - mean(covs[,3]))/sd(covs[,3])
  #Z2 <- covs[,3]
  cor(cbind(X, Z1, Z2)) 
  
  Y2_probs <- exp(B02 + B12*X + B22*Z1 + B32*Z2)/(1 + exp(B02 + B12*X + B22*Z1 + B32*Z2))
  Y2 <- rbinom(N, 1, Y2_probs) # Compute realized value for Y2
  
  Y1_probs <- exp(B01 + B11*X + B21*Z1 + B31*Z2 + B41*Y2)/
    (1 + exp(B01 + B11*X+ B21*Z1 + B31*Z2 + B41*Y2))
  Y1 <- rbinom(N, 1, Y1_probs) # Compute realized value for Y1
  
  full_data <- data.frame(id, X, Z1, Z2, Y1, Y2) 
  
  # Find observed correlation
  cor_Y1_Y2 <- cor(Y1, Y2) 
  
  # Prevalence
  prev_Y1 <- table(Y1)["1"]/length(Y1)
  prev_Y2 <- table(Y2)["1"]/length(Y2)
  
  # Find true coefficients
  true_modelY1 <- glm(Y1 ~ X + Z1 + Z2 + Y2, family = "binomial", data = full_data) 
  true_modelY2 <- glm(Y2 ~ X + Z1 + Z2, family = "binomial", data = full_data) 
  true_B_11 <- coef(true_modelY1)["X"]
  true_B_12 <- coef(true_modelY2)["X"]
  
  
  #####
  ## Generate error-prone Phase 1 data
  ######
  
  # Set new seed
  set.seed(simulations_df["error_seed", scenario])
  
  Z1_prob_obs1 <- ifelse(full_data$Z1 == 1, sensZ1, 1 - specZ1)
  Y1_prob_obs1 <- ifelse(full_data$Y1 == 1, sensY, 1 - specY)
  Y2_prob_obs1 <- ifelse(full_data$Y2 == 1, sensY, 1 - specY)
  
  full_data$Z1_obs <- rbinom(N, 1, Z1_prob_obs1)
  full_data$Z2_obs <- full_data$Z2 + rnorm(N, 0, sqrt(error_varZ2))
  full_data$Y1_obs <- rbinom(N, 1, Y1_prob_obs1)
  full_data$Y2_obs <- rbinom(N, 1, Y2_prob_obs1)
  full_data$X_obs <- full_data$X + rnorm(N, 0, sqrt(error_varX))
  
  ####
  #### Divide into strata based on observed phase 1 data
  full_data <- full_data |>
    dplyr::mutate(Y1_strat = Y1_obs, Y2_strat = Y2_obs, X_strat = X_obs) |>
    split_strata(strata = c("Y1_strat", "Y2_strat" ),
                 split_var = "X_strat",
                 type = "global quantile",
                 split_at = c(0.25, 0.75),
                 trunc = "X")
  
  names(full_data)[names(full_data) == "new_strata"] <- "strata"
  
  
  ######
  ### Phase 2 Sampling - Strategy 1: SRS
  ######
  
  Strategy1 <- function(n = 1004, data = full_data){
    # Sample
    N <- nrow(data)
    samples <- sample(1:N, size = n)
    data$sample_indicator <- ifelse(data$id %in% samples, TRUE, FALSE)
    
    # Generalized Raking
    data$strata <- rep(1, times = nrow(data)) # only one stratum here
    twophase_design <- twophase(id = list(~id, ~id), 
                                strata = list(NULL, ~strata), 
                                subset = ~sample_indicator, data = data)
    
    # Weights
    weightY1 <- svyglm(Y1 ~ X + Z1 + Z2 + Y2, family = quasibinomial, 
                       design = twophase_design)
    weightY2 <- svyglm(Y2 ~ X + Z1 + Z2, family = quasibinomial, 
                       design = twophase_design)
    
    # Imputation model for X, Z, Y1, Y2
    imp_model_x <- svyglm(X ~ X_obs + Z1_obs + Z2_obs, design = twophase_design)
    data$imp_x <- as.vector(predict(imp_model_x, 
                                    newdata = data,
                                    type = "response",
                                    se.fit = FALSE))
    
    imp_model_z1 <- svyglm(Z1 ~ X_obs + Z1_obs + Z2_obs,
                           family = "quasibinomial", design = twophase_design)
    data$imp_z1 <- as.vector(predict(imp_model_z1, 
                                     newdata = data,
                                     type = "response",
                                     se.fit = FALSE))
    
    imp_model_z2 <- svyglm(Z2 ~ X_obs + Z1_obs + Z2_obs, design = twophase_design)
    data$imp_z2 <- as.vector(predict(imp_model_z2, 
                                     newdata = data,
                                     type = "response",
                                     se.fit = FALSE))
    
    imp_model_Y2 <- svyglm(Y2 ~ X_obs + Z1_obs + Z2_obs + Y2_obs,
                           family = "quasibinomial", design = twophase_design)
    data$imp_Y2 <- as.vector(predict(imp_model_Y2, 
                                     newdata = data,
                                     type = "response",
                                     se.fit = FALSE))
    
    # Imputed model for phase 1
    phase1_model_impY1 <- glm(Y1_obs ~ imp_x + imp_z1 + imp_z2 + imp_Y2, 
                              family = binomial, 
                              data = data)
    phase1_model_impY2 <- glm(Y2_obs ~ imp_x + imp_z1 + imp_z2, 
                              family = binomial, 
                              data = data)
    
    # Influence functions from phase1 imputed model
    inf_fun_imp_Y1 <- inf_fun_logit(phase1_model_impY1)
    colnames(inf_fun_imp_Y1) <- c("int","inf_x_Y1",
                                  "inf_z1_Y1", "inf_z2_Y1", "inf_y2_Y1")
    inf_fun_imp_Y2 <- inf_fun_logit(phase1_model_impY2)
    colnames(inf_fun_imp_Y2) <- c("int", "inf_x_Y2",
                                  "inf_z1_Y2", "inf_z2_Y2")
    
    # Re-set up two-phase design
    twophase_design_imp_Y1 <- twophase(id = list(~id, ~id), 
                                       strata = list(NULL, ~strata), 
                                       subset = ~sample_indicator, 
                                       data = cbind(data,
                                                    inf_fun_imp_Y1),
                                       method = "simple")
    
    twophase_design_imp_Y2 <- twophase(id = list(~id, ~id), 
                                       strata = list(NULL, ~strata), 
                                       subset = ~sample_indicator, 
                                       data = cbind(data,
                                                    inf_fun_imp_Y2),
                                       method = "simple")
    
    # Calibrate
    calibration_formula_Y1 <- make.formula(colnames(inf_fun_imp_Y1))
    calibrated_twophase_Y1 <- calibrate(twophase_design_imp_Y1,
                                        calibration_formula_Y1,
                                        phase = 2,
                                        calfun = "raking")
    calibration_formula_Y2 <- make.formula(colnames(inf_fun_imp_Y2))
    calibrated_twophase_Y2 <- calibrate(twophase_design_imp_Y2,
                                        calibration_formula_Y2,
                                        phase = 2,
                                        calfun = "raking")
    
    # Run models
    fitY1 <- svyglm(Y1 ~ X + Z1 + Z2 + Y2, family = quasibinomial, 
                    design = calibrated_twophase_Y1)
    fitY2 <- svyglm(Y2 ~ X + Z1 + Z2, family = quasibinomial, 
                    design = calibrated_twophase_Y2)
    
    
    
    output <- c(fitY1$coefficients["X"], fitY2$coefficients["X"],
                coef(weightY1)["X"], coef(weightY2)["X"])
    return(output)
  }
  
  # And iterate this 1000 times, storing the B-hat each time
  B_hat_Y1_strat1_GR <- c()
  B_hat_Y2_strat1_GR <- c()
  B_hat_Y1_strat1_IPW <- c()
  B_hat_Y2_strat1_IPW <- c()
  
  for (i in 1:1000){
    run <- Strategy1(n = n)
    B_hat_Y1_strat1_GR[i] <- run[1]
    B_hat_Y2_strat1_GR[i] <- run[2]
    B_hat_Y1_strat1_IPW[i] <- run[3]
    B_hat_Y2_strat1_IPW[i] <-run[4]
  }
  
  # GR results
  var_B_11_strat1_GR <- var(B_hat_Y1_strat1_GR)
  var_B_12_strat1_GR <- var(B_hat_Y2_strat1_GR)
  mean_B_11_strat1_GR <- mean(B_hat_Y1_strat1_GR)
  mean_B_12_strat1_GR <- mean(B_hat_Y2_strat1_GR)
  
  # IPW results
  var_B_11_strat1_IPW <- var(B_hat_Y1_strat1_IPW)
  var_B_12_strat1_IPW <- var(B_hat_Y2_strat1_IPW)
  mean_B_11_strat1_IPW <- mean(B_hat_Y1_strat1_IPW)
  mean_B_12_strat1_IPW <- mean(B_hat_Y2_strat1_IPW)
  
  ######
  ### Phase 2 Sampling - Strategy 2: Independent, uniform strategy over 4 waves
  ######
  
  ## Here, each wave chooses n/4 samples where n/8 are chosen to be optimal for
  ## B_11 and n/8 to be optimal for B_12
  
  # Step 1: Initialize phase1_data
  phase1_data <- full_data
  
  # Step 2: Logistic regression on Phase 1 data
  fitY1_phase1 <-  glm(Y1_obs ~ X_obs + Z1_obs + Z2_obs + Y2_obs, 
                       family = "binomial", data = phase1_data)
  fitY2_phase1 <-  glm(Y2_obs ~ X_obs + Z1_obs + Z2_obs, 
                       family = "binomial", data = phase1_data)
  
  # Step 3: Calculate influence functions using Tong's function
  phase1_data$inflB11 <- inf_fun_logit(fitY1_phase1)[,"X_obs"]
  phase1_data$inflB12 <- inf_fun_logit(fitY2_phase1)[,"X_obs"]
  
  # Step 4: Determine optimum allocation for wave 1 with Wright algorithm
  allocation1 <- optimum_allocation(phase1_data,
                                    strata = "strata",
                                    y = "inflB11",
                                    nsample = n/8, method = "WrightII")
  
  allocation2 <- optimum_allocation(phase1_data,
                                    strata = "strata",
                                    y = "inflB12",
                                    nsample = n/8, method = "WrightII")
  
  # Step 5: Combine allocations for total allocation of n/4
  wave1_allocation <- dplyr::left_join(allocation1, allocation2, by = "strata") |>
    dplyr::mutate(stratum_size = stratum_size.x + stratum_size.y)
  
  # Also, remove inflB11 and inflB12 vars
  phase1_data <- subset(phase1_data, select = -c(inflB11,
                                                 inflB12))
  
  
  # Step 6: Create function to estimate beta-hat at each iteration
  Strategy2 <- function(n = n, phase1_data = phase1_data){
    
    ####
    ## Wave 1
    ####
    
    # First 1/4th according to wave1_allocation
    phase2_wave1 <- sample_strata(data = phase1_data,
                                  strata = "strata",
                                  id = "id",
                                  design_data = wave1_allocation,
                                  n_allocated = "stratum_size")
    names(phase2_wave1)[names(phase2_wave1) == "sample_indicator"] <- "sampled_wave1"
    
    #####
    ## Wave 2
    #####
    
    # Calculate influence functions using IPW
    twophase_design_wave1 <- twophase(id = list(~id, ~id), 
                                      strata = list(NULL, ~strata), 
                                      subset = ~as.logical(sampled_wave1), 
                                      data = phase2_wave1)
    fitY1_wave1 <- svyglm(Y1 ~ X + Z1 + Z2 + Y2, family = quasibinomial, 
                          design = twophase_design_wave1)
    fitY2_wave1 <- svyglm(Y2 ~ X + Z1 + Z2, family = quasibinomial, 
                          design = twophase_design_wave1)
    infl_wave1_Y1 <- inf_fun_logit(fitY1_wave1)
    infl_wave1_Y2 <- inf_fun_logit(fitY2_wave1)
    infl_wave1 <- data.frame(as.numeric(rownames(infl_wave1_Y1)), 
                             infl_wave1_Y1[,"X"],
                             infl_wave1_Y2[,"X"])
    names(infl_wave1) <- c("id", "inflB11", "inflB12")
    phase2_wave1 <- dplyr::left_join(phase2_wave1, infl_wave1, by = "id")
    
    
    # Re-calculate allocations
    allocation1 <- allocate_wave_Neyman(phase2_wave1,
                                        strata = "strata",
                                        y = "inflB11", method = "iterative",
                                        already_sampled = "sampled_wave1",
                                        nsample = n/8, 
                                        allocation_method = "Neyman")
    
    allocation2 <- allocate_wave_Neyman(phase2_wave1,
                                        strata = "strata",
                                        y = "inflB12",
                                        already_sampled = "sampled_wave1",
                                        nsample = n/8, method = "iterative",
                                        allocation_method = "Neyman")
    
    # and combine
    wave2_allocation <- dplyr::left_join(allocation1, allocation2, 
                                         by = "strata") |>
      dplyr::mutate(stratum_size = n_to_sample.x + n_to_sample.y)
    
    
    # sample and merge data
    phase2_wave2 <- sample_strata(data = phase2_wave1,
                                  strata = "strata",
                                  id = "id",
                                  already_sampled = "sampled_wave1",
                                  design_data = wave2_allocation,
                                  n_allocated = "stratum_size")
    names(phase2_wave2)[names(phase2_wave2) == "sample_indicator"] <- "sampled_wave2"
    
    # Also, remove inflB11 and inflB12 vars
    phase2_wave2 <- subset(phase2_wave2, select = -c(inflB11,
                                                     inflB12))
    
    #####
    ## Wave 3
    #####
    
    # Already sampled indicator
    phase2_wave2$already_sampled <- phase2_wave2$sampled_wave1 +
      phase2_wave2$sampled_wave2
    
    # Calculate influence functions using IPW
    twophase_design_wave2 <- twophase(id = list(~id, ~id), 
                                      strata = list(NULL, ~strata), 
                                      subset = ~as.logical(already_sampled), 
                                      data = phase2_wave2)
    fitY1_wave2 <- svyglm(Y1 ~ X + Z1 + Z2 + Y2, family = quasibinomial, 
                          design = twophase_design_wave2)
    fitY2_wave2 <- svyglm(Y2 ~ X + Z1 + Z2, family = quasibinomial, 
                          design = twophase_design_wave2)
    infl_wave2_Y1 <- inf_fun_logit(fitY1_wave2)
    infl_wave2_Y2 <- inf_fun_logit(fitY2_wave2)
    infl_wave2 <- data.frame(as.numeric(rownames(infl_wave2_Y1)), 
                             infl_wave2_Y1[,"X"],
                             infl_wave2_Y2[,"X"])
    names(infl_wave2) <- c("id", "inflB11", "inflB12")
    phase2_wave2 <- dplyr::left_join(phase2_wave2, infl_wave2, by = "id")
    
    
    # Re-calculate allocations
    allocation1 <- allocate_wave_Neyman(phase2_wave2,
                                        strata = "strata",
                                        y = "inflB11",
                                        method = "iterative",
                                        nsample = n/8,
                                        already_sampled = "already_sampled",
                                        allocation_method = "Neyman")
    
    allocation2 <- allocate_wave_Neyman(phase2_wave2,
                                        strata = "strata",
                                        y = "inflB12",
                                        method = "iterative",
                                        nsample = n/8, 
                                        already_sampled = "already_sampled",
                                        allocation_method = "Neyman")
    
    # and combine
    wave3_allocation <- dplyr::left_join(allocation1, allocation2, 
                                         by = "strata") |>
      dplyr::mutate(stratum_size = n_to_sample.x + n_to_sample.y)
    
    
    # sample and merge data
    phase2_wave3 <- sample_strata(data = phase2_wave2,
                                  strata = "strata",
                                  id = "id",
                                  already_sampled = "already_sampled",
                                  design_data = wave3_allocation,
                                  n_allocated = "stratum_size")
    names(phase2_wave3)[names(phase2_wave3) == "sample_indicator"] <- "sampled_wave3"
    
    # Also, remove inflB11 and inflB12 vars
    phase2_wave3 <- subset(phase2_wave3, select = -c(inflB11,
                                                     inflB12))
    
    #####
    ## Wave 4
    #####
    
    # Already sampled indicator
    phase2_wave3$already_sampled <- phase2_wave3$sampled_wave1 +
      phase2_wave3$sampled_wave2 + phase2_wave3$sampled_wave3
    
    # Calculate influence functions using IPW
    twophase_design_wave3 <- twophase(id = list(~id, ~id), 
                                      strata = list(NULL, ~strata), 
                                      subset = ~as.logical(already_sampled), 
                                      data = phase2_wave3)
    fitY1_wave3 <- svyglm(Y1 ~ X + Z1 + Z2 + Y2, family = quasibinomial, 
                          design = twophase_design_wave3)
    fitY2_wave3 <- svyglm(Y2 ~ X + Z1 + Z2, family = quasibinomial, 
                          design = twophase_design_wave3)
    infl_wave3_Y1 <- inf_fun_logit(fitY1_wave3)
    infl_wave3_Y2 <- inf_fun_logit(fitY2_wave3)
    infl_wave3 <- data.frame(as.numeric(rownames(infl_wave3_Y1)), 
                             infl_wave3_Y1[,"X"],
                             infl_wave3_Y2[,"X"])
    names(infl_wave3) <- c("id", "inflB11", "inflB12")
    phase2_wave3 <- dplyr::left_join(phase2_wave3, infl_wave3, by = "id")
    
    
    # Re-calculate allocations
    allocation1 <- allocate_wave_Neyman(phase2_wave3,
                                        strata = "strata",
                                        y = "inflB12",
                                        method = "iterative",
                                        nsample = n/8, 
                                        already_sampled = "already_sampled",
                                        detailed = TRUE,
                                        allocation_method = "Neyman")
    
    allocation2 <- allocate_wave_Neyman(phase2_wave3,
                                        strata = "strata",
                                        y = "inflB12",
                                        method = "iterative",
                                        nsample = n/8, 
                                        already_sampled = "already_sampled",
                                        detailed = TRUE,
                                        allocation_method = "Neyman")
    
    # Set indicators for oversampling
    oversampled_Y1 <- ifelse(all(allocation1$nsample_optimal == 
                                   allocation1$nsample_actual),
                             0, 1)
    oversampled_Y2 <- ifelse(all(allocation2$nsample_optimal == 
                                   allocation2$nsample_actual),
                             0, 1)
    
    # and combine
    wave4_allocation <- dplyr::left_join(allocation1, allocation2, 
                                         by = "strata") |>
      dplyr::mutate(stratum_size = n_to_sample.x + n_to_sample.y)
    
    # sample and merge data
    phase2_wave4 <- sample_strata(data = phase2_wave3,
                                  strata = "strata",
                                  id = "id",
                                  already_sampled = "already_sampled",
                                  design_data = wave4_allocation,
                                  n_allocated = "stratum_size")
    names(phase2_wave4)[names(phase2_wave4) == "sample_indicator"] <- "sampled_wave4"
    
    # Remove inflB11 and inflB12 vars
    phase2_wave4 <- subset(phase2_wave4, select = -c(inflB11,
                                                     inflB12))
    
    ####
    ## Sampling done: Now calculate the Beta estimates with raking 
    ## using the survey package
    ####
    
    phase2_wave4$already_sampled <- phase2_wave4$sampled_wave1 +
      phase2_wave4$sampled_wave2 + phase2_wave4$sampled_wave3 +
      phase2_wave4$sampled_wave4
    twophase_design <- twophase(id = list(~id, ~id), 
                                strata = list(NULL, ~strata), 
                                subset = ~as.logical(already_sampled), 
                                data = phase2_wave4)
    
    # Weights
    weightY1 <- svyglm(Y1 ~ X + Z1 + Z2 + Y2, family = quasibinomial, 
                       design = twophase_design)
    weightY2 <- svyglm(Y2 ~ X + Z1 + Z2, family = quasibinomial, 
                       design = twophase_design)
    
    # Imputation model for X, Z, Y1, Y2
    imp_model_x <- svyglm(X ~ X_obs + Z1_obs + Z2_obs, design = twophase_design)
    phase2_wave4$imp_x <- as.vector(predict(imp_model_x, 
                                            newdata = phase2_wave4,
                                            type = "response",
                                            se.fit = FALSE))
    
    imp_model_z1 <- svyglm(Z1 ~ X_obs + Z1_obs + Z2_obs, 
                           family = "quasibinomial", design = twophase_design)
    phase2_wave4$imp_z1 <- as.vector(predict(imp_model_z1, 
                                             newdata = phase2_wave4,
                                             type = "response",
                                             se.fit = FALSE))
    
    imp_model_z2 <- svyglm(Z2 ~ X_obs + Z1_obs + Z2_obs, design = twophase_design)
    phase2_wave4$imp_z2 <- as.vector(predict(imp_model_z2, 
                                             newdata = phase2_wave4,
                                             type = "response",
                                             se.fit = FALSE))
    
    imp_model_Y2 <- svyglm(Y2 ~ X_obs + Z1_obs + Z2_obs + Y2_obs,
                           family = "quasibinomial", design = twophase_design)
    phase2_wave4$imp_Y2 <- as.vector(predict(imp_model_Y2, 
                                             newdata = phase2_wave4,
                                             type = "response",
                                             se.fit = FALSE))
    
    # Imputed model for phase 1
    phase1_model_impY1 <- glm(Y1_obs ~ imp_x + imp_z1 + imp_z2 + imp_Y2, 
                              family = binomial, 
                              data = phase2_wave4)
    phase1_model_impY2 <- glm(Y2_obs ~ imp_x + imp_z1 + imp_z2, 
                              family = binomial, 
                              data = phase2_wave4)
    
    # Influence functions from phase1 imputed model
    inf_fun_imp_Y1 <- inf_fun_logit(phase1_model_impY1)
    colnames(inf_fun_imp_Y1) <- c("int","inf_x_Y1",
                                  "inf_z1_Y1", "inf_z2_Y1", "inf_y2_Y1")
    inf_fun_imp_Y2 <- inf_fun_logit(phase1_model_impY2)
    colnames(inf_fun_imp_Y2) <- c("int", "inf_x_Y2",
                                  "inf_z1_Y2", "inf_z2_Y2")
    
    # Re-set up two-phase design
    twophase_design_imp_Y1 <- twophase(id = list(~id, ~id), 
                                       strata = list(NULL, ~strata), 
                                       subset = ~already_sampled, 
                                       data = cbind(phase2_wave4,
                                                    inf_fun_imp_Y1),
                                       method = "simple")
    
    twophase_design_imp_Y2 <- twophase(id = list(~id, ~id), 
                                       strata = list(NULL, ~strata), 
                                       subset = ~already_sampled, 
                                       data = cbind(phase2_wave4,
                                                    inf_fun_imp_Y2),
                                       method = "simple")
    
    # Calibrate
    calibration_formula_Y1 <- make.formula(colnames(inf_fun_imp_Y1))
    calibrated_twophase_Y1 <- calibrate(twophase_design_imp_Y1,
                                        calibration_formula_Y1,
                                        phase = 2,
                                        calfun = "raking")
    calibration_formula_Y2 <- make.formula(colnames(inf_fun_imp_Y2))
    calibrated_twophase_Y2 <- calibrate(twophase_design_imp_Y2,
                                        calibration_formula_Y2,
                                        phase = 2,
                                        calfun = "raking")
    
    # Run models
    fitY1 <- svyglm(Y1 ~ X + Z1 + Z2 + Y2, family = quasibinomial, 
                    design = calibrated_twophase_Y1)
    fitY2 <- svyglm(Y2 ~ X + Z1 + Z2, family = quasibinomial, 
                    design = calibrated_twophase_Y2)
    
    
    
    output <- c(fitY1$coefficients["X"], fitY2$coefficients["X"],
                coef(weightY1)["X"], coef(weightY2)["X"],
                oversampled_Y1, oversampled_Y2)
    return(output)
  }
  
  # Step 6: Run the function for 1,000 iterations, 
  # And iterate this 1000 times, storing the B-hat each time
  B_hat_11_strat2_GR <- c()
  B_hat_12_strat2_GR <- c()
  B_hat_11_strat2_IPW <- c()
  B_hat_12_strat2_IPW <- c()
  n_oversampled_Y1_strat2 <- 0
  n_oversampled_Y2_strat2 <- 0
  
  pb <- txtProgressBar(min = 0, max = 50, initial = 0) # set progress bar
  
  for (i in 1:1000){
    run <- suppressWarnings(Strategy2(n = n, phase1_data = phase1_data))
    B_hat_11_strat2_GR[i] <- run[1]
    B_hat_12_strat2_GR[i] <- run[2]
    B_hat_11_strat2_IPW[i] <- run[3]
    B_hat_12_strat2_IPW[i] <- run[4]
    n_oversampled_Y1_strat2 <- n_oversampled_Y1_strat2 + run[5]
    n_oversampled_Y2_strat2 <- n_oversampled_Y2_strat2 + run[6]
    setTxtProgressBar(pb, i)
  }
  
  # Raking results
  mean_B_11_strat2_GR <- mean(B_hat_11_strat2_GR)
  mean_B_12_strat2_GR <- mean(B_hat_12_strat2_GR)
  var_B_11_strat2_GR <- var(B_hat_11_strat2_GR)
  var_B_12_strat2_GR <- var(B_hat_12_strat2_GR)
  
  # IPW results
  mean_B_11_strat2_IPW <- mean(B_hat_11_strat2_IPW)
  mean_B_12_strat2_IPW <- mean(B_hat_12_strat2_IPW)
  var_B_11_strat2_IPW <- var(B_hat_11_strat2_IPW)
  var_B_12_strat2_IPW <- var(B_hat_12_strat2_IPW)
  
  
  ######
  ######
  ### Phase 2 Sampling - Strategy 3: Independent sequential strategy over 4 waves
  ######
  ######
  
  ## Here, 1st and 2nd waves (n/4 samples each) are optimized for B_11 and 
  ## 3rd and 4th last n/4 are optimized for B_12. 
  
  # Step 1: Initialize Phase 1 data
  phase1_data <- full_data
  
  # Step 2: Logistic regression on Phase 1 data (Y1 only needed)
  fitY1_phase1 <-  glm(Y1_obs ~ X_obs + Z1_obs + Z2_obs + Y2_obs, 
                       family = "binomial", data = phase1_data)
  
  # Step 3: Calculate influence functions using Tong's function
  phase1_data$inflB11 <- inf_fun_logit(fitY1_phase1)[,"X_obs"]
  
  # Step 4: Determine optimum allocation for wave 1 with Wright algorithm
  allocation1 <- optimum_allocation(phase1_data,
                                    strata = "strata",
                                    y = "inflB11",
                                    nsample = n/4, method = "WrightII")
  
  # Step 6a: Now can remove inflB11 column, 
  phase1_data <- subset(phase1_data, select = -c(inflB11))
  
  
  # Step 6: Create function to estimate beta-hat at each iteration
  Strategy3 <- function(n =n, phase1_data = phase1_data){
    
    ####
    ## Wave 1
    ####
    
    # First n/4 according to wave1_allocation
    phase2_wave1 <- sample_strata(data = phase1_data,
                                  strata = "strata",
                                  id = "id",
                                  design_data = allocation1,
                                  n_allocated = "stratum_size")
    names(phase2_wave1)[names(phase2_wave1) == "sample_indicator"] <- "sampled_wave1"
    
    #####
    ## Wave 2
    #####
    
    # Calculate influence functions using IPW
    twophase_design_wave1 <- twophase(id = list(~id, ~id), 
                                      strata = list(NULL, ~strata), 
                                      subset = ~as.logical(sampled_wave1), 
                                      data = phase2_wave1)
    fitY1_wave1 <- svyglm(Y1 ~ X + Z1 + Z2 + Y2, family = quasibinomial, 
                          design = twophase_design_wave1)
    infl_wave1_Y1 <- inf_fun_logit(fitY1_wave1)
    infl_wave1 <- data.frame(as.numeric(rownames(infl_wave1_Y1)), 
                             infl_wave1_Y1[,"X"])
    names(infl_wave1) <- c("id", "inflB11")
    phase2_wave1 <- dplyr::left_join(phase2_wave1, infl_wave1, by = "id")
    
    
    # Calculate allocation for Y1
    wave2_allocation <- allocate_wave_Neyman(phase2_wave1,
                                             strata = "strata",
                                             y = "inflB11",
                                             nsample = n/4, method = "iterative",
                                             already_sampled = "sampled_wave1",
                                             allocation_method = "Neyman")
    
    
    # sample and merge data
    phase2_wave2 <- sample_strata(data = phase2_wave1,
                                  strata = "strata",
                                  id = "id",
                                  already_sampled = "sampled_wave1",
                                  design_data = wave2_allocation,
                                  n_allocated = "n_to_sample")
    names(phase2_wave2)[names(phase2_wave2) == "sample_indicator"] <- "sampled_wave2"
    
    phase2_wave2 <- subset(phase2_wave2, select = -c(inflB11))
    
    #####
    ## Wave 3
    #####
    
    # Indicator for already sampled
    phase2_wave2$already_sampled <- phase2_wave2$sampled_wave1 +
      phase2_wave2$sampled_wave2
    
    # Calculate influence functions using IPW
    twophase_design_wave2 <- twophase(id = list(~id, ~id), 
                                      strata = list(NULL, ~strata), 
                                      subset = ~as.logical(already_sampled), 
                                      data = phase2_wave2)
    fitY2_wave2 <- svyglm(Y2 ~ X + Z1 + Z2, family = quasibinomial, 
                          design = twophase_design_wave2)
    infl_wave2_Y2 <- inf_fun_logit(fitY2_wave2)
    infl_wave2 <- data.frame(as.numeric(rownames(infl_wave2_Y2)), 
                             infl_wave2_Y2[,"X"])
    names(infl_wave2) <- c("id", "inflB12")
    phase2_wave2 <- dplyr::left_join(phase2_wave2, infl_wave2, by = "id")
    
    
    # Re-calculate allocation
    wave3_allocation <- allocate_wave_Neyman(phase2_wave2,
                                             strata = "strata",
                                             y = "inflB12",
                                             nsample = n/4, method = "iterative",
                                             already_sampled = "already_sampled",
                                             allocation_method = "Neyman")
    
    
    # sample and merge data
    phase2_wave3 <- sample_strata(data = phase2_wave2,
                                  strata = "strata",
                                  id = "id",
                                  already_sampled = "already_sampled",
                                  design_data = wave3_allocation,
                                  n_allocated = "n_to_sample")
    
    names(phase2_wave3)[names(phase2_wave3) == "sample_indicator"] <- "sampled_wave3"
    
    phase2_wave3 <- subset(phase2_wave3, select = -c(inflB12))
    
    
    #####
    ## Wave 4
    #####
    
    # Indicator for already sampled
    phase2_wave3$already_sampled <- phase2_wave3$sampled_wave1 +
      phase2_wave3$sampled_wave2 + phase2_wave3$sampled_wave3
    
    # Calculate influence functions using IPW
    twophase_design_wave3 <- twophase(id = list(~id, ~id), 
                                      strata = list(NULL, ~strata), 
                                      subset = ~as.logical(already_sampled), 
                                      data = phase2_wave3)
    fitY2_wave3 <- svyglm(Y2 ~ X + Z1 + Z2, family = quasibinomial, 
                          design = twophase_design_wave3)
    infl_wave3_Y2 <- inf_fun_logit(fitY2_wave3)
    infl_wave3 <- data.frame(as.numeric(rownames(infl_wave3_Y2)),
                             infl_wave3_Y2[,"X"])
    names(infl_wave3) <- c("id", "inflB12")
    phase2_wave3 <- dplyr::left_join(phase2_wave3, infl_wave3, by = "id")
    
    
    # Re-calculate allocation
    wave4_allocation <- allocate_wave_Neyman(phase2_wave3,
                                             strata = "strata",
                                             y = "inflB12",
                                             nsample = n/4, method = "iterative",
                                             already_sampled = "already_sampled",
                                             detailed = TRUE,
                                             allocation_method = "Neyman")
    
    # Check for oversampling
    oversampled_Y2 <- ifelse(all(wave4_allocation$nsample_optimal == 
                                   wave4_allocation$nsample_actual),
                             0, 1)
    # no reason to check for Y1 here, as optimality in later waves with respect to Y2
    
    # sample and merge data
    phase2_wave4 <- sample_strata(data = phase2_wave3,
                                  strata = "strata",
                                  id = "id",
                                  already_sampled = "already_sampled",
                                  design_data = wave4_allocation,
                                  n_allocated = "n_to_sample")
    names(phase2_wave4)[names(phase2_wave4) == "sample_indicator"] <- "sampled_wave4"
    
    phase2_wave4 <- subset(phase2_wave4, select = -c(inflB12))
    
    ####
    ## Sampling done: Now calculate the Beta estimates with raking 
    ## using the survey package
    ####
    
    phase2_wave4$already_sampled <- phase2_wave4$sampled_wave1 +
      phase2_wave4$sampled_wave2 + phase2_wave4$sampled_wave3 +
      phase2_wave4$sampled_wave4
    twophase_design <- twophase(id = list(~id, ~id), 
                                strata = list(NULL, ~strata), 
                                subset = ~as.logical(already_sampled), 
                                data = phase2_wave4)
    
    # Weights
    weightY1 <- svyglm(Y1 ~ X + Z1 + Z2 + Y2, family = quasibinomial, 
                       design = twophase_design)
    weightY2 <- svyglm(Y2 ~ X + Z1 + Z2, family = quasibinomial, 
                       design = twophase_design)
    
    # Imputation model for X, Z, Y1, Y2
    imp_model_x <- svyglm(X ~ X_obs + Z1_obs + Z2_obs, design = twophase_design)
    phase2_wave4$imp_x <- as.vector(predict(imp_model_x, 
                                            newdata = phase2_wave4,
                                            type = "response",
                                            se.fit = FALSE))
    
    imp_model_z1 <- svyglm(Z1 ~ X_obs + Z1_obs + Z2_obs, 
                           family = "quasibinomial", design = twophase_design)
    phase2_wave4$imp_z1 <- as.vector(predict(imp_model_z1, 
                                             newdata = phase2_wave4,
                                             type = "response",
                                             se.fit = FALSE))
    
    imp_model_z2 <- svyglm(Z2 ~ X_obs + Z1_obs + Z2_obs, design = twophase_design)
    phase2_wave4$imp_z2 <- as.vector(predict(imp_model_z2, 
                                             newdata = phase2_wave4,
                                             type = "response",
                                             se.fit = FALSE))
    
    imp_model_Y2 <- svyglm(Y2 ~ X_obs + Z1_obs + Z2_obs + Y2_obs,
                           family = "quasibinomial", design = twophase_design)
    phase2_wave4$imp_Y2 <- as.vector(predict(imp_model_Y2, 
                                             newdata = phase2_wave4,
                                             type = "response",
                                             se.fit = FALSE))
    
    # Imputed model for phase 1
    phase1_model_impY1 <- glm(Y1_obs ~ imp_x + imp_z1 + imp_z2 + imp_Y2, 
                              family = binomial, 
                              data = phase2_wave4)
    phase1_model_impY2 <- glm(Y2_obs ~ imp_x + imp_z1 + imp_z2, 
                              family = binomial, 
                              data = phase2_wave4)
    
    # Influence functions from phase1 imputed model
    inf_fun_imp_Y1 <- inf_fun_logit(phase1_model_impY1)
    colnames(inf_fun_imp_Y1) <- c("int","inf_x_Y1",
                                  "inf_z1_Y1", "inf_z2_Y1", "inf_y2_Y1")
    inf_fun_imp_Y2 <- inf_fun_logit(phase1_model_impY2)
    colnames(inf_fun_imp_Y2) <- c("int", "inf_x_Y2",
                                  "inf_z1_Y2", "inf_z2_Y2")
    
    # Re-set up two-phase design
    twophase_design_imp_Y1 <- twophase(id = list(~id, ~id), 
                                       strata = list(NULL, ~strata), 
                                       subset = ~already_sampled, 
                                       data = cbind(phase2_wave4,
                                                    inf_fun_imp_Y1),
                                       method = "simple")
    
    twophase_design_imp_Y2 <- twophase(id = list(~id, ~id), 
                                       strata = list(NULL, ~strata), 
                                       subset = ~already_sampled, 
                                       data = cbind(phase2_wave4,
                                                    inf_fun_imp_Y2),
                                       method = "simple")
    
    # Calibrate
    calibration_formula_Y1 <- make.formula(colnames(inf_fun_imp_Y1))
    calibrated_twophase_Y1 <- calibrate(twophase_design_imp_Y1,
                                        calibration_formula_Y1,
                                        phase = 2,
                                        calfun = "raking")
    calibration_formula_Y2 <- make.formula(colnames(inf_fun_imp_Y2))
    calibrated_twophase_Y2 <- calibrate(twophase_design_imp_Y2,
                                        calibration_formula_Y2,
                                        phase = 2,
                                        calfun = "raking")
    
    # Run models
    fitY1 <- svyglm(Y1 ~ X + Z1 + Z2 + Y2, family = quasibinomial, 
                    design = calibrated_twophase_Y1)
    fitY2 <- svyglm(Y2 ~ X + Z1 + Z2, family = quasibinomial, 
                    design = calibrated_twophase_Y2)
    
    
    
    output <- c(fitY1$coefficients["X"], fitY2$coefficients["X"],
                coef(weightY1)["X"], coef(weightY2)["X"],
                oversampled_Y2)
    return(output)
  }
  
  # Step 6: Run the function for 1,000 iterations, 
  # And iterate this 1000 times, storing the B-hat each time
  B_hat_11_strat3_GR <- c()
  B_hat_12_strat3_GR <- c()
  B_hat_11_strat3_IPW <- c()
  B_hat_12_strat3_IPW <- c()
  n_oversampled_Y2_strat3 <- 0
  
  pb <- txtProgressBar(min = 0, max = 1000, initial = 0) # set progress bar
  
  for (i in 1:1000){
    run <- suppressWarnings(Strategy3(n = n, phase1_data = phase1_data))
    B_hat_11_strat3_GR[i] <- run[1]
    B_hat_12_strat3_GR[i] <- run[2]
    B_hat_11_strat3_IPW[i] <- run[3]
    B_hat_12_strat3_IPW[i] <- run[4]
    n_oversampled_Y2_strat3 <- n_oversampled_Y2_strat3 + run[5]
    setTxtProgressBar(pb,i)
  }
  
  #Raking results
  mean_B_11_strat3_GR <- mean(B_hat_11_strat3_GR)
  mean_B_12_strat3_GR <- mean(B_hat_12_strat3_GR)
  var_B_11_strat3_GR <- var(B_hat_11_strat3_GR)
  var_B_12_strat3_GR <- var(B_hat_12_strat3_GR)
  
  # IPW results
  mean_B_11_strat3_IPW <- mean(B_hat_11_strat3_IPW)
  mean_B_12_strat3_IPW <- mean(B_hat_12_strat3_IPW)
  var_B_11_strat3_IPW <- var(B_hat_11_strat3_IPW)
  var_B_12_strat3_IPW <- var(B_hat_12_strat3_IPW)
  
  
  
  ######
  ######
  ### Phase 2 Sampling - Strategy 4: Equally weighted A-optimality over 4 waves
  ######
  ######
  
  # Step 1: Initialize phase1_data
  phase1_data <- full_data
  
  # Step 2: Logistic regression on Phase 1 data
  fitY1_phase1 <-  glm(Y1_obs ~ X_obs + Z1_obs + Z2_obs + Y2_obs, 
                       family = "binomial", data = phase1_data)
  fitY2_phase1 <-  glm(Y2_obs ~ X_obs + Z1_obs + Z2_obs, 
                       family = "binomial", data = phase1_data)
  
  # Step 3: Calculate influence functions using Tong's function
  phase1_data$inflB11 <- inf_fun_logit(fitY1_phase1)[,"X_obs"]
  phase1_data$inflB12 <- inf_fun_logit(fitY2_phase1)[,"X_obs"]
  
  # Step 4: Determine optimum allocation for wave 1 with Wright algorithm
  allocation1 <- a_optimum_allocation(phase1_data,
                                      strata = "strata",
                                      nsample = n/4,
                                      vars = c("inflB11", "inflB12"),
                                      weights = c(0.5, 0.5),
                                      method = "WrightII")
  
  # Also, remove inflB11 and inflB12 vars
  phase1_data <- subset(phase1_data, select = -c(inflB11,
                                                 inflB12))
  
  # Step 5: Create function to estimate beta-hat at each iteration
  Strategy4 <- function(){
    
    ####
    ## Wave 1
    ####
    
    # First n/4 according to wave1_allocation
    phase2_wave1 <- sample_strata(data = phase1_data,
                                  strata = "strata",
                                  id = "id",
                                  design_data = allocation1,
                                  n_allocated = "stratum_size")
    
    names(phase2_wave1)[names(phase2_wave1) == "sample_indicator"] <- "sampled_wave1"
    
    #####
    ## Wave 2
    #####
    
    # Calculate influence functions using IPW
    twophase_design_wave1 <- twophase(id = list(~id, ~id), 
                                      strata = list(NULL, ~strata), 
                                      subset = ~as.logical(sampled_wave1), 
                                      data = phase2_wave1)
    fitY1_wave1 <- svyglm(Y1 ~ X + Z1 + Z2 + Y2, family = quasibinomial, 
                          design = twophase_design_wave1)
    fitY2_wave1 <- svyglm(Y2 ~ X + Z1 + Z2, family = quasibinomial, 
                          design = twophase_design_wave1)
    infl_wave1_Y1 <- inf_fun_logit(fitY1_wave1)
    infl_wave1_Y2 <- inf_fun_logit(fitY2_wave1)
    infl_wave1 <- data.frame(as.numeric(rownames(infl_wave1_Y1)), 
                             infl_wave1_Y1[,"X"],
                             infl_wave1_Y2[,"X"])
    names(infl_wave1) <- c("id", "inflB11", "inflB12")
    phase2_wave1 <- dplyr::left_join(phase2_wave1, infl_wave1, by = "id")
    
    
    # Calculate allocation for wave 2
    wave2_allocation <- a_optimal_allocate_wave(phase2_wave1,
                                                strata = "strata",
                                                vars = c("inflB11", "inflB12"),
                                                weights = c(0.5, 0.5),
                                                already_sampled = "sampled_wave1",
                                                nsample = n/4,
                                                method = "simple",
                                                allocation_method = "Neyman")
    
    
    # sample and merge data
    phase2_wave2 <- sample_strata(data = phase2_wave1,
                                  strata = "strata",
                                  id = "id",
                                  already_sampled = "sampled_wave1",
                                  design_data = wave2_allocation,
                                  n_allocated = "n_to_sample")
    names(phase2_wave2)[names(phase2_wave2) == "sample_indicator"] <- "sampled_wave2"
    
    phase2_wave2 <- subset(phase2_wave2, select = -c(inflB11,
                                                     inflB12))
    
    #####
    ## Wave 3
    #####
    
    # Calculate influence functions using IPW
    phase2_wave2$already_sampled <- phase2_wave2$sampled_wave1 +
      phase2_wave2$sampled_wave2
    twophase_design_wave2 <- twophase(id = list(~id, ~id), 
                                      strata = list(NULL, ~strata), 
                                      subset = ~as.logical(already_sampled), 
                                      data = phase2_wave2)
    fitY1_wave2 <- svyglm(Y1 ~ X + Z1 + Z2 + Y2, family = quasibinomial, 
                          design = twophase_design_wave2)
    fitY2_wave2 <- svyglm(Y2 ~ X + Z1 + Z2, family = quasibinomial, 
                          design = twophase_design_wave2)
    infl_wave2_Y1 <- inf_fun_logit(fitY1_wave2)
    infl_wave2_Y2 <- inf_fun_logit(fitY2_wave2)
    infl_wave2 <- data.frame(as.numeric(rownames(infl_wave2_Y1)), 
                             infl_wave2_Y1[,"X"],
                             infl_wave2_Y2[,"X"])
    names(infl_wave2) <- c("id", "inflB11", "inflB12")
    phase2_wave2 <- dplyr::left_join(phase2_wave2, infl_wave2, by = "id")
    
    
    # Re-calculate allocations
    wave3_allocation <- a_optimal_allocate_wave(phase2_wave2,
                                                strata = "strata",
                                                vars = c("inflB11", "inflB12"),
                                                weights = c(0.5, 0.5),
                                                already_sampled = "already_sampled",
                                                nsample = n/4,
                                                method = "simple",
                                                detailed = TRUE,
                                                allocation_method = "Neyman")
    
    
    # sample and merge data
    phase2_wave3 <- sample_strata(data = phase2_wave2,
                                  strata = "strata",
                                  id = "id",
                                  already_sampled = "already_sampled",
                                  design_data = wave3_allocation,
                                  n_allocated = "n_to_sample")
    names(phase2_wave3)[names(phase2_wave3) == "sample_indicator"] <- "sampled_wave3"
    
    phase2_wave3 <- subset(phase2_wave3, select = -c(inflB11, inflB12))
    
    #####
    ## Wave 4
    #####
    
    # Indicator for already sampled
    phase2_wave3$already_sampled <- phase2_wave3$sampled_wave1 +
      phase2_wave3$sampled_wave2 + phase2_wave3$sampled_wave3
    
    # Calculate influence functions using IPW
    twophase_design_wave3 <- twophase(id = list(~id, ~id), 
                                      strata = list(NULL, ~strata), 
                                      subset = ~as.logical(already_sampled), 
                                      data = phase2_wave3)
    fitY1_wave3 <- svyglm(Y1 ~ X + Z1 + Z2 + Y2, family = quasibinomial, 
                          design = twophase_design_wave3)
    fitY2_wave3 <- svyglm(Y2 ~ X + Z1 + Z2, family = quasibinomial, 
                          design = twophase_design_wave3)
    infl_wave3_Y1 <- inf_fun_logit(fitY1_wave3)
    infl_wave3_Y2 <- inf_fun_logit(fitY2_wave3)
    infl_wave3 <- data.frame(as.numeric(rownames(infl_wave3_Y1)), 
                             infl_wave3_Y1[,"X"],
                             infl_wave3_Y2[,"X"])
    names(infl_wave3) <- c("id", "inflB11", "inflB12")
    phase2_wave3 <- dplyr::left_join(phase2_wave3, infl_wave3, by = "id")
    
    
    # Re-calculate allocation
    wave4_allocation <- a_optimal_allocate_wave(phase2_wave3,
                                                strata = "strata",
                                                vars = c("inflB11", "inflB12"),
                                                weights = c(0.5, 0.5),
                                                already_sampled = "already_sampled",
                                                nsample = n/4,
                                                method = "simple",
                                                allocation_method = "Neyman",
                                                detailed = TRUE)
    
    # Check for oversampling
    oversampled_A_optimal <- ifelse(all(wave4_allocation$nsample_optimal == 
                                          wave4_allocation$nsample_actual),
                                    0, 1)
    
    
    # sample and merge data
    phase2_wave4 <- sample_strata(data = phase2_wave3,
                                  strata = "strata",
                                  id = "id",
                                  design_data = wave4_allocation,
                                  already_sampled = "already_sampled",
                                  n_allocated = "n_to_sample")
    names(phase2_wave4)[names(phase2_wave4) == "sample_indicator"] <- "sampled_wave4"
    
    phase2_wave4 <- subset(phase2_wave4, select = -c(inflB11,
                                                     inflB12))
    
    ####
    ## Sampling done: Now calculate the Beta estimates with raking 
    ## using the survey package
    ####
    
    phase2_wave4$already_sampled <- phase2_wave4$sampled_wave1 + 
      phase2_wave4$sampled_wave2 + phase2_wave4$sampled_wave3 + 
      phase2_wave4$sampled_wave4
    twophase_design <- twophase(id = list(~id, ~id), 
                                strata = list(NULL, ~strata), 
                                subset = ~as.logical(already_sampled), 
                                data = phase2_wave4)
    
    # Weights
    weightY1 <- svyglm(Y1 ~ X + Z1 + Z2 + Y2, family = quasibinomial, 
                       design = twophase_design)
    weightY2 <- svyglm(Y2 ~ X + Z1 + Z2, family = quasibinomial, 
                       design = twophase_design)
    
    # Imputation model for X, Z, Y1, Y2
    imp_model_x <- svyglm(X ~ X_obs + Z1_obs + Z2_obs, design = twophase_design)
    phase2_wave4$imp_x <- as.vector(predict(imp_model_x, 
                                            newdata = phase2_wave4,
                                            type = "response",
                                            se.fit = FALSE))
    
    imp_model_z1 <- svyglm(Z1 ~ X_obs + Z1_obs + Z2_obs, 
                           family = "quasibinomial", design = twophase_design)
    phase2_wave4$imp_z1 <- as.vector(predict(imp_model_z1, 
                                             newdata = phase2_wave4,
                                             type = "response",
                                             se.fit = FALSE))
    
    imp_model_z2 <- svyglm(Z2 ~ X_obs + Z1_obs + Z2_obs, design = twophase_design)
    phase2_wave4$imp_z2 <- as.vector(predict(imp_model_z2, 
                                             newdata = phase2_wave4,
                                             type = "response",
                                             se.fit = FALSE))
    
    imp_model_Y2 <- svyglm(Y2 ~ X_obs + Z1_obs + Z2_obs + Y2_obs,
                           family = "quasibinomial", design = twophase_design)
    phase2_wave4$imp_Y2 <- as.vector(predict(imp_model_Y2, 
                                             newdata = phase2_wave4,
                                             type = "response",
                                             se.fit = FALSE))
    
    # Imputed model for phase 1
    phase1_model_impY1 <- glm(Y1_obs ~ imp_x + imp_z1 + imp_z2 + imp_Y2, 
                              family = binomial, 
                              data = phase2_wave4)
    phase1_model_impY2 <- glm(Y2_obs ~ imp_x + imp_z1 + imp_z2, 
                              family = binomial, 
                              data = phase2_wave4)
    
    # Influence functions from phase1 imputed model
    inf_fun_imp_Y1 <- inf_fun_logit(phase1_model_impY1)
    colnames(inf_fun_imp_Y1) <- c("int","inf_x_Y1",
                                  "inf_z1_Y1", "inf_z2_Y1", "inf_y2_Y1")
    inf_fun_imp_Y2 <- inf_fun_logit(phase1_model_impY2)
    colnames(inf_fun_imp_Y2) <- c("int", "inf_x_Y2",
                                  "inf_z1_Y2", "inf_z2_Y2")
    
    # Re-set up two-phase design
    twophase_design_imp_Y1 <- twophase(id = list(~id, ~id), 
                                       strata = list(NULL, ~strata), 
                                       subset = ~as.logical(already_sampled), 
                                       data = cbind(phase2_wave4,
                                                    inf_fun_imp_Y1),
                                       method = "simple")
    
    twophase_design_imp_Y2 <- twophase(id = list(~id, ~id), 
                                       strata = list(NULL, ~strata), 
                                       subset = ~as.logical(already_sampled), 
                                       data = cbind(phase2_wave4,
                                                    inf_fun_imp_Y2),
                                       method = "simple")
    
    # Calibrate
    calibration_formula_Y1 <- make.formula(colnames(inf_fun_imp_Y1))
    calibrated_twophase_Y1 <- calibrate(twophase_design_imp_Y1,
                                        calibration_formula_Y1,
                                        phase = 2,
                                        calfun = "raking")
    calibration_formula_Y2 <- make.formula(colnames(inf_fun_imp_Y2))
    calibrated_twophase_Y2 <- calibrate(twophase_design_imp_Y2,
                                        calibration_formula_Y2,
                                        phase = 2,
                                        calfun = "raking")
    
    # Run models
    fitY1 <- svyglm(Y1 ~ X + Z1 + Z2 + Y2, family = quasibinomial, 
                    design = calibrated_twophase_Y1)
    fitY2 <- svyglm(Y2 ~ X + Z1 + Z2, family = quasibinomial, 
                    design = calibrated_twophase_Y2)
    
    
    
    output <- c(fitY1$coefficients["X"], fitY2$coefficients["X"], 
                coef(weightY1)["X"], coef(weightY2)["X"],
                oversampled_A_optimal)
    return(output)
  }
  
  # Step 6: Run the function for 1,000 iterations, 
  # And iterate this 1000 times, storing the B-hat each time
  B_hat_11_strat4_GR <- c()
  B_hat_12_strat4_GR <- c()
  B_hat_11_strat4_IPW <- c()
  B_hat_12_strat4_IPW <- c()
  n_oversampled_strat4 <- 0
  
  pb <- txtProgressBar(min = 0, max = 1000, initial = 0) # set progress bar
  
  for (i in 1:1000){
    run <- Strategy4()
    B_hat_11_strat4_GR[i] <- run[1]
    B_hat_12_strat4_GR[i] <- run[2]
    B_hat_11_strat4_IPW[i] <- run[3]
    B_hat_12_strat4_IPW[i] <- run[4]
    n_oversampled_strat4 <- n_oversampled_strat4 + run[5]
    setTxtProgressBar(pb,i)
  }
  
  # Raking results
  mean_B_11_strat4_GR <- mean(B_hat_11_strat4_GR)
  mean_B_12_strat4_GR <- mean(B_hat_12_strat4_GR)
  var_B_11_strat4_GR <- var(B_hat_11_strat4_GR)
  var_B_12_strat4_GR <- var(B_hat_12_strat4_GR)
  
  # IPW results
  mean_B_11_strat4_IPW <- mean(B_hat_11_strat4_IPW)
  mean_B_12_strat4_IPW <- mean(B_hat_12_strat4_IPW)
  var_B_11_strat4_IPW <- var(B_hat_11_strat4_IPW)
  var_B_12_strat4_IPW <- var(B_hat_12_strat4_IPW)
  
  
  
  
  #####
  ## View results
  #####
  
  results <- data.frame(Strategy = c(1,2,3,4),
                        "true_B_11" = c(true_B_11, 0,0,0),
                        "true_B_12" = c(true_B_12, 0,0,0),
                        "cor_Y1_Y2" = c(cor_Y1_Y2, 0,0,0),
                        "prev_Y1" = c(prev_Y1, 0,0,0),
                        "prev_Y2" = c(prev_Y2, 0,0,0),
                        "mean(B_11)_GR" = c(mean_B_11_strat1_GR,
                                            mean_B_11_strat2_GR,
                                            mean_B_11_strat3_GR,
                                            mean_B_11_strat4_GR),
                        "mean(B_12)_GR" = c(mean_B_12_strat1_GR,
                                            mean_B_12_strat2_GR,
                                            mean_B_12_strat3_GR,
                                            mean_B_12_strat4_GR),
                        "var(B_11)_GR" = c(var_B_11_strat1_GR,
                                           var_B_11_strat2_GR,
                                           var_B_11_strat3_GR,
                                           var_B_11_strat4_GR),
                        "var(B_12)_GR" = c(var_B_12_strat1_GR,
                                           var_B_12_strat2_GR,
                                           var_B_12_strat3_GR,
                                           var_B_12_strat4_GR),
                        "mean(B_11)_IPW" = c(mean_B_11_strat1_IPW,
                                             mean_B_11_strat2_IPW,
                                             mean_B_11_strat3_IPW,
                                             mean_B_11_strat4_IPW),
                        "mean(B_12)_IPW" = c(mean_B_12_strat1_IPW,
                                             mean_B_12_strat2_IPW,
                                             mean_B_12_strat3_IPW,
                                             mean_B_12_strat4_IPW),
                        "var(B_11)_IPW" = c(var_B_11_strat1_IPW,
                                            var_B_11_strat2_IPW,
                                            var_B_11_strat3_IPW,
                                            var_B_11_strat4_IPW),
                        "var(B_12)_IPW" = c(var_B_12_strat1_IPW,
                                            var_B_12_strat2_IPW,
                                            var_B_12_strat3_IPW,
                                            var_B_12_strat4_IPW),
                        "n_oversampled_Y1" = c(NA, n_oversampled_Y1_strat2,
                                               NA, NA),
                        "n_oversampled_Y2" = c(NA, n_oversampled_Y2_strat2,
                                               n_oversampled_Y2_strat3, NA),
                        "n_oversampled_overall" = c(NA, NA, NA, 
                                                    n_oversampled_strat4))
  
  print(results)
  
  # save
  pathname <- paste0("20230809results_", names(simulations_df)[scenario], ".csv")
  write.csv(results, pathname, row.names = FALSE)
}

