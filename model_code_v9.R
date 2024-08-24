# Load necessary libraries
library(bigmemory) # Used for rapid management of large matrices
library(bigtabulate) # Used for recording daily counts within each compartment
library(arrow) # Used to work with arrow files
library(data.table) # Used to create the final table containing daily counts
library(progress) # Informative progress bar showing time remaining too
library(ggplot2) # Used to create high-quality plots compared to base R plots
library(dplyr) # For data manipulation tools
library(truncdist) # For truncated gamma distribution, modelling measles
# transmission

# Used for running tasks in parallel
library(future)
library(future.apply)
library(parallel)

# Function to create the population matrix
make_pop <- function(dat) {
  n <- nrow(dat)  # Use nrow for a data frame
  pop <- bigmemory::big.matrix(
    nrow = n, ncol = 4,
    type = "integer",
    dimnames = list(NULL, c("i", "status", "t.exp", "t.inf"))
  )
  
  # Initialise the population matrix
  pop[, 1] <- 1:n
  pop[, 2] <- as.integer(1)  # Susceptible
  pop[, 3] <- NA             # Time when exposed
  pop[, 4] <- NA             # Time when infected
  
  return(pop)
}

# Function to make initial infected cases
make_index_case <- function(pop, index_cases, t) {
  pop[index_cases, 2] <- 3  # Set status to infected (I = 3)
  pop[index_cases, 4] <- t  # Set exposure time to t
  return(pop)
}

# Function to update exposed individuals
make_exposed <- function(pop, exposed_indices, t) {
  pop[exposed_indices, 2] <- 2  # Set status to exposed (E = 2)
  pop[exposed_indices, 3] <- t  # Set exposure time to t
  return(pop)
}

# Function to update infected individuals
make_infected <- function(pop, exposed_indices, t, lambda) {
  latent_times <- pop[exposed_indices, 3] + as.integer(round(rgamma(length(exposed_indices), shape = 0.5, rate = lambda)))
  
  latent_expired <- exposed_indices[t >= latent_times]
  if (length(latent_expired) > 0) {
    pop[latent_expired, 2] <- 3  # Set status to infected (I = 3)
    pop[latent_expired, 4] <- t  # Set infection time to t
  }
  
  return(pop)
}

# Function to update recovered individuals
make_recovered <- function(pop, infected_indices, t, gamma) {
  recovery_times <- pop[infected_indices, 4] + as.integer(round(rgamma(length(infected_indices), shape = 0.5, rate = gamma)))
  
  recovered_indices <- infected_indices[t >= recovery_times]
  if (length(recovered_indices) > 0) {
    pop[recovered_indices, 2] <- 4  # Set status to recovered (R = 4)
  }
  
  return(pop)
}

precompute_data <- function(dat, K_other, K_school, beta, t.step, year_isolation) {
  # Define the fixed order of age groups
  age_group_order <- c("0-4", "5", "6", "7", "8", "9", "10", "11", "12", "13", "14", "15", "16-19",
                       "20-24", "25-29", "30-34", "35-39", "40-44", "45-49", "50-54", "55-59",
                       "60-64", "65-69", "70-74", "75-79", "80+")
  
  # Extract demographic data
  school_names <- dat$school_name
  home_ids <- dat$home_id
  age_groups <- dat$K_ageg
  
  unique_schools <- unique(school_names)
  unique_homes <- unique(home_ids)
  unique_age_groups <- sort(unique(as.character(age_groups)))
  
  # Mapping demographic data to indices
  school_indices <- match(school_names, unique_schools)
  home_indices <- match(home_ids, unique_homes)
  
  # Ensure that age_to_index correctly maps age groups to indices
  age_to_index <- match(age_groups, age_group_order)
  
  # Calculate community contact matrix
  community_contact_matrix <- beta * t.step * K_other
  
  # Initialise aggregate school contact matrix
  # Use a diagonal matrix if year isolation has been implemented
  # i.e. the diagonal of the school matrix is kept, the rest of the values are 0s
  
  if (year_isolation) {
    aggregate_school_matrix <- diag(diag(beta * t.step * K_school))
  } else {
    aggregate_school_matrix <- beta * t.step * K_school
  }
  
  list(
    school_indices = school_indices,
    home_indices = home_indices,
    age_to_index = age_to_index,
    unique_age_groups = unique_age_groups,
    community_contact_matrix = community_contact_matrix,
    aggregate_school_matrix = aggregate_school_matrix
  )
}

# The transmission functions moves people from the susceptible compartment
# to the infected compartment based on the individual's probability of infection.
# This is influenced by the forces of infection from the home, 
# school (if they attend school), and community settings. 

transmission <- function(dat, pop, K_other, current_K_school, t, t.step, beta, precomputed) {
  # Extract the number of age groups from K_other and current_K_school
  num_age_groups <- ncol(K_other)
  N <- nrow(dat)  # Number of rows in the demographic data
  
  # Identify susceptible and infected individuals
  susceptible_indices <- which(pop[, 2] == 1)
  infected_indices <- which(pop[, 2] == 3)
  
  if (length(infected_indices) == 0) return(pop)  # No infected individuals, no transmission
  
  # Use precomputed data to reduce repetitive calculations where possible
  school_indices <- precomputed$school_indices
  home_indices <- precomputed$home_indices
  age_to_index <- precomputed$age_to_index
  unique_age_groups <- precomputed$unique_age_groups
  community_contact_matrix <- precomputed$community_contact_matrix
  
  # Compute the number of infected individuals in each age group
  age_groups <- dat$K_ageg
  infected_counts_by_age_group <- table(age_groups[infected_indices])
  names(infected_counts_by_age_group) <- unique_age_groups
  infected_counts_by_age_group <- as.numeric(infected_counts_by_age_group[unique_age_groups])
  
  # Normalise the infected counts per age group
  total_infected <- sum(infected_counts_by_age_group)
  if (total_infected > 0) {
    infected_proportion <- infected_counts_by_age_group / total_infected
  } else {
    infected_proportion <- rep(0, num_age_groups)
  }
  
  # Compute infected proportions by school and age group
  school_infected_counts <- matrix(0, nrow = num_age_groups, ncol = length(unique(school_indices)))
  school_total_infected <- numeric(length(unique(school_indices)))
  
  for (i in seq_along(infected_indices)) {
    sch_idx <- school_indices[infected_indices[i]]
    age_idx <- age_to_index[infected_indices[i]]
    
    if (!is.na(sch_idx) && !is.na(age_idx)) {
      school_infected_counts[age_idx, sch_idx] <- school_infected_counts[age_idx, sch_idx] + 1
    }
  }
  
  # Compute total infected counts by school
  school_total_infected <- colSums(school_infected_counts)
  
  # Compute proportions
  school_infected_proportions <- matrix(0, nrow = num_age_groups, ncol = length(unique(school_indices)))
  for (j in seq_len(length(unique(school_indices)))) {
    if (school_total_infected[j] > 0) {
      school_infected_proportions[, j] <- school_infected_counts[, j] / school_total_infected[j]
    }
  }
  
  # Compute home contact contributions
  home_infected_counts <- matrix(0, nrow = num_age_groups, ncol = length(unique(home_indices)))
  home_total_infected <- numeric(length(unique(home_indices)))
  
  for (i in seq_along(infected_indices)) {
    home_idx <- home_indices[infected_indices[i]]
    age_idx <- age_to_index[infected_indices[i]]
    
    if (!is.na(home_idx) && !is.na(age_idx)) {
      home_infected_counts[age_idx, home_idx] <- home_infected_counts[age_idx, home_idx] + 1
    }
  }
  
  # Compute total infected counts by home
  home_total_infected <- colSums(home_infected_counts)
  
  # Compute proportions
  home_infected_proportions <- matrix(0, nrow = num_age_groups, ncol = length(unique(home_indices)))
  for (j in seq_len(length(unique(home_indices)))) {
    if (home_total_infected[j] > 0) {
      home_infected_proportions[, j] <- home_infected_counts[, j] / home_total_infected[j]
    }
  }
  
  # Initialise vectors for forces of infection
  FoI_school <- numeric(N)
  FoI_home <- numeric(N)
  FoI_community <- numeric(N)
  
  for (i in seq_len(N)) {
    sch_idx <- school_indices[i]
    home_idx <- home_indices[i]
    age_idx <- age_to_index[i]
    
    # Adjust school contact intensity
    if (!is.na(sch_idx)) {
      FoI_school[i] <- sum(current_K_school[age_idx, ] * school_infected_proportions[age_idx, sch_idx])
    }
    
    # Adjust home contact intensity
    if (!is.na(home_idx)) {
      FoI_home[i] <- sum(beta * t.step * home_infected_proportions[age_idx, home_idx])
    }
    
    # Community contact intensity (same for all individuals)
    FoI_community[i] <- sum(community_contact_matrix[age_idx, ] * infected_proportion)
  }
  
  # Calculate probabilities of infection
  p.inf_school <- 1 - exp(-FoI_school)
  p.inf_community <- 1 - exp(-FoI_community)
  p.inf_home <- 1 - exp(-FoI_home)
  
  # Combine probabilities
  combined_prob <- 1 - (1 - p.inf_school) * (1 - p.inf_community) * (1 - p.inf_home)
  combined_prob <- pmin(combined_prob, 1)
  
  # Determine which susceptible individuals get exposed
  rnd <- runif(N)
  exposed_indices <- susceptible_indices[rnd[susceptible_indices] < combined_prob[susceptible_indices]]
  
  if (length(exposed_indices) > 0) {
    pop <- make_exposed(pop, exposed_indices, t)
  }
  
  return(pop)
}

# Main simulation function, which brings all the functions together
# The function provides overall SEIR counts for the population and by age group.
# The missed school days is also provided by age group, when a reduced school
# week or reactive closures are enforced. 

# The model is designed to be flexible, allowing you to provide your own
# disease parameters. If you do, make sure to add your latent and recovery

# Hospitalisation counts occur once an individual enters the recovered
# compartment. Currently, hospitalisation is not supported when not choosing a
# default disease (covid-19, measles, or influenza). 

# If a supported disease is selected, then hospitalisation counts are provided
# at an overall level as well as by age group at evey time step.

# Each time step is one day. 

simulate_epidemic_plus <- function(dat, K_other, K_school, initial_infected, 
                                   max_days = Inf, school_week = 5, year_isolation = FALSE, 
                                   threshold = NULL, length_of_closure = NULL, disease = NULL, 
                                   lambda = NULL, beta = NULL, gamma = NULL, max_sim_time = Inf) {
  
  # Minimise warnings from bigmemory due to type conversion
  options(bigmemory.typecast.warning=FALSE)
  
  # Conditions to make sure parameters have been inputted correctly
  if (school_week < 0 || school_week > 5) {
    stop("The number of days in a school week must be between 0 and 5")
  }
  
  if (!is.null(threshold) && (threshold < 0 || threshold > 1)) {
    stop("Threshold must be between 0 and 1")
  }
  
  if (!is.null(threshold) && is.null(length_of_closure)) {
    stop("Length of closure must be specified if threshold is provided")
  }
  
  if (!is.null(length_of_closure) && length_of_closure <= 0) {
    stop("Length of closure must be greater than 0")
  }
  
  # Default disease parameters if either covid, measles or influenza is selected
  # If you're providing your own parameters, then there are checks to ensure 
  # you have forgotten to provide one. 
  
  # When specifying your own parameters, make sure to provide your own
  # latent_periods and recovery_periods here. Once you've done that, uncomment
  # the section below
  
  # latent_periods = 
  # recovery_periods = 
  
  if (!is.null(disease)) {
    disease <- tolower(disease)
    if (disease == "measles") {
      beta <- 0.5
      gamma <- 0.01 
      lambda <- 0.98
      latent_periods <- as.integer(round(rtrunc(nrow(dat), spec = "gamma", a = 0, b = 15, shape = 2, rate = lambda)))
      recovery_periods <- as.integer(round(rtrunc(nrow(dat), spec = "gamma", a = 0, b = 25, shape = 0.5, rate = gamma)))
    } else if (disease == "influenza") {
      beta <- 0.007
      gamma <- 2.5 
      lambda <- 2.8 
      latent_periods <- as.integer(rweibull(nrow(dat), shape = 1.8, scale = lambda))
      recovery_periods <- as.integer(rweibull(nrow(dat), shape = 2, scale = gamma))
    } else if (disease == "covid-19") {
      beta <- 0.008
      gamma <- 5 
      lambda <- 4.35
      latent_periods <- as.integer(rweibull(nrow(dat), shape = 1.8, scale = lambda))
      recovery_periods <- as.integer(rweibull(nrow(dat), shape = 2, scale = gamma))
    } else {
      stop("Unsupported disease type. Choose from 'measles', 'influenza', or 'covid-19'.")
    }
  }
  
  if (is.null(lambda) || lambda <= 0) {
    stop("Lambda must be provided and greater than 0")
  }
  
  if (is.null(beta) || beta <= 0) {
    stop("Beta must be provided and greater than 0")
  }
  
  if (is.null(gamma) || gamma <= 0) {
    stop("Gamma must be provided and greater than 0")
  }
  
  # If a specified number of days has not been provided (i.e a max simulation
  # time has been provided instead), then we provide a default at 250 days. 
  
  default_max_days <- 250
  if (is.infinite(max_days)) {
    max_days <- default_max_days
  }
  
  pop <- make_pop(dat)
  
  index_cases <- sample(1:nrow(dat), initial_infected)
  pop <- make_index_case(pop, index_cases, t = 0)
  
  
  precomputed <- precompute_data(dat, K_other, K_school, beta, t.step = 1, year_isolation)
  
  SEIR <- bigmemory::big.matrix(max_days + 1, 6, type = "integer",
                                dimnames = list(NULL, c("S", "E", "I", "R", "Students_No_School", "N_Hospitalised")))
  
  counts <- bigtabulate::bigtable(as.matrix(pop[, 2]), ccols = 1)
  initial_counts <- integer(4)
  names(initial_counts) <- as.character(1:4)
  initial_counts[names(counts)] <- as.integer(counts)
  SEIR[1, ] <- c(initial_counts, 0, 0)
  
  age_groups <- unique(dat$K_ageg)
  n_age_groups <- length(age_groups)
  age_group_counts <- array(0, dim = c(max_days + 1, n_age_groups, 4),
                            dimnames = list(Time = 0:max_days, Age_Group = age_groups, Compartment = c("S", "E", "I", "R")))
  age_group_hospitalised <- array(0, dim = c(max_days + 1, n_age_groups),
                                  dimnames = list(Time = 0:max_days, Age_Group = age_groups))
  
  school_age_groups <- c("0-4", "5", "6", "7", "8", "9", "10", "11", "12", "13", "14", "15", "16-19")
  
  school_age_indices <- which(dat$K_ageg %in% school_age_groups)
  missed_school_days <- integer(nrow(dat))
  missed_school_days[school_age_indices] <- 0
  
  missed_days_per_week <- 5 - school_week
  
  school_counts <- integer(max_days + 1)
  
  if (!is.null(threshold)) {
    unique_schools <- unique(dat$school_name)
    school_closure_weeks <- rep(0, length(unique_schools))
    names(school_closure_weeks) <- unique_schools
  }
  
  if (school_week == 0) {
    school_counts[] <- length(school_age_indices)
  }
  
  hosp_probs <- NULL
  if (!is.null(disease)) {
    if (disease == "measles") {
      hosp_probs <- dat$measles_hosp_probs
    } else if (disease == "influenza") {
      hosp_probs <- dat$flu_hosp_probs
    } else if (disease == "covid-19") {
      hosp_probs <- dat$cov_hosp_probs
    }
  }
  
  hospitalised <- rep(FALSE, nrow(dat))
  
  for (age_group in age_groups) {
    indices <- which(dat$K_ageg == age_group)
    initial_exposed <- sum(pop[indices, 2] == 2)
    age_group_counts[1, age_group, "S"] <- sum(pop[indices, 2] == 1)
    age_group_counts[1, age_group, "E"] <- initial_exposed
    age_group_counts[1, age_group, "I"] <- sum(pop[indices, 2] == 3)
    age_group_counts[1, age_group, "R"] <- sum(pop[indices, 2] == 4)
  }
  
  start_time <- Sys.time()
  
  pb <- progress::progress_bar$new(
    format = "  :bar :percent Elapsed: :elapsed Time remaining: :eta",
    total = max_days,
    clear = FALSE
  )
  
  for (t in seq_len(max_days)) {
    elapsed_time <- as.numeric(difftime(Sys.time(), start_time, units = "mins"))
    if (elapsed_time > max_sim_time) {
      message("Max simulation time exceeded.")
      break
    }
    
    day_of_week <- (t - 1) %% 7 + 1
    
    if (school_week > 0 && day_of_week >= 1 && day_of_week <= school_week) {
      if (!is.null(threshold)) {
        closed_schools <- names(school_closure_weeks)[school_closure_weeks > 0]
        closed_age_groups <- unique(dat$K_ageg[dat$school_name %in% closed_schools])
        if (length(closed_age_groups) > 0) {
          closed_indices <- which(age_groups %in% closed_age_groups)
          if (length(closed_indices) > 0) {
            current_K_school <- precomputed$aggregate_school_matrix
            current_K_school[closed_indices, ] <- 0
            current_K_school[, closed_indices] <- 0
            affected_indices <- which(dat$K_ageg %in% closed_age_groups)
            school_counts[t + 1] <- length(affected_indices)
            missed_school_days[affected_indices] <- missed_school_days[affected_indices] + 1
          } else {
            current_K_school <- precomputed$aggregate_school_matrix
          }
        } else {
          current_K_school <- precomputed$aggregate_school_matrix
        }
      } else {
        current_K_school <- precomputed$aggregate_school_matrix
      }
    } else {
      current_K_school <- matrix(0, nrow = nrow(precomputed$aggregate_school_matrix), ncol = ncol(precomputed$aggregate_school_matrix))
      if (day_of_week >= 1 && day_of_week <= 5) {
        missed_school_days[school_age_indices] <- missed_school_days[school_age_indices] + 1
      }
    }
    
    pop <- transmission(dat, pop, K_other, current_K_school, t, t.step = 1, beta, precomputed)
    
    exposed_indices <- which(pop[, 2] == 2)
    latent_expired <- t >= (pop[exposed_indices, 3] + latent_periods[exposed_indices])
    if (any(latent_expired)) {
      pop <- make_infected(pop, exposed_indices[latent_expired], t, lambda)
    }
    
    infected_indices <- which(pop[, 2] == 3)
    recovered_indices <- t >= (pop[infected_indices, 4] + recovery_periods[infected_indices])
    if (any(recovered_indices)) {
      pop <- make_recovered(pop, infected_indices[recovered_indices], t, gamma)
    }
    
    if (!is.null(hosp_probs)) {
      new_hospitalised <- (pop[, 2] == 4) & (!hospitalised) & (is.na(hosp_probs) | (runif(nrow(pop))) < hosp_probs)
      hospitalised <- hospitalised | new_hospitalised
    }
    
    counts <- bigtabulate::bigtable(as.matrix(pop[, 2]), ccols = 1)
    updated_counts <- integer(4)
    names(updated_counts) <- as.character(1:4)
    updated_counts[names(counts)] <- as.integer(counts)
    SEIR[t + 1, ] <- c(updated_counts, school_counts[t + 1], sum(hospitalised))
    
    for (age_group in age_groups) {
      indices <- which(dat$K_ageg == age_group)
      if (t > 0) {
        age_group_counts[t + 1, age_group, "S"] <- sum(pop[indices, 2] == 1)
        age_group_counts[t + 1, age_group, "E"] <- sum(pop[indices, 2] == 2)
        age_group_counts[t + 1, age_group, "I"] <- sum(pop[indices, 2] == 3)
        age_group_counts[t + 1, age_group, "R"] <- sum(pop[indices, 2] == 4)
        age_group_hospitalised[t + 1, age_group] <- sum(hospitalised[indices])
      }
    }
    
    if (!is.null(threshold)) {
      for (school in unique_schools) {
        school_indices <- which(dat$school_name == school)
        school_infected <- sum(pop[school_indices, 2] == 3)
        school_population <- length(school_indices)
        if (school_population > 0) {
          school_prevalence <- school_infected / school_population
          if (school_prevalence > threshold) {
            school_closure_weeks[school] <- length_of_closure
          }
        }
      }
      
      if (day_of_week == 7) {
        school_closure_weeks <- pmax(school_closure_weeks - 1, 0)
      }
    }
    
    if (all(pop[, 2] == 4)) {
      SEIR <- SEIR[1:(t + 1), ]
      school_counts <- school_counts[1:(t + 1)]
      age_group_counts <- age_group_counts[1:(t + 1), , ]
      age_group_hospitalised <- age_group_hospitalised[1:(t + 1), ]
      missed_school_days <- missed_school_days[school_age_indices]
      pb$terminate()
      break
    }
    
    pb$tick()
  }
  
  pb$terminate()
  
  SEIR_dt <- as.data.table(as.matrix(SEIR[1:(nrow(SEIR)), ]))
  SEIR_dt[, Time := 0:(.N - 1)]
  setcolorder(SEIR_dt, c("Time", "S", "E", "I", "R", "Students_No_School", "N_Hospitalised"))
  
  SEIR_dt[, Hosp_Rate := c(0, diff(N_Hospitalised))]
  SEIR_dt[, Hosp_Rate_Per_Capita := Hosp_Rate * 10000 / nrow(dat)]
  
  age_group_counts_dt <- as.data.table(as.table(age_group_counts[1:(nrow(age_group_counts)), , ]))
  setnames(age_group_counts_dt, c("Time", "Age_Group", "Compartment", "Count"))
  age_group_counts_dt[, Time := as.integer(Time)]
  
  age_group_hospitalised_dt <- as.data.table(as.table(age_group_hospitalised[1:(nrow(age_group_hospitalised)), ]))
  setnames(age_group_hospitalised_dt, c("Time", "Age_Group", "N_Hospitalised"))
  age_group_hospitalised_dt[, Time := as.integer(Time)]
  
  missed_school_days_dt <- data.table(ID = school_age_indices, 
                                      Missed_School_Days = missed_school_days[school_age_indices],
                                      Age_Group = dat$K_ageg[school_age_indices])
  
  missed_school_days_dt[is.na(Missed_School_Days), Missed_School_Days := 0]
  
  result <- list(
    SEIR = SEIR_dt,
    Age_Group_Counts = age_group_counts_dt,
    Missed_School_Days = missed_school_days_dt,
    Age_Group_Hospitalised = age_group_hospitalised_dt
  )
  
  return(result)
}

# Running parallel simulations using shared-memory parallelism
# This can be run on a personal computer as well as a high-end computing cluster.


run_parallel_simulations_plus <- function(
    parquet_file, disease = NULL, beta = NULL, gamma = NULL, lambda = NULL,
    initial_infected, max_days = Inf, max_sim_time = Inf, school_week = 5, num_simulations = 10, 
    year_isolation = FALSE, threshold = NULL, length_of_closure = NULL, output_dir = "simulation_results"
) {
  
  # Load the data from parquet file
  dat <- arrow::read_parquet(parquet_file)
  
  # Load and set up the contact matrices
  K_other <- read.csv('pop data/K_other.csv')
  K_school <- read.csv('pop data/K_school.csv')
  
  K_other <- as.matrix(K_other[,-1])
  K_school <- as.matrix(K_school[,-1])
  
  # Check input parameters
  if (school_week < 0 || school_week > 5) {
    stop("The number of days in a school week must be between 0 and 5")
  }
  
  if (!is.null(lambda) && lambda <= 0) {
    stop("Lambda must be greater than 0")
  }
  
  if (!is.null(gamma) && gamma <= 0) {
    stop("Gamma must be greater than 0")
  }
  
  if (!is.null(beta) && beta <= 0) {
    stop("Beta must be greater than 0")
  }
  
  # Define the parallel plan (using available cores)
  plan(multisession, workers = parallel::detectCores() - 1)
  
  # Function to run a single simulation
  run_single_simulation <- function(sim_num) {
    # Call the simulation function with max_sim_time
    result <- simulate_epidemic_plus(
      dat = dat,
      K_other = K_other,
      K_school = K_school,
      disease = disease,
      beta = beta,
      gamma = gamma,
      lambda = lambda,
      initial_infected = initial_infected,
      max_days = max_days,
      max_sim_time = max_sim_time,
      school_week = school_week,
      year_isolation = year_isolation,
      threshold = threshold,
      length_of_closure = length_of_closure
    )
    
    # Add simulation number to the result
    SEIR_dt <- result$SEIR
    SEIR_dt[, Simulation := as.factor(sim_num)]
    
    age_group_counts_dt <- result$Age_Group_Counts
    age_group_counts_dt[, Simulation := as.factor(sim_num)]
    
    missed_school_days_dt <- result$Missed_School_Days
    missed_school_days_dt[, Simulation := as.factor(sim_num)]
    
    age_group_hospitalised_dt <- result$Age_Group_Hospitalised
    age_group_hospitalised_dt[, Simulation := as.factor(sim_num)]
    
    # Return results
    list(
      SEIR = SEIR_dt,
      Age_Group_Counts = age_group_counts_dt,
      Missed_School_Days = missed_school_days_dt,
      Age_Group_Hospitalised = age_group_hospitalised_dt
    )
  }
  
  # Run simulations in parallel
  results_list <- future.apply::future_lapply(1:num_simulations, run_single_simulation, future.seed = TRUE)
  
  # Combine all simulation results into single data.tables
  combined_SEIR <- data.table::rbindlist(lapply(results_list, `[[`, "SEIR"))
  combined_age_group_counts <- data.table::rbindlist(lapply(results_list, `[[`, "Age_Group_Counts"))
  combined_missed_school_days <- data.table::rbindlist(lapply(results_list, `[[`, "Missed_School_Days"))
  combined_age_group_hospitalised <- data.table::rbindlist(lapply(results_list, `[[`, "Age_Group_Hospitalised"))
  
  # Ensure output directory exists, if not, it will create one. 
  if (!dir.exists(output_dir)) {
    dir.create(output_dir, recursive = TRUE)
  }
  
  # Save combined results to Parquet files
  arrow::write_parquet(combined_SEIR, file.path(output_dir, "combined_SEIR.parquet"))
  arrow::write_parquet(combined_age_group_counts, file.path(output_dir, "combined_Age_Group_Counts.parquet"))
  arrow::write_parquet(combined_missed_school_days, file.path(output_dir, "combined_Missed_School_Days.parquet"))
  arrow::write_parquet(combined_age_group_hospitalised, file.path(output_dir, "combined_Age_Group_Hospitalised.parquet"))
  
  return(list(
    SEIR = file.path(output_dir, "combined_SEIR.parquet"),
    Age_Group_Counts = file.path(output_dir, "combined_Age_Group_Counts.parquet"),
    Missed_School_Days = file.path(output_dir, "combined_Missed_School_Days.parquet"),
    Age_Group_Hospitalised = file.path(output_dir, "combined_Age_Group_Hospitalised.parquet")
  ))
}
