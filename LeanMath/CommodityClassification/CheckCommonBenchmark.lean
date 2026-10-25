module
import LeanMath.CommodityClassification.CheckCESProduction
import LeanMath.CommodityClassification.CommonBenchmarkExample

set_option pp.universes false

#check @CommodityClassification.Equilibrium.benchmarkUtility_value
#print axioms CommodityClassification.Equilibrium.benchmarkUtility_value

#check @CommodityClassification.Equilibrium.benchmarkUtility_derivative
#print axioms CommodityClassification.Equilibrium.benchmarkUtility_derivative

#check @CommodityClassification.Equilibrium.benchmarkUtility_derivative_base
#print axioms CommodityClassification.Equilibrium.benchmarkUtility_derivative_base

#check @CommodityClassification.Equilibrium.benchmarkGradient_derivative
#print axioms CommodityClassification.Equilibrium.benchmarkGradient_derivative

#check @CommodityClassification.Equilibrium.benchmarkGradient_continuous
#print axioms CommodityClassification.Equilibrium.benchmarkGradient_continuous

#check @CommodityClassification.Equilibrium.benchmarkUtility_marginals_positive_near
#print axioms CommodityClassification.Equilibrium.benchmarkUtility_marginals_positive_near

#check @CommodityClassification.Equilibrium.benchmarkUtility_combination_gap
#print axioms CommodityClassification.Equilibrium.benchmarkUtility_combination_gap

#check @CommodityClassification.Equilibrium.benchmarkUtility_strictConcave
#print axioms CommodityClassification.Equilibrium.benchmarkUtility_strictConcave

#check @CommodityClassification.Equilibrium.benchmarkUtility_increment
#print axioms CommodityClassification.Equilibrium.benchmarkUtility_increment

#check @CommodityClassification.Equilibrium.benchmarkUtility_strict_increase
#print axioms CommodityClassification.Equilibrium.benchmarkUtility_strict_increase

#check @CommodityClassification.Equilibrium.benchmarkUtility_surplus_maximum
#print axioms CommodityClassification.Equilibrium.benchmarkUtility_surplus_maximum

#check @CommodityClassification.Equilibrium.benchmarkUtility_household
#print axioms CommodityClassification.Equilibrium.benchmarkUtility_household

#check @CommodityClassification.Equilibrium.matching_utility_benchmark_household
#print axioms CommodityClassification.Equilibrium.matching_utility_benchmark_household

#check @CommodityClassification.Equilibrium.Model.endowment_positive
#print axioms CommodityClassification.Equilibrium.Model.endowment_positive

#check @CommodityClassification.Equilibrium.Model.benchmark_budget
#print axioms CommodityClassification.Equilibrium.Model.benchmark_budget

#check @CommodityClassification.Equilibrium.Model.benchmark_equilibrium
#print axioms CommodityClassification.Equilibrium.Model.benchmark_equilibrium

#check @CommodityClassification.Equilibrium.Model.benchmark_zero_tax
#print axioms CommodityClassification.Equilibrium.Model.benchmark_zero_tax

#check @CommodityClassification.Equilibrium.Model.benchmark_physical_clearing
#print axioms CommodityClassification.Equilibrium.Model.benchmark_physical_clearing

#check @CommodityClassification.Equilibrium.BenchmarkFamily.candidate_total_inputs
#print axioms CommodityClassification.Equilibrium.BenchmarkFamily.candidate_total_inputs

#check @CommodityClassification.Equilibrium.BenchmarkFamily.candidate_endowment
#print axioms CommodityClassification.Equilibrium.BenchmarkFamily.candidate_endowment

#check @CommodityClassification.Equilibrium.BenchmarkFamily.commonEndowment_positive
#print axioms CommodityClassification.Equilibrium.BenchmarkFamily.commonEndowment_positive

#check @CommodityClassification.Equilibrium.BenchmarkFamily.commonUtility_value
#print axioms CommodityClassification.Equilibrium.BenchmarkFamily.commonUtility_value

#check @CommodityClassification.Equilibrium.BenchmarkFamily.commonUtility_derivative
#print axioms CommodityClassification.Equilibrium.BenchmarkFamily.commonUtility_derivative

#check @CommodityClassification.Equilibrium.BenchmarkFamily.commonUtility_hessian
#print axioms CommodityClassification.Equilibrium.BenchmarkFamily.commonUtility_hessian

#check @CommodityClassification.Equilibrium.BenchmarkFamily.commonUtility_strictConcave
#print axioms CommodityClassification.Equilibrium.BenchmarkFamily.commonUtility_strictConcave

#check @CommodityClassification.Equilibrium.BenchmarkFamily.commonUtility_positive_marginals
#print axioms CommodityClassification.Equilibrium.BenchmarkFamily.commonUtility_positive_marginals

#check @CommodityClassification.Equilibrium.BenchmarkFamily.candidate_utility_compatible
#print axioms CommodityClassification.Equilibrium.BenchmarkFamily.candidate_utility_compatible

#check @CommodityClassification.Equilibrium.BenchmarkFamily.candidate_demand_implemented
#print axioms CommodityClassification.Equilibrium.BenchmarkFamily.candidate_demand_implemented

#check @CommodityClassification.Equilibrium.BenchmarkFamily.candidate_demand_derivative
#print axioms CommodityClassification.Equilibrium.BenchmarkFamily.candidate_demand_derivative

#check @CommodityClassification.Equilibrium.BenchmarkFamily.every_candidate_equilibrium
#print axioms CommodityClassification.Equilibrium.BenchmarkFamily.every_candidate_equilibrium

#check @CommodityClassification.Equilibrium.BenchmarkFamily.common_benchmark_exists
#print axioms CommodityClassification.Equilibrium.BenchmarkFamily.common_benchmark_exists

#check @CommodityClassification.Equilibrium.BenchmarkFamily.same_benchmark_budget
#print axioms CommodityClassification.Equilibrium.BenchmarkFamily.same_benchmark_budget

#check @CommodityClassification.Equilibrium.BenchmarkFamily.common_local_utility
#print axioms CommodityClassification.Equilibrium.BenchmarkFamily.common_local_utility

#check @CommodityClassification.Equilibrium.Example.family_endowment
#print axioms CommodityClassification.Equilibrium.Example.family_endowment

#check @CommodityClassification.Equilibrium.Example.distinct_candidates
#print axioms CommodityClassification.Equilibrium.Example.distinct_candidates

#check @CommodityClassification.Equilibrium.Example.same_utility_and_endowment
#print axioms CommodityClassification.Equilibrium.Example.same_utility_and_endowment

#check @CommodityClassification.Equilibrium.Example.empty_family_equilibrium
#print axioms CommodityClassification.Equilibrium.Example.empty_family_equilibrium

#check @CommodityClassification.Equilibrium.benchmarkUtility
#check @CommodityClassification.Equilibrium.benchmarkGradient
#check @CommodityClassification.Equilibrium.Model.BenchmarkEquilibrium
#check @CommodityClassification.Equilibrium.BenchmarkFamily
#check @CommodityClassification.Equilibrium.BenchmarkFamily.Candidate
#check @CommodityClassification.Equilibrium.BenchmarkFamily.model
#check @CommodityClassification.Equilibrium.BenchmarkFamily.referenceCandidate
#check @CommodityClassification.Equilibrium.BenchmarkFamily.commonEndowment
#check @CommodityClassification.Equilibrium.BenchmarkFamily.commonUtility
#check @CommodityClassification.Equilibrium.Example.family
#check @CommodityClassification.Equilibrium.Example.familyPath
#check @CommodityClassification.Equilibrium.Example.emptyFamily
