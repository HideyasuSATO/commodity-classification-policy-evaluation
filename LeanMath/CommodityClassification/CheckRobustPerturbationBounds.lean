module
import LeanMath.CommodityClassification.CheckRobustVariationalControl
import LeanMath.CommodityClassification.RobustFamilyPerturbation

set_option pp.universes false

#check @CommodityClassification.Robust.errorConstant_nonneg
#print axioms CommodityClassification.Robust.errorConstant_nonneg

#check @CommodityClassification.Robust.relative_cross_and_energy
#print axioms CommodityClassification.Robust.relative_cross_and_energy

#check @CommodityClassification.Robust.relative_policy_error
#print axioms CommodityClassification.Robust.relative_policy_error

#check @CommodityClassification.Robust.combined_coefficient_error
#print axioms CommodityClassification.Robust.combined_coefficient_error

#check @CommodityClassification.Robust.energyNorm_nonneg
#print axioms CommodityClassification.Robust.energyNorm_nonneg

#check @CommodityClassification.Robust.energyNorm_sq
#print axioms CommodityClassification.Robust.energyNorm_sq

#check @CommodityClassification.Robust.energyNorm_neg
#print axioms CommodityClassification.Robust.energyNorm_neg

#check @CommodityClassification.Robust.energyNorm_triangle
#print axioms CommodityClassification.Robust.energyNorm_triangle

#check @CommodityClassification.Robust.energyNorm_reverse
#print axioms CommodityClassification.Robust.energyNorm_reverse

#check @CommodityClassification.Robust.reference_energy_bounds
#print axioms CommodityClassification.Robust.reference_energy_bounds

#check @CommodityClassification.Robust.normalization_bounds
#print axioms CommodityClassification.Robust.normalization_bounds

#check @CommodityClassification.Robust.normalization_factors_positive
#print axioms CommodityClassification.Robust.normalization_factors_positive

#check @CommodityClassification.Equilibrium.BenchmarkFamily.withDemandPolicy_candidates
#print axioms CommodityClassification.Equilibrium.BenchmarkFamily.withDemandPolicy_candidates

#check @CommodityClassification.Equilibrium.BenchmarkFamily.withDemandPolicy_endowment
#print axioms CommodityClassification.Equilibrium.BenchmarkFamily.withDemandPolicy_endowment

#check @CommodityClassification.Equilibrium.BenchmarkFamily.withDemandPolicy_substitution
#print axioms CommodityClassification.Equilibrium.BenchmarkFamily.withDemandPolicy_substitution

#check @CommodityClassification.Equilibrium.BenchmarkFamily.perturbation_demand_posDef
#print axioms CommodityClassification.Equilibrium.BenchmarkFamily.perturbation_demand_posDef

#check @CommodityClassification.Equilibrium.BenchmarkFamily.candidate_perturbation_error
#print axioms CommodityClassification.Equilibrium.BenchmarkFamily.candidate_perturbation_error

#check @CommodityClassification.Equilibrium.BenchmarkFamily.perturbation_energy_bounds
#print axioms CommodityClassification.Equilibrium.BenchmarkFamily.perturbation_energy_bounds

#check @CommodityClassification.Equilibrium.BenchmarkFamily.perturbation_energy_positive
#print axioms CommodityClassification.Equilibrium.BenchmarkFamily.perturbation_energy_positive

#check @CommodityClassification.Robust.errorConstant
#print axioms CommodityClassification.Robust.errorConstant
#check @CommodityClassification.Robust.energyNorm
#print axioms CommodityClassification.Robust.energyNorm
#check @CommodityClassification.Robust.normalizationLower
#print axioms CommodityClassification.Robust.normalizationLower
#check @CommodityClassification.Robust.normalizationUpper
#print axioms CommodityClassification.Robust.normalizationUpper
#check @CommodityClassification.Equilibrium.BenchmarkFamily.withDemandPolicy
#print axioms CommodityClassification.Equilibrium.BenchmarkFamily.withDemandPolicy
#check @CommodityClassification.Equilibrium.BenchmarkFamily.benchmarkEnergy
#print axioms CommodityClassification.Equilibrium.BenchmarkFamily.benchmarkEnergy
