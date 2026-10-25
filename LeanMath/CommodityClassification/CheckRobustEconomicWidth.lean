module
import LeanMath.CommodityClassification.CheckGeneralObservationWidth
import LeanMath.CommodityClassification.RobustMarginNeighborhood

set_option pp.universes false

#check @CommodityClassification.Information.values_congr
#print axioms CommodityClassification.Information.values_congr

#check @CommodityClassification.Information.worstWidth_congr
#print axioms CommodityClassification.Information.worstWidth_congr

#check @CommodityClassification.Information.boundedValues_congr
#print axioms CommodityClassification.Information.boundedValues_congr

#check @CommodityClassification.Equilibrium.BenchmarkFamily.candidate_coefficient_bounds
#print axioms CommodityClassification.Equilibrium.BenchmarkFamily.candidate_coefficient_bounds

#check @CommodityClassification.Equilibrium.BenchmarkFamily.coefficient_bounded
#print axioms CommodityClassification.Equilibrium.BenchmarkFamily.coefficient_bounded

#check @CommodityClassification.Equilibrium.BenchmarkFamily.observationWidth_perturbation
#print axioms CommodityClassification.Equilibrium.BenchmarkFamily.observationWidth_perturbation

#check @CommodityClassification.Precision.Data.family_benchmarkEnergy
#print axioms CommodityClassification.Precision.Data.family_benchmarkEnergy

#check @CommodityClassification.Precision.Data.family_observationWidth
#print axioms CommodityClassification.Precision.Data.family_observationWidth

#check @CommodityClassification.Precision.Data.perturbed_width_bounds
#print axioms CommodityClassification.Precision.Data.perturbed_width_bounds

#check @CommodityClassification.Precision.Data.perturbed_moment_width_bound
#print axioms CommodityClassification.Precision.Data.perturbed_moment_width_bound

#check @CommodityClassification.Precision.Data.perturbed_partition_width_lower
#print axioms CommodityClassification.Precision.Data.perturbed_partition_width_lower

#check @CommodityClassification.Precision.Data.perturbed_strict_margin
#print axioms CommodityClassification.Precision.Data.perturbed_strict_margin

#check @CommodityClassification.Robust.strict_margin_neighborhood
#print axioms CommodityClassification.Robust.strict_margin_neighborhood

#check @CommodityClassification.Equilibrium.BenchmarkFamily.observationWidth
#print axioms CommodityClassification.Equilibrium.BenchmarkFamily.observationWidth
#check @CommodityClassification.Precision.Data.perturbedWidth
#print axioms CommodityClassification.Precision.Data.perturbedWidth
