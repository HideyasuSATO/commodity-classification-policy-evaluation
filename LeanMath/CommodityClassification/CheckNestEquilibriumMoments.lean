module
import LeanMath.CommodityClassification.CheckNestResidualCovariance
import LeanMath.CommodityClassification.NestedEquilibriumInformation

set_option pp.universes false

#check @CommodityClassification.InputCoordinates.diagonal_conjugate_sum
#print axioms CommodityClassification.InputCoordinates.diagonal_conjugate_sum

#check @CommodityClassification.DemandNests.Data.weighted_second_conjugate
#print axioms CommodityClassification.DemandNests.Data.weighted_second_conjugate

#check @CommodityClassification.DemandNests.Data.report_conjugate
#print axioms CommodityClassification.DemandNests.Data.report_conjugate

#check @CommodityClassification.DemandNests.Data.weighted_covariance_decomposition
#print axioms CommodityClassification.DemandNests.Data.weighted_covariance_decomposition

#check @CommodityClassification.DemandNests.Data.meanAdjustment_eq
#print axioms CommodityClassification.DemandNests.Data.meanAdjustment_eq

#check @CommodityClassification.DemandNests.Data.adjustedDemand_nest_decomposition
#print axioms CommodityClassification.DemandNests.Data.adjustedDemand_nest_decomposition

#check @CommodityClassification.DemandNests.Data.nest_K_decomposition
#print axioms CommodityClassification.DemandNests.Data.nest_K_decomposition

#check @CommodityClassification.DemandNests.Data.nest_m_decomposition
#print axioms CommodityClassification.DemandNests.Data.nest_m_decomposition

#check @CommodityClassification.DemandNests.Data.covarianceCorrection_matching
#print axioms CommodityClassification.DemandNests.Data.covarianceCorrection_matching

#check @CommodityClassification.Equilibrium.BenchmarkFamily.nested_candidate_m
#print axioms CommodityClassification.Equilibrium.BenchmarkFamily.nested_candidate_m

#check @CommodityClassification.Equilibrium.BenchmarkFamily.nested_candidate_K
#print axioms CommodityClassification.Equilibrium.BenchmarkFamily.nested_candidate_K

#check @CommodityClassification.Equilibrium.BenchmarkFamily.nested_coefficient_recovery
#print axioms CommodityClassification.Equilibrium.BenchmarkFamily.nested_coefficient_recovery

#check @CommodityClassification.Equilibrium.BenchmarkFamily.nested_actual_coefficient_recovery
#print axioms CommodityClassification.Equilibrium.BenchmarkFamily.nested_actual_coefficient_recovery

#check @CommodityClassification.Equilibrium.BenchmarkFamily.nested_information_sufficient
#print axioms CommodityClassification.Equilibrium.BenchmarkFamily.nested_information_sufficient

#check @CommodityClassification.Equilibrium.BenchmarkFamily.nested_matching_reports_sufficient
#print axioms CommodityClassification.Equilibrium.BenchmarkFamily.nested_matching_reports_sufficient

#check @CommodityClassification.Equilibrium.BenchmarkFamily.nested_reported_zero_coefficient
#print axioms CommodityClassification.Equilibrium.BenchmarkFamily.nested_reported_zero_coefficient

#check @CommodityClassification.Equilibrium.BenchmarkFamily.nested_fixed_answer_zero_load
#print axioms CommodityClassification.Equilibrium.BenchmarkFamily.nested_fixed_answer_zero_load

#check @CommodityClassification.DemandNests.Data.meanAdjustment
#print axioms CommodityClassification.DemandNests.Data.meanAdjustment
#check @CommodityClassification.DemandNests.Data.covarianceCorrection
#print axioms CommodityClassification.DemandNests.Data.covarianceCorrection
#check @CommodityClassification.Equilibrium.BenchmarkFamily.nestReportedLoad
#print axioms CommodityClassification.Equilibrium.BenchmarkFamily.nestReportedLoad
#check @CommodityClassification.Equilibrium.BenchmarkFamily.nestReportedK
#print axioms CommodityClassification.Equilibrium.BenchmarkFamily.nestReportedK
#check @CommodityClassification.Equilibrium.BenchmarkFamily.nestReportedCoefficient
#print axioms CommodityClassification.Equilibrium.BenchmarkFamily.nestReportedCoefficient
