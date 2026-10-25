module
import LeanMath.CommodityClassification.CheckPredictionRiskFoundation
import LeanMath.CommodityClassification.PrecisionPredictionRisk

set_option pp.universes false

#check @CommodityClassification.Information.pairRisks_zero
#print axioms CommodityClassification.Information.pairRisks_zero

#check @CommodityClassification.Information.pairRisks_upper
#print axioms CommodityClassification.Information.pairRisks_upper

#check @CommodityClassification.Information.pairRisks_isLUB
#print axioms CommodityClassification.Information.pairRisks_isLUB

#check @CommodityClassification.Information.pairRisks_approximate
#print axioms CommodityClassification.Information.pairRisks_approximate

#check @CommodityClassification.Information.compatibleRisks_isLUB
#print axioms CommodityClassification.Information.compatibleRisks_isLUB

#check @CommodityClassification.Information.compatibleRisks_supremum
#print axioms CommodityClassification.Information.compatibleRisks_supremum

#check @CommodityClassification.Information.twoPointRisk_approximate
#print axioms CommodityClassification.Information.twoPointRisk_approximate

#check @CommodityClassification.Information.compatible_minimizedRisk_supremum
#print axioms CommodityClassification.Information.compatible_minimizedRisk_supremum

#check @CommodityClassification.Information.answer_prior_risk_supremum
#print axioms CommodityClassification.Information.answer_prior_risk_supremum

#check @CommodityClassification.Precision.Data.normalizedWelfare_measurable
#print axioms CommodityClassification.Precision.Data.normalizedWelfare_measurable

#check @CommodityClassification.Precision.Data.observation_prior_compatible
#print axioms CommodityClassification.Precision.Data.observation_prior_compatible

#check @CommodityClassification.Precision.Data.observation_target_bounded
#print axioms CommodityClassification.Precision.Data.observation_target_bounded

#check @CommodityClassification.Precision.Data.observation_prior_risk_decomposition
#print axioms CommodityClassification.Precision.Data.observation_prior_risk_decomposition

#check @CommodityClassification.Precision.Data.observation_prior_risk_supremum
#print axioms CommodityClassification.Precision.Data.observation_prior_risk_supremum

#check @CommodityClassification.Precision.Data.observation_minimizedRisk_supremum
#print axioms CommodityClassification.Precision.Data.observation_minimizedRisk_supremum

#check @CommodityClassification.Information.pairRisks
#print axioms CommodityClassification.Information.pairRisks
