module
import LeanMath.CommodityClassification.CheckUnknownSigmaFloor
import LeanMath.CommodityClassification.PrecisionRecoveryRadius

set_option pp.universes false

#check @CommodityClassification.Information.midpoint_error_bound
#print axioms CommodityClassification.Information.midpoint_error_bound

#check @CommodityClassification.Information.error_values_bddAbove
#print axioms CommodityClassification.Information.error_values_bddAbove

#check @CommodityClassification.Information.error_le_maximalError
#print axioms CommodityClassification.Information.error_le_maximalError

#check @CommodityClassification.Information.half_width_le_maximalError
#print axioms CommodityClassification.Information.half_width_le_maximalError

#check @CommodityClassification.Information.midpoint_maximalError
#print axioms CommodityClassification.Information.midpoint_maximalError

#check @CommodityClassification.Information.maximalError_isLeast
#print axioms CommodityClassification.Information.maximalError_isLeast

#check @CommodityClassification.Information.midpointPredictor_error
#print axioms CommodityClassification.Information.midpointPredictor_error

#check @CommodityClassification.Information.midpointPredictor_uniform
#print axioms CommodityClassification.Information.midpointPredictor_uniform

#check @CommodityClassification.Information.uniform_error_lower
#print axioms CommodityClassification.Information.uniform_error_lower

#check @CommodityClassification.Information.uniform_error_achievable_iff
#print axioms CommodityClassification.Information.uniform_error_achievable_iff

#check @CommodityClassification.Information.uniform_error_isLeast
#print axioms CommodityClassification.Information.uniform_error_isLeast

#check @CommodityClassification.Information.recoveryRadius_eq_half_width
#print axioms CommodityClassification.Information.recoveryRadius_eq_half_width

#check @CommodityClassification.Precision.Data.observation_recovery_radius
#print axioms CommodityClassification.Precision.Data.observation_recovery_radius

#check @CommodityClassification.Precision.Data.width_tolerance_iff_prediction
#print axioms CommodityClassification.Precision.Data.width_tolerance_iff_prediction

#check @CommodityClassification.Precision.Data.partition_recovery_radius
#print axioms CommodityClassification.Precision.Data.partition_recovery_radius

#check @CommodityClassification.Information.valueMidpoint
#print axioms CommodityClassification.Information.valueMidpoint
#check @CommodityClassification.Information.maximalError
#print axioms CommodityClassification.Information.maximalError
#check @CommodityClassification.Information.midpointPredictor
#print axioms CommodityClassification.Information.midpointPredictor
#check @CommodityClassification.Information.UniformErrorBound
#print axioms CommodityClassification.Information.UniformErrorBound
#check @CommodityClassification.Information.recoveryRadius
#print axioms CommodityClassification.Information.recoveryRadius
