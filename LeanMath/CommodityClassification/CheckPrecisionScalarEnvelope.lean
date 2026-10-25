module
import LeanMath.CommodityClassification.CheckPrecisionVarianceAllowance
import LeanMath.CommodityClassification.PrecisionEnvelopeParameters

set_option pp.universes false

#check @CommodityClassification.Precision.Envelope.factor_pos
#print axioms CommodityClassification.Precision.Envelope.factor_pos

#check @CommodityClassification.Precision.Envelope.square_identity
#print axioms CommodityClassification.Precision.Envelope.square_identity

#check @CommodityClassification.Precision.Envelope.cap_pos
#print axioms CommodityClassification.Precision.Envelope.cap_pos

#check @CommodityClassification.Precision.Envelope.value_le_bound
#print axioms CommodityClassification.Precision.Envelope.value_le_bound

#check @CommodityClassification.Precision.Envelope.optimizer_mem
#print axioms CommodityClassification.Precision.Envelope.optimizer_mem

#check @CommodityClassification.Precision.Envelope.optimizer_root
#print axioms CommodityClassification.Precision.Envelope.optimizer_root

#check @CommodityClassification.Precision.Envelope.value_at_optimizer
#print axioms CommodityClassification.Precision.Envelope.value_at_optimizer

#check @CommodityClassification.Precision.Envelope.bound_scaled
#print axioms CommodityClassification.Precision.Envelope.bound_scaled

#check @CommodityClassification.Precision.Envelope.value_isGreatest
#print axioms CommodityClassification.Precision.Envelope.value_isGreatest

#check @CommodityClassification.Precision.Data.minElasticity_pos
#print axioms CommodityClassification.Precision.Data.minElasticity_pos

#check @CommodityClassification.Precision.Data.maxElasticity_pos
#print axioms CommodityClassification.Precision.Data.maxElasticity_pos

#check @CommodityClassification.Precision.Data.minElasticity_le_max
#print axioms CommodityClassification.Precision.Data.minElasticity_le_max

#check @CommodityClassification.Precision.Data.policyShare_pos
#print axioms CommodityClassification.Precision.Data.policyShare_pos

#check @CommodityClassification.Precision.Data.criticalExposure_mem
#print axioms CommodityClassification.Precision.Data.criticalExposure_mem

#check @CommodityClassification.Precision.Data.envelope_bound_formula
#print axioms CommodityClassification.Precision.Data.envelope_bound_formula

#check @CommodityClassification.Precision.Data.precisionFloor_nonneg
#print axioms CommodityClassification.Precision.Data.precisionFloor_nonneg

#check @CommodityClassification.Precision.Data.precisionFloor_matching
#print axioms CommodityClassification.Precision.Data.precisionFloor_matching

#check @CommodityClassification.Precision.Data.momentWidth_full_equals_envelope
#print axioms CommodityClassification.Precision.Data.momentWidth_full_equals_envelope

#check @CommodityClassification.Precision.Data.scalar_envelope_upper
#print axioms CommodityClassification.Precision.Data.scalar_envelope_upper

#check @CommodityClassification.Precision.Data.scalar_envelope_attains
#print axioms CommodityClassification.Precision.Data.scalar_envelope_attains

#check @CommodityClassification.Precision.Data.scalar_envelope_isGreatest
#print axioms CommodityClassification.Precision.Data.scalar_envelope_isGreatest

#check @CommodityClassification.Precision.Envelope.factor
#print axioms CommodityClassification.Precision.Envelope.factor
#check @CommodityClassification.Precision.Envelope.value
#print axioms CommodityClassification.Precision.Envelope.value
#check @CommodityClassification.Precision.Envelope.bound
#print axioms CommodityClassification.Precision.Envelope.bound
#check @CommodityClassification.Precision.Envelope.optimizer
#print axioms CommodityClassification.Precision.Envelope.optimizer
#check @CommodityClassification.Precision.Data.minElasticity
#print axioms CommodityClassification.Precision.Data.minElasticity
#check @CommodityClassification.Precision.Data.maxElasticity
#print axioms CommodityClassification.Precision.Data.maxElasticity
#check @CommodityClassification.Precision.Data.criticalExposure
#print axioms CommodityClassification.Precision.Data.criticalExposure
#check @CommodityClassification.Precision.Data.precisionFloor
#print axioms CommodityClassification.Precision.Data.precisionFloor
