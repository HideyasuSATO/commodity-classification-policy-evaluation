module
import LeanMath.CommodityClassification.CheckSupplyPositivity
import LeanMath.CommodityClassification.CESParameterLimitExample

-- This integrated target retains B.1, coordinates, reports, price derivatives and supply positivity.
set_option pp.universes false

#check @CommodityClassification.CESCost.Data.factor_nonempty
#print axioms CommodityClassification.CESCost.Data.factor_nonempty

#check @CommodityClassification.CESCost.Data.parameterSum_zero
#print axioms CommodityClassification.CESCost.Data.parameterSum_zero

#check @CommodityClassification.CESCost.Data.powerSum_eq_parameterSum
#print axioms CommodityClassification.CESCost.Data.powerSum_eq_parameterSum

#check @CommodityClassification.CESCost.Data.parameterSum_pos
#print axioms CommodityClassification.CESCost.Data.parameterSum_pos

#check @CommodityClassification.CESCost.Data.hasDerivAt_parameterSum_zero
#print axioms CommodityClassification.CESCost.Data.hasDerivAt_parameterSum_zero

#check @CommodityClassification.CESCost.Data.hasDerivAt_log_parameterSum_zero
#print axioms CommodityClassification.CESCost.Data.hasDerivAt_log_parameterSum_zero

#check @CommodityClassification.CESCost.Data.tendsto_log_parameter_quotient
#print axioms CommodityClassification.CESCost.Data.tendsto_log_parameter_quotient

#check @CommodityClassification.CESCost.Data.ces_eq_parameter_exp
#print axioms CommodityClassification.CESCost.Data.ces_eq_parameter_exp

#check @CommodityClassification.CESCost.one_sub_tendsto_punctured
#print axioms CommodityClassification.CESCost.one_sub_tendsto_punctured

#check @CommodityClassification.CESCost.Data.ces_tendsto_cobb
#print axioms CommodityClassification.CESCost.Data.ces_tendsto_cobb

#check @CommodityClassification.CESCost.Data.ces_at_one
#print axioms CommodityClassification.CESCost.Data.ces_at_one

#check @CommodityClassification.CESCost.Data.cost_parameter_continuousAt_one
#print axioms CommodityClassification.CESCost.Data.cost_parameter_continuousAt_one

#check @CommodityClassification.CESCost.Data.cost_tendsto_cobb
#print axioms CommodityClassification.CESCost.Data.cost_tendsto_cobb

#check @CommodityClassification.CESCost.Data.cobb_eq_product
#print axioms CommodityClassification.CESCost.Data.cobb_eq_product

#check @CommodityClassification.CESCost.input_cost_parameter_limit
#print axioms CommodityClassification.CESCost.input_cost_parameter_limit

#check @CommodityClassification.CESCost.coordinate_cost_parameter_limit
#print axioms CommodityClassification.CESCost.coordinate_cost_parameter_limit

#check @CommodityClassification.CESCost.ParameterLimitExample.currentPrices_positive
#print axioms CommodityClassification.CESCost.ParameterLimitExample.currentPrices_positive

#check @CommodityClassification.CESCost.ParameterLimitExample.currentPrices_ne_benchmark
#print axioms CommodityClassification.CESCost.ParameterLimitExample.currentPrices_ne_benchmark

#check @CommodityClassification.CESCost.ParameterLimitExample.cobb_value
#print axioms CommodityClassification.CESCost.ParameterLimitExample.cobb_value

#check @CommodityClassification.CESCost.ParameterLimitExample.raw_ces_one_value
#print axioms CommodityClassification.CESCost.ParameterLimitExample.raw_ces_one_value

#check @CommodityClassification.CESCost.ParameterLimitExample.cobb_gt_raw_at_one
#print axioms CommodityClassification.CESCost.ParameterLimitExample.cobb_gt_raw_at_one

#check @CommodityClassification.CESCost.ParameterLimitExample.off_benchmark_limit
#print axioms CommodityClassification.CESCost.ParameterLimitExample.off_benchmark_limit

#check @CommodityClassification.CESCost.ParameterLimitExample.filled_cost_continuous
#print axioms CommodityClassification.CESCost.ParameterLimitExample.filled_cost_continuous

#check @CommodityClassification.CESCost.Data.parameterSum

#print axioms CommodityClassification.CESCost.ParameterLimitExample.data
