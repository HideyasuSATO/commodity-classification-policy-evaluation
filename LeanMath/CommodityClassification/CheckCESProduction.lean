module
import LeanMath.CommodityClassification.CheckWelfareVariational
import LeanMath.CommodityClassification.CESProductionApplication

set_option pp.universes false

#check @CommodityClassification.CESCost.negative_power_tangent
#print axioms CommodityClassification.CESCost.negative_power_tangent

#check @CommodityClassification.CESCost.power_mean_le_arithmetic
#print axioms CommodityClassification.CESCost.power_mean_le_arithmetic

#check @CommodityClassification.CESCost.Data.cost_pos
#print axioms CommodityClassification.CESCost.Data.cost_pos

#check @CommodityClassification.CESCost.Data.cost_partial_pos
#print axioms CommodityClassification.CESCost.Data.cost_partial_pos

#check @CommodityClassification.CESCost.Data.ces_support
#print axioms CommodityClassification.CESCost.Data.ces_support

#check @CommodityClassification.CESCost.Data.cobb_support
#print axioms CommodityClassification.CESCost.Data.cobb_support

#check @CommodityClassification.CESCost.Data.cost_support
#print axioms CommodityClassification.CESCost.Data.cost_support

#check @CommodityClassification.CESCost.Data.cost_support_affine
#print axioms CommodityClassification.CESCost.Data.cost_support_affine

#check @CommodityClassification.CESCost.Data.feasible_zero
#print axioms CommodityClassification.CESCost.Data.feasible_zero

#check @CommodityClassification.CESCost.Data.feasible_scale
#print axioms CommodityClassification.CESCost.Data.feasible_scale

#check @CommodityClassification.CESCost.Data.feasible_add
#print axioms CommodityClassification.CESCost.Data.feasible_add

#check @CommodityClassification.CESCost.Data.feasible_convex
#print axioms CommodityClassification.CESCost.Data.feasible_convex

#check @CommodityClassification.CESCost.Data.feasible_disposal
#print axioms CommodityClassification.CESCost.Data.feasible_disposal

#check @CommodityClassification.CESCost.Data.optimalInput_feasible
#print axioms CommodityClassification.CESCost.Data.optimalInput_feasible

#check @CommodityClassification.CESCost.Data.optimalInput_expenditure
#print axioms CommodityClassification.CESCost.Data.optimalInput_expenditure

#check @CommodityClassification.CESCost.Data.feasible_expenditure_lower
#print axioms CommodityClassification.CESCost.Data.feasible_expenditure_lower

#check @CommodityClassification.CESCost.Data.production_cost_isLeast
#print axioms CommodityClassification.CESCost.Data.production_cost_isLeast

#check @CommodityClassification.CESCost.Data.unit_cost_isLeast
#print axioms CommodityClassification.CESCost.Data.unit_cost_isLeast

#check @CommodityClassification.CESCost.Data.feasible_profit_nonpos
#print axioms CommodityClassification.CESCost.Data.feasible_profit_nonpos

#check @CommodityClassification.CESCost.Data.optimalInput_profit_zero
#print axioms CommodityClassification.CESCost.Data.optimalInput_profit_zero

#check @CommodityClassification.CESCost.Data.production_profit_isGreatest
#print axioms CommodityClassification.CESCost.Data.production_profit_isGreatest

#check @CommodityClassification.CESCost.Data.benchmark_production
#print axioms CommodityClassification.CESCost.Data.benchmark_production

#check @CommodityClassification.CESCost.Data.zero_output
#print axioms CommodityClassification.CESCost.Data.zero_output

#check @CommodityClassification.CESCost.zero_factors_impossible
#print axioms CommodityClassification.CESCost.zero_factors_impossible

#check @CommodityClassification.CESCost.one_factor_cost
#print axioms CommodityClassification.CESCost.one_factor_cost

#check @CommodityClassification.Production.fixed_iff
#print axioms CommodityClassification.Production.fixed_iff

#check @CommodityClassification.Production.fixed_zero
#print axioms CommodityClassification.Production.fixed_zero

#check @CommodityClassification.Production.fixed_scale
#print axioms CommodityClassification.Production.fixed_scale

#check @CommodityClassification.Production.fixed_add
#print axioms CommodityClassification.Production.fixed_add

#check @CommodityClassification.Production.fixed_convex
#print axioms CommodityClassification.Production.fixed_convex

#check @CommodityClassification.Production.fixed_disposal
#print axioms CommodityClassification.Production.fixed_disposal

#check @CommodityClassification.Production.fixed_plan
#print axioms CommodityClassification.Production.fixed_plan

#check @CommodityClassification.Production.fixed_cost_lower
#print axioms CommodityClassification.Production.fixed_cost_lower

#check @CommodityClassification.Production.fixed_cost_isLeast
#print axioms CommodityClassification.Production.fixed_cost_isLeast

#check @CommodityClassification.Production.fixed_profit_nonpos
#print axioms CommodityClassification.Production.fixed_profit_nonpos

#check @CommodityClassification.Production.fixed_profit_zero
#print axioms CommodityClassification.Production.fixed_profit_zero

#check @CommodityClassification.Production.numeraire_certificate
#print axioms CommodityClassification.Production.numeraire_certificate

#check @CommodityClassification.Equilibrium.Model.currentInputs_optimalInput
#print axioms CommodityClassification.Equilibrium.Model.currentInputs_optimalInput

#check @CommodityClassification.Equilibrium.Model.current_production_certificate
#print axioms CommodityClassification.Equilibrium.Model.current_production_certificate

#check @CommodityClassification.Equilibrium.Model.benchmark_production_certificate
#print axioms CommodityClassification.Equilibrium.Model.benchmark_production_certificate

#check @CommodityClassification.Equilibrium.Model.numeraire_production_certificate
#print axioms CommodityClassification.Equilibrium.Model.numeraire_production_certificate

#check @CommodityClassification.Equilibrium.Example.concrete_production
#print axioms CommodityClassification.Equilibrium.Example.concrete_production

#check @CommodityClassification.Equilibrium.Example.concrete_numeraire
#print axioms CommodityClassification.Equilibrium.Example.concrete_numeraire

#check @CommodityClassification.CESCost.Data.Feasible
#check @CommodityClassification.CESCost.Data.optimalInput
#check @CommodityClassification.Production.FixedFeasible
#check @CommodityClassification.Equilibrium.Model.ProductionFeasible
