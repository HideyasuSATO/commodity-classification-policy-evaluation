module
import LeanMath.CommodityClassification.CheckUniformRegularity
import LeanMath.CommodityClassification.EquilibriumConsistency

-- Explicit integrated target: retains all prior research checks.
set_option pp.universes false

#check @CommodityClassification.Equilibrium.matCLM_apply
#print axioms CommodityClassification.Equilibrium.matCLM_apply

#check @CommodityClassification.Equilibrium.taxCLM_apply
#print axioms CommodityClassification.Equilibrium.taxCLM_apply

#check @CommodityClassification.Equilibrium.coordCLM_apply
#print axioms CommodityClassification.Equilibrium.coordCLM_apply

#check @CommodityClassification.Equilibrium.Model.hessian_apply
#print axioms CommodityClassification.Equilibrium.Model.hessian_apply

#check @CommodityClassification.Equilibrium.Model.currentPrice_zero
#print axioms CommodityClassification.Equilibrium.Model.currentPrice_zero

#check @CommodityClassification.Equilibrium.Model.costs_base
#print axioms CommodityClassification.Equilibrium.Model.costs_base

#check @CommodityClassification.Equilibrium.Model.inputs_base
#print axioms CommodityClassification.Equilibrium.Model.inputs_base

#check @CommodityClassification.Equilibrium.Model.prices_zero
#print axioms CommodityClassification.Equilibrium.Model.prices_zero

#check @CommodityClassification.Equilibrium.Model.quantities_zero
#print axioms CommodityClassification.Equilibrium.Model.quantities_zero

#check @CommodityClassification.Equilibrium.Model.factorDemand_zero
#print axioms CommodityClassification.Equilibrium.Model.factorDemand_zero

#check @CommodityClassification.Equilibrium.Model.excess_base
#print axioms CommodityClassification.Equilibrium.Model.excess_base

#check @CommodityClassification.Equilibrium.Model.priceChange_apply
#print axioms CommodityClassification.Equilibrium.Model.priceChange_apply

#check @CommodityClassification.Equilibrium.Model.quantityChange_apply
#print axioms CommodityClassification.Equilibrium.Model.quantityChange_apply

#check @CommodityClassification.Equilibrium.Model.factorChange_apply
#print axioms CommodityClassification.Equilibrium.Model.factorChange_apply

#check @CommodityClassification.Equilibrium.Model.excessChange_apply
#print axioms CommodityClassification.Equilibrium.Model.excessChange_apply

#check @CommodityClassification.Equilibrium.Model.currentPrice_normalized
#print axioms CommodityClassification.Equilibrium.Model.currentPrice_normalized

#check @CommodityClassification.Equilibrium.Model.currentPrice_continuous
#print axioms CommodityClassification.Equilibrium.Model.currentPrice_continuous

#check @CommodityClassification.Equilibrium.Model.positivePrice_neighborhood
#print axioms CommodityClassification.Equilibrium.Model.positivePrice_neighborhood

#check @CommodityClassification.Equilibrium.Model.positivePrice_domain_open
#print axioms CommodityClassification.Equilibrium.Model.positivePrice_domain_open

#check @CommodityClassification.Equilibrium.Model.reduced_eq_project_excess
#print axioms CommodityClassification.Equilibrium.Model.reduced_eq_project_excess

#check @CommodityClassification.Equilibrium.hessianRow_apply
#print axioms CommodityClassification.Equilibrium.hessianRow_apply

#check @CommodityClassification.Equilibrium.Model.currentPrice_hasFDerivAt
#print axioms CommodityClassification.Equilibrium.Model.currentPrice_hasFDerivAt

#check @CommodityClassification.Equilibrium.Model.costs_hasFDerivAt
#print axioms CommodityClassification.Equilibrium.Model.costs_hasFDerivAt

#check @CommodityClassification.Equilibrium.Model.currentInputs_hasFDerivAt
#print axioms CommodityClassification.Equilibrium.Model.currentInputs_hasFDerivAt

#check @CommodityClassification.Equilibrium.Model.prices_hasFDerivAt
#print axioms CommodityClassification.Equilibrium.Model.prices_hasFDerivAt

#check @CommodityClassification.Equilibrium.Model.quantities_hasFDerivAt
#print axioms CommodityClassification.Equilibrium.Model.quantities_hasFDerivAt

#check @CommodityClassification.Equilibrium.Model.factorDemand_hasFDerivAt
#print axioms CommodityClassification.Equilibrium.Model.factorDemand_hasFDerivAt

#check @CommodityClassification.Equilibrium.Model.excess_hasFDerivAt
#print axioms CommodityClassification.Equilibrium.Model.excess_hasFDerivAt

#check @CommodityClassification.Equilibrium.Model.reduced_hasFDerivAt
#print axioms CommodityClassification.Equilibrium.Model.reduced_hasFDerivAt

#check @CommodityClassification.Equilibrium.frame_dual_kernel
#print axioms CommodityClassification.Equilibrium.frame_dual_kernel

#check @CommodityClassification.Equilibrium.numeraire_adjustment
#print axioms CommodityClassification.Equilibrium.numeraire_adjustment

#check @CommodityClassification.Equilibrium.numeraire_adjustment_unique
#print axioms CommodityClassification.Equilibrium.numeraire_adjustment_unique

#check @CommodityClassification.Equilibrium.numeraire_solvability
#print axioms CommodityClassification.Equilibrium.numeraire_solvability

#check @CommodityClassification.Equilibrium.Model.projected_hessian
#print axioms CommodityClassification.Equilibrium.Model.projected_hessian

#check @CommodityClassification.Equilibrium.Model.project_physical_change
#print axioms CommodityClassification.Equilibrium.Model.project_physical_change

#check @CommodityClassification.Equilibrium.Model.projected_factorChange
#print axioms CommodityClassification.Equilibrium.Model.projected_factorChange

#check @CommodityClassification.Equilibrium.Model.reducedChange_apply
#print axioms CommodityClassification.Equilibrium.Model.reducedChange_apply

#check @CommodityClassification.Equilibrium.Model.reduced_derivative_apply
#print axioms CommodityClassification.Equilibrium.Model.reduced_derivative_apply

#check @CommodityClassification.Equilibrium.Model.price_jacobian
#print axioms CommodityClassification.Equilibrium.Model.price_jacobian

#check @CommodityClassification.Equilibrium.Model.tax_derivative
#print axioms CommodityClassification.Equilibrium.Model.tax_derivative

#check @CommodityClassification.Equilibrium.Model.m_eq_fixedAnswer
#print axioms CommodityClassification.Equilibrium.Model.m_eq_fixedAnswer

#check @CommodityClassification.Equilibrium.Model.R_eq_parent
#print axioms CommodityClassification.Equilibrium.Model.R_eq_parent

#check @CommodityClassification.Equilibrium.Model.K_posDef
#print axioms CommodityClassification.Equilibrium.Model.K_posDef

#check @CommodityClassification.Equilibrium.Model.K_zSolution
#print axioms CommodityClassification.Equilibrium.Model.K_zSolution

#check @CommodityClassification.Equilibrium.Model.zSolution_unique
#print axioms CommodityClassification.Equilibrium.Model.zSolution_unique

#check @CommodityClassification.Equilibrium.Model.qSolution_formula
#print axioms CommodityClassification.Equilibrium.Model.qSolution_formula

#check @CommodityClassification.Equilibrium.Model.solution_projected
#print axioms CommodityClassification.Equilibrium.Model.solution_projected

#check @CommodityClassification.Equilibrium.Model.solution_linearized
#print axioms CommodityClassification.Equilibrium.Model.solution_linearized

#check @CommodityClassification.Equilibrium.Model.linearized_iff_change
#print axioms CommodityClassification.Equilibrium.Model.linearized_iff_change

#check @CommodityClassification.Equilibrium.Model.linearized_unique
#print axioms CommodityClassification.Equilibrium.Model.linearized_unique

#check @CommodityClassification.Equilibrium.Model.linearized_existsUnique
#print axioms CommodityClassification.Equilibrium.Model.linearized_existsUnique

#check @CommodityClassification.Equilibrium.Model.economic_linearized_solution
#print axioms CommodityClassification.Equilibrium.Model.economic_linearized_solution

#check @CommodityClassification.Equilibrium.Model.quantity_path_derivative
#print axioms CommodityClassification.Equilibrium.Model.quantity_path_derivative

#check @CommodityClassification.Equilibrium.Model.path_positive_prices
#print axioms CommodityClassification.Equilibrium.Model.path_positive_prices

#check @CommodityClassification.Equilibrium.Model.clearing_path_linearized
#print axioms CommodityClassification.Equilibrium.Model.clearing_path_linearized

#check @CommodityClassification.Equilibrium.Model.economic_path_derivatives
#print axioms CommodityClassification.Equilibrium.Model.economic_path_derivatives

#check @CommodityClassification.Equilibrium.affineDemand_base
#print axioms CommodityClassification.Equilibrium.affineDemand_base

#check @CommodityClassification.Equilibrium.affineDemand_derivative
#print axioms CommodityClassification.Equilibrium.affineDemand_derivative

#check @CommodityClassification.Equilibrium.Example.ones_pos
#print axioms CommodityClassification.Equilibrium.Example.ones_pos

#check @CommodityClassification.Equilibrium.Example.frame_price_pos
#print axioms CommodityClassification.Equilibrium.Example.frame_price_pos

#check @CommodityClassification.Equilibrium.Example.model_report
#print axioms CommodityClassification.Equilibrium.Example.model_report

#check @CommodityClassification.Equilibrium.Example.model_total_pos
#print axioms CommodityClassification.Equilibrium.Example.model_total_pos

#check @CommodityClassification.Equilibrium.Example.model_K_posDef
#print axioms CommodityClassification.Equilibrium.Example.model_K_posDef

#check @CommodityClassification.Equilibrium.Example.concrete_linearized
#print axioms CommodityClassification.Equilibrium.Example.concrete_linearized

#check @CommodityClassification.Equilibrium.Example.concrete_solution
#print axioms CommodityClassification.Equilibrium.Example.concrete_solution

#check @CommodityClassification.Equilibrium.matCLM

#check @CommodityClassification.Equilibrium.taxCLM

#check @CommodityClassification.Equilibrium.coordCLM

#check @CommodityClassification.Equilibrium.Model

#check @CommodityClassification.Equilibrium.Model.A

#check @CommodityClassification.Equilibrium.Model.costData

#check @CommodityClassification.Equilibrium.Model.currentPrice

#check @CommodityClassification.Equilibrium.Model.costs

#check @CommodityClassification.Equilibrium.Model.currentInputs

#check @CommodityClassification.Equilibrium.Model.prices

#check @CommodityClassification.Equilibrium.Model.quantities

#check @CommodityClassification.Equilibrium.Model.factorDemand

#check @CommodityClassification.Equilibrium.Model.excess

#check @CommodityClassification.Equilibrium.Model.reduced

#check @CommodityClassification.Equilibrium.Model.hessian

#check @CommodityClassification.Equilibrium.Model.aggregateHessian

#check @CommodityClassification.Equilibrium.Model.R

#check @CommodityClassification.Equilibrium.Model.K

#check @CommodityClassification.Equilibrium.Model.m

#check @CommodityClassification.Equilibrium.Model.priceChange

#check @CommodityClassification.Equilibrium.Model.quantityChange

#check @CommodityClassification.Equilibrium.Model.factorChange

#check @CommodityClassification.Equilibrium.Model.excessChange

#check @CommodityClassification.Equilibrium.Model.reducedChange

#check @CommodityClassification.Equilibrium.Model.zSolution

#check @CommodityClassification.Equilibrium.Model.qSolution

#check @CommodityClassification.Equilibrium.Model.sSolution

#check @CommodityClassification.Equilibrium.Model.Linearized

#check @CommodityClassification.Equilibrium.affineDemand

#check @CommodityClassification.Equilibrium.Model.ofAffine

#check @CommodityClassification.Equilibrium.Example.model
