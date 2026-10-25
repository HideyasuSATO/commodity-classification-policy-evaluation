module
import LeanMath.CommodityClassification.CheckPrecisionConcentratedSales
import LeanMath.CommodityClassification.RobustQuadraticCauchy

set_option pp.universes false

#check @CommodityClassification.Equilibrium.Model.withPolicy_K
#print axioms CommodityClassification.Equilibrium.Model.withPolicy_K

#check @CommodityClassification.Equilibrium.Model.withPolicy_substitution
#print axioms CommodityClassification.Equilibrium.Model.withPolicy_substitution

#check @CommodityClassification.Equilibrium.Model.withPolicy_self
#print axioms CommodityClassification.Equilibrium.Model.withPolicy_self

#check @CommodityClassification.Equilibrium.Model.welfareMatrix_quadratic
#print axioms CommodityClassification.Equilibrium.Model.welfareMatrix_quadratic

#check @CommodityClassification.Equilibrium.Model.welfareMatrix_correction_posSemidef
#print axioms CommodityClassification.Equilibrium.Model.welfareMatrix_correction_posSemidef

#check @CommodityClassification.Equilibrium.Model.welfareMatrix_isHermitian
#print axioms CommodityClassification.Equilibrium.Model.welfareMatrix_isHermitian

#check @CommodityClassification.Equilibrium.Model.welfareMatrix_posSemidef
#print axioms CommodityClassification.Equilibrium.Model.welfareMatrix_posSemidef

#check @CommodityClassification.Equilibrium.Model.welfareMatrix_le_demand
#print axioms CommodityClassification.Equilibrium.Model.welfareMatrix_le_demand

#check @CommodityClassification.Equilibrium.Model.welfareMatrix_current_coefficient
#print axioms CommodityClassification.Equilibrium.Model.welfareMatrix_current_coefficient

#check @CommodityClassification.Robust.loewner_quadratic_lower
#print axioms CommodityClassification.Robust.loewner_quadratic_lower

#check @CommodityClassification.Robust.loewner_quadratic_upper
#print axioms CommodityClassification.Robust.loewner_quadratic_upper

#check @CommodityClassification.Robust.objective_loewner_comparison
#print axioms CommodityClassification.Robust.objective_loewner_comparison

#check @CommodityClassification.Robust.coefficient_loewner_comparison
#print axioms CommodityClassification.Robust.coefficient_loewner_comparison

#check @CommodityClassification.Robust.semidefinite_cauchy_sq
#print axioms CommodityClassification.Robust.semidefinite_cauchy_sq

#check @CommodityClassification.Robust.semidefinite_cross_bound
#print axioms CommodityClassification.Robust.semidefinite_cross_bound

#check @CommodityClassification.Robust.semidefinite_add_expansion
#print axioms CommodityClassification.Robust.semidefinite_add_expansion

#check @CommodityClassification.Robust.semidefinite_quadratic_subtraction
#print axioms CommodityClassification.Robust.semidefinite_quadratic_subtraction

#check @CommodityClassification.Equilibrium.Model.withPolicy
#print axioms CommodityClassification.Equilibrium.Model.withPolicy
#check @CommodityClassification.Equilibrium.Model.welfareMatrix
#print axioms CommodityClassification.Equilibrium.Model.welfareMatrix
