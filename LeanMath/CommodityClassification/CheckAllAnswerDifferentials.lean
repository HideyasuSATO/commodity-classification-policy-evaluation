module
import LeanMath.CommodityClassification.CheckAnswerCoordinates
import LeanMath.CommodityClassification.AllAnswerLinearResidual
import LeanMath.CommodityClassification.AllAnswerCongruenceExpansion

set_option pp.universes false

#check @CommodityClassification.FixedAnswer.matrix_ne_zero_entry
#print axioms CommodityClassification.FixedAnswer.matrix_ne_zero_entry

#check @CommodityClassification.FixedAnswer.matrix_unit_sandwich
#print axioms CommodityClassification.FixedAnswer.matrix_unit_sandwich

#check @CommodityClassification.FixedAnswer.universal_cross_zero
#print axioms CommodityClassification.FixedAnswer.universal_cross_zero

#check @CommodityClassification.FixedAnswer.universal_linear_zero
#print axioms CommodityClassification.FixedAnswer.universal_linear_zero

#check @CommodityClassification.FixedAnswer.symmetric_zero_of_quadratic
#print axioms CommodityClassification.FixedAnswer.symmetric_zero_of_quadratic

#check @CommodityClassification.FixedAnswer.universal_quadratic_zero
#print axioms CommodityClassification.FixedAnswer.universal_quadratic_zero

#check @CommodityClassification.FixedAnswer.hasDerivAt_matrixInverse
#print axioms CommodityClassification.FixedAnswer.hasDerivAt_matrixInverse

#check @CommodityClassification.FixedAnswer.hasDerivAt_schurResidual
#print axioms CommodityClassification.FixedAnswer.hasDerivAt_schurResidual

#check @CommodityClassification.FixedAnswer.Data.schur_transpose
#print axioms CommodityClassification.FixedAnswer.Data.schur_transpose

#check @CommodityClassification.FixedAnswer.Data.hasDerivAt_loadingAlong
#print axioms CommodityClassification.FixedAnswer.Data.hasDerivAt_loadingAlong

#check @CommodityClassification.FixedAnswer.Data.hasDerivAt_schurAlong
#print axioms CommodityClassification.FixedAnswer.Data.hasDerivAt_schurAlong

#check @CommodityClassification.FixedAnswer.Data.cross_equation
#print axioms CommodityClassification.FixedAnswer.Data.cross_equation

#check @CommodityClassification.FixedAnswer.Data.inverse_loading_ne_zero
#print axioms CommodityClassification.FixedAnswer.Data.inverse_loading_ne_zero

#check @CommodityClassification.FixedAnswer.Data.cross_vanishes
#print axioms CommodityClassification.FixedAnswer.Data.cross_vanishes

#check @CommodityClassification.FixedAnswer.second_derivative_from_cross
#print axioms CommodityClassification.FixedAnswer.second_derivative_from_cross

#check @CommodityClassification.FixedAnswer.Data.original_cross_second_derivative
#print axioms CommodityClassification.FixedAnswer.Data.original_cross_second_derivative

#check @CommodityClassification.FixedAnswer.Data.parent_schur_vanishes
#print axioms CommodityClassification.FixedAnswer.Data.parent_schur_vanishes

#check @CommodityClassification.FixedAnswer.Data.hasDerivAt_linearResidualAlong
#print axioms CommodityClassification.FixedAnswer.Data.hasDerivAt_linearResidualAlong

#check @CommodityClassification.FixedAnswer.Data.linear_residual_vanishes
#print axioms CommodityClassification.FixedAnswer.Data.linear_residual_vanishes

#check @CommodityClassification.FixedAnswer.Data.parent_congruence_with_residual
#print axioms CommodityClassification.FixedAnswer.Data.parent_congruence_with_residual

#check @CommodityClassification.FixedAnswer.Data.loading_congruence_of_cross_zero
#print axioms CommodityClassification.FixedAnswer.Data.loading_congruence_of_cross_zero

#check @CommodityClassification.FixedAnswer.Data.withDirections
#check @CommodityClassification.FixedAnswer.Data.loading
#check @CommodityClassification.FixedAnswer.Data.schur
#check @CommodityClassification.FixedAnswer.Data.solvedResponse
#check @CommodityClassification.FixedAnswer.Data.linearResidual
