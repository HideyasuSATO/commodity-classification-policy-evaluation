module
import LeanMath.CommodityClassification.CheckCESCostDerivatives
import LeanMath.CommodityClassification.SupplyBoundaryExample

-- The imported audit retains B.1, input coordinates, reports and the actual CES derivatives.
-- The declarations below are proofs, including the actual-candidate closure example.
set_option pp.universes false

#check @CommodityClassification.Supply.curvature_symmetric
#print axioms CommodityClassification.Supply.curvature_symmetric

#check @CommodityClassification.Supply.curvature_quad
#print axioms CommodityClassification.Supply.curvature_quad

#check @CommodityClassification.Supply.curvature_variance
#print axioms CommodityClassification.Supply.curvature_variance

#check @CommodityClassification.Supply.curvature_nonneg
#print axioms CommodityClassification.Supply.curvature_nonneg

#check @CommodityClassification.Supply.curvature_zero_iff
#print axioms CommodityClassification.Supply.curvature_zero_iff

#check @CommodityClassification.Supply.curvature_posSemidef
#print axioms CommodityClassification.Supply.curvature_posSemidef

#check @CommodityClassification.Supply.relative_not_proportional
#print axioms CommodityClassification.Supply.relative_not_proportional

#check @CommodityClassification.Supply.curvature_relative_pos
#print axioms CommodityClassification.Supply.curvature_relative_pos

#check @CommodityClassification.Supply.quad_conjugate
#print axioms CommodityClassification.Supply.quad_conjugate

#check @CommodityClassification.Supply.curvature_relative_posDef
#print axioms CommodityClassification.Supply.curvature_relative_posDef

#check @CommodityClassification.Supply.negative_cost_hessian
#print axioms CommodityClassification.Supply.negative_cost_hessian

#check @CommodityClassification.Supply.actual_cost_hessian
#print axioms CommodityClassification.Supply.actual_cost_hessian

#check @CommodityClassification.Supply.totalInputs_pos
#print axioms CommodityClassification.Supply.totalInputs_pos

#check @CommodityClassification.Supply.goods_nonempty_of_total_pos
#print axioms CommodityClassification.Supply.goods_nonempty_of_total_pos

#check @CommodityClassification.Supply.knownR_posDef
#print axioms CommodityClassification.Supply.knownR_posDef

#check @CommodityClassification.Supply.aggregate_curvature
#print axioms CommodityClassification.Supply.aggregate_curvature

#check @CommodityClassification.Supply.residual_eq_sum
#print axioms CommodityClassification.Supply.residual_eq_sum

#check @CommodityClassification.Supply.residual_posDef
#print axioms CommodityClassification.Supply.residual_posDef

#check @CommodityClassification.Supply.substitution_posDef
#print axioms CommodityClassification.Supply.substitution_posDef

#check @CommodityClassification.Supply.substitution_posSemidef
#print axioms CommodityClassification.Supply.substitution_posSemidef

#check @CommodityClassification.Supply.aggregate_negative_hessian
#print axioms CommodityClassification.Supply.aggregate_negative_hessian

#check @CommodityClassification.Supply.aggregate_actual_hessian
#print axioms CommodityClassification.Supply.aggregate_actual_hessian

#check @CommodityClassification.Supply.sum_report_eq_total
#print axioms CommodityClassification.Supply.sum_report_eq_total

#check @CommodityClassification.Supply.total_eq_of_report
#print axioms CommodityClassification.Supply.total_eq_of_report

#check @CommodityClassification.Supply.coordinate_total_eq
#print axioms CommodityClassification.Supply.coordinate_total_eq

#check @CommodityClassification.Supply.candidate_total_eq
#print axioms CommodityClassification.Supply.candidate_total_eq

#check @CommodityClassification.Supply.candidate_R_eq
#print axioms CommodityClassification.Supply.candidate_R_eq

#check @CommodityClassification.Supply.candidate_R_posDef
#print axioms CommodityClassification.Supply.candidate_R_posDef

#check @CommodityClassification.Supply.candidate_residual_posDef
#print axioms CommodityClassification.Supply.candidate_residual_posDef

#check @CommodityClassification.Supply.candidate_substitution_posDef
#print axioms CommodityClassification.Supply.candidate_substitution_posDef

#check @CommodityClassification.Supply.candidate_actual_hessian
#print axioms CommodityClassification.Supply.candidate_actual_hessian

#check @CommodityClassification.Supply.closure_report_eq
#print axioms CommodityClassification.Supply.closure_report_eq

#check @CommodityClassification.Supply.closure_R_eq
#print axioms CommodityClassification.Supply.closure_R_eq

#check @CommodityClassification.Supply.residual_symmetric
#print axioms CommodityClassification.Supply.residual_symmetric

#check @CommodityClassification.Supply.residual_quad_continuous
#print axioms CommodityClassification.Supply.residual_quad_continuous

#check @CommodityClassification.Supply.closure_residual_posSemidef
#print axioms CommodityClassification.Supply.closure_residual_posSemidef

#check @CommodityClassification.Supply.candidate_closure_residual_posSemidef
#print axioms CommodityClassification.Supply.candidate_closure_residual_posSemidef

#check @CommodityClassification.Supply.candidate_closure_substitution_posSemidef
#print axioms CommodityClassification.Supply.candidate_closure_substitution_posSemidef

#check @CommodityClassification.Supply.Example.path_cost
#print axioms CommodityClassification.Supply.Example.path_cost

#check @CommodityClassification.Supply.Example.path_reconstruct
#print axioms CommodityClassification.Supply.Example.path_reconstruct

#check @CommodityClassification.Supply.Example.path_exposure
#print axioms CommodityClassification.Supply.Example.path_exposure

#check @CommodityClassification.Supply.Example.path_report
#print axioms CommodityClassification.Supply.Example.path_report

#check @CommodityClassification.Supply.Example.path_total
#print axioms CommodityClassification.Supply.Example.path_total

#check @CommodityClassification.Supply.Example.path_positive
#print axioms CommodityClassification.Supply.Example.path_positive

#check @CommodityClassification.Supply.Example.path_mem
#print axioms CommodityClassification.Supply.Example.path_mem

#check @CommodityClassification.Supply.Example.path_continuous
#print axioms CommodityClassification.Supply.Example.path_continuous

#check @CommodityClassification.Supply.Example.boundary_in_actual_closure
#print axioms CommodityClassification.Supply.Example.boundary_in_actual_closure

#check @CommodityClassification.Supply.Example.fixed_R
#print axioms CommodityClassification.Supply.Example.fixed_R

#check @CommodityClassification.Supply.Example.path_residual
#print axioms CommodityClassification.Supply.Example.path_residual

#check @CommodityClassification.Supply.Example.interior_positive
#print axioms CommodityClassification.Supply.Example.interior_positive

#check @CommodityClassification.Supply.Example.boundary_zero
#print axioms CommodityClassification.Supply.Example.boundary_zero

#check @CommodityClassification.Supply.Example.boundary_not_posDef
#print axioms CommodityClassification.Supply.Example.boundary_not_posDef

#check @CommodityClassification.Supply.curvature

#check @CommodityClassification.Supply.totalInputs

#check @CommodityClassification.Supply.xi

#check @CommodityClassification.Supply.knownR

#check @CommodityClassification.Supply.residual

#check @CommodityClassification.Supply.substitution

#check @CommodityClassification.Supply.candidateR

#check @CommodityClassification.Supply.Example.frame

#check @CommodityClassification.Supply.Example.parent

#check @CommodityClassification.Supply.Example.ones

#check @CommodityClassification.Supply.Example.inputs

#check @CommodityClassification.Supply.Example.path

#print axioms CommodityClassification.Supply.Example.frame

#print axioms CommodityClassification.Supply.Example.parent
