module
import LeanMath.CommodityClassification.FixedAnswerComplete
open CommodityClassification.FixedAnswer

-- These examples force elaboration against the expanded original statements.
example {n k r : ℕ} (a : Data n k r) (U : Set (Mat r k))
    (h : a.Hypotheses U) : a.ConstantOn U ↔ a.CongruenceCriterion :=
  lemmaB1_local a U h

example {n k r : ℕ} (a : Data n k r) (U : Set (Mat r k))
    (h : a.Hypotheses U) (hc : a.CongruenceCriterion)
    (Z : Mat r k) (hZ : (a.K (a.point Z)).PosDef) :
    a.F (a.point Z) = a.F a.C₀ :=
  lemmaB1_global a U h hc Z hZ

example : LemmaB1Statement := lemmaB1_proved

#check @lemmaB1_local
#check @lemmaB1_global
#check @lemmaB1_proved
#check @nonzeroLoad_constantOn_iff
#check @zeroLoad_constantOn_iff
#check @constantOn_noHiddenDirections

#print axioms Data.m_point
#print axioms invQuadratic_eq_zero_iff
#print axioms Data.F_eq_zero_iff
#print axioms vector_eq_zero_of_transpose_mulVec_on_open
#print axioms zeroLoad_constantOn_iff
#print axioms zeroLoad_noHiddenDirections
#print axioms Data.K₀_posDef
#print axioms Data.K_point
#print axioms Data.K_congruence
#print axioms Data.m_congruence
#print axioms isUnit_of_posDef_congruence
#print axioms inverseEnergy_congruence
#print axioms congruence_sufficient_global
#print axioms Data.K₀_mul_y₀
#print axioms Data.y₀_ne_zero
#print axioms inverseEnergy_variational_bound
#print axioms quadratic_linear_coefficient_zero
#print axioms mulVec_surjective_in_matrix
#print axioms Data.variational_gap
#print axioms firstMoment_of_constant_nonzero
#print axioms Data.recenter_point
#print axioms firstMoment_of_constant
#print axioms firstMoment_at
#print axioms Data.K_mul_response
#print axioms Data.reduced_response
#print axioms Data.residual_response_zero
#print axioms Data.continuousAt_response_zero
#print axioms secondMoment_of_constant_nonzero
#print axioms nonzeroLoad_necessary
#print axioms nonzeroLoad_constantOn_iff
#print axioms zeroLoad_constantOn_global
#print axioms lemmaB1_local
#print axioms lemmaB1_global
#print axioms lemmaB1_proved
#print axioms constantOn_noHiddenDirections
