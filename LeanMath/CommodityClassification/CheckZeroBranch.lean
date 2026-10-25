module

import LeanMath.CommodityClassification.FixedAnswerZeroBranch

/- Audit of actual proof declarations, not merely Prop-valued definitions. -/
open CommodityClassification.FixedAnswer

#check @Data.m_point
#check @invQuadratic_eq_zero_iff
#check @Data.F_eq_zero_iff
#check @vector_eq_zero_of_transpose_mulVec_on_open
#check @zeroLoad_constantOn_iff
#check @zeroLoad_noHiddenDirections

#print axioms Data.m_point
#print axioms invQuadratic_eq_zero_iff
#print axioms Data.F_eq_zero_iff
#print axioms vector_eq_zero_of_transpose_mulVec_on_open
#print axioms zeroLoad_constantOn_iff
#print axioms zeroLoad_noHiddenDirections
