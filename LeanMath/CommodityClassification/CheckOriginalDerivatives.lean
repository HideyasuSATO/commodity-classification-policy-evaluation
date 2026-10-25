module
import LeanMath.CommodityClassification.FixedAnswerOriginalDerivatives
open CommodityClassification.FixedAnswer Matrix

-- Explicit universal-dimensional checks against the mathematical formulas.
example {n k r : ℕ} (a : Data n k r) (U : Set (Mat r k))
    (h : a.Hypotheses U) (Z : Mat r k) :
    HasDerivAt (fun t : ℝ => a.F (a.point (t • Z)))
      (2 * dotProduct (Z *ᵥ a.y₀) (a.r_N - a.A_N *ᵥ a.y₀)) 0 :=
  a.original_first_derivative U h Z

example {n k r : ℕ} (a : Data n k r) (U : Set (Mat r k))
    (h : a.Hypotheses U) (Z : Mat r k) (hr : a.r_N = a.A_N *ᵥ a.y₀) :
    HasDerivAt (deriv (fun t : ℝ => a.F (a.point (t • Z))))
      (-2 * dotProduct (Z *ᵥ a.y₀)
        ((a.S_NN - a.A_N * a.K₀⁻¹ * a.A_N.transpose) *ᵥ (Z *ᵥ a.y₀))) 0 :=
  a.original_second_derivative U h Z hr

-- Hidden dimension zero: both scalar derivatives are zero, without a load restriction.
example {n k : ℕ} (a : Data n k 0) (U : Set (Mat 0 k))
    (h : a.Hypotheses U) (Z : Mat 0 k) : HasDerivAt (a.lineF Z) 0 0 := by
  simpa [dotProduct] using a.original_first_derivative U h Z

example {n k : ℕ} (a : Data n k 0) (U : Set (Mat 0 k))
    (h : a.Hypotheses U) (Z : Mat 0 k) : HasDerivAt (deriv (a.lineF Z)) 0 0 := by
  have hr : a.r_N = a.A_N *ᵥ a.y₀ := Subsingleton.elim _ _
  simpa [dotProduct] using a.original_second_derivative U h Z hr

#check @Data.original_first_derivative
#check @Data.original_response_derivative
#check @Data.original_residual_derivative
#check @Data.original_second_derivative

#print axioms hasDerivAt_dotProduct
#print axioms hasDerivAt_mulVec
#print axioms hasDerivAt_matrixMul
#print axioms hasDerivAt_transpose
#print axioms differentiableAt_det_entries
#print axioms differentiableAt_inv_entries
#print axioms differentiableAt_inverse_mulVec
#print axioms hasDerivAt_inverse_mulVec
#print axioms hasDerivAt_inverseEnergy
#print axioms Data.lineA_zero
#print axioms Data.lineY_zero
#print axioms Data.lineG_zero
#print axioms Data.hasDerivAt_pointLine
#print axioms Data.hasDerivAt_lineA
#print axioms Data.hasDerivAt_mLine
#print axioms Data.hasDerivAt_KLine
#print axioms Data.hasDerivAt_lineY
#print axioms Data.hasDerivAt_lineF
#print axioms Data.original_first_derivative
#print axioms Data.original_response_derivative
#print axioms Data.original_residual_derivative
#print axioms Data.original_second_derivative
