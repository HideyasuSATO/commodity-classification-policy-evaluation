module
public import LeanMath.CommodityClassification.FixedAnswerComplete

/-! Algebraic corollaries matching the clarified Section 3.1 explanation.
The economic derivation of the coefficient nu - F is a separate obligation. -/
public section
namespace CommodityClassification.FixedAnswer
open Matrix
variable {n k r : ℕ}

/-- At a fixed answer containing a zero-load candidate, all coefficients equal
nu exactly when the load vanishes along every hidden direction. -/
theorem zeroLoad_coefficient_eq_iff (a : Data n k r) (U : Set (Mat r k))
    (h : a.Hypotheses U) (hm : a.m₀ = 0) (nu : ℝ) :
    (∀ Z ∈ U, nu - a.F (a.point Z) = nu) ↔ a.r_N = 0 := by
  have hF0 : a.F a.C₀ = 0 := by
    change dotProduct a.m₀ (a.K₀⁻¹ *ᵥ a.m₀) = 0
    simp only [hm, mulVec_zero, dotProduct_zero]
  constructor
  · intro hc
    apply (zeroLoad_constantOn_iff a U h hm).mp
    intro Z hZ
    rw [hF0]
    exact sub_eq_self.mp (hc Z hZ)
  · intro hr Z hZ
    rw [(zeroLoad_constantOn_iff a U h hm).mpr hr Z hZ, hF0, sub_zero]

/-- The common coefficient extends to the whole admissible affine fiber. -/
theorem zeroLoad_coefficient_eq_global (a : Data n k r)
    (hm : a.m₀ = 0) (hr : a.r_N = 0) (nu : ℝ) :
    ∀ Z ∈ a.AdmissibleCoordinates, nu - a.F (a.point Z) = nu := by
  have hF0 : a.F a.C₀ = 0 := by
    change dotProduct a.m₀ (a.K₀⁻¹ *ᵥ a.m₀) = 0
    simp only [hm, mulVec_zero, dotProduct_zero]
  intro Z hZ
  rw [zeroLoad_constantOn_global a hm hr Z hZ, hF0, sub_zero]

end CommodityClassification.FixedAnswer
