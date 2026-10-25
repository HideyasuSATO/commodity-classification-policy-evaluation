module

public import LeanMath.CommodityClassification.AllAnswerSecondDerivative

/-! Actual linear-residual derivative for all-answer identification. -/
@[expose] public section
noncomputable section
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
namespace CommodityClassification.FixedAnswer
open Matrix Filter
open scoped BigOperators Topology
variable {n k r s u : ℕ}

local instance (a b : ℕ) : NormedAddCommGroup (Mat a b) :=
  inferInstanceAs (NormedAddCommGroup (Fin a → Fin b → ℝ))
local instance (a b : ℕ) : NormedSpace ℝ (Mat a b) :=
  inferInstanceAs (NormedSpace ℝ (Fin a → Fin b → ℝ))

def Data.solvedResponse (a : Data n k r) (C : Mat n k) : Vec k :=
  (a.K C)⁻¹ *ᵥ a.m C

def Data.linearResidual (a : Data n k r) (U : Mat n s) (C : Mat n k) : Vec s :=
  U.transpose *ᵥ a.d - a.loading U C *ᵥ a.solvedResponse C

theorem Data.hasDerivAt_linearResidualAlong (a : Data n k r) (U : Mat n s)
    (V : Mat n u) (X : Mat u k) (t : ℝ) (hL : a.L.transpose = a.L)
    (hK : (a.K ((a.withDirections V).point (t • X))).PosDef) :
    HasDerivAt (fun z => a.linearResidual U ((a.withDirections V).point (z • X)))
      (-(a.schur U V ((a.withDirections V).point (t • X)) *ᵥ
          (X *ᵥ a.solvedResponse ((a.withDirections V).point (t • X)))) -
        (a.loading U ((a.withDirections V).point (t • X)) *
          (a.K ((a.withDirections V).point (t • X)))⁻¹) *ᵥ
          (X.transpose *ᵥ a.linearResidual V ((a.withDirections V).point (t • X)))) t := by
  have hy := (a.withDirections V).hasDerivAt_lineY hL X t hK
  have hd := (hasDerivAt_const t (U.transpose *ᵥ a.d)).sub
    (hasDerivAt_mulVec (a.hasDerivAt_loadingAlong U V X t) hy)
  apply hd.congr_deriv
  simp only [Data.linearResidual, Data.schur, Data.solvedResponse,
    Data.lineY, Data.lineA, Data.r_N, Data.withDirections,
    Data.loading, Data.K, Data.m,
    sub_mulVec, add_mulVec, mulVec_sub, mulVec_add, ← mulVec_mulVec, zero_sub]
  abel

theorem Data.linear_residual_vanishes (a : Data n k r) (U : Mat n s)
    (hL : a.L.transpose = a.L) (hK : a.K₀.PosDef) (hA : a.A_N ≠ 0)
    (hcross : a.schur a.N U a.C₀ = 0)
    (hz : ∀ X : Mat s k, ∀ᶠ t : ℝ in 𝓝 0,
      a.linearResidual a.N ((a.withDirections U).point (t • X)) = 0) :
    a.linearResidual U a.C₀ = 0 := by
  apply universal_linear_zero (a.K₀⁻¹ * a.A_N.transpose)
    (a.inverse_loading_ne_zero hK hA) (a.linearResidual U a.C₀)
  intro X
  have hd := a.hasDerivAt_linearResidualAlong a.N U X 0 hL (by
    simpa only [Data.point, Data.withDirections, zero_smul, Matrix.mul_zero,
      add_zero, Data.K₀] using hK)
  have heq : (fun t : ℝ => a.linearResidual a.N ((a.withDirections U).point (t • X)))
      =ᶠ[𝓝 0] (fun _ => (0:Vec r)) := hz X
  have he := (hd.congr_of_eventuallyEq heq.symm).unique (hasDerivAt_const 0 (0:Vec r))
  simp only [Data.point, Data.withDirections, zero_smul, Matrix.mul_zero,
    add_zero, hcross, zero_mulVec, neg_zero, zero_sub, neg_eq_zero] at he
  have hi : (a.K₀⁻¹).transpose = a.K₀⁻¹ := hK.inv.isHermitian.isSymm
  simp only [transpose_mul, transpose_transpose, hi]
  simpa only [← mulVec_mulVec,
    Data.K₀, Data.A_N, Data.loading] using he

end CommodityClassification.FixedAnswer
