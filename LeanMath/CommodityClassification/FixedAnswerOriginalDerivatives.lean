module

public import LeanMath.CommodityClassification.FixedAnswerDifferentialTools

/-! Original derivative formulas in B.1. The manuscript and existing proofs are unchanged. -/
@[expose] public section
noncomputable section
namespace CommodityClassification.FixedAnswer
open Matrix Filter
open scoped BigOperators Topology
variable {n k r : ℕ}

-- The standard finite product norm. This adds no hypothesis to any theorem.
local instance (u v : ℕ) : NormedAddCommGroup (Mat u v) :=
  inferInstanceAs (NormedAddCommGroup (Fin u → Fin v → ℝ))
local instance (u v : ℕ) : NormedSpace ℝ (Mat u v) :=
  inferInstanceAs (NormedSpace ℝ (Fin u → Fin v → ℝ))

def Data.lineA (a : Data n k r) (Z : Mat r k) (t : ℝ) : Mat r k :=
  a.N.transpose * a.L * a.point (t • Z)
noncomputable def Data.lineY (a : Data n k r) (Z : Mat r k) (t : ℝ) : Vec k :=
  (a.K (a.point (t • Z)))⁻¹ *ᵥ a.m (a.point (t • Z))
noncomputable def Data.lineG (a : Data n k r) (Z : Mat r k) (t : ℝ) : Vec r :=
  a.r_N - a.lineA Z t *ᵥ a.lineY Z t
noncomputable def Data.lineF (a : Data n k r) (Z : Mat r k) (t : ℝ) : ℝ :=
  a.F (a.point (t • Z))

@[simp] theorem Data.lineA_zero (a : Data n k r) (Z : Mat r k) :
    a.lineA Z 0 = a.A_N := by simp [Data.lineA, Data.point, Data.A_N]
@[simp] theorem Data.lineY_zero (a : Data n k r) (Z : Mat r k) :
    a.lineY Z 0 = a.y₀ := by simp [Data.lineY, Data.point, Data.y₀, Data.K₀, Data.m₀]
@[simp] theorem Data.lineG_zero (a : Data n k r) (Z : Mat r k) :
    a.lineG Z 0 = a.r_N - a.A_N *ᵥ a.y₀ := by simp [Data.lineG]

theorem Data.hasDerivAt_pointLine (a : Data n k r) (Z : Mat r k) (t : ℝ) :
    HasDerivAt (fun s : ℝ => a.point (s • Z)) (a.N * Z) t := by
  have hz : HasDerivAt (fun s : ℝ => s • Z) Z t := by
    simpa using (hasDerivAt_id t).smul_const Z
  simpa only [Data.point, Matrix.zero_mul, zero_add] using
    (hasDerivAt_matrixMul (hasDerivAt_const t a.N) hz).const_add a.C₀

theorem Data.hasDerivAt_lineA (a : Data n k r) (Z : Mat r k) (t : ℝ) :
    HasDerivAt (a.lineA Z) (a.S_NN * Z) t := by
  change HasDerivAt (fun s => a.N.transpose * a.L * a.point (s • Z)) (a.S_NN * Z) t
  simpa only [Data.S_NN, Matrix.zero_mul, zero_add, Matrix.mul_assoc] using
    hasDerivAt_matrixMul (hasDerivAt_const t (a.N.transpose * a.L))
      (a.hasDerivAt_pointLine Z t)

theorem Data.hasDerivAt_mLine (a : Data n k r) (Z : Mat r k) (t : ℝ) :
    HasDerivAt (fun s => a.m (a.point (s • Z))) (Z.transpose *ᵥ a.r_N) t := by
  simpa only [Data.m, Data.r_N, transpose_mul, mulVec_mulVec,
    mulVec_zero, add_zero] using
    hasDerivAt_mulVec (hasDerivAt_transpose (a.hasDerivAt_pointLine Z t))
      (hasDerivAt_const t a.d)

theorem Data.hasDerivAt_KLine (a : Data n k r) (hL : a.L.transpose = a.L)
    (Z : Mat r k) (t : ℝ) :
    HasDerivAt (fun s => a.K (a.point (s • Z)))
      ((a.lineA Z t).transpose * Z + Z.transpose * a.lineA Z t) t := by
  have hc := a.hasDerivAt_pointLine Z t
  have hh := (hasDerivAt_matrixMul
    (hasDerivAt_matrixMul (hasDerivAt_transpose hc) (hasDerivAt_const t a.L)) hc).const_add a.base
  convert hh using 1
  · rfl
  · simp only [Data.lineA, transpose_mul, transpose_transpose, hL,
      Matrix.mul_zero, add_zero, Matrix.mul_assoc]
    abel

theorem Data.hasDerivAt_lineY (a : Data n k r) (hL : a.L.transpose = a.L)
    (Z : Mat r k) (t : ℝ) (hK : (a.K (a.point (t • Z))).PosDef) :
    HasDerivAt (a.lineY Z)
      ((a.K (a.point (t • Z)))⁻¹ *ᵥ
        (Z.transpose *ᵥ a.r_N -
         ((a.lineA Z t).transpose * Z + Z.transpose * a.lineA Z t) *ᵥ a.lineY Z t)) t := by
  exact hasDerivAt_inverse_mulVec (a.hasDerivAt_KLine hL Z t)
    (a.hasDerivAt_mLine Z t)
    ((a.K (a.point (t • Z))).isUnit_iff_isUnit_det.mp hK.isUnit)

theorem Data.hasDerivAt_lineF (a : Data n k r) (hL : a.L.transpose = a.L)
    (Z : Mat r k) (t : ℝ) (hK : (a.K (a.point (t • Z))).PosDef) :
    HasDerivAt (a.lineF Z) (2 * dotProduct (Z *ᵥ a.lineY Z t) (a.lineG Z t)) t := by
  have hh := hasDerivAt_inverseEnergy (a.hasDerivAt_KLine hL Z t)
    (a.hasDerivAt_mLine Z t) hK
  change HasDerivAt (a.lineF Z) _ t at hh
  apply hh.congr_deriv
  change 2 * dotProduct (Z.transpose *ᵥ a.r_N) (a.lineY Z t) -
    dotProduct (a.lineY Z t)
      (((a.lineA Z t).transpose * Z + Z.transpose * a.lineA Z t) *ᵥ a.lineY Z t) = _
  simp only [Data.lineG, add_mulVec, dotProduct_add, dotProduct_sub,
    ← mulVec_mulVec, dotProduct_transpose_mulVec]
  rw [dotProduct_comm (Z.transpose *ᵥ a.r_N), dotProduct_transpose_mulVec]
  rw [dotProduct_comm (a.lineA Z t *ᵥ a.lineY Z t)]
  rw [dotProduct_comm a.r_N]
  ring

/-- First-derivative formula for the manuscript's fixed-answer function. -/
theorem Data.original_first_derivative (a : Data n k r) (U : Set (Mat r k))
    (h : a.Hypotheses U) (Z : Mat r k) :
    HasDerivAt (a.lineF Z)
      (2 * dotProduct (Z *ᵥ a.y₀) (a.r_N - a.A_N *ᵥ a.y₀)) 0 := by
  simpa only [a.lineY_zero, a.lineG_zero] using
    a.hasDerivAt_lineF h.L_symmetric Z 0 (by
      simpa only [zero_smul] using h.K_posDef 0 h.origin_mem)

/-- Manuscript y'(0), using only the first-moment equality. -/
theorem Data.original_response_derivative (a : Data n k r) (U : Set (Mat r k))
    (h : a.Hypotheses U) (Z : Mat r k) (hr : a.r_N = a.A_N *ᵥ a.y₀) :
    HasDerivAt (a.lineY Z) (-(a.K₀⁻¹ *ᵥ (a.A_N.transpose *ᵥ (Z *ᵥ a.y₀)))) 0 := by
  have hh := a.hasDerivAt_lineY h.L_symmetric Z 0 (by
    simpa only [zero_smul] using h.K_posDef 0 h.origin_mem)
  apply hh.congr_deriv
  simp only [a.lineY_zero, a.lineA_zero, zero_smul, Data.point, Matrix.mul_zero, add_zero]
  change a.K₀⁻¹ *ᵥ (Z.transpose *ᵥ a.r_N -
    (a.A_N.transpose * Z + Z.transpose * a.A_N) *ᵥ a.y₀) = _
  have he : Z.transpose *ᵥ a.r_N -
      (a.A_N.transpose * Z + Z.transpose * a.A_N) *ᵥ a.y₀ =
      -(a.A_N.transpose *ᵥ (Z *ᵥ a.y₀)) := by
    simp only [hr, add_mulVec, ← mulVec_mulVec]
    abel
  rw [he, mulVec_neg]

/-- Manuscript g_N'(0); A(t)=N'LC(t) varies along with y(t). -/
theorem Data.original_residual_derivative (a : Data n k r) (U : Set (Mat r k))
    (h : a.Hypotheses U) (Z : Mat r k) (hr : a.r_N = a.A_N *ᵥ a.y₀) :
    HasDerivAt (a.lineG Z)
      (-((a.S_NN - a.A_N * a.K₀⁻¹ * a.A_N.transpose) *ᵥ (Z *ᵥ a.y₀))) 0 := by
  have hh := (hasDerivAt_const 0 a.r_N).sub
    (hasDerivAt_mulVec (a.hasDerivAt_lineA Z 0) (a.original_response_derivative U h Z hr))
  change HasDerivAt (a.lineG Z) _ 0 at hh
  apply hh.congr_deriv
  simp only [zero_sub, a.lineY_zero, a.lineA_zero, mulVec_neg,
    sub_mulVec, ← mulVec_mulVec]
  abel

/-- Manuscript F''(0), the derivative of the actual first-derivative function. -/
theorem Data.original_second_derivative (a : Data n k r) (U : Set (Mat r k))
    (h : a.Hypotheses U) (Z : Mat r k) (hr : a.r_N = a.A_N *ᵥ a.y₀) :
    HasDerivAt (deriv (a.lineF Z))
      (-2 * dotProduct (Z *ᵥ a.y₀)
        ((a.S_NN - a.A_N * a.K₀⁻¹ * a.A_N.transpose) *ᵥ (Z *ᵥ a.y₀))) 0 := by
  have hy := a.original_response_derivative U h Z hr
  have hg := a.original_residual_derivative U h Z hr
  have hzy := hasDerivAt_mulVec (hasDerivAt_const 0 Z) hy
  have hexpr := (hasDerivAt_dotProduct hzy hg).const_mul 2
  have hcalc : HasDerivAt
      (fun t => 2 * dotProduct (Z *ᵥ a.lineY Z t) (a.lineG Z t))
      (-2 * dotProduct (Z *ᵥ a.y₀)
        ((a.S_NN - a.A_N * a.K₀⁻¹ * a.A_N.transpose) *ᵥ (Z *ᵥ a.y₀))) 0 := by
    convert hexpr using 1
    simp only [a.lineG_zero, hr, sub_self, dotProduct_zero,
      a.lineY_zero, dotProduct_neg, zero_add]
    ring
  apply hcalc.congr_of_eventuallyEq
  have hc : Continuous (fun t : ℝ => t • Z) := continuous_id.smul continuous_const
  have htU : ∀ᶠ t : ℝ in 𝓝 0, t • Z ∈ U :=
    hc.continuousAt.preimage_mem_nhds (by
      simpa only [zero_smul] using h.domain_open.mem_nhds h.origin_mem)
  filter_upwards [htU] with t ht
  exact (a.hasDerivAt_lineF h.L_symmetric Z t (h.K_posDef _ ht)).deriv

end CommodityClassification.FixedAnswer
