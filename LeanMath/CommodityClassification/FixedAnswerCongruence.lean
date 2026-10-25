module

public import LeanMath.CommodityClassification.FixedAnswerZeroBranch
public import Mathlib.Tactic.Abel

/-! Congruence sufficiency in Lemma B.1. Existing definitions are unchanged. -/
public section
namespace CommodityClassification.FixedAnswer
open Matrix
open scoped BigOperators
variable {n k r : ℕ}

theorem Data.K₀_posDef (a : Data n k r) (U : Set (Mat r k))
    (h : a.Hypotheses U) : a.K₀.PosDef := by
  simpa [Data.point, Data.K₀] using h.K_posDef 0 h.origin_mem

theorem Data.K_point (a : Data n k r) (hL : a.L.transpose = a.L) (Z : Mat r k) :
    a.K (a.point Z) = a.K₀ + a.A_N.transpose * Z + Z.transpose * a.A_N +
      Z.transpose * a.S_NN * Z := by
  simp only [Data.K, Data.K₀, Data.point, Data.A_N, Data.S_NN,
    transpose_add, transpose_mul, transpose_transpose, hL, Matrix.add_mul, Matrix.mul_add,
    Matrix.mul_assoc]
  abel

noncomputable def Data.congruenceMap (a : Data n k r) (Z : Mat r k) : Mat k k :=
  1 + a.K₀⁻¹ * a.A_N.transpose * Z

theorem Data.K_congruence (a : Data n k r) (hL : a.L.transpose = a.L)
    (hK : a.K₀.PosDef)
    (hS : a.S_NN = a.A_N * a.K₀⁻¹ * a.A_N.transpose) (Z : Mat r k) :
    a.K (a.point Z) = (a.congruenceMap Z).transpose * a.K₀ * a.congruenceMap Z := by
  have hi : a.K₀⁻¹.transpose = a.K₀⁻¹ := by
    simpa only [IsHermitian, conjTranspose_eq_transpose_of_trivial] using hK.inv.isHermitian
  have hu := a.K₀.isUnit_iff_isUnit_det.mp hK.isUnit
  rw [a.K_point hL, hS]
  simp only [Data.congruenceMap, transpose_add, transpose_one, transpose_mul,
    transpose_transpose, hi, add_mul, mul_add, Matrix.one_mul, Matrix.mul_one,
    Matrix.mul_assoc]
  simp only [← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hu,
    Matrix.mul_nonsing_inv _ hu, Matrix.mul_one, Matrix.one_mul]
  abel

theorem Data.m_congruence (a : Data n k r) (hK : a.K₀.PosDef)
    (hr : a.r_N = a.A_N *ᵥ a.y₀) (Z : Mat r k) :
    a.m (a.point Z) = (a.congruenceMap Z).transpose *ᵥ a.m₀ := by
  have hi : a.K₀⁻¹.transpose = a.K₀⁻¹ := by
    simpa only [IsHermitian, conjTranspose_eq_transpose_of_trivial] using hK.inv.isHermitian
  simp only [a.m_point, hr, Data.congruenceMap, transpose_add, transpose_one,
    transpose_mul, transpose_transpose, hi, add_mulVec, one_mulVec,
    mulVec_mulVec, Data.y₀]

/-- Positive definiteness of the congruence forces the square factor to be invertible. -/
theorem isUnit_of_posDef_congruence (K H : Mat k k)
    (h : (H.transpose * K * H).PosDef) : IsUnit H := by
  apply mulVec_injective_iff_isUnit.mp
  intro x y hxy
  apply h.mulVec_injective
  simpa only [mulVec_mulVec, Matrix.mul_assoc] using
    congrArg (fun z => H.transpose *ᵥ (K *ᵥ z)) hxy

/-- The inverse energy is unchanged by a nonsingular congruence. -/
theorem inverseEnergy_congruence (K H : Mat k k) (x : Vec k)
    (_hK : K.PosDef) (hH : IsUnit H) :
    dotProduct (H.transpose *ᵥ x) ((H.transpose * K * H)⁻¹ *ᵥ (H.transpose *ᵥ x)) =
      dotProduct x (K⁻¹ *ᵥ x) := by
  have hu := H.isUnit_iff_isUnit_det.mp hH
  have hut : IsUnit H.transpose.det := by simpa using hu
  rw [Matrix.mul_inv_rev, Matrix.mul_inv_rev]
  simp only [mulVec_mulVec, Matrix.mul_assoc,
    Matrix.nonsing_inv_mul _ hut, Matrix.mul_one]
  rw [dotProduct_comm, dotProduct_transpose_mulVec, dotProduct_comm]
  simp only [mulVec_mulVec, ← Matrix.mul_assoc,
    Matrix.mul_nonsing_inv _ hu, Matrix.one_mul]
  exact dotProduct_comm _ _

/-- B1.CONGRUENCE_SUFFICIENCY: applies to every positive-definite point, including outside U. -/
theorem congruence_sufficient_global (a : Data n k r) (U : Set (Mat r k))
    (h : a.Hypotheses U) (hr : a.r_N = a.A_N *ᵥ a.y₀)
    (hS : a.S_NN = a.A_N * a.K₀⁻¹ * a.A_N.transpose) :
    a.ConstantOn a.AdmissibleCoordinates := by
  intro Z hZ
  have hK := a.K₀_posDef U h
  have heq := a.K_congruence h.L_symmetric hK hS Z
  have hHZ : (a.congruenceMap Z).transpose * a.K₀ * a.congruenceMap Z |>.PosDef := by
    rw [← heq]
    exact hZ
  have hu := isUnit_of_posDef_congruence a.K₀ (a.congruenceMap Z) hHZ
  change dotProduct (a.m (a.point Z)) ((a.K (a.point Z))⁻¹ *ᵥ a.m (a.point Z)) = _
  rw [heq, a.m_congruence hK hr]
  exact inverseEnergy_congruence a.K₀ (a.congruenceMap Z) a.m₀ hK hu

end CommodityClassification.FixedAnswer
