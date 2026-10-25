module
public import LeanMath.CommodityClassification.DemandSpectralBound
public import Mathlib.Tactic.Abel
@[expose] public section
set_option maxHeartbeats 1800000
namespace CommodityClassification.Regularity
open Matrix
open scoped BigOperators
variable {n k r : ℕ}

noncomputable def adjustedDemand (p q : Vec n) (D : Mat n n) (σ : ℝ) : Mat n n :=
  D - σ • Supply.xi p q

/-- The manuscript's adjustment matrix, as an algebraic definition. -/
noncomputable def K (p q : Vec n) (D : Mat n n) (R : Mat k k) (σ : ℝ)
    (C : Mat n k) : Mat k k := σ • R + C.transpose * adjustedDemand p q D σ * C

theorem K_eq_demand_add_substitution (p q : Vec n) (D : Mat n n) (R : Mat k k)
    (σ : ℝ) (C : Mat n k) :
    K p q D R σ C = C.transpose * D * C + Supply.substitution σ R p q C := by
  simp only [K, adjustedDemand, Supply.substitution, Supply.residual, Matrix.mul_sub,
    Matrix.sub_mul, Matrix.mul_smul, Matrix.smul_mul, smul_sub]
  abel

theorem K_first_gap (p q : Vec n) (D : Mat n n) (R : Mat k k)
    (σ lam : ℝ) (C : Mat n k) :
    K p q D R σ C - (lam • (C.transpose * Supply.xi p q * C) +
      Supply.substitution σ R p q C) = C.transpose * (D - lam • Supply.xi p q) * C := by
  rw [K_eq_demand_add_substitution]
  simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.smul_mul]
  abel

theorem K_gap_decomposition (p q : Vec n) (D : Mat n n) (R : Mat k k)
    (σ lam α : ℝ) (C : Mat n k) :
    K p q D R σ C - α • R =
      C.transpose * (D - lam • Supply.xi p q) * C +
      (lam-α) • (C.transpose * Supply.xi p q * C) +
      (σ-α) • Supply.residual R p q C := by
  simp only [K, adjustedDemand, Supply.residual, Matrix.mul_sub, Matrix.sub_mul,
    Matrix.mul_smul, Matrix.smul_mul, smul_sub, sub_smul]
  abel

theorem K_first_lower_bound (p q : Vec n) (D : Mat n n) (R : Mat k k)
    (σ lam : ℝ) (C : Mat n k) (hD : (D - lam • Supply.xi p q).PosSemidef) :
    (K p q D R σ C - (lam • (C.transpose * Supply.xi p q * C) +
      Supply.substitution σ R p q C)).PosSemidef := by
  rw [K_first_gap]
  simpa using hD.conjTranspose_mul_mul_same C

/-- The algebraic lower bound needs only semidefinite residual supply curvature. -/
theorem K_uniform_lower_bound (p q : Vec n) (D : Mat n n) (R : Mat k k)
    (σ lam : ℝ) (C : Mat n k) (hXi : (Supply.xi p q).PosSemidef)
    (hD : (D - lam • Supply.xi p q).PosSemidef)
    (hS : (Supply.residual R p q C).PosSemidef) :
    (K p q D R σ C - min lam σ • R).PosSemidef := by
  rw [K_gap_decomposition p q D R σ lam (min lam σ) C]
  have h1 : (C.transpose * (D - lam • Supply.xi p q) * C).PosSemidef := by
    simpa using hD.conjTranspose_mul_mul_same C
  have h2 : (C.transpose * Supply.xi p q * C).PosSemidef := by
    simpa using hXi.conjTranspose_mul_mul_same C
  exact (h1.add (h2.smul (sub_nonneg.mpr (min_le_left lam σ)))).add
    (hS.smul (sub_nonneg.mpr (min_le_right lam σ)))

theorem posDef_of_positive_lower_bound (M R : Mat k k) (α : ℝ)
    (hgap : (M - α • R).PosSemidef) (hR : R.PosDef) (hα : 0 < α) : M.PosDef := by
  have hh := (hR.smul hα).add_posSemidef hgap
  simpa only [add_sub_cancel] using hh

theorem K_posDef (p q : Vec n) (D : Mat n n) (R : Mat k k)
    (σ lam : ℝ) (C : Mat n k) (hXi : (Supply.xi p q).PosSemidef)
    (hD : (D - lam • Supply.xi p q).PosSemidef)
    (hS : (Supply.residual R p q C).PosSemidef) (hR : R.PosDef)
    (hσ : 0 < σ) (hlam : 0 < lam) : (K p q D R σ C).PosDef :=
  posDef_of_positive_lower_bound _ R (min lam σ)
    (K_uniform_lower_bound p q D R σ lam C hXi hD hS) hR (lt_min hlam hσ)

theorem inverse_identities (M : Mat k k) (hM : M.PosDef) :
    M.det ≠ 0 ∧ M * M⁻¹ = 1 ∧ M⁻¹ * M = 1 := by
  let := hM.isUnit.invertible
  exact ⟨ne_of_gt hM.det_pos, Matrix.mul_inv_of_invertible M, Matrix.inv_mul_of_invertible M⟩

/-- Algebraic data for applying B.1 to an economic fiber. -/
noncomputable def fixedAnswerData (p q : Vec n) (D : Mat n n) (R : Mat k k)
    (σ : ℝ) (b : Vec n) (C0 : Mat n k) (N : Mat n r) : FixedAnswer.Data n k r where
  base := σ • R
  L := adjustedDemand p q D σ
  d := D *ᵥ b
  C₀ := C0
  N := N

theorem fixedAnswer_K_eq (p q : Vec n) (D : Mat n n) (R : Mat k k)
    (σ : ℝ) (b : Vec n) (C0 C : Mat n k) (N : Mat n r) :
    (fixedAnswerData p q D R σ b C0 N).K C = K p q D R σ C := rfl

end CommodityClassification.Regularity
