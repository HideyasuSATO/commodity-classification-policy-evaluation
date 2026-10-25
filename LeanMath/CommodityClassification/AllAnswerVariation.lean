module

public import LeanMath.CommodityClassification.FixedAnswerOriginalDerivatives
public import LeanMath.CommodityClassification.FixedAnswerVariation
public import Mathlib.Data.Matrix.Basis

/-! Universal matrix variations used in the all-answer dichotomy. -/
@[expose] public section
noncomputable section
namespace CommodityClassification.FixedAnswer
open Matrix
open scoped BigOperators
variable {k r s : ℕ}

theorem matrix_ne_zero_entry (E : Mat k r) (hE : E ≠ 0) :
    ∃ i j, E i j ≠ 0 := by
  contrapose! hE
  ext i j
  exact hE i j

theorem matrix_unit_sandwich (M : Mat r s) (E : Mat k r)
    (a : Fin s) (b : Fin k) (i j : Fin r) :
    (M * Matrix.single a b (1:ℝ) * E) i j = M i a * E b j := by
  simp [Matrix.mul_apply, Matrix.single, ite_and]

theorem universal_cross_zero (M : Mat r s) (E : Mat k r) (hE : E ≠ 0)
    (h : ∀ X : Mat s k,
      M * X * E + E.transpose * X.transpose * M.transpose = 0) : M = 0 := by
  obtain ⟨b,j,hbj⟩ := matrix_ne_zero_entry E hE
  have entry (a : Fin s) (i : Fin r) :
      M i a * E b j + E b i * M j a = 0 := by
    have hh := congrFun (congrFun (h (Matrix.single a b 1)) i) j
    have ht : E.transpose * (Matrix.single a b (1:ℝ)).transpose * M.transpose =
        (M * Matrix.single a b (1:ℝ) * E).transpose := by
      simp only [transpose_mul, Matrix.mul_assoc]
    rw [ht] at hh
    simpa only [Matrix.add_apply, transpose_apply, matrix_unit_sandwich,
      Matrix.zero_apply, mul_comm (M j a)] using hh
  have row (a : Fin s) : M j a = 0 := by
    have hh := entry a j
    have hz : M j a * E b j = 0 := by nlinarith [hh]
    exact (mul_eq_zero.mp hz).resolve_right hbj
  ext i a
  have hh := entry a i
  rw [row a, mul_zero, add_zero] at hh
  exact (mul_eq_zero.mp hh).resolve_right hbj

theorem universal_linear_zero (E : Mat k r) (hE : E ≠ 0) (g : Vec s)
    (h : ∀ X : Mat s k, E.transpose *ᵥ (X.transpose *ᵥ g) = 0) : g = 0 := by
  obtain ⟨b,j,hbj⟩ := matrix_ne_zero_entry E hE
  ext a
  have hh := congrFun (h (Matrix.single a b 1)) j
  have : E b j * g a = 0 := by
    simpa [Matrix.mulVec, dotProduct, Matrix.single, ite_and, eq_comm] using hh
  exact (mul_eq_zero.mp this).resolve_left hbj

theorem symmetric_zero_of_quadratic (B : Mat s s) (hB : B.transpose = B)
    (h : ∀ x : Vec s, dotProduct x (B *ᵥ x) = 0) : B = 0 := by
  have diag (i : Fin s) : B i i = 0 := by
    simpa using h (Pi.single i 1)
  ext i j
  change B i j = 0
  have hh := h (Pi.single i 1 + Pi.single j 1)
  have hsym : B j i = B i j := congrFun (congrFun hB i) j
  simp only [mulVec_add, dotProduct_add, add_dotProduct] at hh
  simp only [mulVec_single_one, single_dotProduct,
    col_apply, one_mul, diag] at hh
  rw [hsym] at hh
  linarith

theorem universal_quadratic_zero (E : Mat k r) (hE : E ≠ 0)
    (B : Mat s s) (hB : B.transpose = B)
    (h : ∀ X : Mat s k,
      E.transpose * X.transpose * B * X * E = 0) : B = 0 := by
  obtain ⟨b,j,hbj⟩ := matrix_ne_zero_entry E hE
  have hv : E *ᵥ Pi.single j 1 ≠ 0 := by
    intro hz
    apply hbj
    simpa using congrFun hz b
  apply symmetric_zero_of_quadratic B hB
  intro z
  obtain ⟨X,hX⟩ := mulVec_surjective_in_matrix (E *ᵥ Pi.single j 1) hv z
  have hh := congrArg (fun A : Mat r r =>
    dotProduct (Pi.single j 1) (A *ᵥ Pi.single j 1)) (h X)
  simp only [← mulVec_mulVec, dotProduct_transpose_mulVec, hX,
    zero_mulVec, dotProduct_zero] at hh
  rw [dotProduct_comm, dotProduct_transpose_mulVec, hX, dotProduct_comm] at hh
  exact hh

end CommodityClassification.FixedAnswer
