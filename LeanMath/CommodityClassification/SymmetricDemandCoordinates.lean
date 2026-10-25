module

public import LeanMath.CommodityClassification.DemandUpdatedFamily
public import Mathlib.Topology.Algebra.MvPolynomial

/-! Genuine independent real coordinates for symmetric demand matrices. -/
@[expose] public section
noncomputable section
namespace CommodityClassification.Genericity
open Matrix FixedAnswer
variable {n : ℕ}

local instance (a b : ℕ) : NormedAddCommGroup (Mat a b) :=
  inferInstanceAs (NormedAddCommGroup (Fin a → Fin b → ℝ))
local instance (a b : ℕ) : NormedSpace ℝ (Mat a b) :=
  inferInstanceAs (NormedSpace ℝ (Fin a → Fin b → ℝ))

abbrev SymmetricEntry (n : ℕ) := {ij : Fin n × Fin n // ij.1 ≤ ij.2}

def symmetricFill (x : SymmetricEntry n → ℝ) : Mat n n :=
  fun i j => if h : i≤j then x ⟨(i,j),h⟩ else x ⟨(j,i),le_of_not_ge h⟩

theorem symmetricFill_transpose (x : SymmetricEntry n → ℝ) :
    (symmetricFill x).transpose=symmetricFill x := by
  ext i j
  simp only [transpose_apply,symmetricFill]
  split_ifs with hji hij hij
  · have he : i=j := le_antisymm hij hji
    subst j
    rfl
  · rfl
  · rfl
  · exact False.elim (hij (le_of_not_ge hji))

def symmetricCoordinates : SymmetricDemand n ≃ₗ[ℝ] (SymmetricEntry n → ℝ) where
  toFun D := fun a => D.val a.val.1 a.val.2
  invFun x := ⟨symmetricFill x,symmetricFill_transpose x⟩
  left_inv D := by
    apply Subtype.ext
    ext i j
    simp only [symmetricFill]
    split_ifs with h
    · rfl
    · exact congrFun (congrFun D.property i) j
  right_inv x := by
    funext a
    simp [symmetricFill,a.property]
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem symmetricCoordinates_continuous : Continuous (symmetricCoordinates (n:=n)) :=
  symmetricCoordinates.toLinearMap.continuous_of_finiteDimensional

theorem symmetricCoordinates_inverse_continuous : Continuous (symmetricCoordinates (n:=n)).symm :=
  symmetricCoordinates.symm.toLinearMap.continuous_of_finiteDimensional

def symbolicDemand (n : ℕ) : Matrix (Fin n) (Fin n) (MvPolynomial (SymmetricEntry n) ℝ) :=
  fun i j => if h : i≤j then MvPolynomial.X ⟨(i,j),h⟩
    else MvPolynomial.X ⟨(j,i),le_of_not_ge h⟩

theorem symbolicDemand_evaluated (D : SymmetricDemand n) :
    (symbolicDemand n).map (MvPolynomial.eval (symmetricCoordinates D))=D.val := by
  ext i j
  simp only [Matrix.map_apply,symbolicDemand]
  split_ifs with h
  · rw [MvPolynomial.eval_X]
    rfl
  · rw [MvPolynomial.eval_X]
    change D.val j i=D.val i j
    exact congrFun (congrFun D.property i) j

theorem symmetric_polynomial_continuous (P : MvPolynomial (SymmetricEntry n) ℝ) :
    Continuous (fun D : SymmetricDemand n => MvPolynomial.eval (symmetricCoordinates D) P) :=
  P.continuous_eval.comp symmetricCoordinates_continuous

theorem symmetric_polynomial_zero_closed (P : MvPolynomial (SymmetricEntry n) ℝ) :
    IsClosed {D : SymmetricDemand n | MvPolynomial.eval (symmetricCoordinates D) P=0} :=
  isClosed_eq (symmetric_polynomial_continuous P) continuous_const

end CommodityClassification.Genericity
