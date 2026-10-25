module

public import LeanMath.CommodityClassification.RobustVariationalComparison
public import Mathlib.Algebra.QuadraticDiscriminant

/-! Cauchy--Schwarz for semidefinite welfare matrices, including zero directions. -/
@[expose] public section
noncomputable section
set_option maxHeartbeats 1800000
namespace CommodityClassification.Robust
open Matrix Equilibrium
variable {n : ℕ}

theorem semidefinite_cauchy_sq (W : Mat n n) (hW : W.PosSemidef) (x y : Vec n) :
    (dotProduct x (W *ᵥ y))^2≤dotProduct x (W *ᵥ x)*dotProduct y (W *ᵥ y) := by
  have hn : ∀t : ℝ,0≤dotProduct y (W *ᵥ y)*(t*t)+
      (2*dotProduct x (W *ᵥ y))*t+dotProduct x (W *ᵥ x) := by
    intro t
    have hh := hW.dotProduct_mulVec_nonneg (x+t • y)
    simp only [star_trivial,Matrix.mulVec_add,Matrix.mulVec_smul,add_dotProduct,
      dotProduct_add,smul_dotProduct,dotProduct_smul,smul_eq_mul] at hh
    have hs : dotProduct y (W *ᵥ x)=dotProduct x (W *ᵥ y) :=
      hW.isHermitian.isSymm.dotProduct_mulVec_comm
    rw [hs] at hh
    nlinarith
  have hd := discrim_le_zero hn
  unfold discrim at hd
  nlinarith

theorem semidefinite_cross_bound (W : Mat n n) (hW : W.PosSemidef)
    (x y : Vec n) (A B : ℝ) (hA : 0≤A) (hB : 0≤B)
    (hx : dotProduct x (W *ᵥ x)≤A^2) (hy : dotProduct y (W *ᵥ y)≤B^2) :
    |dotProduct x (W *ᵥ y)|≤A*B := by
  have hs := semidefinite_cauchy_sq W hW x y
  have hx0 := hW.dotProduct_mulVec_nonneg x
  have hy0 := hW.dotProduct_mulVec_nonneg y
  simp only [star_trivial] at hx0 hy0
  have hp := mul_le_mul hx hy hy0 (sq_nonneg A)
  have hab := mul_nonneg hA hB
  have habs := abs_nonneg (dotProduct x (W *ᵥ y))
  have he := sq_abs (dotProduct x (W *ᵥ y))
  nlinarith

theorem semidefinite_add_expansion (W : Mat n n) (hW : W.PosSemidef) (x y : Vec n) :
    dotProduct (x+y) (W *ᵥ (x+y))=
      dotProduct x (W *ᵥ x)+2*dotProduct x (W *ᵥ y)+dotProduct y (W *ᵥ y) := by
  simp only [Matrix.mulVec_add,add_dotProduct,dotProduct_add]
  have hs : dotProduct y (W *ᵥ x)=dotProduct x (W *ᵥ y) :=
    hW.isHermitian.isSymm.dotProduct_mulVec_comm
  rw [hs]
  ring

theorem semidefinite_quadratic_subtraction (W : Mat n n) (hW : W.PosSemidef) (b b0 : Vec n) :
    dotProduct b (W *ᵥ b)-dotProduct b0 (W *ᵥ b0)=
      2*dotProduct (b-b0) (W *ᵥ b0)+dotProduct (b-b0) (W *ᵥ (b-b0)) := by
  have hh := semidefinite_add_expansion W hW (b-b0) b0
  rw [sub_add_cancel] at hh
  linarith

end CommodityClassification.Robust
