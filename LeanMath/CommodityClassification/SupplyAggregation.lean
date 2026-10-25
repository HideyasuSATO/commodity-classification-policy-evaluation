module
public import LeanMath.CommodityClassification.SupplyCurvature
public import Mathlib.Algebra.Order.Star.Real
@[expose] public section
set_option maxHeartbeats 2000000
namespace CommodityClassification.Supply
open Matrix
open scoped BigOperators Topology
variable {n f k : ℕ}

noncomputable def totalInputs (q : Vec n) (A : Mat n f) : Vec f :=
  fun j => ∑ i, q i * A i j
noncomputable def xi (p q : Vec n) : Mat n n := diagonal (fun i => q i/p i)
noncomputable def knownR (w : Vec f) (V : Mat f k) (I : Vec f) : Mat k k :=
  V.transpose * diagonal (fun j => I j/w j) * V
noncomputable def residual (R : Mat k k) (p q : Vec n) (C : Mat n k) : Mat k k :=
  R - C.transpose * xi p q * C
noncomputable def substitution (σ : ℝ) (R : Mat k k) (p q : Vec n) (C : Mat n k) : Mat k k :=
  σ • residual R p q C

theorem totalInputs_pos (q : Vec n) (A : Mat n f) (hn : 0<n)
    (hq : ∀ i,0<q i) (hA : InputCoordinates.Positive A) (j : Fin f) :
    0 < totalInputs q A j := by
  exact Finset.sum_pos (fun i _ => mul_pos (hq i) (hA i j)) ⟨⟨0,hn⟩,Finset.mem_univ _⟩

theorem goods_nonempty_of_total_pos (q : Vec n) (A : Mat n (k+1))
    (hI : ∀ j,0<totalInputs q A j) : 0<n := by
  by_contra hn
  have hn0 : n=0 := Nat.eq_zero_of_not_pos hn
  subst n
  have hh := hI 0
  simp [totalInputs] at hh

theorem knownR_posDef (w : Vec f) (V : Mat f k) (I : Vec f)
    (hw : ∀ j,0<w j) (hI : ∀ j,0<I j) (hV : Function.Injective (fun z => V *ᵥ z)) :
    (knownR w V I).PosDef := by
  have hd := Matrix.PosDef.diagonal (fun j => div_pos (hI j) (hw j))
  simpa [knownR] using hd.conjTranspose_mul_mul_same hV

theorem aggregate_curvature (A : Mat n f) (p q : Vec n) (w : Vec f) :
    (∑ i, q i • curvature (A i) w (p i)) =
      diagonal (fun j => totalInputs q A j/w j) - A.transpose * xi p q * A := by
  ext j l
  simp only [curvature, Matrix.sum_apply, smul_eq_mul,
    Matrix.sub_apply, Matrix.smul_apply, vecMulVec, Matrix.of_apply,
    Matrix.mul_apply, Matrix.transpose_apply, xi, Matrix.diagonal_apply]
  simp only [mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ,
    ite_true]
  by_cases hjl : j=l
  · subst l
    simp only [ite_true]
    simp only [mul_sub, Finset.sum_sub_distrib, totalInputs, div_eq_mul_inv, Finset.sum_mul]
    congr 1
    · apply Finset.sum_congr rfl; intro i hi; ring
    · apply Finset.sum_congr rfl; intro i hi; ring
  · simp only [hjl, ite_false, zero_sub, mul_neg, Finset.sum_neg_distrib]
    congr 1
    apply Finset.sum_congr rfl; intro i hi; ring

theorem residual_eq_sum (A : Mat n f) (p q : Vec n) (w : Vec f) (V : Mat f k) :
    residual (knownR w V (totalInputs q A)) p q (A*V) =
      ∑ i, q i • (V.transpose * curvature (A i) w (p i) * V) := by
  have hh := congrArg (fun B : Mat f f => V.transpose * B * V) (aggregate_curvature A p q w)
  simpa only [Matrix.mul_sum, Matrix.sum_mul, Matrix.mul_smul, Matrix.smul_mul,
    Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_assoc, Matrix.transpose_mul,
    residual, knownR] using hh.symm

theorem residual_posDef (e : InputCoordinates.Frame k) (A : Mat n (k+1)) (p q : Vec n)
    (hn : 0<n) (hp : ∀ i,0<p i) (hq : ∀ i,0<q i) (hw : ∀ j,0<e.w j)
    (hA : InputCoordinates.Positive A) (hc : A *ᵥ e.w = p) :
    (residual (knownR e.w e.V (totalInputs q A)) p q (A*e.V)).PosDef := by
  rw [residual_eq_sum]
  apply Matrix.posDef_sum ⟨⟨0,hn⟩,Finset.mem_univ _⟩
  intro i hi
  exact (curvature_relative_posDef e (CESCost.ofInputs A p e.w hA hp hw hc i) rfl).smul (hq i)

theorem substitution_posDef (σ : ℝ) (hσ : 0<σ) (R : Mat k k) (p q : Vec n) (C : Mat n k)
    (hS : (residual R p q C).PosDef) : (substitution σ R p q C).PosDef := hS.smul hσ

theorem substitution_posSemidef (σ : ℝ) (hσ : 0≤σ) (R : Mat k k) (p q : Vec n) (C : Mat n k)
    (hS : (residual R p q C).PosSemidef) : (substitution σ R p q C).PosSemidef := hS.smul hσ

theorem aggregate_negative_hessian (A : Mat n f) (p q : Vec n) (w : Vec f) (V : Mat f k)
    (hA : InputCoordinates.Positive A) (hp : ∀ i,0<p i) (hw : ∀ j,0<w j)
    (hc : A *ᵥ w = p) (σ : ℝ) :
    -(∑ i, q i • (V.transpose * (CESCost.ofInputs A p w hA hp hw hc i).hessian σ * V)) =
      substitution σ (knownR w V (totalInputs q A)) p q (A*V) := by
  rw [substitution, residual_eq_sum, Finset.smul_sum, ← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  have hh := negative_cost_hessian (CESCost.ofInputs A p w hA hp hw hc i) σ
  rw [← smul_neg, ← Matrix.neg_mul, ← Matrix.mul_neg, hh,
    Matrix.mul_smul, Matrix.smul_mul, smul_comm]
  rfl

theorem aggregate_actual_hessian (A : Mat n f) (p q : Vec n) (w : Vec f) (V : Mat f k)
    (hA : InputCoordinates.Positive A) (hp : ∀ i,0<p i) (hw : ∀ j,0<w j)
    (hc : A *ᵥ w = p) (σ : ℝ) :
    -(∑ i, q i • (V.transpose *
        Matrix.of (fun j l => CESCost.pricePartial
          (CESCost.pricePartial ((CESCost.ofInputs A p w hA hp hw hc i).cost σ) j) l w) * V)) =
      substitution σ (knownR w V (totalInputs q A)) p q (A*V) := by
  have heq (i : Fin n) :
      Matrix.of (fun j l => CESCost.pricePartial
        (CESCost.pricePartial ((CESCost.ofInputs A p w hA hp hw hc i).cost σ) j) l w) =
        (CESCost.ofInputs A p w hA hp hw hc i).hessian σ := by
    ext j l
    exact (CESCost.ofInputs A p w hA hp hw hc i).cost_mixed_derivative σ j l
  simp_rw [heq]
  exact aggregate_negative_hessian A p q w V hA hp hw hc σ

end CommodityClassification.Supply
