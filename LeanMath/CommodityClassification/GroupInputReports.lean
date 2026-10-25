module

public import LeanMath.CommodityClassification.InputCoordinates
public import Mathlib.Tactic.FieldSimp

/-! GE.REPORT_MEAN: physical reports, refinement and positive group means.
The input candidates satisfy benchmark costs; no equilibrium derivative is assumed. -/
@[expose] public section
namespace CommodityClassification.InputCoordinates
open Matrix
open scoped BigOperators
variable {n k g h t : ℕ}

structure Partition (n g : ℕ) where
  group : Fin n → Fin g
  onto : Function.Surjective group

def Partition.cell (P : Partition n g) (a : Fin g) : Finset (Fin n) :=
  Finset.univ.filter (fun i => P.group i = a)

@[simp] theorem Partition.mem_cell (P : Partition n g) (a : Fin g) (i : Fin n) :
    i ∈ P.cell a ↔ P.group i = a := by simp [Partition.cell]

theorem Partition.cell_nonempty (P : Partition n g) (a : Fin g) : (P.cell a).Nonempty := by
  obtain ⟨i, hi⟩ := P.onto a
  exact ⟨i, (P.mem_cell a i).mpr hi⟩

def Partition.Q (P : Partition n g) (q : Vec n) : Mat n g :=
  fun i a => if P.group i = a then q i else 0

def Partition.report (P : Partition n g) (q : Vec n) (A : Mat n t) : Mat g t :=
  (P.Q q).transpose * A

def Partition.sales (P : Partition n g) (p q : Vec n) : Vec g :=
  (P.Q q).transpose *ᵥ p

theorem Partition.report_apply (P : Partition n g) (q : Vec n) (A : Mat n t)
    (a : Fin g) (j : Fin t) :
    P.report q A a j = ∑ i ∈ P.cell a, q i * A i j := by
  simp [Partition.report, Partition.Q, Partition.cell, Matrix.mul_apply, Finset.sum_filter,
    ite_mul]

theorem Partition.sales_apply (P : Partition n g) (p q : Vec n) (a : Fin g) :
    P.sales p q a = ∑ i ∈ P.cell a, q i * p i := by
  simp [Partition.sales, Partition.Q, Partition.cell, Matrix.mulVec, dotProduct,
    Finset.sum_filter, ite_mul]

theorem Partition.report_mul (P : Partition n g) (q : Vec n)
    (A : Mat n t) (B : Mat t k) : P.report q (A*B) = P.report q A * B := by
  exact (Matrix.mul_assoc _ _ _).symm

theorem Partition.report_cost (P : Partition n g) (e : Frame k) (p q : Vec n)
    (A : Mat n (k+1)) (hA : A *ᵥ e.w = p) :
    P.report q A *ᵥ e.w = P.sales p q := by
  simp only [Partition.report, Partition.sales, ← Matrix.mulVec_mulVec, hA]

theorem Partition.report_equiv (P : Partition n g) (e : Frame k) (p q : Vec n)
    (A E : Mat n (k+1)) (hA : A *ᵥ e.w = p) (hE : E *ᵥ e.w = p) :
    P.report q A = P.report q E ↔ P.report q (A*e.V) = P.report q (E*e.V) := by
  constructor
  · intro hh
    rw [P.report_mul, P.report_mul, hh]
  · intro hh
    have h1 := e.reconstruct_original (P.report q A)
    have h2 := e.reconstruct_original (P.report q E)
    rw [P.report_cost e p q A hA, ← P.report_mul] at h1
    rw [P.report_cost e p q E hE, ← P.report_mul] at h2
    rw [hh] at h1
    exact h1.symm.trans h2

/-- An explicit inverse of the coordinate report, including the known group sales. -/
theorem Partition.report_reconstruct (P : Partition n g) (e : Frame k)
    (p q : Vec n) (C : Mat n k) :
    P.report q (e.reconstruct p C) = e.reconstruct (P.sales p q) (P.report q C) := by
  calc
    _ = e.reconstruct (P.report q (e.reconstruct p C) *ᵥ e.w)
        (P.report q (e.reconstruct p C) * e.V) :=
      (e.reconstruct_original _).symm
    _ = _ := by
      rw [P.report_cost e p q _ (e.reconstruct_cost p C), ← P.report_mul,
        e.reconstruct_exposure]

theorem Partition.sales_pos (P : Partition n g) (p q : Vec n)
    (hp : ∀ i, 0 < p i) (hq : ∀ i, 0 < q i) (a : Fin g) : 0 < P.sales p q a := by
  rw [P.sales_apply]
  exact Finset.sum_pos (fun i _ => mul_pos (hq i) (hp i)) (P.cell_nonempty a)

theorem Partition.report_positive (P : Partition n g) (q : Vec n)
    (hq : ∀ i, 0 < q i) (A : Mat n t) (hA : Positive A) : Positive (P.report q A) := by
  intro a j
  rw [P.report_apply]
  exact Finset.sum_pos (fun i _ => mul_pos (hq i) (hA i j)) (P.cell_nonempty a)

noncomputable def Partition.mean (P : Partition n g) (p q : Vec n) (A : Mat n t) : Mat n t :=
  fun i j => p i / P.sales p q (P.group i) * P.report q A (P.group i) j

theorem Partition.mean_positive (P : Partition n g) (p q : Vec n)
    (hp : ∀ i, 0 < p i) (hq : ∀ i, 0 < q i) (A : Mat n t) (hA : Positive A) :
    Positive (P.mean p q A) := by
  intro i j
  exact mul_pos (div_pos (hp i) (P.sales_pos p q hp hq _))
    (P.report_positive q hq A hA _ j)

theorem Partition.mean_report (P : Partition n g) (p q : Vec n)
    (hp : ∀ i, 0 < p i) (hq : ∀ i, 0 < q i) (A : Mat n t) :
    P.report q (P.mean p q A) = P.report q A := by
  ext a j
  rw [P.report_apply]
  calc
    (∑ i ∈ P.cell a, q i * P.mean p q A i j) =
        (∑ i ∈ P.cell a, q i * p i) * (P.report q A a j / P.sales p q a) := by
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro i hi
      simp only [Partition.mean, (P.mem_cell a i).mp hi]
      ring
    _ = P.report q A a j := by
      rw [← P.sales_apply]
      field_simp [(P.sales_pos p q hp hq a).ne']

theorem Partition.mean_cost (P : Partition n g) (e : Frame k) (p q : Vec n)
    (hp : ∀ i, 0 < p i) (hq : ∀ i, 0 < q i)
    (A : Mat n (k+1)) (hA : A *ᵥ e.w = p) : P.mean p q A *ᵥ e.w = p := by
  ext i
  change (∑ j, (p i / P.sales p q (P.group i) * P.report q A (P.group i) j) * e.w j) = p i
  simp_rw [mul_assoc]
  rw [← Finset.mul_sum]
  have hc := congrFun (P.report_cost e p q A hA) (P.group i)
  change (∑ j, P.report q A (P.group i) j * e.w j) = _ at hc
  rw [hc]
  exact div_mul_cancel₀ _ (P.sales_pos p q hp hq _).ne'

theorem Partition.mean_exposure (P : Partition n g) (e : Frame k) (p q : Vec n)
    (A : Mat n (k+1)) :
    P.mean p q A * e.V = P.mean p q (A * e.V) := by
  ext i j
  change (∑ a, (p i / P.sales p q (P.group i) * P.report q A (P.group i) a) * e.V a j) = _
  simp_rw [mul_assoc]
  rw [← Finset.mul_sum]
  have hh := congrFun (congrFun (P.report_mul q A e.V) (P.group i)) j
  change P.report q (A * e.V) (P.group i) j = (∑ a, P.report q A (P.group i) a * e.V a j) at hh
  rw [← hh]
  rfl

theorem Partition.reconstruct_mean (P : Partition n g) (e : Frame k) (p q : Vec n)
    (hp : ∀ i, 0 < p i) (hq : ∀ i, 0 < q i) (C : Mat n k) :
    e.reconstruct p (P.mean p q C) = P.mean p q (e.reconstruct p C) := by
  have hh := e.reconstruct_original (P.mean p q (e.reconstruct p C))
  rw [P.mean_cost e p q hp hq _ (e.reconstruct_cost p C),
    P.mean_exposure, e.reconstruct_exposure] at hh
  exact hh

/-- A refinement has a parent label for each fine cell, with compatible memberships. -/
structure Refinement (P : Partition n g) (P0 : Partition n h) where
  parent : Fin g → Fin h
  compatible : ∀ i, P0.group i = parent (P.group i)

def Refinement.incidence {P : Partition n g} {P0 : Partition n h}
    (R : Refinement P P0) : Mat g h := fun a b => if R.parent a = b then 1 else 0

theorem Refinement.Q_factor {P : Partition n g} {P0 : Partition n h}
    (R : Refinement P P0) (q : Vec n) : P0.Q q = P.Q q * R.incidence := by
  ext i b
  simp only [Partition.Q, Matrix.mul_apply, Refinement.incidence, R.compatible]
  rw [Finset.sum_eq_single (P.group i)]
  · simp
  · intro a _ ha
    simp [Ne.symm ha]
  · simp

theorem Refinement.report_factor {P : Partition n g} {P0 : Partition n h}
    (R : Refinement P P0) (q : Vec n) (A : Mat n t) :
    P0.report q A = R.incidence.transpose * P.report q A := by
  simp only [Partition.report, R.Q_factor, Matrix.transpose_mul, Matrix.mul_assoc]

theorem Refinement.report_preserved {P : Partition n g} {P0 : Partition n h}
    (R : Refinement P P0) (q : Vec n) (A E : Mat n t)
    (he : P.report q A = P.report q E) : P0.report q A = P0.report q E := by
  rw [R.report_factor, R.report_factor, he]

theorem Refinement.mean_parent {P : Partition n g} {P0 : Partition n h}
    (R : Refinement P P0) (p q : Vec n) (hp : ∀ i, 0 < p i) (hq : ∀ i, 0 < q i)
    (A : Mat n t) : P0.report q (P.mean p q A) = P0.report q A :=
  R.report_preserved q _ _ (P.mean_report p q hp hq A)

end CommodityClassification.InputCoordinates
