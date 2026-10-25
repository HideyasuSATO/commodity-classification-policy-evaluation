module

public import LeanMath.CommodityClassification.FixedAnswer
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Analysis.Convex.Basic
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.FunProp

/-! GE.COORDINATES. Real finite dimensions, f=k+1; the economic application has k>0.
No welfare, equilibrium, or positive-definiteness assertion is made here. -/
@[expose] public section
namespace CommodityClassification.InputCoordinates
open Matrix
open scoped BigOperators
abbrev Mat (n m : ℕ) := Matrix (Fin n) (Fin m) ℝ
abbrev Vec (n : ℕ) := Fin n → ℝ

structure Frame (k : ℕ) where
  w : Vec (k+1)
  a0 : Vec (k+1)
  V : Mat (k+1) k
  normalized : dotProduct a0 w = 1
  annihilates : V.transpose *ᵥ a0 = 0
  independent : Function.Injective (fun z => V *ᵥ z)

variable {n k : ℕ}

def Frame.B (e : Frame k) : Mat (k+1) (k+1) :=
  fun i => Fin.cons (e.w i) (e.V i)

theorem Frame.B_mulVec (e : Frame k) (x : Vec (k+1)) :
    e.B *ᵥ x = x 0 • e.w + e.V *ᵥ (fun j => x j.succ) := by
  ext i
  simp [Matrix.mulVec, dotProduct, Frame.B, Fin.sum_univ_succ, mul_comm]

theorem Frame.a0_dot_V (e : Frame k) (z : Vec k) :
    dotProduct e.a0 (e.V *ᵥ z) = 0 := by
  rw [dotProduct_mulVec]
  have hv : e.a0 ᵥ* e.V = 0 := by
    simpa only [mulVec_transpose] using e.annihilates
  rw [hv, zero_dotProduct]

theorem Frame.B_isUnit (e : Frame k) : IsUnit e.B := by
  apply Matrix.mulVec_injective_iff_isUnit.mp
  intro x y hxy
  rw [e.B_mulVec, e.B_mulVec] at hxy
  have hzero : x 0 = y 0 := by
    have h := congrArg (fun v => dotProduct e.a0 v) hxy
    simpa [dotProduct_add, dotProduct_smul, e.normalized, e.a0_dot_V] using h
  have htail : (fun j : Fin k => x j.succ) = (fun j => y j.succ) := by
    apply e.independent
    rw [hzero] at hxy
    exact add_left_cancel hxy
  ext j
  refine Fin.cases hzero (fun i => congrFun htail i) j

theorem Frame.spans_kernel (e : Frame k) (v : Vec (k+1)) :
    dotProduct e.a0 v = 0 ↔ ∃ z : Vec k, e.V *ᵥ z = v := by
  constructor
  · intro hv
    obtain ⟨x, hx⟩ := (Matrix.mulVec_surjective_iff_isUnit.mpr e.B_isUnit) v
    have hzero : x 0 = 0 := by
      have hh := congrArg (fun u => dotProduct e.a0 u) hx
      simpa [e.B_mulVec, dotProduct_add, dotProduct_smul, e.normalized, e.a0_dot_V, hv] using hh
    refine ⟨fun j => x j.succ, ?_⟩
    simpa [e.B_mulVec, hzero] using hx
  · rintro ⟨z, rfl⟩
    exact e.a0_dot_V z

def augment (p : Vec n) (C : Mat n k) : Mat n (k+1) :=
  fun i => Fin.cons (p i) (C i)

theorem Frame.mul_B (e : Frame k) (A : Mat n (k+1)) :
    A * e.B = augment (A *ᵥ e.w) (A * e.V) := by
  ext i j
  refine Fin.cases ?_ (fun t => ?_) j
  · simp [Matrix.mul_apply, Matrix.mulVec, dotProduct, Frame.B, augment]
  · simp [Matrix.mul_apply, Frame.B, augment]

noncomputable def Frame.reconstruct (e : Frame k) (p : Vec n) (C : Mat n k) :
    Mat n (k+1) := augment p C * e.B⁻¹

theorem Frame.reconstruct_mul_B (e : Frame k) (p : Vec n) (C : Mat n k) :
    e.reconstruct p C * e.B = augment p C := by
  rw [Frame.reconstruct, Matrix.mul_assoc,
    Matrix.nonsing_inv_mul _ (Matrix.isUnit_iff_isUnit_det _ |>.mp e.B_isUnit),
    Matrix.mul_one]

theorem Frame.reconstruct_cost (e : Frame k) (p : Vec n) (C : Mat n k) :
    e.reconstruct p C *ᵥ e.w = p := by
  have h := e.reconstruct_mul_B p C
  rw [e.mul_B] at h
  exact funext fun i => congrFun (congrFun h i) 0

theorem Frame.reconstruct_exposure (e : Frame k) (p : Vec n) (C : Mat n k) :
    e.reconstruct p C * e.V = C := by
  have h := e.reconstruct_mul_B p C
  rw [e.mul_B] at h
  exact funext fun i => funext fun j => congrFun (congrFun h i) j.succ

theorem Frame.reconstruct_original (e : Frame k) (A : Mat n (k+1)) :
    e.reconstruct (A *ᵥ e.w) (A * e.V) = A := by
  rw [Frame.reconstruct, ← e.mul_B, Matrix.mul_assoc,
    Matrix.mul_nonsing_inv _ (Matrix.isUnit_iff_isUnit_det _ |>.mp e.B_isUnit),
    Matrix.mul_one]

theorem Frame.coordinates_unique (e : Frame k) (p : Vec n) (C : Mat n k) :
    ∃! A : Mat n (k+1), A *ᵥ e.w = p ∧ A * e.V = C := by
  refine ⟨e.reconstruct p C, ⟨e.reconstruct_cost p C, e.reconstruct_exposure p C⟩, ?_⟩
  intro A h
  simpa only [h.1, h.2] using (e.reconstruct_original A).symm

def Positive {s t : ℕ} (A : Mat s t) : Prop := ∀ i j, 0 < A i j
def Frame.PositiveDomain (e : Frame k) (p : Vec n) : Set (Mat n k) :=
  {C | Positive (e.reconstruct p C)}

theorem Frame.reconstruct_continuous (e : Frame k) (p : Vec n) :
    Continuous (e.reconstruct p) := by
  unfold Frame.reconstruct
  apply Continuous.matrix_mul ?_ continuous_const
  apply continuous_matrix; intro i j
  refine Fin.cases ?_ (fun b => ?_) j
  · change Continuous (fun _ : Mat n k => p i)
    exact continuous_const
  · change Continuous (fun C : Mat n k => C i b)
    fun_prop

theorem Frame.positiveDomain_open (e : Frame k) (p : Vec n) :
    IsOpen (e.PositiveDomain p) := by
  change IsOpen {C | ∀ i j, 0 < e.reconstruct p C i j}
  simp only [Set.ofPred_forall]
  apply isOpen_iInter_of_finite; intro i
  apply isOpen_iInter_of_finite; intro j
  exact isOpen_lt continuous_const
    ((continuous_apply j).comp ((continuous_apply i).comp (e.reconstruct_continuous p)))

theorem Frame.reconstruct_combination (e : Frame k) (p : Vec n)
    (C E : Mat n k) (a b : ℝ) (hab : a+b=1) :
    e.reconstruct p (a • C + b • E) = a • e.reconstruct p C + b • e.reconstruct p E := by
  unfold Frame.reconstruct
  have h : augment p (a • C + b • E) = a • augment p C + b • augment p E := by
    ext i j
    refine Fin.cases ?_ (fun t => ?_) j
    · change p i = a * p i + b * p i
      rw [← add_mul, hab, one_mul]
    · rfl
  rw [h, Matrix.add_mul, Matrix.smul_mul, Matrix.smul_mul]

theorem Frame.positiveDomain_convex (e : Frame k) (p : Vec n) :
    Convex ℝ (e.PositiveDomain p) := by
  intro C hC E hE a b ha hb hab
  change Positive (e.reconstruct p (a • C + b • E))
  rw [e.reconstruct_combination p C E a b hab]
  intro i j
  change 0 < a * e.reconstruct p C i j + b * e.reconstruct p E i j
  have hc := hC i j
  have he := hE i j
  by_cases hapos : 0 < a
  · exact add_pos_of_pos_of_nonneg (mul_pos hapos hc) (mul_nonneg hb he.le)
  · have hbpos : 0 < b := by linarith
    exact add_pos_of_nonneg_of_pos (mul_nonneg ha hc.le) (mul_pos hbpos he)

theorem Frame.exposure_continuous (e : Frame k) :
    Continuous (fun A : Mat n (k+1) => A * e.V) :=
  continuous_id.matrix_mul continuous_const

/-- Positive prices and a positive numeraire technology give a positive cost-feasible input.
The additional parent report must still be realizable. -/
theorem Frame.positiveDomain_nonempty (e : Frame k) (p : Vec n)
    (hp : ∀ i, 0 < p i) (ha : ∀ j, 0 < e.a0 j) : (e.PositiveDomain p).Nonempty := by
  let A : Mat n (k+1) := fun i j => p i * e.a0 j
  have hc : A *ᵥ e.w = p := by
    ext i
    change (∑ j, (p i * e.a0 j) * e.w j) = p i
    simp_rw [mul_assoc]
    rw [← Finset.mul_sum]
    change p i * dotProduct e.a0 e.w = p i
    rw [e.normalized, mul_one]
  refine ⟨A*e.V, ?_⟩
  change Positive (e.reconstruct p (A*e.V))
  rw [← hc, e.reconstruct_original]
  exact fun i j => mul_pos (hp i) (ha j)

end CommodityClassification.InputCoordinates
