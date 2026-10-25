module

public import LeanMath.CommodityClassification.GroupInputReports
public import Mathlib.LinearAlgebra.FiniteDimensional.Basic

/-! A finite basis of the unobserved directions and exact affine fibers.
`exists_hiddenBasis` constructs the hidden-coordinate basis. -/
@[expose] public section
namespace CommodityClassification.InputCoordinates
open Matrix
open scoped BigOperators
variable {n k g r : ℕ}

structure HiddenBasis (Q : Mat n g) (r : ℕ) where
  N : Mat n r
  independent : Function.Injective (fun z => N *ᵥ z)
  spans : ∀ x : Vec n, Q.transpose *ᵥ x = 0 ↔ ∃ z : Vec r, N *ᵥ z = x

theorem exists_hiddenBasis (Q : Mat n g) : ∃ r, Nonempty (HiddenBasis Q r) := by
  classical
  let S := LinearMap.ker Q.transpose.mulVecLin
  let b := Module.finBasis ℝ S
  let N : Mat n (Module.finrank ℝ S) := fun i j => (b j).val i
  have hN (z : Vec (Module.finrank ℝ S)) :
      N *ᵥ z = (b.equivFun.symm z).val := by
    ext i
    simp [N, Matrix.mulVec, dotProduct, Module.Basis.equivFun_symm_apply, mul_comm]
  refine ⟨Module.finrank ℝ S, ⟨{N := N, independent := ?_, spans := ?_}⟩⟩
  · intro z v h
    apply b.equivFun.symm.injective
    apply Subtype.ext
    simpa only [← hN] using h
  · intro x
    constructor
    · intro hx
      let u : S := ⟨x, hx⟩
      refine ⟨b.equivFun u, ?_⟩
      rw [hN, b.equivFun.symm_apply_apply]
    · rintro ⟨z, rfl⟩
      rw [hN]
      exact (b.equivFun.symm z).property

theorem HiddenBasis.annihilates {Q : Mat n g} (H : HiddenBasis Q r) :
    Q.transpose * H.N = 0 := by
  ext i j
  have hh := (H.spans (H.N *ᵥ Pi.single j 1)).mpr ⟨Pi.single j 1, rfl⟩
  simp only [Matrix.mulVec_single_one] at hh
  exact congrFun hh i

theorem HiddenBasis.mul_injective {Q : Mat n g} (H : HiddenBasis Q r) :
    Function.Injective (fun Z : Mat r k => H.N * Z) := by
  intro Z W h
  have hh (j : Fin k) : (fun a => Z a j) = (fun a => W a j) := by
    apply H.independent
    exact funext fun i => congrFun (congrFun h i) j
  exact funext fun a => funext fun j => congrFun (hh j) a

theorem HiddenBasis.report_point {Q : Mat n g} (H : HiddenBasis Q r)
    (C0 : Mat n k) (Z : Mat r k) :
    Q.transpose * (C0 + H.N * Z) = Q.transpose * C0 := by
  rw [Matrix.mul_add, ← Matrix.mul_assoc, H.annihilates, Matrix.zero_mul, add_zero]

theorem HiddenBasis.fiber_iff {Q : Mat n g} (H : HiddenBasis Q r)
    (C0 C : Mat n k) :
    Q.transpose * C = Q.transpose * C0 ↔ ∃! Z : Mat r k, C = C0 + H.N * Z := by
  classical
  constructor
  · intro h
    have hc (j : Fin k) : Q.transpose *ᵥ (fun i => (C-C0) i j) = 0 := by
      have hz : Q.transpose * (C-C0) = 0 := by rw [Matrix.mul_sub, h, sub_self]
      exact funext fun i => congrFun (congrFun hz i) j
    choose z hz using fun j => (H.spans _).mp (hc j)
    let Z : Mat r k := fun a j => z j a
    have hZ : H.N * Z = C-C0 := by
      exact funext fun i => funext fun j => congrFun (hz j) i
    refine ⟨Z, ?_, ?_⟩
    · change C = C0 + H.N * Z
      rw [hZ]
      abel
    · intro W hW
      apply H.mul_injective
      change H.N * W = H.N * Z
      rw [hZ]
      exact eq_sub_iff_add_eq.mpr (by simpa only [add_comm] using hW.symm)
  · rintro ⟨Z, hZ, _⟩
    rw [hZ, H.report_point]

theorem HiddenBasis.fiber_exists_iff {Q : Mat n g} (H : HiddenBasis Q r)
    (C0 C : Mat n k) :
    Q.transpose * C = Q.transpose * C0 ↔ ∃ Z : Mat r k, C = C0 + H.N * Z := by
  constructor
  · intro hh
    exact ((H.fiber_iff C0 C).mp hh).exists
  · rintro ⟨Z, rfl⟩
    exact H.report_point C0 Z

theorem HiddenBasis.zeroDim_point {Q : Mat n g} (H : HiddenBasis Q 0)
    (C0 : Mat n k) (Z : Mat 0 k) : C0 + H.N * Z = C0 := by
  have hh : H.N * Z = 0 := by ext i j; simp [Matrix.mul_apply]
  rw [hh, add_zero]

def Partition.singleton (n : ℕ) : Partition n n := ⟨id, Function.surjective_id⟩

theorem Partition.singleton_kernel (q : Vec n) (hq : ∀ i, 0 < q i) (x : Vec n) :
    ((Partition.singleton n).Q q).transpose *ᵥ x = 0 ↔ x = 0 := by
  constructor
  · intro hh
    ext i
    have hi := congrFun hh i
    have hi' : q i * x i = 0 := by
      simpa [Partition.singleton, Partition.Q, Matrix.mulVec, dotProduct, eq_comm] using hi
    exact (mul_eq_zero.mp hi').resolve_left (hq i).ne'
  · rintro rfl
    exact Matrix.mulVec_zero _

theorem Partition.singleton_hiddenBasis (q : Vec n) (hq : ∀ i, 0 < q i) :
    Nonempty (HiddenBasis ((Partition.singleton n).Q q) 0) := by
  refine ⟨{N := 0, independent := ?_, spans := ?_}⟩
  · intro z v _
    exact Subsingleton.elim _ _
  · intro x
    rw [Partition.singleton_kernel q hq]
    constructor
    · rintro rfl
      exact ⟨0, Matrix.zero_mulVec _⟩
    · rintro ⟨z, hz⟩
      simpa using hz.symm

end CommodityClassification.InputCoordinates
