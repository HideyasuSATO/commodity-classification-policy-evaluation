module

public import LeanMath.CommodityClassification.PrecisionUniformPositiveWitnesses
public import Mathlib.Analysis.Convex.Jensen
public import Mathlib.Analysis.Convex.Combination

/-! Convex within-cell input dispersion and the sign-vector maximum principle. -/
@[expose] public section
noncomputable section
set_option maxHeartbeats 1600000
namespace CommodityClassification.Precision.Data
open InputCoordinates
open scoped BigOperators
variable {n g : ℕ} (d : Precision.Data n)

def cellVariance (P : Partition n g) (a : Fin g) (c : Vec n) : ℝ :=
  ∑i∈P.cell a,d.w i*(c i-d.groupTotal P c a/d.groupWeight P a)^2

theorem cellVariance_nonneg (P : Partition n g) (a : Fin g) (c : Vec n) :
    0≤d.cellVariance P a c :=
  Finset.sum_nonneg (fun i _ => mul_nonneg (d.hw i).le (sq_nonneg _))

theorem cellVariance_formula (P : Partition n g) (a : Fin g) (c : Vec n) :
    d.cellVariance P a c=(∑i∈P.cell a,d.w i*(c i)^2)-(d.groupTotal P c a)^2/d.groupWeight P a :=
  d.cell_variance_identity P c a

theorem cellVariance_convex_identity (P : Partition n g) (a : Fin g) (c e : Vec n)
    (s t : ℝ) (hst : s+t=1) :
    d.cellVariance P a (s • c+t • e)=s*d.cellVariance P a c+t*d.cellVariance P a e-
      s*t*d.cellVariance P a (c-e) := by
  unfold cellVariance
  rw [d.groupTotal_add,d.groupTotal_smul,d.groupTotal_smul,d.groupTotal_sub]
  simp only [Pi.add_apply,Pi.sub_apply,Pi.smul_apply,smul_eq_mul,
    Finset.mul_sum,←Finset.sum_add_distrib,←Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _
  have ht : t=1-s := by linarith
  rw [ht]
  ring

theorem cellVariance_convex (P : Partition n g) (a : Fin g) :
    ConvexOn ℝ Set.univ (d.cellVariance P a) := by
  refine ⟨convex_univ,?_⟩
  intro c _ e _ s t hs ht hst
  rw [d.cellVariance_convex_identity P a c e s t hst]
  simp only [smul_eq_mul]
  have hh := mul_nonneg (mul_nonneg hs ht) (d.cellVariance_nonneg P a (c-e))
  linarith

end CommodityClassification.Precision.Data

namespace CommodityClassification.Precision.Box
open InputCoordinates
variable {n : ℕ}

def signs (n : ℕ) : Set (Vec n) := Set.univ.pi (fun _ => {(-1:ℝ),1})

theorem signs_iff (c : Vec n) : c∈signs n ↔ ∀i,c i= -1 ∨ c i=1 := by
  simp [signs,Set.mem_pi]

theorem signs_nonempty : (signs n).Nonempty := by
  refine ⟨fun _ => 1,(signs_iff _).mpr ?_⟩
  intro i
  exact Or.inr rfl

theorem signs_finite : (signs n).Finite := Set.Finite.pi (fun _ => Set.toFinite _)

theorem signs_mem_box (c : Vec n) (hc : c∈signs n) : ∀i,|c i|≤1 := by
  intro i
  rcases (signs_iff c).mp hc i with hi|hi <;> rw [hi] <;> norm_num

theorem box_mem_convexHull_signs (c : Vec n) (hc : ∀i,|c i|≤1) : c∈convexHull ℝ (signs n) := by
  apply mem_convexHull_pi
  intro i _
  rw [convexHull_pair,segment_eq_Icc (by norm_num : (-1:ℝ)≤1)]
  exact abs_le.mp (hc i)

end CommodityClassification.Precision.Box

namespace CommodityClassification.Precision.Data
open InputCoordinates
variable {n g : ℕ} (d : Precision.Data n)

theorem cellVariance_dominated_by_sign (P : Partition n g) (a : Fin g) (c : Vec n)
    (hc : ∀i,|c i|≤1) :
    ∃s∈Precision.Box.signs n,d.cellVariance P a c≤d.cellVariance P a s :=
  (d.cellVariance_convex P a).exists_ge_of_mem_convexHull (Set.subset_univ _)
    (Precision.Box.box_mem_convexHull_signs c hc)

end CommodityClassification.Precision.Data
