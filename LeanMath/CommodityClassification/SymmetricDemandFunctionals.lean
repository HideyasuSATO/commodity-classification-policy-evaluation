module

public import LeanMath.CommodityClassification.ExactCommodityPairRule
public import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
public import Mathlib.MeasureTheory.Measure.OpenPos

/-! Proper policy-load hyperplanes in the space of real symmetric demand matrices. -/
@[expose] public section
noncomputable section
namespace CommodityClassification.Genericity
open Matrix FixedAnswer
open scoped Topology
variable {n : ℕ}

local instance (a b : ℕ) : NormedAddCommGroup (Mat a b) :=
  inferInstanceAs (NormedAddCommGroup (Fin a → Fin b → ℝ))
local instance (a b : ℕ) : NormedSpace ℝ (Mat a b) :=
  inferInstanceAs (NormedSpace ℝ (Fin a → Fin b → ℝ))

def symmetricSpace (n : ℕ) : Submodule ℝ (Mat n n) where
  carrier := {D | D.transpose=D}
  zero_mem' := by simp
  add_mem' := by
    intro A B hA hB
    change A.transpose=A at hA
    change B.transpose=B at hB
    change (A+B).transpose=A+B
    rw [transpose_add,hA,hB]
  smul_mem' := by
    intro c A hA
    change A.transpose=A at hA
    change (c • A).transpose=c • A
    rw [transpose_smul,hA]

abbrev SymmetricDemand (n : ℕ) := ↥(symmetricSpace n)

instance symmetricDemandMeasurableSpace (n : ℕ) : MeasurableSpace (SymmetricDemand n) := borel _

instance symmetricDemandBorelSpace (n : ℕ) : BorelSpace (SymmetricDemand n) := ⟨rfl⟩

def pairFunctional (b v : Vec n) : SymmetricDemand n →ₗ[ℝ] ℝ where
  toFun D := dotProduct v (D.val *ᵥ b)
  map_add' := by intro A B; simp only [Submodule.coe_add,add_mulVec,dotProduct_add]
  map_smul' := by intro c A; simp only [Submodule.coe_smul,smul_mulVec,dotProduct_smul,smul_eq_mul,RingHom.id_apply]

theorem symmetric_outer_sum (b v : Vec n) :
    (vecMulVec b v+vecMulVec v b).transpose=vecMulVec b v+vecMulVec v b := by
  rw [transpose_add,transpose_vecMulVec,transpose_vecMulVec,add_comm]

theorem outer_sum_load (b v : Vec n) :
    dotProduct v ((vecMulVec b v+vecMulVec v b) *ᵥ b)=
      (dotProduct v b)^2+dotProduct v v*dotProduct b b := by
  simp only [add_mulVec,vecMulVec_mulVec,dotProduct_add,dotProduct_smul,op_smul_eq_smul,smul_eq_mul]
  ring

theorem outer_sum_load_pos (b v : Vec n) (hb : b≠0) (hv : v≠0) :
    0<dotProduct v ((vecMulVec b v+vecMulVec v b) *ᵥ b) := by
  have hbq : 0<dotProduct b b := by simpa using (dotProduct_self_star_pos_iff.mpr hb)
  have hvq : 0<dotProduct v v := by simpa using (dotProduct_self_star_pos_iff.mpr hv)
  rw [outer_sum_load]
  exact add_pos_of_nonneg_of_pos (sq_nonneg _) (mul_pos hvq hbq)

theorem symmetric_coefficient_nonzero (b v : Vec n) (hb : b≠0) (hv : v≠0) :
    (1/2 : ℝ) • (vecMulVec b v+vecMulVec v b)≠0 := by
  have hsum : vecMulVec b v+vecMulVec v b≠0 := by
    intro hz
    have hh := outer_sum_load_pos b v hb hv
    simp only [hz,zero_mulVec,dotProduct_zero,lt_self_iff_false] at hh
  exact smul_ne_zero (by norm_num) hsum

theorem pairFunctional_nonzero (b v : Vec n) (hb : b≠0) (hv : v≠0) :
    pairFunctional b v≠0 := by
  let E : SymmetricDemand n := ⟨vecMulVec b v+vecMulVec v b,symmetric_outer_sum b v⟩
  intro hf
  have hh := congrArg (fun f : SymmetricDemand n →ₗ[ℝ] ℝ => f E) hf
  change dotProduct v ((vecMulVec b v+vecMulVec v b) *ᵥ b)=0 at hh
  exact (ne_of_gt (outer_sum_load_pos b v hb hv)) hh

theorem pairFunctional_kernel_proper (b v : Vec n) (hb : b≠0) (hv : v≠0) :
    LinearMap.ker (pairFunctional b v)≠⊤ := by
  intro hk
  exact pairFunctional_nonzero b v hb hv (LinearMap.ker_eq_top.mp hk)

theorem pairFunctional_surjective (b v : Vec n) (hb : b≠0) (hv : v≠0) :
    Function.Surjective (pairFunctional b v) := by
  let E : SymmetricDemand n := ⟨vecMulVec b v+vecMulVec v b,symmetric_outer_sum b v⟩
  have hE : pairFunctional b v E≠0 := ne_of_gt (outer_sum_load_pos b v hb hv)
  intro x
  refine ⟨(x/pairFunctional b v E) • E,?_⟩
  rw [map_smul]
  exact div_mul_cancel₀ x hE

theorem pairFunctional_continuous (b v : Vec n) : Continuous (pairFunctional b v) :=
  (pairFunctional b v).continuous_of_finiteDimensional

theorem pairFunctional_kernel_closed (b v : Vec n) :
    IsClosed (LinearMap.ker (pairFunctional b v) : Set (SymmetricDemand n)) :=
  (LinearMap.ker (pairFunctional b v)).closed_of_finiteDimensional

theorem pairFunctional_kernel_null (b v : Vec n) (hb : b≠0) (hv : v≠0)
    (μ : MeasureTheory.Measure (SymmetricDemand n)) [MeasureTheory.Measure.IsAddHaarMeasure μ] :
    μ (LinearMap.ker (pairFunctional b v))=0 :=
  MeasureTheory.Measure.addHaar_submodule μ _ (pairFunctional_kernel_proper b v hb hv)

end CommodityClassification.Genericity
