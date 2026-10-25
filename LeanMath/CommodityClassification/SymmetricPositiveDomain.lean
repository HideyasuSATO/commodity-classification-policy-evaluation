module

public import LeanMath.CommodityClassification.ParentExceptionNongeneric

/-! The SPD cone is open in the actual space of symmetric demand matrices. -/
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

def positiveDemandCone (n : ℕ) : Set (SymmetricDemand n) := {D | D.val.PosDef}

theorem symmetric_posDef_iff_sphere (D : SymmetricDemand n) :
    D.val.PosDef ↔ ∀x : Vec n,‖x‖=1 → 0<dotProduct x (D.val *ᵥ x) := by
  constructor
  · intro hD x hx
    have hne : x≠0 := by intro he; simp [he] at hx
    simpa using hD.dotProduct_mulVec_pos hne
  · intro h
    apply Matrix.PosDef.of_dotProduct_mulVec_pos
    · have hs : D.val.transpose=D.val := D.property
      simpa only [Matrix.IsHermitian,conjTranspose_eq_transpose_of_trivial] using hs
    · intro x hx
      have hn : 0<‖x‖ := norm_pos_iff.mpr hx
      have hu : ‖(‖x‖⁻¹ : ℝ) • x‖=1 := norm_smul_inv_norm hx
      have hp := h _ hu
      simp only [mulVec_smul,smul_dotProduct,dotProduct_smul,smul_eq_mul] at hp
      have hr : 0<‖x‖⁻¹ := inv_pos.mpr hn
      have hq : 0<dotProduct x (D.val *ᵥ x) := by
        exact (mul_pos_iff_of_pos_left hr).mp ((mul_pos_iff_of_pos_left hr).mp hp)
      simpa using hq

theorem joint_demand_quadratic_continuous :
    Continuous (fun z : SymmetricDemand n × Vec n => dotProduct z.2 (z.1.val *ᵥ z.2)) := by
  simp only [dotProduct,mulVec]
  apply continuous_finsetSum
  intro i _
  apply Continuous.mul ((continuous_apply i).comp continuous_snd)
  apply continuous_finsetSum
  intro j _
  have hi : Continuous (fun A : Mat n n => A i) := continuous_apply i
  have hij : Continuous (fun A : Mat n n => A i j) := (continuous_apply j).comp hi
  exact (hij.comp (continuous_subtype_val.comp continuous_fst)).mul
    ((continuous_apply j).comp continuous_snd)

theorem positiveDemandCone_isOpen : IsOpen (positiveDemandCone n) := by
  rw [isOpen_iff_mem_nhds]
  intro D hD
  have hs : ∀ᶠA : SymmetricDemand n in 𝓝 D,
      ∀x∈Metric.sphere (0 : Vec n) 1,0<dotProduct x (A.val *ᵥ x) := by
    apply (isCompact_sphere (0 : Vec n) 1).eventually_forall_of_forall_eventually
    intro x hx
    have hnorm : ‖x‖=1 := by simpa [Metric.mem_sphere,dist_zero_right] using hx
    exact (isOpen_lt continuous_const joint_demand_quadratic_continuous).mem_nhds
      ((symmetric_posDef_iff_sphere D).mp hD x hnorm)
  filter_upwards [hs] with A hA
  apply (symmetric_posDef_iff_sphere A).mpr
  intro x hx
  exact hA x (by simpa [Metric.mem_sphere,dist_zero_right] using hx)

theorem dense_relative_positive_domain {Z : Set (SymmetricDemand n)} (hZ : Dense Zᶜ) :
    Dense {D : ↥(positiveDemandCone n) | D.val∉Z} :=
  hZ.preimage positiveDemandCone_isOpen.isOpenMap_subtype_val

end CommodityClassification.Genericity
