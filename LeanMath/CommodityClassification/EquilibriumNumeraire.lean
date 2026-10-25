module
public import LeanMath.CommodityClassification.EquilibriumDefinitions
@[expose] public section
namespace CommodityClassification.Equilibrium
open Matrix
open scoped BigOperators
variable {k : ℕ}

theorem frame_dual_kernel (e : InputCoordinates.Frame k) (v : Vec (k+1)) :
    e.V.transpose *ᵥ v = 0 ↔ v = dotProduct e.w v • e.a0 := by
  constructor
  · intro hv
    apply Matrix.mulVec_injective_of_isUnit ((Matrix.isUnit_transpose e.B).mpr e.B_isUnit)
    ext j
    refine Fin.cases ?_ (fun t => ?_) j
    · change dotProduct e.w v = dotProduct e.w (dotProduct e.w v • e.a0)
      rw [dotProduct_smul, dotProduct_comm e.w e.a0, e.normalized]
      simp
    · change (e.V.transpose *ᵥ v) t = (e.V.transpose *ᵥ (dotProduct e.w v • e.a0)) t
      rw [hv, Matrix.mulVec_smul, e.annihilates]
      simp
  · intro hv
    rw [hv, Matrix.mulVec_smul, e.annihilates, smul_zero]

theorem numeraire_adjustment (e : InputCoordinates.Frame k) (v : Vec (k+1))
    (hv : e.V.transpose *ᵥ v = 0) : v + (-dotProduct e.w v) • e.a0 = 0 := by
  have h := (frame_dual_kernel e v).mp hv
  rw [neg_smul, ← h, add_neg_cancel]

theorem numeraire_adjustment_unique (e : InputCoordinates.Frame k) (v : Vec (k+1)) (s : ℝ)
    (hs : v + s • e.a0 = 0) : s = -dotProduct e.w v := by
  have h := congrArg (dotProduct e.w) hs
  rw [dotProduct_add, dotProduct_smul, dotProduct_comm e.w e.a0,
    e.normalized, smul_eq_mul, mul_one, dotProduct_zero] at h
  linarith

theorem numeraire_solvability (e : InputCoordinates.Frame k) (v : Vec (k+1)) :
    (∃! s : ℝ, v + s • e.a0 = 0) ↔ e.V.transpose *ᵥ v = 0 := by
  constructor
  · rintro ⟨s,hs,_⟩
    have h := congrArg (fun u => e.V.transpose *ᵥ u) hs
    simpa [Matrix.mulVec_add, Matrix.mulVec_smul, e.annihilates] using h
  · intro hv
    exact ⟨-dotProduct e.w v, numeraire_adjustment e v hv,
      fun s hs => numeraire_adjustment_unique e v s hs⟩
end CommodityClassification.Equilibrium
