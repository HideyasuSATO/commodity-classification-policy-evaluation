module

public import LeanMath.CommodityClassification.GroupQuantityCompetitivePath

/-! Neighborhood variations against one nonzero response detect an entire matrix. -/
@[expose] public section
noncomputable section
namespace CommodityClassification.InputCoordinates
open Matrix Filter
open scoped Topology
variable {g r k : ℕ}

theorem matrix_zero_of_small_response_variations (M : Mat g r) (y : Vec k) (hy : y≠0)
    (hv : ∀ᶠZ : Mat r k in 𝓝 0,M *ᵥ (Z *ᵥ y)=0) : M=0 := by
  have hall (Z : Mat r k) : M *ᵥ (Z *ᵥ y)=0 := by
    have hc : Continuous (fun t : ℝ => t • Z) :=
      continuous_pi fun i => continuous_pi fun j => continuous_id.mul continuous_const
    have ht : ∀ᶠt : ℝ in 𝓝 0,M *ᵥ ((t • Z) *ᵥ y)=0 := by
      have hct : Tendsto (fun t : ℝ => t • Z) (𝓝 0) (𝓝 (0 : Mat r k)) := by
        simpa only [zero_smul] using hc.tendsto 0
      exact hct.eventually hv
    have hne : ∀ᶠt : ℝ in 𝓝[≠] 0,t≠0 := self_mem_nhdsWithin
    have hboth : ∀ᶠt : ℝ in 𝓝[≠] (0 : ℝ),M *ᵥ ((t • Z) *ᵥ y)=0 ∧ t≠0 :=
      (ht.filter_mono inf_le_left).and hne
    obtain ⟨t,ht,hne⟩ := hboth.exists
    rw [Matrix.smul_mulVec,Matrix.mulVec_smul] at ht
    exact (smul_eq_zero.mp ht).resolve_left hne
  have hz (x : Vec r) : M *ᵥ x=0 := by
    obtain ⟨Z,hZ⟩ := FixedAnswer.mulVec_surjective_in_matrix y hy x
    simpa only [hZ] using hall Z
  ext a j
  change M a j=0
  have hh := congrFun (hz (Pi.single j 1)) a
  simpa only [Matrix.mulVec_single_one,Matrix.col_apply,Pi.zero_apply] using hh

end CommodityClassification.InputCoordinates
