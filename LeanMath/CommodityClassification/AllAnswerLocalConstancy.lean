module

public import LeanMath.CommodityClassification.AllAnswerDomain

/-! All-answer constancy supplies the neighborhood identities used in B.2. -/
@[expose] public section
noncomputable section
namespace CommodityClassification.FixedAnswer
open Matrix Filter
open scoped BigOperators Topology
variable {n k r s : ℕ}

theorem Data.nonzero_neighborhood_along_parent (a : Data n k r)
    (U : Mat n s) (Ω : Set (Mat s k)) (hΩ : IsOpen Ω)
    (Y : Mat s k) (hY : Y ∈ Ω) (hm : a.m ((a.withDirections U).point Y) ≠ 0)
    (X : Mat s k) :
    ∀ᶠ t : ℝ in 𝓝 0, Y + t • X ∈ Ω ∧
      a.m ((a.withDirections U).point (Y + t • X)) ≠ 0 := by
  have hy : Continuous (fun t : ℝ => Y + t • X) :=
    continuous_const.add (continuous_id.smul continuous_const)
  have hmcont : Continuous (fun t : ℝ => a.m ((a.withDirections U).point (Y + t • X))) := by
    simp only [Data.m,Data.point]
    exact ((continuous_const.add (continuous_const.matrix_mul hy)).matrix_transpose).matrix_mulVec
      continuous_const
  have hmem : ∀ᶠ t : ℝ in 𝓝 0, Y + t • X ∈ Ω :=
    hy.continuousAt.preimage_mem_nhds (by simpa only [zero_smul,add_zero] using hΩ.mem_nhds hY)
  have hn : ∀ᶠ t : ℝ in 𝓝 0, a.m ((a.withDirections U).point (Y+t•X)) ≠ 0 :=
    hmcont.continuousAt.eventually_ne (by simpa only [zero_smul,add_zero] using hm)
  exact hmem.and hn

theorem AllAnswersIdentified.residuals_near (a : Data n k r)
    (U : Mat n s) (J : Mat s r) (Ω : Set (Mat s k))
    (h : AllAnswerHypotheses a U J Ω) (hc : AllAnswersIdentified a U J Ω)
    (Y : Mat s k) (hY : Y ∈ Ω) (hm : a.m ((a.withDirections U).point Y) ≠ 0)
    (X : Mat s k) :
    ∀ᶠ t : ℝ in 𝓝 0,
      (a.atParent U Y).schur a.N a.N (((a.atParent U Y).withDirections U).point (t•X)) = 0 ∧
      (a.atParent U Y).linearResidual a.N (((a.atParent U Y).withDirections U).point (t•X)) = 0 := by
  filter_upwards [a.nonzero_neighborhood_along_parent U Ω h.parent.domain_open Y hY hm X] with t ht
  rw [a.parent_translation U Y (t • X)]
  exact hc.nonzero_residuals a U J Ω h (Y+t•X) ht.1 ht.2

theorem AllAnswersIdentified.parent_moments_at_nonzero_loading (a : Data n k r)
    (U : Mat n s) (J : Mat s r) (Ω : Set (Mat s k))
    (h : AllAnswerHypotheses a U J Ω) (hc : AllAnswersIdentified a U J Ω)
    (Y : Mat s k) (hY : Y ∈ Ω) (hm : a.m ((a.withDirections U).point Y) ≠ 0)
    (hA : (a.atParent U Y).A_N ≠ 0) :
    (a.atParent U Y).schur U U (a.atParent U Y).C₀ = 0 ∧
      (a.atParent U Y).linearResidual U (a.atParent U Y).C₀ = 0 := by
  have hh := h.parent_hypotheses a U J Ω Y hY
  have hK : (a.atParent U Y).K₀.PosDef :=
    ((a.atParent U Y).withDirections U).K₀_posDef _ hh
  have hs : ∀ X : Mat s k, ∀ᶠ t : ℝ in 𝓝 0,
      (a.atParent U Y).schur (a.atParent U Y).N (a.atParent U Y).N
        (((a.atParent U Y).withDirections U).point (t•X)) = 0 :=
    fun X => (hc.residuals_near a U J Ω h Y hY hm X).mono (fun _ ht => ht.1)
  have hg : ∀ X : Mat s k, ∀ᶠ t : ℝ in 𝓝 0,
      (a.atParent U Y).linearResidual (a.atParent U Y).N
        (((a.atParent U Y).withDirections U).point (t•X)) = 0 :=
    fun X => (hc.residuals_near a U J Ω h Y hY hm X).mono (fun _ ht => ht.2)
  have hcross := (a.atParent U Y).cross_vanishes U h.parent.L_symmetric hK hA hs
  exact ⟨(a.atParent U Y).parent_schur_vanishes U _ hh hA hs,
    (a.atParent U Y).linear_residual_vanishes U h.parent.L_symmetric hK hA hcross hg⟩

theorem AllAnswersIdentified.parent_constant_of_nonzero_loading (a : Data n k r)
    (U : Mat n s) (J : Mat s r) (Ω : Set (Mat s k))
    (h : AllAnswerHypotheses a U J Ω) (hc : AllAnswersIdentified a U J Ω)
    (Y : Mat s k) (hY : Y ∈ Ω) (hm : a.m ((a.withDirections U).point Y) ≠ 0)
    (hA : (a.atParent U Y).A_N ≠ 0) :
    (a.withDirections U).ConstantOn Ω := by
  have hh := h.parent_hypotheses a U J Ω Y hY
  have hr := hc.parent_moments_at_nonzero_loading a U J Ω h Y hY hm hA
  have hcB : ((a.atParent U Y).withDirections U).CongruenceCriterion :=
    Or.inr ⟨hm,sub_eq_zero.mp hr.2,sub_eq_zero.mp hr.1⟩
  have hglobal := lemmaB1_global ((a.atParent U Y).withDirections U) _ hh hcB
  have he (W : Mat s k) (hW : W ∈ Ω) :
      a.F ((a.withDirections U).point W) = a.F ((a.withDirections U).point Y) := by
    have hp : ((a.atParent U Y).withDirections U).point (W-Y) = (a.withDirections U).point W := by
      rw [a.parent_translation U Y (W-Y)]
      congr 1
      abel
    have hs := hglobal (W-Y) (by
      change (((a.atParent U Y).withDirections U).K
        (((a.atParent U Y).withDirections U).point (W-Y))).PosDef
      rw [hp]
      exact h.parent.K_posDef W hW)
    rw [hp] at hs
    exact hs
  intro W hW
  have hzero := he 0 h.parent.origin_mem
  have hz : (a.withDirections U).point 0 = a.C₀ := by
    simp only [Data.point,Data.withDirections,Matrix.mul_zero,add_zero]
  rw [hz] at hzero
  exact (he W hW).trans hzero.symm

end CommodityClassification.FixedAnswer
