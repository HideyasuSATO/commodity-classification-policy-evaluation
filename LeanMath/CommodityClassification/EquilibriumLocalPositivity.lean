module
public import LeanMath.CommodityClassification.EquilibriumLocalClearing
@[expose] public section
set_option maxHeartbeats 2000000
namespace CommodityClassification.Equilibrium
open Matrix Filter
open scoped BigOperators Topology ContDiff
variable {n k : ℕ}
namespace Model
variable (E : Model n k)

def PositiveState (y : PolicyPrice k) (s : ℝ) : Prop :=
  (∀ j, 0 < E.currentPrice y.2 j) ∧ (∀ i, 0 < E.prices y i) ∧
  (∀ i, 0 < E.quantities y i) ∧ 0 < s ∧
  (∀ i j, 0 < E.currentInputs (E.currentPrice y.2) i j)

theorem positiveState_neighborhood (h : E.DemandC1) (hq : ∀ i, 0 < E.q i)
    (s0 : ℝ) (hs0 : 0 < s0) :
    ∀ᶠ ys : PolicyPrice k × ℝ in 𝓝 (0,s0), E.PositiveState ys.1 ys.2 := by
  have hw : ∀ᶠ ys : PolicyPrice k × ℝ in 𝓝 (0,s0),
      ∀ j, 0 < E.currentPrice ys.1.2 j := by
    apply Filter.eventually_all.mpr
    intro j
    have hc : ContinuousAt (fun ys : PolicyPrice k × ℝ => E.currentPrice ys.1.2 j) (0,s0) := by
      exact (continuous_apply j).continuousAt.comp
        (E.currentPrice_continuous.continuousAt.comp (continuousAt_snd.comp continuousAt_fst))
    exact hc (eventually_gt_nhds (by simpa only [Prod.snd_zero,E.currentPrice_zero] using E.hw j))
  have hp : ∀ᶠ ys : PolicyPrice k × ℝ in 𝓝 (0,s0), ∀ i, 0 < E.prices ys.1 i := by
    apply Filter.eventually_all.mpr
    intro i
    have hc := ((contDiffAt_pi.mp E.prices_contDiffAt i).continuousAt).comp
      (x := (0,s0)) continuousAt_fst
    exact hc (eventually_gt_nhds (by simpa only [Function.comp_apply,E.prices_zero] using E.hp i))
  have hqq : ∀ᶠ ys : PolicyPrice k × ℝ in 𝓝 (0,s0), ∀ i, 0 < E.quantities ys.1 i := by
    apply Filter.eventually_all.mpr
    intro i
    have hc := ((contDiffAt_pi.mp (E.quantities_contDiffAt h) i).continuousAt).comp
      (x := (0,s0)) continuousAt_fst
    exact hc (eventually_gt_nhds (by simpa only [Function.comp_apply,E.quantities_zero] using hq i))
  have hs : ∀ᶠ ys : PolicyPrice k × ℝ in 𝓝 (0,s0), 0 < ys.2 :=
    continuousAt_snd (eventually_gt_nhds hs0)
  have ha : ∀ᶠ ys : PolicyPrice k × ℝ in 𝓝 (0,s0),
      ∀ i j, 0 < E.currentInputs (E.currentPrice ys.1.2) i j := by
    apply Filter.eventually_all.mpr
    intro i
    apply Filter.eventually_all.mpr
    intro j
    have hc : ContinuousAt (fun ys : PolicyPrice k × ℝ =>
        E.currentInputs (E.currentPrice ys.1.2) i j) (0,s0) := by
      have hinput : ContinuousAt (fun w => E.currentInputs w i j) (E.currentPrice ((0 : PolicyPrice k),s0).1.2) := by
        simp only [Prod.snd_zero,E.currentPrice_zero]
        exact (E.currentInputs_contDiffAt E.hw i j).continuousAt
      have hwc : ContinuousAt (fun ys : PolicyPrice k × ℝ => E.currentPrice ys.1.2) (0,s0) :=
        E.currentPrice_continuous.continuousAt.comp (continuousAt_snd.comp continuousAt_fst)
      exact hinput.comp (f := fun ys : PolicyPrice k × ℝ => E.currentPrice ys.1.2) hwc
    exact hc (eventually_gt_nhds (by
      simpa only [Prod.snd_zero,E.currentPrice_zero,E.inputs_base] using (show 0 < E.A i j from E.hC i j)))
  filter_upwards [hw,hp,hqq,hs,ha] with ys hw hp hqq hs ha
  exact ⟨hw,hp,hqq,hs,ha⟩

theorem local_positive_state (h : E.DemandC1) (hK : E.K.PosDef)
    (hq : ∀ i, 0 < E.q i) (s0 : ℝ) (hs0 : 0 < s0) :
    ∀ᶠ t in 𝓝 (0 : ℝ), E.PositiveState
      (t,E.localPricePath h hK s0 t) (E.localNumerairePath h hK s0 t) := by
  have hc : ContinuousAt (fun t : ℝ => ((t,E.localPricePath h hK s0 t),
      E.localNumerairePath h hK s0 t)) 0 :=
    (continuousAt_id.prodMk (E.localPricePath_contDiffAt h hK s0).continuousAt).prodMk
      (E.localNumerairePath_contDiffAt h hK s0).continuousAt
  have ht : Tendsto (fun t : ℝ => ((t,E.localPricePath h hK s0 t),E.localNumerairePath h hK s0 t))
      (𝓝 0) (𝓝 (0,s0)) := by
    change Tendsto _ (𝓝 0) (𝓝 ((0,0),s0))
    simpa only [ContinuousAt,E.localPricePath_base,E.localNumerairePath_base] using hc
  exact ht (E.positiveState_neighborhood h hq s0 hs0)

/-- One open policy neighborhood has clearing, all positivity conditions and C1 paths. -/
theorem local_common_neighborhood (h : E.DemandC1) (hK : E.K.PosDef)
    (hq : ∀ i, 0 < E.q i) (s0 : ℝ) (hs0 : 0 < s0) :
    ∃ I : Set ℝ, IsOpen I ∧ 0 ∈ I ∧ ∀ t ∈ I,
      E.excess (E.endowment s0) ((t,E.localPricePath h hK s0 t),E.localNumerairePath h hK s0 t) = 0 ∧
      E.PositiveState (t,E.localPricePath h hK s0 t) (E.localNumerairePath h hK s0 t) ∧
      ContDiffAt ℝ 1 (E.localPricePath h hK s0) t ∧ ContDiffAt ℝ 1 (E.localNumerairePath h hK s0) t := by
  have hall : ∀ᶠ t in 𝓝 (0 : ℝ),
      E.excess (E.endowment s0) ((t,E.localPricePath h hK s0 t),E.localNumerairePath h hK s0 t) = 0 ∧
      E.PositiveState (t,E.localPricePath h hK s0 t) (E.localNumerairePath h hK s0 t) ∧
      ContDiffAt ℝ 1 (E.localPricePath h hK s0) t ∧ ContDiffAt ℝ 1 (E.localNumerairePath h hK s0) t := by
    filter_upwards [E.local_full_clearing h hK s0,E.local_positive_state h hK hq s0 hs0,
      (E.localPricePath_contDiffAt h hK s0).eventually (by norm_num),
      (E.localNumerairePath_contDiffAt h hK s0).eventually (by norm_num)] with t h1 h2 h3 h4
    exact ⟨h1,h2,h3,h4⟩
  obtain ⟨I,hI,ho,h0⟩ := mem_nhds_iff.mp hall
  exact ⟨I,ho,h0,fun t ht => hI ht⟩
end Model
end CommodityClassification.Equilibrium
