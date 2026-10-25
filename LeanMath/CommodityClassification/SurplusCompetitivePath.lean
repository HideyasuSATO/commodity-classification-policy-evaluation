module

public import LeanMath.CommodityClassification.LocalCompetitiveState

/-! A general surplus-optimal demand implements the same positive clearing path. -/
@[expose] public section
noncomputable section
set_option maxHeartbeats 1000000
namespace CommodityClassification.Equilibrium.Model
open Matrix Filter
open scoped Topology
variable {n k : ℕ} (E : Model n k)

theorem positive_path_consumer_prices_tendsto (s0 : ℝ) (u : ℝ → Vec k) (s : ℝ → ℝ)
    (hp : E.PositiveLocalPath s0 u s) :
    Tendsto (fun t => E.prices (t,u t)) (𝓝 0) (𝓝 E.p) := by
  obtain ⟨I,_,hI0,hI⟩ := hp.neighborhood
  have hu : ContinuousAt (fun t : ℝ => (t,u t)) 0 :=
    continuousAt_id.prodMk (hI 0 hI0).2.2.1.continuousAt
  have ht : Tendsto (fun t : ℝ => (t,u t)) (𝓝 0) (𝓝 (0 : PolicyPrice k)) := by
    change Tendsto _ (𝓝 0) (𝓝 (0,0))
    simpa only [ContinuousAt,hp.price_base] using hu
  have hpr : Tendsto E.prices (𝓝 0) (𝓝 E.p) := by
    simpa only [ContinuousAt,E.prices_zero] using E.prices_contDiffAt.continuousAt
  exact hpr.comp ht

theorem positive_path_competitive_of_surplus (hσ : 0<E.sigma) (ha : ∀j,0≤E.frame.a0 j)
    (utility : Vec n → ℝ) (U : Set (Vec n)) (s0 : ℝ) (u : ℝ → Vec k) (s : ℝ → ℝ)
    (hp : E.PositiveLocalPath s0 u s)
    (hopt : ∀ᶠr in 𝓝 E.p,E.demand r∈U ∧ ∀x∈U,
      utility x-dotProduct r x≤utility (E.demand r)-dotProduct r (E.demand r)) :
    ∃I : Set ℝ,IsOpen I ∧ 0∈I ∧ ∀t∈I,
      E.CompetitiveState utility U (E.endowment s0) (t,u t) (s t) := by
  have ho := (E.positive_path_consumer_prices_tendsto s0 u s hp).eventually hopt
  obtain ⟨J,hJo,hJ0,hJ⟩ := hp.neighborhood
  have hj : ∀ᶠt : ℝ in 𝓝 0,t∈J := hJo.mem_nhds hJ0
  have hall := hj.and ho
  obtain ⟨I,hI,hIo,hI0⟩ := mem_nhds_iff.mp hall
  refine ⟨I,hIo,hI0,?_⟩
  intro t ht
  obtain ⟨hjt,hot⟩ := hI ht
  exact E.competitive_of_surplus hσ ha utility U (E.endowment s0) (t,u t) (s t)
    (hJ t hjt).2.1 (hJ t hjt).1 hot.1 hot.2

end CommodityClassification.Equilibrium.Model
