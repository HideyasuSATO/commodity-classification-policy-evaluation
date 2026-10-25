module
public import LeanMath.CommodityClassification.WelfareBudget
@[expose] public section
set_option maxHeartbeats 2400000
namespace CommodityClassification.Equilibrium
open Matrix Filter
open scoped BigOperators Topology ContDiff
variable {n k g : ℕ}
namespace Model
variable (E : Model n k)

noncomputable def welfare (utility : Vec n → ℝ) (u : ℝ → Vec k) (s : ℝ → ℝ) (t : ℝ) : ℝ :=
  utility (E.quantities (t,u t))+s t

theorem welfare_derivative (abar : Vec (k+1)) (utility : Vec n → ℝ)
    (u : ℝ → Vec k) (s : ℝ → ℝ) (t : ℝ) (z : Vec k) (ds : ℝ) (dQ : Vec n)
    (hu : HasDerivAt u z t) (hs : HasDerivAt s ds t)
    (hQ : HasDerivAt (fun x => E.quantities (x,u x)) dQ t)
    (hw : E.currentPrice (u t) ∈ CESCost.PositivePrices (k+1))
    (hclear : ∀ᶠ x in 𝓝 t, E.excess abar ((x,u x),s x)=0)
    (hutility : HasFDerivAt utility (CESCost.weightedLinear (E.prices (t,u t)))
      (E.quantities (t,u t))) :
    HasDerivAt (E.welfare utility u s) (t * dotProduct E.b dQ) t := by
  have hr := E.resource_derivative abar u s t z ds dQ hu hs hQ hw hclear
  have hh := (hutility.comp_hasDerivAt t hQ).add hs
  apply hh.congr_deriv
  simp only [CESCost.weightedLinear_apply, prices,add_dotProduct,smul_dotProduct,smul_eq_mul]
  linarith

/-- Pointwise verified clearing, budget and actual derivatives. -/
def WelfareState (s0 : ℝ) (utility : Vec n → ℝ) (u : ℝ → Vec k) (s : ℝ → ℝ) (t : ℝ) : Prop :=
    E.excess (E.endowment s0) ((t,u t),s t)=0 ∧
    E.PositiveState (t,u t) (s t) ∧
    dotProduct (E.prices (t,u t)) (E.quantities (t,u t))+s t = E.householdIncome (E.endowment s0) (t,u t) ∧
    HasDerivAt (fun x => E.quantities (x,u x)) (deriv (fun x => E.quantities (x,u x)) t) t ∧
    HasDerivAt (E.welfare utility u s) (t * dotProduct E.b (deriv (fun x => E.quantities (x,u x)) t)) t

/-- The welfare identity on an open neighborhood of the benchmark. -/
def WelfareNeighborhood (s0 : ℝ) (utility : Vec n → ℝ) (u : ℝ → Vec k) (s : ℝ → ℝ) : Prop :=
  ∃ I : Set ℝ, IsOpen I ∧ 0 ∈ I ∧ ∀ t ∈ I, E.WelfareState s0 utility u s t

theorem constructed_welfare_neighborhood (h : E.DemandC1) (hK : E.K.PosDef)
    (hq : ∀ i, 0 < E.q i) (s0 : ℝ) (hs0 : 0 < s0)
    (utility : Vec n → ℝ) (hutility : E.UtilityCompatible utility) :
    E.WelfareNeighborhood s0 utility (E.localPricePath h hK s0) (E.localNumerairePath h hK s0) := by
  let u := E.localPricePath h hK s0
  let s := E.localNumerairePath h hK s0
  have hcont : ContinuousAt (fun t : ℝ => (t,u t)) 0 :=
    continuousAt_id.prodMk (E.localPricePath_contDiffAt h hK s0).continuousAt
  have ht : Tendsto (fun t : ℝ => (t,u t)) (𝓝 0) (𝓝 (0 : PolicyPrice k)) := by
    change Tendsto _ (𝓝 0) (𝓝 (0,0))
    simpa only [ContinuousAt,u,E.localPricePath_base] using hcont
  have hp : Tendsto E.prices (𝓝 0) (𝓝 E.p) := by
    simpa only [ContinuousAt,E.prices_zero] using E.prices_contDiffAt.continuousAt
  have hutil := (hp.comp ht).eventually hutility
  have hquant := ht.eventually ((E.quantities_contDiffAt h).eventually (by norm_num))
  obtain ⟨J,hJo,hJ0,hJ⟩ := E.local_common_neighborhood h hK hq s0 hs0
  have hall : ∀ᶠ t in 𝓝 (0 : ℝ), t ∈ J ∧
      ContDiffAt ℝ 1 E.quantities (t,u t) ∧
      HasFDerivAt utility (CESCost.weightedLinear (E.prices (t,u t))) (E.quantities (t,u t)) := by
    filter_upwards [hJo.mem_nhds hJ0,hquant,hutil] with t ht' hq' hu'
    exact ⟨ht',hq',hu'⟩
  obtain ⟨I,hI,hIo,hI0⟩ := mem_nhds_iff.mp hall
  refine ⟨I,hIo,hI0,?_⟩
  intro t hit
  obtain ⟨hjt,hqt,hut⟩ := hI hit
  obtain ⟨hc,hpos,hu,hs⟩ := hJ t hjt
  have hdu : HasDerivAt u (deriv u t) t := (hu.differentiableAt (by norm_num)).hasDerivAt
  have hds : HasDerivAt s (deriv s t) t := (hs.differentiableAt (by norm_num)).hasDerivAt
  have hdQ : HasDerivAt (fun x => E.quantities (x,u x))
      (deriv (fun x => E.quantities (x,u x)) t) t := by
    apply DifferentiableAt.hasDerivAt
    exact DifferentiableAt.comp (f := fun x : ℝ => (x,u x)) (g := E.quantities) t
      (hqt.differentiableAt (by norm_num))
      (differentiableAt_id.prodMk hdu.differentiableAt)
  have hce : ∀ᶠ x in 𝓝 t, E.excess (E.endowment s0) ((x,u x),s x)=0 := by
    filter_upwards [hIo.mem_nhds hit] with x hx
    exact (hJ x (hI hx).1).1
  exact ⟨hc,hpos,E.household_budget (abar := E.endowment s0) (y := (t,u t)) (s := s t) hpos.1 hc,hdQ,
    E.welfare_derivative (E.endowment s0) utility u s t (deriv u t) (deriv s t)
      (deriv (fun x => E.quantities (x,u x)) t) hdu hds hdQ hpos.1 hce hut⟩

theorem economic_welfare_identity (h : E.DemandC1)
    (P : InputCoordinates.Partition n g) (J : Mat g k)
    (hreport : P.report E.q E.C=J) (hq : ∀ i, 0 < E.q i)
    (hI : ∀ j, 0 < Supply.totalInputs E.q E.A j) (hD : E.D.PosDef) (hσ : 0 < E.sigma)
    (s0 : ℝ) (hs0 : 0 < s0) (utility : Vec n → ℝ) (hutility : E.UtilityCompatible utility) :
    ∃ u : ℝ → Vec k, ∃ s : ℝ → ℝ, E.PositiveLocalPath s0 u s ∧
      E.WelfareNeighborhood s0 utility u s := by
  let hK := E.K_posDef P J hreport hq hI hD hσ
  exact ⟨E.localPricePath h hK s0,E.localNumerairePath h hK s0,
    E.constructed_positive_path h hK hq s0 hs0,
    E.constructed_welfare_neighborhood h hK hq s0 hs0 utility hutility⟩

end Model
end CommodityClassification.Equilibrium
