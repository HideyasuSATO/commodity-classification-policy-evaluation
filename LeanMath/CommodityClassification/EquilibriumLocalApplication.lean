module
public import LeanMath.CommodityClassification.EquilibriumLocalExistence
@[expose] public section
set_option maxHeartbeats 2400000
namespace CommodityClassification.Equilibrium
open Matrix Filter
open scoped BigOperators Topology ContDiff
variable {n k : ℕ}

/-- Transfer the optimizer to any utility agreeing with the local quadratic form
on U. The conclusion compares only quantities in U, not remote consumption. -/
theorem local_utility_optimum (p q : Vec n) (D : Mat n n) (hD : D.PosDef)
    (utility : Vec n → ℝ) (c : ℝ) (U : Set (Vec n)) (hU : U ∈ 𝓝 q)
    (hmatch : ∀ r ∈ U, utility r = c + quadraticUtility p D (r-q)) :
    ∀ᶠ v in 𝓝 p,
      affineDemand p q D v ∈ U ∧
      (∀ r ∈ U, utility r - dotProduct v r ≤
        utility (affineDemand p q D v) - dotProduct v (affineDemand p q D v)) ∧
      (∀ r ∈ U, r ≠ affineDemand p q D v → utility r - dotProduct v r <
        utility (affineDemand p q D v) - dotProduct v (affineDemand p q D v)) := by
  filter_upwards [affineDemand_local p q D U hU] with v hv
  have hs (r : Vec n) (hr : r ∈ U) :
      utility r - dotProduct v r = c - dotProduct v q + quadraticSurplus p D v (r-q) := by
    rw [hmatch r hr]
    simp only [quadraticSurplus,dotProduct_sub]
    ring
  have hchoice : affineDemand p q D v - q = quadraticChoice p D v := by
    rw [affineDemand_eq_choice]
    abel
  refine ⟨hv,?_,?_⟩
  · intro r hr
    rw [hs r hr,hs _ hv,hchoice]
    have hh := quadraticSurplus_maximum p v (r-q) D hD
    linarith
  · intro r hr hne
    rw [hs r hr,hs _ hv,hchoice]
    apply add_lt_add_right
    apply quadraticSurplus_strict p v (r-q) D hD
    intro heq
    apply hne
    rw [affineDemand_eq_choice]
    rw [←heq]
    abel

namespace Model
variable (E : Model n k)

theorem factor_price_path_derivative (u : ℝ → Vec k) (z : Vec k)
    (hu0 : u 0 = 0) (hu : HasDerivAt u z 0) :
    HasDerivAt (fun t => E.currentPrice (u t)) (E.frame.V *ᵥ z) 0 := by
  have hc : HasFDerivAt E.currentPrice (matCLM E.frame.V) (u 0) := by
    rw [hu0]
    exact E.currentPrice_hasFDerivAt 0
  simpa only [Function.comp_def,matCLM_apply] using hc.comp_hasDerivAt (0 : ℝ) hu

theorem consumer_price_path_derivative (u : ℝ → Vec k) (z : Vec k)
    (hu0 : u 0 = 0) (hu : HasDerivAt u z 0) :
    HasDerivAt (fun t => E.prices (t,u t)) (E.b + E.C *ᵥ z) 0 := by
  have ht : HasDerivAt (fun t : ℝ => (t,u t)) (1,z) 0 :=
    HasDerivAt.prodMk (hasDerivAt_id (0 : ℝ)) hu
  have hc : HasFDerivAt E.prices E.priceChange (0,u 0) := by
    rw [hu0]
    exact E.prices_hasFDerivAt
  simpa only [Function.comp_def,E.priceChange_apply,one_smul,add_comm] using hc.comp_hasDerivAt (0 : ℝ) ht

theorem zero_relative_dimension (E0 : Model n 0) (h : E0.DemandC1)
    (hK : E0.K.PosDef) (s0 t : ℝ) : E0.localPricePath h hK s0 t = 0 :=
  Subsingleton.elim _ _

/-- Along the constructed path consumer prices and quantities remain in any
specified benchmark neighborhoods, so a local implementation is sufficient. -/
theorem local_path_stays_local (h : E.DemandC1) (hK : E.K.PosDef) (s0 : ℝ)
    (P Q : Set (Vec n)) (hP : P ∈ 𝓝 E.p) (hQ : Q ∈ 𝓝 E.q) :
    ∀ᶠ t in 𝓝 (0 : ℝ), E.prices (t,E.localPricePath h hK s0 t) ∈ P ∧
      E.quantities (t,E.localPricePath h hK s0 t) ∈ Q := by
  have hu : ContinuousAt (fun t : ℝ => (t,E.localPricePath h hK s0 t)) 0 :=
    continuousAt_id.prodMk (E.localPricePath_contDiffAt h hK s0).continuousAt
  have ht : Tendsto (fun t : ℝ => (t,E.localPricePath h hK s0 t)) (𝓝 0) (𝓝 (0 : PolicyPrice k)) := by
    change Tendsto _ (𝓝 0) (𝓝 (0,0))
    simpa only [ContinuousAt,E.localPricePath_base] using hu
  have hp : Tendsto E.prices (𝓝 0) (𝓝 E.p) := by
    simpa only [ContinuousAt,E.prices_zero] using E.prices_contDiffAt.continuousAt
  have hq : Tendsto E.quantities (𝓝 0) (𝓝 E.q) := by
    simpa only [ContinuousAt,E.quantities_zero] using (E.quantities_contDiffAt h).continuousAt
  filter_upwards [(hp.comp ht) hP,(hq.comp ht) hQ] with t hp' hq'
  exact ⟨hp',hq'⟩

theorem quadratic_path_local_optimum (h : E.DemandC1) (hK : E.K.PosDef) (s0 : ℝ)
    (hD : E.D.PosDef) (haff : E.demand = affineDemand E.p E.q E.D)
    (utility : Vec n → ℝ) (c : ℝ) (U : Set (Vec n)) (hU : U ∈ 𝓝 E.q)
    (hmatch : ∀ r ∈ U, utility r = c + quadraticUtility E.p E.D (r-E.q)) :
    ∀ᶠ t in 𝓝 (0 : ℝ),
      let v := E.prices (t,E.localPricePath h hK s0 t)
      let r := E.quantities (t,E.localPricePath h hK s0 t)
      r ∈ U ∧ (∀ a ∈ U, utility a - dotProduct v a ≤ utility r - dotProduct v r) ∧
      (∀ a ∈ U, a ≠ r → utility a - dotProduct v a < utility r - dotProduct v r) := by
  have hu : ContinuousAt (fun t : ℝ => (t,E.localPricePath h hK s0 t)) 0 :=
    continuousAt_id.prodMk (E.localPricePath_contDiffAt h hK s0).continuousAt
  have ht : Tendsto (fun t : ℝ => (t,E.localPricePath h hK s0 t)) (𝓝 0) (𝓝 (0 : PolicyPrice k)) := by
    change Tendsto _ (𝓝 0) (𝓝 (0,0))
    simpa only [ContinuousAt,E.localPricePath_base] using hu
  have hp : Tendsto E.prices (𝓝 0) (𝓝 E.p) := by
    simpa only [ContinuousAt,E.prices_zero] using E.prices_contDiffAt.continuousAt
  have hh := (hp.comp ht).eventually (local_utility_optimum E.p E.q E.D hD utility c U hU hmatch)
  filter_upwards [hh] with t ht'
  simpa only [quantities,haff,Function.comp_apply] using ht'
end Model

namespace Example
open Supply.Example

theorem model_demandC1 : model.DemandC1 :=
  Model.ofAffine_demandC1 frame ones ones (path (1/2)) 1 ![1,0] 1
    ones_pos frame_price_pos (path_mem (by norm_num) (by norm_num)).1

/-- A nonempty interior example of the nonlinear theorem at Cobb--Douglas sigma=1. -/
theorem concrete_local_existence :
    ∃ u : ℝ → Vec 1, ∃ s : ℝ → ℝ, model.PositiveLocalPath 1 u s ∧
      HasDerivAt u ![-1/4] 0 ∧ HasDerivAt s 1 0 ∧
      HasDerivAt (fun t => model.quantities (t,u t)) ![-7/8,-1/8] 0 := by
  have hh := model.economic_local_existence model_demandC1 parent 0 model_report ones_pos
    model_total_pos Matrix.PosDef.one (by norm_num [model,Model.ofAffine]) 1 (by norm_num)
  simpa only [concrete_solution.1,concrete_solution.2.1,concrete_solution.2.2] using hh
end Example
end CommodityClassification.Equilibrium
