module
public import LeanMath.CommodityClassification.EquilibriumLocalApplication
@[expose] public section
set_option maxHeartbeats 2000000
namespace CommodityClassification.Equilibrium
open Matrix Filter
open scoped BigOperators Topology
variable {n k : ℕ}

/-- Local compatibility between demand and marginal utility. -/
def Model.UtilityCompatible (E : Model n k) (utility : Vec n → ℝ) : Prop :=
  ∀ᶠ v in 𝓝 E.p, HasFDerivAt utility (CESCost.weightedLinear v) (E.demand v)

theorem shifted_quadratic_derivative (p q : Vec n) (D : Mat n n) (hD : D.PosDef)
    (c : ℝ) (r : Vec n) :
    HasFDerivAt (fun a => c + quadraticUtility p D (a-q))
      (CESCost.weightedLinear (p-D⁻¹ *ᵥ (r-q))) r := by
  have hh := (quadraticUtility_derivative p D hD (r-q)).comp r
    ((hasFDerivAt_id r).sub_const q)
  simpa using hh.const_add c

theorem local_quadratic_derivative (p q : Vec n) (D : Mat n n) (hD : D.PosDef)
    (utility : Vec n → ℝ) (c : ℝ) (U : Set (Vec n)) (hU : IsOpen U)
    (hmatch : ∀ r ∈ U, utility r = c + quadraticUtility p D (r-q))
    {r : Vec n} (hr : r ∈ U) :
    HasFDerivAt utility (CESCost.weightedLinear (p-D⁻¹ *ᵥ (r-q))) r := by
  apply (shifted_quadratic_derivative p q D hD c r).congr_of_eventuallyEq
  filter_upwards [hU.mem_nhds hr] with a ha
  exact hmatch a ha

theorem local_quadratic_demand_compatible (p q : Vec n) (D : Mat n n) (hD : D.PosDef)
    (utility : Vec n → ℝ) (c : ℝ) (U : Set (Vec n)) (hU : U ∈ 𝓝 q)
    (hmatch : ∀ r ∈ U, utility r = c + quadraticUtility p D (r-q)) :
    ∀ᶠ v in 𝓝 p, HasFDerivAt utility (CESCost.weightedLinear v) (affineDemand p q D v) := by
  obtain ⟨O,hOU,hO,hq⟩ := mem_nhds_iff.mp hU
  filter_upwards [affineDemand_local p q D O (hO.mem_nhds hq)] with v hv
  have hd := local_quadratic_derivative p q D hD utility c O hO
    (fun r hr => hmatch r (hOU hr)) hv
  have he : p-D⁻¹ *ᵥ (affineDemand p q D v-q) = v := by
    rw [affineDemand_eq_choice]
    have hsub : q+quadraticChoice p D v-q = quadraticChoice p D v := by abel
    rw [hsub,quadraticChoice_foc p v D hD]
    abel
  rwa [he] at hd

theorem Model.quadratic_utility_compatible (E : Model n k) (hD : E.D.PosDef)
    (haff : E.demand = affineDemand E.p E.q E.D)
    (utility : Vec n → ℝ) (c : ℝ) (U : Set (Vec n)) (hU : U ∈ 𝓝 E.q)
    (hmatch : ∀ r ∈ U, utility r = c + quadraticUtility E.p E.D (r-E.q)) :
    E.UtilityCompatible utility := by
  unfold Model.UtilityCompatible
  rw [haff]
  exact local_quadratic_demand_compatible E.p E.q E.D hD utility c U hU hmatch

/-- Surplus optimality implies household optimality with fixed income and transfer.
Even weak budget feasibility suffices because the numeraire enters linearly. -/
theorem household_optimum_of_surplus (utility : Vec n → ℝ) (v Q : Vec n)
    (s income : ℝ) (U : Set (Vec n))
    (hbudget : dotProduct v Q+s=income)
    (hmax : ∀ r ∈ U, utility r-dotProduct v r ≤ utility Q-dotProduct v Q) :
    ∀ r ∈ U, ∀ z : ℝ, dotProduct v r+z ≤ income → utility r+z ≤ utility Q+s := by
  intro r hr z hb
  have hh := hmax r hr
  linarith

theorem household_strict_of_surplus (utility : Vec n → ℝ) (v Q : Vec n)
    (s income : ℝ) (U : Set (Vec n))
    (hbudget : dotProduct v Q+s=income)
    (hmax : ∀ r ∈ U, r ≠ Q → utility r-dotProduct v r < utility Q-dotProduct v Q) :
    ∀ r ∈ U, ∀ z : ℝ, r ≠ Q → dotProduct v r+z ≤ income → utility r+z < utility Q+s := by
  intro r hr z hne hb
  have hh := hmax r hr hne
  linarith

end CommodityClassification.Equilibrium
