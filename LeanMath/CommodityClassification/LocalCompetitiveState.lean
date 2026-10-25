module
public import LeanMath.CommodityClassification.WelfareFixedAnswerBridge
@[expose] public section
set_option maxHeartbeats 2400000
namespace CommodityClassification.Equilibrium
open Matrix Filter
open scoped BigOperators Topology
variable {n k : ℕ}
namespace Model
variable (E : Model n k)

/-- Competitive implementation at one tax-price state. Producer prices are
costs; consumer prices include tau*b. Household income holds the equilibrium
lump-sum rebate fixed when comparing alternative consumption. U specifies
the scope of household comparison (univ for the canonical continuation). -/
structure CompetitiveState (utility : Vec n → ℝ) (U : Set (Vec n))
    (abar : Vec (k+1)) (y : PolicyPrice k) (s : ℝ) : Prop where
  positive : E.PositiveState y s
  producer_prices_positive : ∀i,0<E.costs (E.currentPrice y.2) i
  consumer_price_rule : E.prices y=E.costs (E.currentPrice y.2)+y.1 • E.b
  numeraire_normalized : dotProduct E.frame.a0 (E.currentPrice y.2)=1
  commodity_feasible : ∀i,E.ProductionFeasible i (E.quantities y i)
    (E.quantities y i • E.currentInputs (E.currentPrice y.2) i)
  commodity_profit : ∀i,E.costs (E.currentPrice y.2) i*E.quantities y i-
    dotProduct (E.currentPrice y.2) (E.quantities y i • E.currentInputs (E.currentPrice y.2) i)=0
  commodity_optimal : ∀i z x,E.ProductionFeasible i z x →
    E.costs (E.currentPrice y.2) i*z-dotProduct (E.currentPrice y.2) x≤0
  numeraire_feasible : Production.FixedFeasible E.frame.a0 s (s • E.frame.a0)
  numeraire_profit : s-dotProduct (E.currentPrice y.2) (s • E.frame.a0)=0
  numeraire_optimal : ∀z x,Production.FixedFeasible E.frame.a0 z x →
    z-dotProduct (E.currentPrice y.2) x≤0
  clearing : E.excess abar (y,s)=0
  budget : dotProduct (E.prices y) (E.quantities y)+s=E.householdIncome abar y
  quantity_in_domain : E.quantities y ∈ U
  household_optimal : ∀r∈U,(∀i,0≤r i) → ∀z : ℝ,0≤z →
    dotProduct (E.prices y) r+z≤E.householdIncome abar y →
      utility r+z≤utility (E.quantities y)+s

theorem competitive_of_household (hσ : 0<E.sigma) (ha : ∀j,0≤E.frame.a0 j)
    (utility : Vec n → ℝ) (U : Set (Vec n)) (abar : Vec (k+1)) (y : PolicyPrice k) (s : ℝ)
    (hpos : E.PositiveState y s) (hc : E.excess abar (y,s)=0) (hU : E.quantities y∈U)
    (hopt : ∀r∈U,∀z : ℝ,dotProduct (E.prices y) r+z≤E.householdIncome abar y →
      utility r+z≤utility (E.quantities y)+s) :
    E.CompetitiveState utility U abar y s := by
  have hn := E.numeraire_production_certificate ha hpos.1 hpos.2.2.2.1.le
  refine ⟨hpos,?_,rfl,E.currentPrice_normalized y.2,?_,?_,?_,hn.1,hn.2.2.2,
    hn.2.2.1,hc,E.household_budget hpos.1 hc,hU,?_⟩
  · intro i
    exact (E.costData i).cost_pos E.sigma hpos.1
  · intro i
    exact (E.current_production_certificate hσ hpos.1 i (hpos.2.2.1 i).le).1
  · intro i
    exact (E.current_production_certificate hσ hpos.1 i (hpos.2.2.1 i).le).2.2.2.2
  · intro i
    exact (E.current_production_certificate hσ hpos.1 i (hpos.2.2.1 i).le).2.2.2.1
  · intro r hr _ z _ hb
    exact hopt r hr z hb

theorem competitive_of_surplus (hσ : 0<E.sigma) (ha : ∀j,0≤E.frame.a0 j)
    (utility : Vec n → ℝ) (U : Set (Vec n)) (abar : Vec (k+1)) (y : PolicyPrice k) (s : ℝ)
    (hpos : E.PositiveState y s) (hc : E.excess abar (y,s)=0) (hU : E.quantities y∈U)
    (hopt : ∀r∈U,utility r-dotProduct (E.prices y) r ≤
      utility (E.quantities y)-dotProduct (E.prices y) (E.quantities y)) :
    E.CompetitiveState utility U abar y s :=
  E.competitive_of_household hσ ha utility U abar y s hpos hc hU
    (household_optimum_of_surplus utility _ _ _ _ U (E.household_budget hpos.1 hc) hopt)

theorem canonical_competitive_state (hσ : 0<E.sigma) (ha : ∀j,0≤E.frame.a0 j)
    (hD : E.D.PosDef) (haff : E.demand=affineDemand E.p E.q E.D)
    (c : ℝ) (abar : Vec (k+1)) (y : PolicyPrice k) (s : ℝ)
    (hpos : E.PositiveState y s) (hc : E.excess abar (y,s)=0) :
    E.CompetitiveState (benchmarkUtility E.p E.q E.D c) Set.univ abar y s := by
  apply E.competitive_of_surplus hσ ha _ _ abar y s hpos hc (Set.mem_univ _)
  intro r _
  simpa only [quantities,haff] using benchmarkUtility_surplus_maximum E.p E.q (E.prices y) r E.D hD c

theorem quadratic_neighborhood_competitive (hσ : 0<E.sigma) (ha : ∀j,0≤E.frame.a0 j)
    (s0 : ℝ) (utility : Vec n → ℝ) (U : Set (Vec n)) (u : ℝ → Vec k) (s : ℝ → ℝ)
    (h : E.QuadraticWelfareNeighborhood s0 utility U u s) :
    ∃I : Set ℝ,IsOpen I ∧ 0∈I ∧ ∀t∈I,
      E.CompetitiveState utility U (E.endowment s0) (t,u t) (s t) := by
  obtain ⟨I,hIo,hI0,hI⟩ := h
  refine ⟨I,hIo,hI0,?_⟩
  intro t ht
  have hw := (hI t ht).1
  have hh := (hI t ht).2
  exact E.competitive_of_household hσ ha utility U (E.endowment s0) (t,u t) (s t)
    hw.2.1 hw.1 hh.1 hh.2.1

end Model
end CommodityClassification.Equilibrium
