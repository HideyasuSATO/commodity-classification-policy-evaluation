module
public import LeanMath.CommodityClassification.CommonBenchmarkUtility
public import LeanMath.CommodityClassification.CESProductionApplication
@[expose] public section
set_option maxHeartbeats 2400000
namespace CommodityClassification.Equilibrium
open Matrix Filter
open scoped BigOperators Topology
variable {n k : ℕ}
namespace Model
variable (E : Model n k)

/-- An explicit zero-tax benchmark equilibrium certificate. Household choice is
over nonnegative quantities and numeraire with a weak budget constraint.
Commodity technology varies with E; utility and endowment are explicit inputs. -/
structure BenchmarkEquilibrium (utility : Vec n → ℝ) (abar : Vec (k+1)) (s0 : ℝ) : Prop where
  quantities_positive : ∀i,0<E.q i
  numeraire_positive : 0<s0
  commodity_feasible : ∀i,E.ProductionFeasible i (E.q i) (E.q i • E.A i)
  commodity_profit : ∀i,E.p i*E.q i-dotProduct E.frame.w (E.q i • E.A i)=0
  commodity_optimal : ∀i y x,E.ProductionFeasible i y x → E.p i*y-dotProduct E.frame.w x≤0
  numeraire_feasible : Production.FixedFeasible E.frame.a0 s0 (s0 • E.frame.a0)
  numeraire_profit : s0-dotProduct E.frame.w (s0 • E.frame.a0)=0
  numeraire_optimal : ∀y x,Production.FixedFeasible E.frame.a0 y x → y-dotProduct E.frame.w x≤0
  clearing : E.A.transpose *ᵥ E.q+s0 • E.frame.a0=abar
  budget : dotProduct E.p E.q+s0=dotProduct E.frame.w abar
  household_optimal : ∀r : Vec n, (∀i,0≤r i) → ∀z : ℝ,0≤z →
    dotProduct E.p r+z≤dotProduct E.frame.w abar → utility r+z≤utility E.q+s0

theorem endowment_positive (hq : ∀i,0≤E.q i) (ha : ∀j,0<E.frame.a0 j)
    {s0 : ℝ} (hs : 0<s0) : ∀j,0<E.endowment s0 j := by
  intro j
  have hn : 0 ≤ (E.A.transpose *ᵥ E.q) j := by
    change 0 ≤ ∑i,E.A i j*E.q i
    apply Finset.sum_nonneg
    intro i _
    exact mul_nonneg (E.hC i j).le (hq i)
  exact add_pos_of_nonneg_of_pos hn (mul_pos hs (ha j))

theorem benchmark_budget (s0 : ℝ) :
    dotProduct E.p E.q+s0=dotProduct E.frame.w (E.endowment s0) := by
  have hh := E.household_budget (abar := E.endowment s0) (y := 0) (s := s0)
    (by change E.currentPrice 0 ∈ CESCost.PositivePrices (k+1); rw [E.currentPrice_zero]; exact E.hw) (E.excess_base s0)
  simpa [householdIncome,taxTransfer] using hh

theorem benchmark_equilibrium (hD : E.D.PosDef) (hσ : 0<E.sigma)
    (hq : ∀i,0<E.q i) (ha : ∀j,0≤E.frame.a0 j) {s0 : ℝ} (hs : 0<s0) (c : ℝ) :
    E.BenchmarkEquilibrium (benchmarkUtility E.p E.q E.D c) (E.endowment s0) s0 := by
  have hn := E.numeraire_production_certificate ha (u := 0)
    (by rw [E.currentPrice_zero]; exact E.hw) hs.le
  simp only [E.currentPrice_zero] at hn
  refine ⟨hq,hs,?_,?_,?_,hn.1,hn.2.2.2,hn.2.2.1,rfl,E.benchmark_budget s0,?_⟩
  · intro i
    exact (E.benchmark_production_certificate hσ i (hq i).le).1
  · intro i
    exact (E.benchmark_production_certificate hσ i (hq i).le).2.2.2.2
  · intro i
    exact (E.benchmark_production_certificate hσ i (hq i).le).2.2.2.1
  · intro r _ z _ hb
    have hh := benchmarkUtility_household E.p E.q E.p E.D hD c s0
      (dotProduct E.frame.w (E.endowment s0))
    simpa only [affineDemand_base] using
      hh (by simpa only [affineDemand_base] using E.benchmark_budget s0) r z hb

theorem benchmark_zero_tax (s0 : ℝ) :
    E.taxTransfer 0=0 ∧ E.householdIncome (E.endowment s0) 0=dotProduct E.frame.w (E.endowment s0) := by
  simp [taxTransfer,householdIncome]

theorem benchmark_physical_clearing (s0 : ℝ) : E.excess (E.endowment s0) (0,s0)=0 :=
  E.excess_base s0

end Model
end CommodityClassification.Equilibrium
