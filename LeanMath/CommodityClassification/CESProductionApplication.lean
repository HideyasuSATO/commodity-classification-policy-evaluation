module
public import LeanMath.CommodityClassification.FixedInputProduction
public import LeanMath.CommodityClassification.EquilibriumConsistency
@[expose] public section
namespace CommodityClassification.Equilibrium
open Matrix
open scoped BigOperators
variable {n k : ℕ}

namespace Model
variable (E : Model n k)

def ProductionFeasible (i : Fin n) (y : ℝ) (x : Vec (k+1)) : Prop :=
  (E.costData i).Feasible E.sigma y x

theorem currentInputs_optimalInput (i : Fin n) (w : Vec (k+1)) (y : ℝ) :
    (E.costData i).optimalInput E.sigma w y = y • E.currentInputs w i := rfl

theorem current_production_certificate (hs : 0 < E.sigma)
    {w : Vec (k+1)} (hw : w ∈ CESCost.PositivePrices (k+1)) (i : Fin n)
    {y : ℝ} (hy : 0 ≤ y) :
    E.ProductionFeasible i y (y • E.currentInputs w i) ∧
    dotProduct w (y • E.currentInputs w i)=y*E.costs w i ∧
    IsLeast {e : ℝ | ∃x, E.ProductionFeasible i y x ∧ dotProduct w x=e} (y*E.costs w i) ∧
    (∀z x, E.ProductionFeasible i z x → E.costs w i*z-dotProduct w x ≤ 0) ∧
    E.costs w i*y-dotProduct w (y • E.currentInputs w i)=0 := by
  exact ⟨(E.costData i).optimalInput_feasible hs hw hy,
    (E.costData i).optimalInput_expenditure E.sigma hw y,
    (E.costData i).production_cost_isLeast hs hw hy,
    fun z x h => (E.costData i).feasible_profit_nonpos E.sigma hw h,
    (E.costData i).optimalInput_profit_zero E.sigma hw y⟩

theorem benchmark_production_certificate (hs : 0 < E.sigma) (i : Fin n) (hq : 0 ≤ E.q i) :
    E.ProductionFeasible i (E.q i) (E.q i • E.A i) ∧
    dotProduct E.frame.w (E.q i • E.A i)=E.q i*E.p i ∧
    IsLeast {e : ℝ | ∃x, E.ProductionFeasible i (E.q i) x ∧ dotProduct E.frame.w x=e} (E.q i*E.p i) ∧
    (∀z x, E.ProductionFeasible i z x → E.p i*z-dotProduct E.frame.w x ≤ 0) ∧
    E.p i*E.q i-dotProduct E.frame.w (E.q i • E.A i)=0 := by
  simpa only [E.inputs_base,E.costs_base] using E.current_production_certificate hs E.hw i hq

/-- Production implementation with positive numeraire inputs. -/
theorem numeraire_production_certificate (ha : ∀j, 0 ≤ E.frame.a0 j)
    {u : Vec k} (hw : E.currentPrice u ∈ CESCost.PositivePrices (k+1))
    {y : ℝ} (hy : 0 ≤ y) :
    Production.FixedFeasible E.frame.a0 y (y • E.frame.a0) ∧
    dotProduct (E.currentPrice u) (y • E.frame.a0)=y ∧
    (∀z x, Production.FixedFeasible E.frame.a0 z x → z-dotProduct (E.currentPrice u) x ≤ 0) ∧
    y-dotProduct (E.currentPrice u) (y • E.frame.a0)=0 :=
  Production.numeraire_certificate ha (fun j => (hw j).le) (E.currentPrice_normalized u) hy

end Model

namespace Example
theorem concrete_production (i : Fin 2) :
    model.ProductionFeasible i (model.q i) (model.q i • model.A i) ∧
    dotProduct model.frame.w (model.q i • model.A i)=model.q i*model.p i ∧
    IsLeast {e : ℝ | ∃x, model.ProductionFeasible i (model.q i) x ∧ dotProduct model.frame.w x=e}
      (model.q i*model.p i) ∧
    (∀z x, model.ProductionFeasible i z x → model.p i*z-dotProduct model.frame.w x ≤ 0) ∧
    model.p i*model.q i-dotProduct model.frame.w (model.q i • model.A i)=0 :=
  model.benchmark_production_certificate (by norm_num [model,Model.ofAffine]) i (ones_pos i).le

theorem concrete_numeraire {y : ℝ} (hy : 0 ≤ y) :
    Production.FixedFeasible model.frame.a0 y (y • model.frame.a0) ∧
    dotProduct model.frame.w (y • model.frame.a0)=y ∧
    (∀z x, Production.FixedFeasible model.frame.a0 z x → z-dotProduct model.frame.w x ≤ 0) ∧
    y-dotProduct model.frame.w (y • model.frame.a0)=0 := by
  have ha : ∀j, 0 ≤ model.frame.a0 j := by
    intro j; fin_cases j <;> norm_num [model,Model.ofAffine,Supply.Example.frame]
  simpa only [model.currentPrice_zero] using
    model.numeraire_production_certificate ha (u := 0) (by rw [model.currentPrice_zero]; exact model.hw) hy
end Example
end CommodityClassification.Equilibrium
