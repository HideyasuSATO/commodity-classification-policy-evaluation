module

public import LeanMath.CommodityClassification.CompositeCostData

/-! Attained optimized expenditure and actual first derivative of the composite. -/
@[expose] public section
noncomputable section
set_option maxHeartbeats 600000
namespace CommodityClassification.Composite.Data
open Matrix InputCoordinates
variable {n f : ℕ} (e : Composite.Data n f)

theorem compositeCost_positive {w : Vec f} (hw : ∀j,0<w j) : 0<e.compositeCost w :=
  e.nest.expenditure_positive (e.costs_positive hw)

theorem compositeCost_isLeast {w : Vec f} (hw : ∀j,0<w j) :
    IsLeast {v : ℝ | ∃x : Vec n,(∀i,0≤x i) ∧ 1≤e.nest.quantityOnNonnegative x ∧
      v=dotProduct (e.costs w) x} (e.compositeCost w) :=
  e.nest.nonnegative_unit_expenditure_isLeast (e.costs_positive hw)

theorem compositeMix_positive {w : Vec f} (hw : ∀j,0<w j) : ∀i,0<e.compositeMix w i :=
  e.nest.unitBundle_positive (e.costs_positive hw)

theorem compositeMix_quantity {w : Vec f} (hw : ∀j,0<w j) :
    e.nest.quantityOnNonnegative (e.compositeMix w)=1 :=
  e.nest.unitBundle_extended_quantity (e.costs_positive hw)

theorem compositeMix_cost {w : Vec f} (hw : ∀j,0<w j) :
    dotProduct (e.costs w) (e.compositeMix w)=e.compositeCost w :=
  e.nest.unitBundle_expenditure (e.costs_positive hw)

theorem compositeMix_unique {w : Vec f} (hw : ∀j,0<w j) {x : Vec n}
    (hx : ∀i,0≤x i) (hF : 1≤e.nest.quantityOnNonnegative x)
    (hc : dotProduct (e.costs w) x=e.compositeCost w) : x=e.compositeMix w :=
  e.nest.nonnegative_optimum_unique (e.costs_positive hw) hx hF hc

theorem compositeCost_benchmark : e.compositeCost e.w0=1 := by
  rw [compositeCost,e.costs_benchmark,e.nest.expenditure_benchmark]

theorem compositeMix_benchmark : e.compositeMix e.w0=fun i => e.nest.q i/e.nest.sales := by
  rw [compositeMix,e.costs_benchmark,e.nest.unitBundle_benchmark]

theorem compositeCost_smooth {w : Vec f} (hw : ∀j,0<w j) :
    ContDiffAt ℝ ⊤ e.compositeCost w :=
  (e.nest.expenditure_smooth (e.costs_positive hw)).comp w (e.costs_smooth hw)

theorem compositeCost_derivative :
    HasFDerivAt e.compositeCost (CESCost.weightedLinear e.meanInputs) e.w0 := by
  have he : HasFDerivAt e.nest.expenditureIndex
      (CESCost.weightedLinear (fun i => e.nest.q i/e.nest.sales)) (e.costs e.w0) := by
    rw [e.costs_benchmark]
    exact e.nest.expenditure_derivative
  have hh := he.comp e.w0 e.costs_derivative
  have hL : (CESCost.weightedLinear (fun i => e.nest.q i/e.nest.sales)).comp e.costDerivative=
      CESCost.weightedLinear e.meanInputs := by
    apply ContinuousLinearMap.ext
    intro v
    simp only [ContinuousLinearMap.comp_apply,CESCost.weightedLinear_apply,e.costDerivative_apply]
    exact (e.meanInputs_apply v).symm
  rw [hL] at hh
  exact hh

theorem compositeCost_gradient (j : Fin f) :
    CESCost.pricePartial e.compositeCost j e.w0=e.meanInputs j := by
  rw [CESCost.pricePartial,e.compositeCost_derivative.fderiv,CESCost.weightedLinear_single]

end CommodityClassification.Composite.Data
