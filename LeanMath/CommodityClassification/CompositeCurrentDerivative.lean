module

public import LeanMath.CommodityClassification.CompositeCostEconomicConnection

/-! Differentiate the actual composite at every positive current factor price. -/
@[expose] public section
noncomputable section
set_option maxHeartbeats 600000
namespace CommodityClassification.Composite.Data
open Matrix InputCoordinates
open scoped BigOperators
variable {n f : ℕ} (e : Composite.Data n f)

def currentCostDerivative (w : Vec f) : Vec f →L[ℝ] Vec n :=
  ContinuousLinearMap.pi (fun i => CESCost.weightedLinear
    (fun j => CESCost.pricePartial ((e.costData i).cost e.sigma) j w))

theorem costs_current_derivative {w : Vec f} (hw : ∀j,0<w j) :
    HasFDerivAt e.costs (e.currentCostDerivative w) w :=
  hasFDerivAt_pi.mpr (fun i => (e.costData i).hasFDerivAt_cost_current e.sigma hw)

theorem currentCostDerivative_single (w : Vec f) (j : Fin f) (i : Fin n) :
    e.currentCostDerivative w (Pi.single j 1) i=
      CESCost.pricePartial ((e.costData i).cost e.sigma) j w :=
  CESCost.weightedLinear_single _ j

theorem compositeCost_current_derivative {w : Vec f} (hw : ∀j,0<w j) :
    HasFDerivAt e.compositeCost
      ((CESCost.weightedLinear (fun i => CESCost.pricePartial e.nest.expenditureIndex i
        (e.costs w))).comp (e.currentCostDerivative w)) w :=
  (e.nest.expenditureData.hasFDerivAt_cost_current e.nest.eta (e.costs_positive hw)).comp w
    (e.costs_current_derivative hw)

theorem compositeCost_current_partial {w : Vec f} (hw : ∀j,0<w j) (j : Fin f) :
    CESCost.pricePartial e.compositeCost j w=
      ∑i,CESCost.pricePartial e.nest.expenditureIndex i (e.costs w)*
        CESCost.pricePartial ((e.costData i).cost e.sigma) j w := by
  rw [CESCost.pricePartial,(e.compositeCost_current_derivative hw).fderiv,
    ContinuousLinearMap.comp_apply,CESCost.weightedLinear_apply]
  exact Finset.sum_congr rfl (fun i _ => congrArg
    (fun x => CESCost.pricePartial e.nest.expenditureIndex i (e.costs w)*x)
      (e.currentCostDerivative_single w j i))

end CommodityClassification.Composite.Data
