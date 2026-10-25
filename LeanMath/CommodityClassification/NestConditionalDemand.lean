module

public import LeanMath.CommodityClassification.NestPositiveExpenditure
public import Mathlib.Analysis.Calculus.LocalExtr.Basic

/-! Conditional demand as the derivative of the actual attained expenditure. -/
@[expose] public section
noncomputable section
set_option maxHeartbeats 2400000
namespace CommodityClassification.DemandNest.Data
open Matrix Filter
open scoped Topology BigOperators
variable {n : ℕ} (d : DemandNest.Data n)

theorem positive_optimum_support {r x : Vec n}
    (hx : ∀ i,0<x i) (hF : 1≤d.quantityIndex x)
    (hcost : dotProduct r x=d.expenditureIndex r) {v : Vec n} (hv : ∀i,0<v i) :
    dotProduct r x-d.expenditureIndex r ≤ dotProduct v x-d.expenditureIndex v := by
  have h := d.positive_dual_inequality hv hx
  have hp := d.expenditure_positive hv
  rw [hcost]
  nlinarith

theorem positive_optimum_localMin {r x : Vec n} (hr : ∀i,0<r i)
    (hx : ∀i,0<x i) (hF : 1≤d.quantityIndex x)
    (hcost : dotProduct r x=d.expenditureIndex r) :
    IsLocalMin (fun v => dotProduct v x-d.expenditureIndex v) r := by
  filter_upwards [CESCost.positivePrices_open.mem_nhds hr] with v hv
  exact d.positive_optimum_support hx hF hcost hv

theorem positive_optimum_eq_gradient {r x : Vec n} (hr : ∀i,0<r i)
    (hx : ∀i,0<x i) (hF : 1≤d.quantityIndex x)
    (hcost : dotProduct r x=d.expenditureIndex r) :
    x=fun i => CESCost.pricePartial d.expenditureIndex i r := by
  have hlin : HasFDerivAt (fun v : Vec n => dotProduct v x) (CESCost.weightedLinear x) r := by
    convert (CESCost.weightedLinear x).hasFDerivAt (x := r) using 1
    funext v
    exact (dotProduct_comm v x).trans (CESCost.weightedLinear_apply x v).symm
  have hP : HasFDerivAt d.expenditureIndex
      (CESCost.weightedLinear (fun i => CESCost.pricePartial d.expenditureIndex i r)) r :=
    d.expenditureData.hasFDerivAt_cost_current d.eta hr
  have hzero := (d.positive_optimum_localMin hr hx hF hcost).hasFDerivAt_eq_zero
    (hlin.sub hP)
  funext i
  have hi := congrArg (fun L : Vec n →L[ℝ] ℝ => L (Pi.single i 1)) hzero
  simpa only [_root_.sub_apply,_root_.zero_apply,
    CESCost.weightedLinear_single,sub_eq_zero] using hi

theorem unitBundle_eq_gradient {r : Vec n} (hr : ∀i,0<r i) :
    d.unitBundle r=fun i => CESCost.pricePartial d.expenditureIndex i r :=
  d.positive_optimum_eq_gradient hr (d.unitBundle_positive hr)
    (d.unitBundle_quantity hr).ge (d.unitBundle_expenditure hr)

theorem positive_optimum_unique {r x : Vec n} (hr : ∀i,0<r i)
    (hx : ∀i,0<x i) (hF : 1≤d.quantityIndex x)
    (hcost : dotProduct r x=d.expenditureIndex r) : x=d.unitBundle r :=
  (d.positive_optimum_eq_gradient hr hx hF hcost).trans (d.unitBundle_eq_gradient hr).symm

theorem unitBundle_benchmark : d.unitBundle d.p=fun i => d.q i/d.sales := by
  rw [d.unitBundle_eq_gradient d.hp]
  funext i
  exact d.expenditure_gradient i

end CommodityClassification.DemandNest.Data
