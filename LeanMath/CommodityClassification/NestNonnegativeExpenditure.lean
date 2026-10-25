module

public import LeanMath.CommodityClassification.NestNonnegativeIndex

/-! Attainment and conditional demand on the nonnegative primal domain. -/
@[expose] public section
noncomputable section
set_option maxHeartbeats 2400000
namespace CommodityClassification.DemandNest.Data
open Matrix Filter
open scoped Topology BigOperators
variable {n : ℕ} (d : DemandNest.Data n)

theorem unitBundle_extended_quantity {r : Vec n} (hr : ∀i,0<r i) :
    d.quantityOnNonnegative (d.unitBundle r)=1 := by
  rw [d.quantityOnNonnegative_of_positive (d.unitBundle_positive hr),d.unitBundle_quantity hr]

theorem nonnegative_unit_expenditure_isLeast {r : Vec n} (hr : ∀i,0<r i) :
    IsLeast {v : ℝ | ∃x : Vec n,(∀i,0≤x i) ∧ 1≤d.quantityOnNonnegative x ∧ v=dotProduct r x}
      (d.expenditureIndex r) := by
  constructor
  · exact ⟨d.unitBundle r,fun i => (d.unitBundle_positive hr i).le,
      (d.unitBundle_extended_quantity hr).ge,(d.unitBundle_expenditure hr).symm⟩
  · rintro v ⟨x,hx,hF,rfl⟩
    have hl := d.nonnegative_dual_inequality hr hx
    have hp := d.expenditure_positive hr
    nlinarith

theorem nonnegative_optimum_eq_gradient {r x : Vec n} (hr : ∀i,0<r i)
    (hx : ∀i,0≤x i) (hF : 1≤d.quantityOnNonnegative x)
    (hcost : dotProduct r x=d.expenditureIndex r) :
    x=fun i => CESCost.pricePartial d.expenditureIndex i r := by
  have hmin : IsLocalMin (fun v : Vec n => dotProduct v x-d.expenditureIndex v) r := by
    filter_upwards [CESCost.positivePrices_open.mem_nhds hr] with v hv
    have hl := d.nonnegative_dual_inequality hv hx
    have hp := d.expenditure_positive hv
    rw [hcost]
    nlinarith
  have hlin : HasFDerivAt (fun v : Vec n => dotProduct v x) (CESCost.weightedLinear x) r := by
    convert (CESCost.weightedLinear x).hasFDerivAt (x := r) using 1
    funext v
    exact (dotProduct_comm v x).trans (CESCost.weightedLinear_apply x v).symm
  have hP : HasFDerivAt d.expenditureIndex
      (CESCost.weightedLinear (fun i => CESCost.pricePartial d.expenditureIndex i r)) r :=
    d.expenditureData.hasFDerivAt_cost_current d.eta hr
  have hzero := hmin.hasFDerivAt_eq_zero (hlin.sub hP)
  funext i
  have hi := congrArg (fun L : Vec n →L[ℝ] ℝ => L (Pi.single i 1)) hzero
  simpa only [_root_.sub_apply,_root_.zero_apply,CESCost.weightedLinear_single,sub_eq_zero] using hi

theorem nonnegative_optimum_unique {r x : Vec n} (hr : ∀i,0<r i)
    (hx : ∀i,0≤x i) (hF : 1≤d.quantityOnNonnegative x)
    (hcost : dotProduct r x=d.expenditureIndex r) : x=d.unitBundle r :=
  (d.nonnegative_optimum_eq_gradient hr hx hF hcost).trans (d.unitBundle_eq_gradient hr).symm

theorem nonnegative_optimum_positive {r x : Vec n} (hr : ∀i,0<r i)
    (hx : ∀i,0≤x i) (hF : 1≤d.quantityOnNonnegative x)
    (hcost : dotProduct r x=d.expenditureIndex r) : ∀i,0<x i := by
  rw [d.nonnegative_optimum_unique hr hx hF hcost]
  exact d.unitBundle_positive hr

end CommodityClassification.DemandNest.Data
