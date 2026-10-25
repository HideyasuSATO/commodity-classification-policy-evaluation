module

public import LeanMath.CommodityClassification.NestDualRay

/-! The Cobb branch and the common supporting gradient for all positive elasticities. -/
@[expose] public section
noncomputable section
set_option maxHeartbeats 2400000
namespace CommodityClassification.DemandNest.Data
open Matrix
open scoped BigOperators
variable {n : ℕ} (d : DemandNest.Data n)

theorem dualRay_logSum (hη : d.eta=1) {r : Vec n} (hr : ∀i,0<r i) :
    d.quantityData.logSum (d.dualRay r)= -d.expenditureData.logSum r := by
  unfold CESCost.Data.logSum
  rw [←Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro i _
  rw [d.quantity_share,d.expenditure_share,d.dualRay_ratio]
  change d.share i*Real.log ((r i/d.p i)^(-d.eta))=
    -(d.share i*Real.log (r i/d.p i))
  rw [Real.log_rpow (div_pos (hr i) (d.hp i)),hη]
  ring

theorem dualRay_cobb_gradient (hη : d.eta=1) {r : Vec n} (hr : ∀i,0<r i) (i : Fin n) :
    CESCost.pricePartial d.quantityIndex i (d.dualRay r)=r i/d.expenditureIndex r := by
  have hi : 1/d.eta=1 := by rw [hη];norm_num
  have hpow : (d.quantityData.ratio (d.dualRay r) i)^(-(1 : ℝ))=r i/d.p i := by
    simpa only [hη,div_one] using d.dualRay_gradient_power hr i
  rw [quantityIndex,d.quantityData.cost_eq_cobb hi,
    d.quantityData.cobb_partial (d.dualRay_positive hr)]
  change d.p i*Real.exp (d.quantityData.logSum (d.dualRay r))*
    (d.quantityData.ratio (d.dualRay r) i)^(-(1 : ℝ))=_
  rw [d.dualRay_logSum hη hr,Real.exp_neg,hpow]
  have hP : d.expenditureIndex r=Real.exp (d.expenditureData.logSum r) := by
    rw [expenditureIndex,d.expenditureData.cost_eq_cobb hη]
    change 1*Real.exp (d.expenditureData.logSum r)=_
    ring
  rw [hP]
  field_simp [ne_of_gt (d.hp i)]

theorem dualRay_gradient {r : Vec n} (hr : ∀i,0<r i) (i : Fin n) :
    CESCost.pricePartial d.quantityIndex i (d.dualRay r)=r i/d.expenditureIndex r := by
  by_cases hη : d.eta=1
  · exact d.dualRay_cobb_gradient hη hr i
  · exact d.dualRay_ces_gradient hη hr i

end CommodityClassification.DemandNest.Data
