module

public import LeanMath.CommodityClassification.NestLiteralIndices

/-! A positive quantity ray whose primal gradient supports current expenditure. -/
@[expose] public section
noncomputable section
set_option maxHeartbeats 2400000
namespace CommodityClassification.DemandNest.Data
open Matrix
open scoped BigOperators
variable {n : ℕ} (d : DemandNest.Data n)

def dualRay (r : Vec n) (i : Fin n) : ℝ := d.q i*(r i/d.p i)^(-d.eta)

theorem dualRay_positive {r : Vec n} (hr : ∀i,0<r i) : ∀i,0<d.dualRay r i :=
  fun i => mul_pos (d.hq i) (Real.rpow_pos_of_pos (div_pos (hr i) (d.hp i)) _)

theorem dualRay_ratio (r : Vec n) (i : Fin n) :
    d.quantityData.ratio (d.dualRay r) i=(r i/d.p i)^(-d.eta) := by
  change (d.q i*(r i/d.p i)^(-d.eta))/d.q i=_
  field_simp [ne_of_gt (d.hq i)]

theorem dualRay_powerSum {r : Vec n} (hr : ∀i,0<r i) :
    d.quantityData.powerSum (1/d.eta) (d.dualRay r)=d.expenditureData.powerSum d.eta r := by
  unfold CESCost.Data.powerSum
  apply Finset.sum_congr rfl
  intro i _
  rw [d.quantity_share,d.expenditure_share,d.dualRay_ratio]
  change d.share i*((r i/d.p i)^(-d.eta))^(1-1/d.eta)=
    d.share i*(r i/d.p i)^(1-d.eta)
  rw [←Real.rpow_mul (div_pos (hr i) (d.hp i)).le]
  congr 2
  field_simp [ne_of_gt d.heta]
  ring

theorem dualRay_gradient_power {r : Vec n} (hr : ∀i,0<r i) (i : Fin n) :
    (d.quantityData.ratio (d.dualRay r) i)^(-(1/d.eta))=r i/d.p i := by
  rw [d.dualRay_ratio,←Real.rpow_mul (div_pos (hr i) (d.hp i)).le]
  have he : (-d.eta)*(-(1/d.eta))=1 := by field_simp [ne_of_gt d.heta]
  rw [he,Real.rpow_one]

theorem dualRay_ces_gradient (hη : d.eta≠1) {r : Vec n} (hr : ∀i,0<r i) (i : Fin n) :
    CESCost.pricePartial d.quantityIndex i (d.dualRay r)=r i/d.expenditureIndex r := by
  have hi : 1/d.eta≠1 := by
    intro he
    have h := (div_eq_iff (ne_of_gt d.heta)).mp he
    apply hη
    linarith
  rw [quantityIndex,d.quantityData.cost_eq_ces hi,
    d.quantityData.ces_partial (1/d.eta) hi (d.dualRay_positive hr)]
  change d.p i*(d.quantityData.powerSum (1/d.eta) (d.dualRay r))^(1/(1-1/d.eta)-1)*
    (d.quantityData.ratio (d.dualRay r) i)^(-(1/d.eta))=_
  rw [d.dualRay_powerSum hr,d.dualRay_gradient_power hr]
  have hexp : 1/(1-1/d.eta)-1= -(1/(1-d.eta)) := by
    field_simp [ne_of_gt d.heta,sub_ne_zero.mpr (Ne.symm hη)]
    ring
  have hP : d.expenditureIndex r=(d.expenditureData.powerSum d.eta r)^(1/(1-d.eta)) := by
    rw [expenditureIndex,d.expenditureData.cost_eq_ces hη]
    change 1*(d.expenditureData.powerSum d.eta r)^(1/(1-d.eta))=_
    ring
  rw [hexp,hP,Real.rpow_neg (d.expenditureData.powerSum_pos d.eta hr).le]
  field_simp [ne_of_gt (d.hp i)]

end CommodityClassification.DemandNest.Data
