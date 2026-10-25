module

public import LeanMath.CommodityClassification.NestDualCobb

/-! An attained unit-expenditure minimum on the strictly positive primal domain. -/
@[expose] public section
noncomputable section
set_option maxHeartbeats 2400000
namespace CommodityClassification.DemandNest.Data
open Matrix
open scoped BigOperators
variable {n : ℕ} (d : DemandNest.Data n)

theorem expenditure_positive {r : Vec n} (hr : ∀i,0<r i) : 0<d.expenditureIndex r :=
  d.expenditureData.cost_pos d.eta hr

theorem quantity_positive {x : Vec n} (hx : ∀i,0<x i) : 0<d.quantityIndex x :=
  d.quantityData.cost_pos (1/d.eta) hx

theorem gradient_expenditure (r x : Vec n) :
    dotProduct (fun i => r i/d.expenditureIndex r) x=dotProduct r x/d.expenditureIndex r := by
  simp only [dotProduct,div_mul_eq_mul_div,←Finset.sum_div]

theorem positive_dual_inequality {r x : Vec n} (hr : ∀i,0<r i) (hx : ∀i,0<x i) :
    d.expenditureIndex r*d.quantityIndex x≤dotProduct r x := by
  have h := d.quantityData.cost_support (one_div_pos.mpr d.heta) hx (d.dualRay_positive hr)
  change d.quantityIndex x≤dotProduct
    (fun i => CESCost.pricePartial d.quantityIndex i (d.dualRay r)) x at h
  simp_rw [d.dualRay_gradient hr] at h
  rw [d.gradient_expenditure] at h
  simpa only [mul_comm] using (le_div_iff₀ (d.expenditure_positive hr)).mp h

theorem dualRay_expenditure {r : Vec n} (hr : ∀i,0<r i) :
    dotProduct r (d.dualRay r)=d.expenditureIndex r*d.quantityIndex (d.dualRay r) := by
  have h := d.quantityData.cost_euler (1/d.eta) (d.dualRay_positive hr)
  change d.quantityIndex (d.dualRay r)=dotProduct
    (fun i => CESCost.pricePartial d.quantityIndex i (d.dualRay r)) (d.dualRay r) at h
  simp_rw [d.dualRay_gradient hr] at h
  rw [d.gradient_expenditure] at h
  have hh := (eq_div_iff (ne_of_gt (d.expenditure_positive hr))).mp h
  simpa only [mul_comm] using hh.symm

def unitBundle (r : Vec n) : Vec n := (d.quantityIndex (d.dualRay r))⁻¹ • d.dualRay r

theorem unitBundle_positive {r : Vec n} (hr : ∀i,0<r i) : ∀i,0<d.unitBundle r i := by
  intro i
  exact mul_pos (inv_pos.mpr (d.quantity_positive (d.dualRay_positive hr))) (d.dualRay_positive hr i)

theorem unitBundle_quantity {r : Vec n} (hr : ∀i,0<r i) : d.quantityIndex (d.unitBundle r)=1 := by
  have h := d.quantityData.cost_smul (1/d.eta) (d.quantityIndex (d.dualRay r))⁻¹
    (inv_pos.mpr (d.quantity_positive (d.dualRay_positive hr))) (d.dualRay_positive hr)
  change d.quantityIndex (d.unitBundle r)=
    (d.quantityIndex (d.dualRay r))⁻¹*d.quantityIndex (d.dualRay r) at h
  rw [inv_mul_cancel₀ (ne_of_gt (d.quantity_positive (d.dualRay_positive hr)))] at h
  exact h

theorem unitBundle_expenditure {r : Vec n} (hr : ∀i,0<r i) :
    dotProduct r (d.unitBundle r)=d.expenditureIndex r := by
  rw [unitBundle,dotProduct_smul,smul_eq_mul,d.dualRay_expenditure hr]
  field_simp [ne_of_gt (d.quantity_positive (d.dualRay_positive hr))]

theorem positive_unit_expenditure_isLeast {r : Vec n} (hr : ∀i,0<r i) :
    IsLeast {v : ℝ | ∃x : Vec n,(∀i,0<x i) ∧ 1≤d.quantityIndex x ∧ v=dotProduct r x}
      (d.expenditureIndex r) := by
  constructor
  · exact ⟨d.unitBundle r,d.unitBundle_positive hr,(d.unitBundle_quantity hr).ge,
      (d.unitBundle_expenditure hr).symm⟩
  · rintro v ⟨x,hx,hF,rfl⟩
    have hl := d.positive_dual_inequality hr hx
    have hp := d.expenditure_positive hr
    nlinarith

end CommodityClassification.DemandNest.Data
