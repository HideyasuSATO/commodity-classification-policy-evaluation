module

public import LeanMath.CommodityClassification.NestNonnegativeExpenditure

/-! Boundary estimates for elasticities below one and the literal Cobb extension. -/
@[expose] public section
noncomputable section
set_option maxHeartbeats 400000
namespace CommodityClassification.DemandNest.Data
open Matrix Filter
open scoped Topology BigOperators
variable {n : ℕ} (d : DemandNest.Data n)

theorem small_elasticity_component_bound (hη : d.eta<1) {x : Vec n} (hx : ∀i,0<x i)
    (j : Fin n) : d.quantityIndex x≤
      d.sales*(d.share j)^(d.eta/(d.eta-1))*(x j/d.q j) := by
  have hs : d.share j*(x j/d.q j)^((d.eta-1)/d.eta)≤
      ∑i,d.share i*(x i/d.q i)^((d.eta-1)/d.eta) :=
    Finset.single_le_sum (fun i _ => mul_nonneg (d.share_pos i).le
      (Real.rpow_nonneg (div_pos (hx i) (d.hq i)).le _)) (Finset.mem_univ j)
  have hp := mul_pos (d.share_pos j) (Real.rpow_pos_of_pos (div_pos (hx j) (d.hq j))
    ((d.eta-1)/d.eta))
  have he : d.eta/(d.eta-1)≤0 := (div_neg_of_pos_of_neg d.heta (sub_neg.mpr hη)).le
  have hb := Real.rpow_le_rpow_of_nonpos hp hs he
  rw [Real.mul_rpow (d.share_pos j).le (Real.rpow_nonneg (div_pos (hx j) (d.hq j)).le _),
    ←Real.rpow_mul (div_pos (hx j) (d.hq j)).le] at hb
  have hexp : ((d.eta-1)/d.eta)*(d.eta/(d.eta-1))=1 := by
    field_simp [ne_of_gt d.heta,sub_ne_zero.mpr (ne_of_lt hη)]
  rw [hexp,Real.rpow_one] at hb
  rw [d.quantity_ces_normalized (ne_of_lt hη)]
  simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hb d.sales_pos.le

theorem nonnegative_component_bound (hη : d.eta<1) {x : Vec n} (hx : ∀i,0≤x i)
    (j : Fin n) : d.quantityOnNonnegative x≤
      d.sales*(d.share j)^(d.eta/(d.eta-1))*(x j/d.q j) := by
  by_cases hp : ∀i,0<x i
  · rw [d.quantityOnNonnegative_of_positive hp]
    exact d.small_elasticity_component_bound hη hp j
  · rw [d.quantityOnNonnegative_boundary hη.le hp]
    exact mul_nonneg (mul_nonneg d.sales_pos.le (Real.rpow_nonneg (d.share_pos j).le _))
      (div_nonneg (hx j) (d.hq j).le)

theorem nonnegative_zero_component {x : Vec n} (hx : ∀i,0≤x i) (hp : ¬∀i,0<x i) :
    ∃j,x j=0 := by
  push Not at hp
  obtain ⟨j,hj⟩ := hp
  exact ⟨j,le_antisymm hj (hx j)⟩

theorem cobb_boundary_product (hη : d.eta=1) {x : Vec n} (hx : ∀i,0≤x i) :
    d.quantityOnNonnegative x=∏i,(d.p i*x i/d.share i)^(d.share i) := by
  by_cases hp : ∀i,0<x i
  · rw [d.quantityOnNonnegative_of_positive hp]
    exact d.quantity_literal_cobb hη x hp
  · rw [d.quantityOnNonnegative_boundary hη.le hp]
    obtain ⟨j,hj⟩ := nonnegative_zero_component hx hp
    symm
    apply Finset.prod_eq_zero (Finset.mem_univ j)
    simp only [hj,mul_zero,zero_div,Real.zero_rpow (ne_of_gt (d.share_pos j))]

theorem cobb_product_continuous :
    Continuous (fun x : Vec n => ∏i,(d.p i*x i/d.share i)^(d.share i)) := by
  apply continuous_finsetProd
  intro i _
  have hc : Continuous (fun x : Vec n => d.p i*x i/d.share i) :=
    (continuous_const.mul (continuous_apply i)).div_const _
  exact hc.rpow_const (fun _ => Or.inr (d.share_pos i).le)

end CommodityClassification.DemandNest.Data
