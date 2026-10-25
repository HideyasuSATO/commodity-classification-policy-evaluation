module

public import LeanMath.CommodityClassification.NestedCellProduct

/-! Literal square-root quantity indices, including nonnegative boundaries. -/
@[expose] public section
noncomputable section
set_option maxHeartbeats 1800000
namespace CommodityClassification.UntaxedNest
open Matrix InputCoordinates

theorem nest_share_half (a : Fin 2) (j : Fin (nestData.size a)) :
    (nestData.nest a).share j=1/2 := by
  rw [nestData.nest_share]
  change (1 : ℝ)*(1/4)/(nests.sales prices quantities a)=1/2
  rw [nest_sales]
  fin_cases a <;> norm_num

theorem first_cell_positive_iff (x : Vec 4) :
    (∀j,0<nestData.restrict 0 x j) ↔ 0<x 0 ∧ 0<x 1 := by
  rw [nestData.restrict_positive_iff]
  simp only [Partition.mem_cell]
  norm_num [nestData,nests,SeparableFour.fine,Fin.forall_fin_succ]

theorem first_quantity_positive (x : Vec 4) (hx : ∀i,0≤x i)
    (hp : ∀j,0<nestData.restrict 0 x j) :
    nestData.quantityMap x 0=2*Real.sqrt (x 0*x 1) := by
  change (nestData.nest 0).quantityOnNonnegative (nestData.restrict 0 x)=_
  rw [(nestData.nest 0).quantityOnNonnegative_of_positive hp,
    (nestData.nest 0).quantity_literal_cobb (by rfl) _ hp]
  simp_rw [nest_share_half]
  have he (j : Fin (nestData.size 0)) :
      ((nestData.nest 0).p j*nestData.restrict 0 x j/(1/2))^(1/2 : ℝ)=
        Real.sqrt (2*x (nestData.product 0 j)) := by
    rw [Real.sqrt_eq_rpow]
    congr 1
    change (1 : ℝ)*x (nestData.product 0 j)/(1/2)=2*x (nestData.product 0 j)
    ring
  simp_rw [he]
  rw [nestData.prod_restrict 0 (fun i => Real.sqrt (2*x i))]
  simp only [Partition.cell,Finset.prod_filter]
  norm_num [nestData,nests,SeparableFour.fine,Fin.prod_univ_succ]
  rw [Real.sqrt_mul (hx 0)]
  calc
    _=(Real.sqrt 2)^2*(Real.sqrt (x 0)*Real.sqrt (x 1)) := by ring
    _=_ := by rw [Real.sq_sqrt (by norm_num)]

theorem first_quantity_nonnegative (x : Vec 4) (hx : ∀i,0≤x i) :
    nestData.quantityMap x 0=2*Real.sqrt (x 0*x 1) := by
  by_cases hp : ∀j,0<nestData.restrict 0 x j
  · exact first_quantity_positive x hx hp
  · change (nestData.nest 0).quantityOnNonnegative (nestData.restrict 0 x)=_
    rw [(nestData.nest 0).quantityOnNonnegative_boundary (by norm_num [DemandNests.Data.nest,nestData,eta]) hp]
    have hn : ¬(0<x 0 ∧ 0<x 1) := fun hh => hp ((first_cell_positive_iff x).mpr hh)
    have hz : x 0*x 1=0 := by
      by_cases h0 : x 0=0
      · simp [h0]
      · have h0p : 0<x 0 := lt_of_le_of_ne (hx 0) (Ne.symm h0)
        have h1 : x 1=0 := le_antisymm (le_of_not_gt (fun h1p => hn ⟨h0p,h1p⟩)) (hx 1)
        simp [h1]
    simp [hz]

theorem second_quantity_nonnegative (x : Vec 4) (hx : ∀i,0≤x i) :
    nestData.quantityMap x 1=(Real.sqrt (x 2)+Real.sqrt (x 3))^2/2 := by
  change (nestData.nest 1).quantityOnNonnegative (nestData.restrict 1 x)=_
  rw [(nestData.nest 1).quantityOnNonnegative_of_large (by norm_num [DemandNests.Data.nest,nestData,eta]),
    (nestData.nest 1).quantity_ces_normalized (by norm_num [DemandNests.Data.nest,nestData,eta])]
  rw [nestData.nest_sales]
  simp_rw [nest_share_half]
  change nests.sales prices quantities 1*(∑j,(1/2 : ℝ)*
    (x (nestData.product 1 j)/(1/4 : ℝ))^((2-1)/2 : ℝ))^(2/(2-1) : ℝ)=_
  rw [nestData.sum_restrict 1 (fun i => (1/2 : ℝ)*(x i/(1/4 : ℝ))^((2-1)/2 : ℝ))]
  rw [nest_sales]
  simp only [Partition.cell,Finset.sum_filter]
  norm_num [nestData,nests,SeparableFour.fine,Fin.sum_univ_succ]
  simp_rw [←Real.sqrt_eq_rpow]
  rw [Real.sqrt_div (hx 2),Real.sqrt_div (hx 3)]
  norm_num
  rw [show Real.sqrt 4=2 from (Real.sqrt_eq_iff_eq_sq (by norm_num) (by norm_num)).mpr (by norm_num)]
  ring

end CommodityClassification.UntaxedNest
