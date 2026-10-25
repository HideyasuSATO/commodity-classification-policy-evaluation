module

public import LeanMath.CommodityClassification.NestIndexDerivatives
public import LeanMath.CommodityClassification.CESParameterLimit

/-! Equality with the manuscript's literal primal and dual index formulas. -/
@[expose] public section
noncomputable section
set_option maxHeartbeats 2400000
namespace CommodityClassification.DemandNest.Data
open Matrix Filter
open scoped BigOperators Topology
variable {n : ℕ} (d : DemandNest.Data n)

theorem primal_term_normalization (x : Vec n) (hx : ∀i,0<x i) (i : Fin n) :
    (d.share i)^(1/d.eta)*(d.p i*x i)^((d.eta-1)/d.eta)=
      d.sales^((d.eta-1)/d.eta)*(d.share i*(x i/d.q i)^((d.eta-1)/d.eta)) := by
  have he : d.p i*x i=(d.sales*d.share i)*(x i/d.q i) := by
    unfold share
    field_simp [ne_of_gt d.sales_pos,ne_of_gt (d.hq i)]
  rw [he,Real.mul_rpow (mul_pos d.sales_pos (d.share_pos i)).le (div_pos (hx i) (d.hq i)).le,
    Real.mul_rpow d.sales_pos.le (d.share_pos i).le]
  have hh : 1/d.eta+(d.eta-1)/d.eta=1 := by field_simp [ne_of_gt d.heta];ring
  have hp : (d.share i)^(1/d.eta)*(d.share i)^((d.eta-1)/d.eta)=d.share i := by
    rw [←Real.rpow_add (d.share_pos i),hh,Real.rpow_one]
  calc
    _ = d.sales^((d.eta-1)/d.eta)*
      ((d.share i)^(1/d.eta)*(d.share i)^((d.eta-1)/d.eta))*
        (x i/d.q i)^((d.eta-1)/d.eta) := by ring
    _ = _ := by rw [hp];ring

theorem quantity_literal_ces (hη : d.eta≠1) (x : Vec n) (hx : ∀i,0<x i) :
    d.quantityIndex x=(∑i,(d.share i)^(1/d.eta)*(d.p i*x i)^((d.eta-1)/d.eta))^
      (d.eta/(d.eta-1)) := by
  rw [d.quantity_ces_normalized hη]
  simp_rw [d.primal_term_normalization x hx]
  rw [←Finset.mul_sum]
  have hs : 0≤∑i,d.share i*(x i/d.q i)^((d.eta-1)/d.eta) :=
    Finset.sum_nonneg (fun i _ => mul_nonneg (d.share_pos i).le
      (Real.rpow_nonneg (div_pos (hx i) (d.hq i)).le _))
  rw [Real.mul_rpow (Real.rpow_nonneg d.sales_pos.le _) hs,←Real.rpow_mul d.sales_pos.le]
  have he : ((d.eta-1)/d.eta)*(d.eta/(d.eta-1))=1 := by
    field_simp [ne_of_gt d.heta,sub_ne_zero.mpr hη]
  rw [he,Real.rpow_one]

theorem expenditure_literal_cobb (hη : d.eta=1) (r : Vec n) (hr : ∀i,0<r i) :
    d.expenditureIndex r=∏i,(r i/d.p i)^(d.share i) := by
  rw [d.expenditure_cobb_log hη,Real.exp_sum]
  apply Finset.prod_congr rfl
  intro i _
  rw [Real.rpow_def_of_pos (div_pos (hr i) (d.hp i))]
  congr 1
  ring

theorem quantity_literal_cobb (hη : d.eta=1) (x : Vec n) (hx : ∀i,0<x i) :
    d.quantityIndex x=∏i,(d.p i*x i/d.share i)^(d.share i) := by
  rw [d.quantity_cobb_log hη]
  have he (i : Fin n) : d.p i*x i/d.share i=d.sales*(x i/d.q i) := by
    unfold share
    field_simp [ne_of_gt d.sales_pos,ne_of_gt (d.hp i),ne_of_gt (d.hq i)]
  have hp : (∏i,(d.p i*x i/d.share i)^(d.share i))=
      Real.exp (∑i,d.share i*Real.log (d.p i*x i/d.share i)) := by
    rw [Real.exp_sum]
    apply Finset.prod_congr rfl
    intro i _
    rw [Real.rpow_def_of_pos (div_pos (mul_pos (d.hp i) (hx i)) (d.share_pos i))]
    congr 1
    ring
  rw [hp]
  simp_rw [he,Real.log_mul (ne_of_gt d.sales_pos) (ne_of_gt (div_pos (hx _) (d.hq _))),mul_add]
  rw [Finset.sum_add_distrib,←Finset.sum_mul,d.share_sum,one_mul,Real.exp_add,
    Real.exp_log d.sales_pos]

theorem expenditure_geometric_limit (r : Vec n) (hr : ∀i,0<r i) :
    Tendsto (fun η : ℝ => d.expenditureData.cost η r) (𝓝 1)
      (𝓝 (∏i,(r i/d.p i)^(d.share i))) := by
  have he : d.expenditureData.cobb r=∏i,(r i/d.p i)^(d.share i) := by
    rw [d.expenditureData.cobb_eq_product hr]
    change 1*(∏i,(r i/d.p i)^(d.expenditureData.share i))=_
    simp only [d.expenditure_share,one_mul]
  rw [←he]
  exact d.expenditureData.cost_tendsto_cobb hr

end CommodityClassification.DemandNest.Data
