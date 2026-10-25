module

public import LeanMath.CommodityClassification.UntaxedLiteralQuantity

/-! Printed costs and utility equal the actual implemented primitives. -/
@[expose] public section
noncomputable section
set_option maxHeartbeats 1800000
namespace CommodityClassification.UntaxedNest
open Matrix InputCoordinates

theorem actual_cost_inputs (t : ℝ) (ht : |t|≤1/4) (i : Fin 4) :
    ((family.nestedModel nests eta eta_pos outerD family_demand_eq (candidate t ht)).costData i).a=inputs t i :=
  congrFun (reconstruct_inputs t) i

theorem actual_cost_literal (t : ℝ) (ht : |t|≤1/4) (i : Fin 4)
    (w : Vec 2) (hw : ∀j,0<w j) :
    (family.nestedModel nests eta eta_pos outerD family_demand_eq (candidate t ht)).costs w i=
      w 0^((1+coordinates t i 0)/2)*w 1^((1-coordinates t i 0)/2) := by
  let d := (family.nestedModel nests eta eta_pos outerD family_demand_eq (candidate t ht)).costData i
  change d.cost 1 w=_
  rw [d.cost_eq_cobb rfl,d.cobb_eq_product hw]
  have hp : d.p=1 := rfl
  have ha : d.a=inputs t i := actual_cost_inputs t ht i
  have hs (j : Fin 2) : d.share j=inputs t i j := by
    rw [CESCost.Data.share,ha,hp]
    change Supply.Example.frame.w j*inputs t i j/1=inputs t i j
    fin_cases j <;> norm_num [Supply.Example.frame]
  have hr (j : Fin 2) : d.ratio w j=w j := by
    change w j/Supply.Example.frame.w j=w j
    fin_cases j <;> norm_num [Supply.Example.frame]
  simp_rw [hs,hr]
  rw [hp,one_mul,Fin.prod_univ_two]
  simp [inputs]

theorem quantity_map_literal (x : Vec 4) (hx : ∀i,0≤x i) :
    nestData.quantityMap x=![2*Real.sqrt (x 0*x 1),(Real.sqrt (x 2)+Real.sqrt (x 3))^2/2] := by
  ext a;fin_cases a
  · exact first_quantity_nonnegative x hx
  · exact second_quantity_nonnegative x hx

theorem original_utility_literal (c : ℝ) (x : Vec 4) (hx : ∀i,0≤x i) :
    (family.nestData nests eta eta_pos).nestedUtility outerD c x=
      nestData.outerUtility outerD c ![2*Real.sqrt (x 0*x 1),(Real.sqrt (x 2)+Real.sqrt (x 3))^2/2] := by
  change nestData.outerUtility outerD c (nestData.quantityMap x)=_
  rw [quantity_map_literal x hx]

end CommodityClassification.UntaxedNest
