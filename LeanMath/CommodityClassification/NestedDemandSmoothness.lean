module

public import LeanMath.CommodityClassification.NestedDirectWitness

/-! Near-price regularity of the actual nested demand, separate from a point derivative. -/
@[expose] public section
noncomputable section
set_option maxHeartbeats 1000000
namespace CommodityClassification.DemandNest.Data
open Matrix Filter
open scoped Topology
variable {n : ℕ} (d : DemandNest.Data n)

theorem unitBundle_smooth {r : Vec n} (hr : ∀i,0<r i) : ContDiffAt ℝ ⊤ d.unitBundle r := by
  apply contDiffAt_pi.mpr
  intro i
  have hh : ContDiffAt ℝ ⊤ (CESCost.pricePartial d.expenditureIndex i) r :=
    (d.expenditure_smooth hr).fderiv_right (by simp) |>.clm_apply contDiffAt_const
  apply hh.congr_of_eventuallyEq
  filter_upwards [CESCost.positivePrices_open.mem_nhds hr] with w hw
  exact congrFun (d.unitBundle_eq_gradient hw) i

end CommodityClassification.DemandNest.Data

namespace CommodityClassification.DemandNests.Data
open Matrix InputCoordinates Equilibrium Filter
open scoped Topology
variable {n g : ℕ} (d : DemandNests.Data n g)

theorem priceMap_smooth {r : Vec n} (hr : ∀i,0<r i) : ContDiffAt ℝ ⊤ d.priceMap r := by
  apply contDiffAt_pi.mpr
  intro a
  exact ((d.nest a).expenditure_smooth (d.restrict_positive a hr)).comp r (d.restrict a).contDiff.contDiffAt

theorem conditionalQuantities_smooth {r : Vec n} (hr : ∀i,0<r i) :
    ContDiffAt ℝ ⊤ d.conditionalQuantities r := by
  apply contDiffAt_pi.mpr
  intro i
  have hh := ((d.nest (d.partition.group i)).unitBundle_smooth
    (d.restrict_positive (d.partition.group i) hr)).comp r (d.restrict (d.partition.group i)).contDiff.contDiffAt
  exact (contDiffAt_pi.mp hh) (d.localIndex i)

theorem demand_smooth (outer : Vec g → Vec g) {r : Vec n} (hr : ∀i,0<r i)
    (ho : ContDiffAt ℝ ⊤ outer (d.priceMap r)) : ContDiffAt ℝ ⊤ (d.demand outer) r := by
  apply contDiffAt_pi.mpr
  intro i
  exact ((contDiffAt_pi.mp (ho.comp r (d.priceMap_smooth hr))) (d.partition.group i)).mul
    ((contDiffAt_pi.mp (d.conditionalQuantities_smooth hr)) i)

theorem quadraticOuter_smooth (DG : Matrix (Fin g) (Fin g) ℝ) :
    ContDiff ℝ ⊤ (d.quadraticOuter DG) := by
  change ContDiff ℝ ⊤ (fun r => d.partition.sales d.p d.q-DG *ᵥ (r-(fun _ => 1)))
  have hh : ContDiff ℝ ⊤ (fun r : Vec g => d.partition.sales d.p d.q-
      (matCLM DG) (r-(fun _ => 1))) :=
    contDiff_const.sub ((matCLM DG).contDiff.comp (contDiff_id.sub contDiff_const))
  simpa only [matCLM_apply] using hh

theorem quadratic_nested_smooth (DG : Matrix (Fin g) (Fin g) ℝ) {r : Vec n} (hr : ∀i,0<r i) :
    ContDiffAt ℝ ⊤ (d.demand (d.quadraticOuter DG)) r :=
  d.demand_smooth _ hr (d.quadraticOuter_smooth DG).contDiffAt

theorem quantityMap_smooth {x : Vec n} (hx : ∀i,0<x i) : ContDiffAt ℝ ⊤ d.quantityMap x := by
  apply contDiffAt_pi.mpr
  intro a
  have hh := ((d.nest a).quantity_smooth (d.restrict_positive a hx)).comp x (d.restrict a).contDiff.contDiffAt
  apply hh.congr_of_eventuallyEq
  filter_upwards [CESCost.positivePrices_open.mem_nhds hx] with y hy
  exact (d.nest a).quantityOnNonnegative_of_positive (d.restrict_positive a hy)

end CommodityClassification.DemandNests.Data
