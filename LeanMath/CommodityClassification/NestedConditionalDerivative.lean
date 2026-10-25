module

public import LeanMath.CommodityClassification.NestedExpenditureMaps

/-! Actual derivatives of the optimizing conditional quantities. -/
@[expose] public section
noncomputable section
set_option maxHeartbeats 400000
namespace CommodityClassification.DemandNests.Data
open Matrix InputCoordinates Filter
open scoped BigOperators Topology
variable {n g : ℕ} (d : DemandNests.Data n g)

def conditionalDerivative : Vec n →L[ℝ] Vec n := ContinuousLinearMap.pi (fun i =>
  ((d.nest (d.partition.group i)).expenditureData.hessianRow (d.eta (d.partition.group i))
    (d.localIndex i)).comp (d.restrict (d.partition.group i)))

theorem conditionalQuantities_hasFDerivAt :
    HasFDerivAt d.conditionalQuantities d.conditionalDerivative d.p := by
  apply hasFDerivAt_pi.mpr
  intro i
  have hh := ((d.nest (d.partition.group i)).expenditureData.hasFDerivAt_cost_partial_benchmark
    (d.eta (d.partition.group i)) (d.localIndex i)).comp d.p
      (d.restrict (d.partition.group i)).hasFDerivAt
  apply hh.congr_of_eventuallyEq
  filter_upwards [CESCost.positivePrices_open.mem_nhds d.hp] with r hr
  exact d.conditionalQuantities_gradient hr i

theorem conditionalDerivative_apply (h : Vec n) (i : Fin n) :
    d.conditionalDerivative h i=
      d.eta (d.partition.group i)*(d.q i/d.partition.sales d.p d.q (d.partition.group i))*
        (d.priceDerivative h (d.partition.group i)-h i/d.p i) := by
  change ((d.nest (d.partition.group i)).expenditureData.hessianRow
    (d.eta (d.partition.group i)) (d.localIndex i)) (d.restrict (d.partition.group i) h)=_
  simp only [CESCost.Data.hessianRow,_root_.sub_apply,_root_.smul_apply,
    ContinuousLinearMap.proj_apply,smul_eq_mul]
  have hw : CESCost.weightedLinear (d.nest (d.partition.group i)).expenditureData.a
      (d.restrict (d.partition.group i) h)=d.priceDerivative h (d.partition.group i) := rfl
  rw [hw]
  change (d.eta (d.partition.group i)*(d.q (d.product (d.partition.group i) (d.localIndex i))/
      (d.nest (d.partition.group i)).sales)/1)*d.priceDerivative h (d.partition.group i)-
    (d.eta (d.partition.group i)*(d.q (d.product (d.partition.group i) (d.localIndex i))/
      (d.nest (d.partition.group i)).sales)/d.p (d.product (d.partition.group i) (d.localIndex i)))*
        h (d.product (d.partition.group i) (d.localIndex i))=_
  rw [d.product_localIndex,d.nest_sales]
  ring

end CommodityClassification.DemandNests.Data
