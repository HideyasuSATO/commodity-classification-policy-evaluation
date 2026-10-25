module

public import LeanMath.CommodityClassification.NestedDemandData

/-! Actual expenditure maps assembled across all cells, with their derivatives. -/
@[expose] public section
noncomputable section
set_option maxHeartbeats 400000
namespace CommodityClassification.DemandNests.Data
open Matrix InputCoordinates
open scoped BigOperators
variable {n g : ℕ} (d : DemandNests.Data n g)

def priceMap (r : Vec n) : Vec g := fun a => (d.nest a).expenditureIndex (d.restrict a r)

def priceDerivative : Vec n →L[ℝ] Vec g := ContinuousLinearMap.pi (fun a =>
  (CESCost.weightedLinear (fun j => (d.nest a).q j/(d.nest a).sales)).comp (d.restrict a))

def conditionalQuantities (r : Vec n) : Vec n := fun i =>
  (d.nest (d.partition.group i)).unitBundle (d.restrict (d.partition.group i) r) (d.localIndex i)

theorem priceMap_benchmark : d.priceMap d.p=fun _ => 1 := by
  funext a
  exact (d.nest a).expenditure_benchmark

theorem priceMap_positive {r : Vec n} (hr : ∀i,0<r i) : ∀a,0<d.priceMap r a :=
  fun a => (d.nest a).expenditure_positive (d.restrict_positive a hr)

theorem priceMap_hasFDerivAt : HasFDerivAt d.priceMap d.priceDerivative d.p := by
  apply hasFDerivAt_pi.mpr
  intro a
  exact (d.nest a).expenditure_derivative.comp d.p (d.restrict a).hasFDerivAt

theorem priceDerivative_apply (h : Vec n) (a : Fin g) :
    d.priceDerivative h a=(∑i∈d.partition.cell a,d.q i*h i)/d.partition.sales d.p d.q a := by
  change (CESCost.weightedLinear (fun j => (d.nest a).q j/(d.nest a).sales)) (d.restrict a h)=_
  rw [CESCost.weightedLinear_apply,d.nest_sales]
  change (∑j,(d.q (d.product a j)/d.partition.sales d.p d.q a)*h (d.product a j))=_
  simp only [div_mul_eq_mul_div,←Finset.sum_div]
  rw [d.sum_restrict a (fun i => d.q i*h i)]

theorem priceDerivative_matrix (h : Vec n) :
    d.priceDerivative h=(diagonal (fun a => (d.partition.sales d.p d.q a)⁻¹)*
      (d.partition.Q d.q).transpose) *ᵥ h := by
  funext a
  rw [d.priceDerivative_apply,←Matrix.mulVec_mulVec,Matrix.mulVec_diagonal]
  have ht : ((d.partition.Q d.q).transpose *ᵥ h) a=∑i∈d.partition.cell a,d.q i*h i := by
    exact d.partition.sales_apply h d.q a
  rw [ht,div_eq_mul_inv,mul_comm]

theorem conditionalQuantities_positive {r : Vec n} (hr : ∀i,0<r i) :
    ∀i,0<d.conditionalQuantities r i := fun i =>
  (d.nest (d.partition.group i)).unitBundle_positive
    (d.restrict_positive (d.partition.group i) hr) (d.localIndex i)

theorem conditionalQuantities_benchmark (i : Fin n) :
    d.conditionalQuantities d.p i=d.q i/d.partition.sales d.p d.q (d.partition.group i) := by
  have h := congrFun (d.nest (d.partition.group i)).unitBundle_benchmark (d.localIndex i)
  change d.conditionalQuantities d.p i=
    d.q (d.product (d.partition.group i) (d.localIndex i))/(d.nest (d.partition.group i)).sales at h
  simpa only [d.product_localIndex,d.nest_sales] using h

theorem conditionalQuantities_gradient {r : Vec n} (hr : ∀i,0<r i) (i : Fin n) :
    d.conditionalQuantities r i=CESCost.pricePartial (d.nest (d.partition.group i)).expenditureIndex
      (d.localIndex i) (d.restrict (d.partition.group i) r) :=
  congrFun ((d.nest (d.partition.group i)).unitBundle_eq_gradient
    (d.restrict_positive (d.partition.group i) hr)) (d.localIndex i)

end CommodityClassification.DemandNests.Data
