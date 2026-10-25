module

public import LeanMath.CommodityClassification.NestedPolicyIdentities

/-! Recover each cell's actual optimizer and scale it to an outer quantity. -/
@[expose] public section
noncomputable section
set_option maxHeartbeats 600000
namespace CommodityClassification.DemandNests.Data
open Matrix InputCoordinates
open scoped BigOperators
variable {n g : ℕ} (d : DemandNests.Data n g)

def quantityMap (x : Vec n) : Vec g := fun a =>
  (d.nest a).quantityOnNonnegative (d.restrict a x)

def allocation (r : Vec n) (Y : Vec g) : Vec n := fun i =>
  Y (d.partition.group i)*d.conditionalQuantities r i

theorem conditionalQuantities_product (r : Vec n) (a : Fin g) (j : Fin (d.size a)) :
    d.conditionalQuantities r (d.product a j)=
      (d.nest a).unitBundle (d.restrict a r) j := by
  generalize hi : d.product a j=i
  have hg : d.partition.group i=a := hi ▸ d.product_group a j
  subst a
  have hl : d.localIndex i=j := d.product_injective _ ((d.product_localIndex i).trans hi.symm)
  change (d.nest (d.partition.group i)).unitBundle (d.restrict (d.partition.group i) r)
    (d.localIndex i)=_
  rw [hl]

theorem conditionalQuantities_restrict (r : Vec n) (a : Fin g) :
    d.restrict a (d.conditionalQuantities r)=(d.nest a).unitBundle (d.restrict a r) := by
  funext j
  exact d.conditionalQuantities_product r a j

theorem allocation_restrict (r : Vec n) (Y : Vec g) (a : Fin g) :
    d.restrict a (d.allocation r Y)=Y a • (d.nest a).unitBundle (d.restrict a r) := by
  funext j
  change Y (d.partition.group (d.product a j))*d.conditionalQuantities r (d.product a j)=_
  rw [d.product_group,d.conditionalQuantities_product]
  rfl

theorem allocation_positive {r : Vec n} (hr : ∀i,0<r i) {Y : Vec g} (hY : ∀a,0<Y a) :
    ∀i,0<d.allocation r Y i :=
  fun i => mul_pos (hY (d.partition.group i)) (d.conditionalQuantities_positive hr i)

theorem quantityMap_nonneg {x : Vec n} (hx : ∀i,0≤x i) : ∀a,0≤d.quantityMap x a :=
  fun a => (d.nest a).quantityOnNonnegative_nonneg (fun j => hx (d.product a j))

theorem allocation_quantityMap {r : Vec n} (hr : ∀i,0<r i) {Y : Vec g} (hY : ∀a,0<Y a) :
    d.quantityMap (d.allocation r Y)=Y := by
  funext a
  change (d.nest a).quantityOnNonnegative (d.restrict a (d.allocation r Y))=Y a
  rw [(d.nest a).quantityOnNonnegative_of_positive
    (d.restrict_positive a (d.allocation_positive hr hY)),d.allocation_restrict]
  have hs := (d.nest a).quantityData.cost_smul (1/(d.nest a).eta) (Y a) (hY a)
    ((d.nest a).unitBundle_positive (d.restrict_positive a hr))
  change (d.nest a).quantityIndex (Y a • (d.nest a).unitBundle (d.restrict a r))=
    Y a*(d.nest a).quantityIndex ((d.nest a).unitBundle (d.restrict a r)) at hs
  rw [hs,(d.nest a).unitBundle_quantity (d.restrict_positive a hr),mul_one]

theorem allocation_eq_demand (outer : Vec g → Vec g) (r : Vec n) :
    d.allocation r (outer (d.priceMap r))=d.demand outer r := rfl

end CommodityClassification.DemandNests.Data
