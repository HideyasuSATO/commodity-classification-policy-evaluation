module

public import LeanMath.CommodityClassification.UntaxedNestEquilibrium

/-! Product and positivity transfer independent of the chosen finite enumeration. -/
@[expose] public section
noncomputable section
namespace CommodityClassification.DemandNests.Data
open scoped BigOperators
variable {n g : ℕ} (d : DemandNests.Data n g)

theorem prod_restrict (a : Fin g) (v : Vec n) :
    ∏j,v (d.product a j)=∏i∈d.partition.cell a,v i := by
  change (∏j,(fun i : d.partition.cell a => v i) (d.enumeration a j))=_
  exact ((d.enumeration a).prod_comp (fun i : d.partition.cell a => v i)).trans
    (Finset.prod_coe_sort (d.partition.cell a) v)

theorem restrict_positive_iff (a : Fin g) (x : Vec n) :
    (∀j,0<d.restrict a x j) ↔ ∀i∈d.partition.cell a,0<x i := by
  constructor
  · intro hx i hi
    let j := (d.enumeration a).symm ⟨i,hi⟩
    have hp : d.product a j=i := congrArg Subtype.val ((d.enumeration a).apply_symm_apply ⟨i,hi⟩)
    have hh := hx j
    simpa only [d.restrict_apply,hp] using hh
  · intro hx j
    exact hx (d.product a j) (d.product_mem a j)

end CommodityClassification.DemandNests.Data
