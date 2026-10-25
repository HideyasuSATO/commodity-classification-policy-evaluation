module

public import LeanMath.CommodityClassification.NestBoundaryContinuity
public import Mathlib.Data.Fintype.EquivFin

/-! Nonempty cells of an arbitrary finite demand partition. -/
@[expose] public section
noncomputable section
set_option maxHeartbeats 400000
namespace CommodityClassification.DemandNests
open Matrix InputCoordinates
open scoped BigOperators
abbrev Vec (n : ℕ) := Fin n → ℝ

structure Data (n g : ℕ) where
  partition : Partition n g
  p : Vec n
  q : Vec n
  eta : Vec g
  hp : ∀i,0<p i
  hq : ∀i,0<q i
  heta : ∀a,0<eta a

namespace Data
variable {n g : ℕ} (d : Data n g)

def size (a : Fin g) : ℕ := (d.partition.cell a).card

def enumeration (a : Fin g) : Fin (d.size a) ≃ d.partition.cell a :=
  (d.partition.cell a).equivFin.symm

def product (a : Fin g) (j : Fin (d.size a)) : Fin n := (d.enumeration a j).val

theorem size_pos (a : Fin g) : 0<d.size a :=
  Finset.card_pos.mpr (d.partition.cell_nonempty a)

theorem product_mem (a : Fin g) (j : Fin (d.size a)) : d.product a j ∈ d.partition.cell a :=
  (d.enumeration a j).property

theorem product_group (a : Fin g) (j : Fin (d.size a)) : d.partition.group (d.product a j)=a :=
  (d.partition.mem_cell a _).mp (d.product_mem a j)

theorem product_injective (a : Fin g) : Function.Injective (d.product a) :=
  Subtype.val_injective.comp (d.enumeration a).injective

def localIndex (i : Fin n) : Fin (d.size (d.partition.group i)) :=
  (d.enumeration (d.partition.group i)).symm ⟨i,(d.partition.mem_cell _ _).mpr rfl⟩

theorem product_localIndex (i : Fin n) : d.product (d.partition.group i) (d.localIndex i)=i := by
  exact congrArg Subtype.val ((d.enumeration _).apply_symm_apply _)

def restrict (a : Fin g) : Vec n →L[ℝ] Vec (d.size a) :=
  ContinuousLinearMap.pi (fun j => ContinuousLinearMap.proj (d.product a j))

theorem restrict_apply (a : Fin g) (v : Vec n) (j : Fin (d.size a)) :
    d.restrict a v j=v (d.product a j) := rfl

theorem restrict_positive (a : Fin g) {v : Vec n} (hv : ∀i,0<v i) :
    ∀j,0<d.restrict a v j := fun j => hv (d.product a j)

theorem sum_restrict (a : Fin g) (v : Vec n) :
    ∑j,v (d.product a j)=∑i∈d.partition.cell a,v i := by
  change (∑j,(fun i : d.partition.cell a => v i) (d.enumeration a j))=_
  exact ((d.enumeration a).sum_comp (fun i : d.partition.cell a => v i)).trans
    (Finset.sum_coe_sort (d.partition.cell a) v)

def nest (a : Fin g) : DemandNest.Data (d.size a) where
  p := d.restrict a d.p
  q := d.restrict a d.q
  eta := d.eta a
  hp := d.restrict_positive a d.hp
  hq := d.restrict_positive a d.hq
  heta := d.heta a
  nonempty := d.size_pos a

theorem nest_sales (a : Fin g) : (d.nest a).sales=d.partition.sales d.p d.q a := by
  change (∑j,d.p (d.product a j)*d.q (d.product a j))=_
  rw [d.sum_restrict a (fun i => d.p i*d.q i),d.partition.sales_apply]
  apply Finset.sum_congr rfl
  intro i _
  exact mul_comm _ _

theorem nest_share (a : Fin g) (j : Fin (d.size a)) :
    (d.nest a).share j=d.p (d.product a j)*d.q (d.product a j)/d.partition.sales d.p d.q a := by
  unfold DemandNest.Data.share
  rw [d.nest_sales]
  rfl

end Data
end CommodityClassification.DemandNests
