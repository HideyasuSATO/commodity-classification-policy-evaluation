module

public import LeanMath.CommodityClassification.NestedQuantityAllocation

/-! Transfer outer surplus optimality to the actual nested preference problem. -/
@[expose] public section
noncomputable section
set_option maxHeartbeats 600000
namespace CommodityClassification.DemandNests.Data
open Matrix InputCoordinates
open scoped BigOperators
variable {n g : ℕ} (d : DemandNests.Data n g)

theorem expenditure_split (r x : Vec n) :
    dotProduct r x=∑a,dotProduct (d.restrict a r) (d.restrict a x) := by
  have he (a : Fin g) : dotProduct (d.restrict a r) (d.restrict a x)=
      ∑i∈d.partition.cell a,r i*x i := d.sum_restrict a (fun i => r i*x i)
  simp_rw [he]
  exact (d.sum_by_nest (fun i => r i*x i)).symm

theorem aggregate_expenditure_inequality {r x : Vec n} (hr : ∀i,0<r i) (hx : ∀i,0≤x i) :
    dotProduct (d.priceMap r) (d.quantityMap x)≤dotProduct r x := by
  rw [d.expenditure_split]
  apply Finset.sum_le_sum
  intro a _
  exact (d.nest a).nonnegative_dual_inequality (d.restrict_positive a hr)
    (fun j => hx (d.product a j))

theorem allocation_cell_expenditure {r : Vec n} (hr : ∀i,0<r i) (Y : Vec g) (a : Fin g) :
    dotProduct (d.restrict a r) (d.restrict a (d.allocation r Y))=d.priceMap r a*Y a := by
  rw [d.allocation_restrict,dotProduct_smul,smul_eq_mul,
    (d.nest a).unitBundle_expenditure (d.restrict_positive a hr)]
  exact mul_comm _ _

theorem allocation_expenditure {r : Vec n} (hr : ∀i,0<r i) (Y : Vec g) :
    dotProduct r (d.allocation r Y)=dotProduct (d.priceMap r) Y := by
  rw [d.expenditure_split]
  exact Finset.sum_congr rfl (fun a _ => d.allocation_cell_expenditure hr Y a)

theorem nested_surplus_optimal {r : Vec n} (hr : ∀i,0<r i)
    (U : Vec g → ℝ) (Ω : Set (Vec g)) {Y : Vec g} (hY : ∀a,0<Y a)
    (hopt : ∀Z∈Ω,U Z-dotProduct (d.priceMap r) Z≤U Y-dotProduct (d.priceMap r) Y)
    {x : Vec n} (hx : ∀i,0≤x i) (hΩ : d.quantityMap x∈Ω) :
    U (d.quantityMap x)-dotProduct r x≤
      U (d.quantityMap (d.allocation r Y))-dotProduct r (d.allocation r Y) := by
  rw [d.allocation_quantityMap hr hY,d.allocation_expenditure hr]
  have he := d.aggregate_expenditure_inequality hr hx
  have hu := hopt (d.quantityMap x) hΩ
  linarith

theorem nested_surplus_isMaxOn {r : Vec n} (hr : ∀i,0<r i)
    (U : Vec g → ℝ) (Ω : Set (Vec g)) {Y : Vec g} (hY : ∀a,0<Y a) (hmem : Y∈Ω)
    (hopt : ∀Z∈Ω,U Z-dotProduct (d.priceMap r) Z≤U Y-dotProduct (d.priceMap r) Y) :
    (∀i,0<d.allocation r Y i) ∧ d.quantityMap (d.allocation r Y)∈Ω ∧
      IsMaxOn (fun x => U (d.quantityMap x)-dotProduct r x)
        {x | (∀i,0≤x i) ∧ d.quantityMap x∈Ω} (d.allocation r Y) := by
  refine ⟨d.allocation_positive hr hY,?_,?_⟩
  · rw [d.allocation_quantityMap hr hY]
    exact hmem
  · intro x hx
    exact d.nested_surplus_optimal hr U Ω hY hopt hx.1 hx.2

theorem actual_demand_optimal {r : Vec n} (hr : ∀i,0<r i)
    (outer : Vec g → Vec g) (U : Vec g → ℝ) (Ω : Set (Vec g))
    (hY : ∀a,0<outer (d.priceMap r) a) (hmem : outer (d.priceMap r)∈Ω)
    (hopt : ∀Z∈Ω,U Z-dotProduct (d.priceMap r) Z≤
      U (outer (d.priceMap r))-dotProduct (d.priceMap r) (outer (d.priceMap r))) :
    (∀i,0<d.demand outer r i) ∧ d.quantityMap (d.demand outer r)∈Ω ∧
      IsMaxOn (fun x => U (d.quantityMap x)-dotProduct r x)
        {x | (∀i,0≤x i) ∧ d.quantityMap x∈Ω} (d.demand outer r) :=
  d.nested_surplus_isMaxOn hr U Ω hY hmem hopt

end CommodityClassification.DemandNests.Data
