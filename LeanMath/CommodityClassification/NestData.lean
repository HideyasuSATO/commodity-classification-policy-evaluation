module

public import LeanMath.CommodityClassification.FixedCancellationIdentification

/-! A single nonempty demand nest and two calibrated homogeneous functions. -/
@[expose] public section
noncomputable section
namespace CommodityClassification.DemandNest
open Matrix
open scoped BigOperators
abbrev Vec (n : ℕ) := Fin n → ℝ

structure Data (n : ℕ) where
  p : Vec n
  q : Vec n
  eta : ℝ
  hp : ∀i,0<p i
  hq : ∀i,0<q i
  heta : 0<eta
  nonempty : 0<n

namespace Data
variable {n : ℕ} (d : Data n)

def sales : ℝ := ∑i,d.p i*d.q i
def share (i : Fin n) : ℝ := d.p i*d.q i/d.sales

theorem sales_pos : 0<d.sales := by
  apply Finset.sum_pos
  · intro i _;exact mul_pos (d.hp i) (d.hq i)
  · exact ⟨⟨0,d.nonempty⟩,Finset.mem_univ _⟩

theorem share_pos (i : Fin n) : 0<d.share i := div_pos (mul_pos (d.hp i) (d.hq i)) d.sales_pos

theorem share_sum : ∑i,d.share i=1 := by
  simp only [share,←Finset.sum_div]
  exact div_self (ne_of_gt d.sales_pos)

def quantityData : CESCost.Data n where
  p := d.sales
  w0 := d.q
  a := d.p
  p_pos := d.sales_pos
  w0_pos := d.hq
  a_pos := d.hp
  cost_identity := rfl

def expenditureData : CESCost.Data n where
  p := 1
  w0 := d.p
  a := fun i => d.q i/d.sales
  p_pos := by norm_num
  w0_pos := d.hp
  a_pos := fun i => div_pos (d.hq i) d.sales_pos
  cost_identity := by
    change (∑i,d.q i/d.sales*d.p i)=1
    simp only [div_mul_eq_mul_div,←Finset.sum_div]
    have hh : (∑i,d.q i*d.p i)=d.sales := by simp [sales,mul_comm]
    rw [hh,div_self (ne_of_gt d.sales_pos)]

theorem quantity_share (i : Fin n) : d.quantityData.share i=d.share i := by
  simp [CESCost.Data.share,quantityData,share,mul_comm]

theorem expenditure_share (i : Fin n) : d.expenditureData.share i=d.share i := by
  simp [CESCost.Data.share,expenditureData,share,mul_div_assoc]

def quantityIndex : Vec n → ℝ := d.quantityData.cost (1/d.eta)
def expenditureIndex : Vec n → ℝ := d.expenditureData.cost d.eta

theorem expenditure_ces (hη : d.eta≠1) (r : Vec n) :
    d.expenditureIndex r=(∑i,d.share i*(r i/d.p i)^(1-d.eta))^(1/(1-d.eta)) := by
  rw [expenditureIndex,d.expenditureData.cost_eq_ces hη]
  change 1*(∑i,d.expenditureData.share i*(r i/d.p i)^(1-d.eta))^(1/(1-d.eta))=_
  simp only [d.expenditure_share,one_mul]

theorem quantity_ces_normalized (hη : d.eta≠1) (x : Vec n) :
    d.quantityIndex x=d.sales*(∑i,d.share i*(x i/d.q i)^((d.eta-1)/d.eta))^
      (d.eta/(d.eta-1)) := by
  have hi : 1/d.eta≠1 := by
    intro he
    apply hη
    have ht := (div_eq_iff (ne_of_gt d.heta)).mp he
    linarith
  rw [quantityIndex,d.quantityData.cost_eq_ces hi]
  have hr : 1-1/d.eta=(d.eta-1)/d.eta := by field_simp [ne_of_gt d.heta]
  have he : 1/(1-1/d.eta)=d.eta/(d.eta-1) := by
    rw [hr]
    field_simp [ne_of_gt d.heta,sub_ne_zero.mpr hη]
  change d.sales*(∑i,d.quantityData.share i*(x i/d.q i)^(1-1/d.eta))^(1/(1-1/d.eta))=_
  rw [he]
  simp only [d.quantity_share,hr]

theorem expenditure_cobb_log (hη : d.eta=1) (r : Vec n) :
    d.expenditureIndex r=Real.exp (∑i,d.share i*Real.log (r i/d.p i)) := by
  rw [expenditureIndex,d.expenditureData.cost_eq_cobb hη]
  change 1*Real.exp (∑i,d.expenditureData.share i*Real.log (r i/d.p i))=_
  simp only [d.expenditure_share,one_mul]

theorem quantity_cobb_log (hη : d.eta=1) (x : Vec n) :
    d.quantityIndex x=d.sales*Real.exp (∑i,d.share i*Real.log (x i/d.q i)) := by
  have he : 1/d.eta=1 := by rw [hη];norm_num
  rw [quantityIndex,d.quantityData.cost_eq_cobb he]
  change d.sales*Real.exp (∑i,d.quantityData.share i*Real.log (x i/d.q i))=_
  simp only [d.quantity_share]

end Data
end CommodityClassification.DemandNest
