module

public import LeanMath.CommodityClassification.PrecisionIsolatedPartition

/-! Isolated products remove their entire sales mass from the capacity bound. -/
@[expose] public section
noncomputable section
set_option maxHeartbeats 1600000
namespace CommodityClassification.Precision.Data
open InputCoordinates
open scoped BigOperators
variable {n g : ℕ} (d : Precision.Data n)

def residualSales (S : Finset (Fin n)) : ℝ := 1-∑i∈S,d.w i
def tailSales (k : ℕ) : ℝ := 1-d.largestSales k

theorem residualSales_sum (S : Finset (Fin n)) :
    d.residualSales S=∑i,if i∈S then 0 else d.w i := by
  classical
  have hs : (∑i,if i∈S then d.w i else 0)=∑i∈S,d.w i := by
    rw [←Finset.sum_filter]
    simp
  have he : (∑i,if i∈S then d.w i else 0)+(∑i,if i∈S then 0 else d.w i)=1 := by
    rw [←Finset.sum_add_distrib]
    calc
      (∑i,((if i∈S then d.w i else 0)+(if i∈S then 0 else d.w i)))=∑i,d.w i := by
        apply Finset.sum_congr rfl
        intro i _
        by_cases hi : i∈S <;> simp [hi]
      _=1 := d.sum_w
  rw [hs] at he
  unfold residualSales
  linarith

theorem residualSales_nonneg (S : Finset (Fin n)) : 0≤d.residualSales S := by
  classical
  rw [d.residualSales_sum]
  apply Finset.sum_nonneg
  intro i _
  split_ifs
  · exact le_rfl
  · exact (d.hw i).le

theorem cellCapacity_remaining_mass (S : Finset (Fin n)) (P : Partition n g)
    (hiso : ∀i∈S,P.cell (P.group i)={i}) (a : Fin g) :
    d.cellCapacity P a≤∑i∈P.cell a,if i∈S then 0 else d.w i := by
  classical
  by_cases h : ∃i∈P.cell a,i∈S
  · obtain ⟨i,hi,hS⟩ := h
    have hia := (P.mem_cell a i).mp hi
    have hcell : P.cell a={i} := by rw [←hia];exact hiso i hS
    rw [d.cellCapacity_singleton P a i hcell,hcell]
    simp [hS]
  · have hn : ∀i∈P.cell a,i∉S := by
      intro i hi hS
      exact h ⟨i,hi,hS⟩
    calc
      d.cellCapacity P a≤d.groupWeight P a := (d.cellCapacity_bounds P a).2
      _=∑i∈P.cell a,if i∈S then 0 else d.w i := by
        unfold groupWeight
        apply Finset.sum_congr rfl
        intro i hi
        simp [hn i hi]

theorem isolated_capacity_bound (S : Finset (Fin n)) (P : Partition n g)
    (hiso : ∀i∈S,P.cell (P.group i)={i}) : d.totalCapacity P≤d.residualSales S := by
  classical
  calc
    d.totalCapacity P≤∑a,∑i∈P.cell a,if i∈S then 0 else d.w i :=
      Finset.sum_le_sum (fun a _ => d.cellCapacity_remaining_mass S P hiso a)
    _=∑i,if i∈S then 0 else d.w i := sum_by_partition P _
    _=d.residualSales S := (d.residualSales_sum S).symm

theorem isolation_capacity_bound (S : Finset (Fin n)) (P : Partition n g)
    (hP : d.IsIsolationPartition S P) : d.totalCapacity P≤d.residualSales S :=
  d.isolated_capacity_bound S P (d.isolation_cell_singleton S P hP)

theorem isolation_welfare_bound (S : Finset (Fin n)) (P : Partition n g)
    (hP : d.IsIsolationPartition S P) :
    d.exAnteWidth P≤min d.precisionFloor (d.capacityMultiplier*d.residualSales S) := by
  have ht := d.isolation_typeRespecting S P hP
  exact le_min (d.exAnteWidth_upper P ht)
    ((d.exAnte_capacity_bound P ht).trans
      (mul_le_mul_of_nonneg_left (d.isolation_capacity_bound S P hP) d.capacityMultiplier_nonneg))

theorem tailSales_bounds (k : ℕ) : 0≤d.tailSales k ∧ d.tailSales k≤1 := by
  unfold tailSales
  have h := d.largestSales_bounds k
  constructor <;> linarith

theorem tailSales_saturated (k : ℕ) (hk : n≤k) : d.tailSales k=0 := by
  rw [tailSales,d.largestSales_saturated k hk,sub_self]

theorem tailSales_le_residual (k : ℕ) (S : Finset (Fin n)) (hS : S.card≤k) :
    d.tailSales k≤d.residualSales S := by
  unfold tailSales residualSales
  linarith [d.subset_sales_le_largest k S hS]

theorem largest_isolation_exists (k : ℕ) :
    ∃S : Finset (Fin n),S.card=min k n ∧
      (∀i∈S,∀j∉S,d.w j≤d.w i) ∧ d.residualSales S=d.tailSales k ∧
      ∃g,∃P : Partition n g,d.IsIsolationPartition S P ∧ g≤min k n+2 ∧
        d.TypeRespecting P ∧ d.totalCapacity P≤d.tailSales k ∧
        d.exAnteWidth P≤min d.precisionFloor (d.capacityMultiplier*d.tailSales k) := by
  obtain ⟨S,hcard,hs,horder⟩ := d.largestSales_top_weights k
  have hr : d.residualSales S=d.tailSales k := by rw [residualSales,hs,tailSales]
  obtain ⟨g,P,hP,hg,ht,_,_⟩ := d.isolation_partition_properties S
  refine ⟨S,hcard,horder,hr,g,P,hP,?_,ht,?_,?_⟩
  · simpa only [hcard] using hg
  · rw [←hr];exact d.isolation_capacity_bound S P hP
  · rw [←hr];exact d.isolation_welfare_bound S P hP

theorem largest_isolation_guarantee (k : ℕ) (eps : ℝ)
    (heps : d.capacityMultiplier*d.tailSales k≤eps) :
    ∃S : Finset (Fin n),S.card=min k n ∧ ∃g,∃P : Partition n g,
      d.IsIsolationPartition S P ∧ g≤min k n+2 ∧
      ∀c,d.Admissible c→d.manuscriptAnswerWidth P (d.groupTotal P c)≤eps := by
  obtain ⟨S,hcard,_,_,g,P,hP,hg,ht,_,hW⟩ := d.largest_isolation_exists k
  refine ⟨S,hcard,g,P,hP,hg,?_⟩
  exact (d.exAnteWidth_le_iff P ht eps).mp ((hW.trans (min_le_right _ _)).trans heps)

theorem residual_mass_certificate_minimal (k : ℕ) (S : Finset (Fin n))
    (hS : d.residualSales S=d.tailSales k) (T : Finset (Fin n)) (hT : T.card≤k) :
    d.residualSales S≤d.residualSales T ∧
      d.capacityMultiplier*d.residualSales S≤d.capacityMultiplier*d.residualSales T := by
  have h := hS ▸ d.tailSales_le_residual k T hT
  exact ⟨h,mul_le_mul_of_nonneg_left h d.capacityMultiplier_nonneg⟩

end CommodityClassification.Precision.Data
