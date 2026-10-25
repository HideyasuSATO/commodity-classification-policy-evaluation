module

public import LeanMath.CommodityClassification.PrecisionClassificationVertex
public import Mathlib.Order.ConditionallyCompleteLattice.Finset

/-! Finite-sales concentration: the sum of the largest min(k,n) weights. -/
@[expose] public section
noncomputable section
set_option maxHeartbeats 1400000
namespace CommodityClassification.Precision.Data
open Matrix InputCoordinates
open scoped BigOperators
variable {n g : ℕ} (d : Precision.Data n)

def salesSums (k : ℕ) : Set ℝ :=
  (fun S : Finset (Fin n) => ∑i∈S,d.w i) '' {S | S.card≤k}

def largestSales (k : ℕ) : ℝ := sSup (d.salesSums k)

def coarseSales (m : ℕ) : ℝ := d.largestSales (m+1)

theorem salesSums_nonempty (k : ℕ) : (d.salesSums k).Nonempty :=
  ⟨0,∅,by simp,rfl⟩

theorem salesSums_finite (k : ℕ) : (d.salesSums k).Finite :=
  (Set.toFinite _).image _

theorem largestSales_isGreatest (k : ℕ) : IsGreatest (d.salesSums k) (d.largestSales k) :=
  (d.salesSums_nonempty k).isGreatest_csSup (d.salesSums_finite k)

theorem subset_sales_le_largest (k : ℕ) (S : Finset (Fin n)) (hS : S.card≤k) :
    (∑i∈S,d.w i)≤d.largestSales k := (d.largestSales_isGreatest k).2 ⟨S,hS,rfl⟩

theorem largestSales_bounds (k : ℕ) : 0≤d.largestSales k ∧ d.largestSales k≤1 := by
  constructor
  · simpa using d.subset_sales_le_largest k ∅ (by simp)
  · obtain ⟨S,_,hS⟩ := (d.largestSales_isGreatest k).1
    rw [←hS,←d.sum_w]
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ S) (fun i _ _ => (d.hw i).le)

theorem largestSales_attained (k : ℕ) :
    ∃S : Finset (Fin n),S.card=min k n ∧ (∑i∈S,d.w i)=d.largestSales k := by
  obtain ⟨S,hSk,hS⟩ := (d.largestSales_isGreatest k).1
  change (∑i∈S,d.w i)=d.largestSales k at hS
  refine ⟨S,?_,hS⟩
  have hn : S.card≤n := by simpa only [Fintype.card_fin] using S.card_le_univ
  have hle : S.card≤min k n := le_min hSk hn
  by_contra hne
  have hlt : S.card<min k n := lt_of_le_of_ne hle hne
  have hcard : S.card<(Finset.univ : Finset (Fin n)).card := by
    simpa using hlt.trans_le (min_le_right k n)
  obtain ⟨i,_,hi⟩ := Finset.exists_mem_notMem_of_card_lt_card hcard
  have hinsert : (insert i S).card≤k := by rw [Finset.card_insert_of_notMem hi]; omega
  have hh := d.subset_sales_le_largest k (insert i S) hinsert
  rw [Finset.sum_insert hi,hS] at hh
  linarith [d.hw i]

theorem largestSales_maximizer_ordered (k : ℕ) (S : Finset (Fin n)) (hSk : S.card≤k)
    (hS : (∑i∈S,d.w i)=d.largestSales k) (i j : Fin n) (hi : i∈S) (hj : j∉S) :
    d.w j≤d.w i := by
  have hje : j∉S.erase i := fun he => hj (Finset.mem_of_mem_erase he)
  have hc : (insert j (S.erase i)).card≤k := by
    rw [Finset.card_insert_of_notMem hje,Finset.card_erase_of_mem hi]
    have hp : 0<S.card := Finset.card_pos.mpr ⟨i,hi⟩
    omega
  have hh := d.subset_sales_le_largest k (insert j (S.erase i)) hc
  rw [Finset.sum_insert hje,←hS] at hh
  have he := Finset.sum_erase_add S d.w hi
  linarith

theorem largestSales_top_weights (k : ℕ) :
    ∃S : Finset (Fin n),S.card=min k n ∧ (∑i∈S,d.w i)=d.largestSales k ∧
      ∀i∈S,∀j∉S,d.w j≤d.w i := by
  obtain ⟨S,hc,hs⟩ := d.largestSales_attained k
  refine ⟨S,hc,hs,?_⟩
  intro i hi j hj
  exact d.largestSales_maximizer_ordered k S (hc ▸ min_le_left k n) hs i j hi hj

theorem largestSales_monotone : Monotone d.largestSales := by
  intro a b hab
  obtain ⟨S,hc,hs⟩ := d.largestSales_attained a
  rw [←hs]
  exact d.subset_sales_le_largest b S ((hc ▸ min_le_left a n).trans hab)

theorem largestSales_saturated (k : ℕ) (hk : n≤k) : d.largestSales k=1 := by
  apply le_antisymm (d.largestSales_bounds k).2
  have hh := d.subset_sales_le_largest k Finset.univ (by simpa using hk)
  simpa only [d.sum_w] using hh

theorem classification_vertex_concentration (P : Partition n g) (c : Vec n)
    (hc : ∀i,|c i|≤1) :
    ∃e,e∈(Precision.Box.slice (d.classificationConstraints P)
      (d.classificationConstraints P c)).extremePoints ℝ ∧
      IsMaxOn d.secondMoment (Precision.Box.slice (d.classificationConstraints P)
        (d.classificationConstraints P c)) e ∧
      d.theta e=d.theta c ∧ d.groupTotal P e=d.groupTotal P c ∧
      1-d.coarseSales g≤d.secondMoment e := by
  obtain ⟨e,he,hm,hr,hw⟩ := d.classification_vertex_weight_bound P c hc
  have hh := d.subset_sales_le_largest (g+1) (Precision.Box.interiors e) hr
  have hreport := (d.classificationConstraints_eq_iff P e c).mp he.1.2
  refine ⟨e,he,hm,hreport.1,hreport.2,?_⟩
  unfold coarseSales
  linarith

end CommodityClassification.Precision.Data
