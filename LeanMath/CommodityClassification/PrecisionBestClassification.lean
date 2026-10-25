module

public import LeanMath.CommodityClassification.ExactCardinalityRefinement

/-! The infimum over all exact-m classifications and its matching precision limit. -/
@[expose] public section
noncomputable section
set_option maxHeartbeats 1400000
namespace CommodityClassification.Precision.Data
open InputCoordinates Filter
open scoped Topology
variable {n : ℕ} (d : Precision.Data n)

def classificationWidths (m : ℕ) : Set ℝ := Set.range (fun P : Partition n m => d.exAnteWidth P)
def bestClassificationWidth (m : ℕ) : ℝ := sInf (d.classificationWidths m)

theorem classificationWidths_nonempty (m : ℕ) (h2 : 2≤m) (hm : m≤n) :
    (d.classificationWidths m).Nonempty := by
  obtain ⟨P,_,_⟩ := d.exact_type_partition_exists m h2 hm
  exact ⟨d.exAnteWidth P,P,rfl⟩

theorem classificationWidths_bddBelow (m : ℕ) : BddBelow (d.classificationWidths m) := by
  refine ⟨d.coarseLowerWidth m,?_⟩
  rintro x ⟨P,rfl⟩
  exact d.all_partition_lower P

theorem bestClassificationWidth_lower (m : ℕ) (h2 : 2≤m) (hm : m≤n) :
    d.coarseLowerWidth m≤d.bestClassificationWidth m := by
  apply le_csInf (d.classificationWidths_nonempty m h2 hm)
  rintro x ⟨P,rfl⟩
  exact d.all_partition_lower P

theorem bestClassificationWidth_upper (m : ℕ) (h2 : 2≤m) (hm : m≤n) :
    d.bestClassificationWidth m≤d.precisionFloor := by
  obtain ⟨P,_,hu⟩ := d.exact_type_partition_exists m h2 hm
  exact (csInf_le (d.classificationWidths_bddBelow m) ⟨P,rfl⟩).trans hu

theorem bestClassificationWidth_error (m : ℕ) (h2 : 2≤m) (hm : m≤n) :
    0≤d.precisionFloor-d.bestClassificationWidth m ∧
      d.precisionFloor-d.bestClassificationWidth m≤d.coarseErrorConstant*d.coarseSales m := by
  have hl := d.bestClassificationWidth_lower m h2 hm
  have hu := d.bestClassificationWidth_upper m h2 hm
  have he := (d.precisionFloor_error_bound m).2
  exact ⟨by linarith,by linarith⟩

theorem bestClassificationWidth_tendsto {N : ℕ → ℕ} (E : ∀j,Precision.Data (N j)) (m : ℕ → ℕ)
    (hη : ∀j,(E j).eta=d.eta) (hα : ∀j,(E j).alpha=d.alpha)
    (hβ : ∀j,(E j).beta=d.beta) (hσ : ∀j,(E j).sigma=d.sigma)
    (hsize : ∀j,2≤m j ∧ m j≤N j)
    (hm : Tendsto (fun j => (E j).coarseSales (m j)) atTop (𝓝 0)) :
    Tendsto (fun j => (E j).bestClassificationWidth (m j)) atTop (𝓝 d.precisionFloor) := by
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le
    (d.lowerWidth_tendsto E m hη hα hβ hσ hm) tendsto_const_nhds
  · intro j
    exact (E j).bestClassificationWidth_lower (m j) (hsize j).1 (hsize j).2
  · intro j
    have hh := (E j).bestClassificationWidth_upper (m j) (hsize j).1 (hsize j).2
    rwa [(E j).precisionFloor_parameters_eq d (hη j) (hα j) (hβ j) (hσ j)] at hh

end CommodityClassification.Precision.Data
