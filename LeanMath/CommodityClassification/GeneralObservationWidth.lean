module

public import LeanMath.CommodityClassification.RealSetWidth

/-! Arbitrary fixed observations, feasible-answer widths and their same-report characterization. -/
@[expose] public section
noncomputable section
namespace CommodityClassification.Information
variable {A B : Type*}

def BoundedValues (S : Set A) (f : A→ℝ) : Prop := BddAbove (f '' S) ∧ BddBelow (f '' S)
def values (S : Set A) (O : A→B) (f : A→ℝ) (y : B) : Set ℝ := f '' {x | x∈S ∧ O x=y}
def answerWidth (S : Set A) (O : A→B) (f : A→ℝ) (y : B) : ℝ := setWidth (values S O f y)
def worstWidth (S : Set A) (O : A→B) (f : A→ℝ) : ℝ := sSup (answerWidth S O f '' (O '' S))

theorem values_subset (S : Set A) (O : A→B) (f : A→ℝ) (y : B) : values S O f y⊆f '' S := by
  rintro z ⟨x,hx,rfl⟩
  exact ⟨x,hx.1,rfl⟩

theorem values_nonempty (S : Set A) (O : A→B) (f : A→ℝ) (x : A) (hx : x∈S) :
    (values S O f (O x)).Nonempty := ⟨f x,x,⟨hx,rfl⟩,rfl⟩

theorem answerWidth_nonneg (S : Set A) (O : A→B) (f : A→ℝ) (hf : BoundedValues S f)
    (x : A) (hx : x∈S) : 0≤answerWidth S O f (O x) :=
  setWidth_nonneg _ (values_nonempty S O f x hx)
    (hf.1.mono (values_subset S O f _)) (hf.2.mono (values_subset S O f _))

theorem answerWidth_le_global (S : Set A) (O : A→B) (f : A→ℝ) (hf : BoundedValues S f)
    (x : A) (hx : x∈S) : answerWidth S O f (O x)≤setWidth (f '' S) :=
  setWidth_mono (values_nonempty S O f x hx) (values_subset S O f _) hf.1 hf.2

theorem answerWidths_nonempty (S : Set A) (hne : S.Nonempty) (O : A→B) (f : A→ℝ) :
    (answerWidth S O f '' (O '' S)).Nonempty := hne.image O |>.image _

theorem answerWidths_bddAbove (S : Set A) (O : A→B) (f : A→ℝ) (hf : BoundedValues S f) :
    BddAbove (answerWidth S O f '' (O '' S)) := by
  refine ⟨setWidth (f '' S),?_⟩
  rintro y ⟨_,⟨x,hx,rfl⟩,rfl⟩
  exact answerWidth_le_global S O f hf x hx

theorem worstWidth_nonneg (S : Set A) (hne : S.Nonempty) (O : A→B) (f : A→ℝ)
    (hf : BoundedValues S f) : 0≤worstWidth S O f := by
  obtain ⟨x,hx⟩ := hne
  exact (answerWidth_nonneg S O f hf x hx).trans
    (le_csSup (answerWidths_bddAbove S O f hf) ⟨O x,⟨x,hx,rfl⟩,rfl⟩)

theorem worstWidth_le_iff (S : Set A) (hne : S.Nonempty) (O : A→B) (f : A→ℝ)
    (hf : BoundedValues S f) (eps : ℝ) :
    worstWidth S O f≤eps ↔ ∀x∈S,answerWidth S O f (O x)≤eps := by
  constructor
  · intro hh x hx
    exact (le_csSup (answerWidths_bddAbove S O f hf) ⟨O x,⟨x,hx,rfl⟩,rfl⟩).trans hh
  · intro hh
    apply csSup_le (answerWidths_nonempty S hne O f)
    rintro y ⟨_,⟨x,hx,rfl⟩,rfl⟩
    exact hh x hx

theorem worstWidth_pairs_iff (S : Set A) (hne : S.Nonempty) (O : A→B) (f : A→ℝ)
    (hf : BoundedValues S f) (eps : ℝ) :
    worstWidth S O f≤eps ↔ ∀x∈S,∀z∈S,O z=O x→|f x-f z|≤eps := by
  rw [worstWidth_le_iff S hne O f hf eps]
  constructor
  · intro hh x hx z hz hO
    exact (pair_le_setWidth _ (hf.1.mono (values_subset S O f _))
      (hf.2.mono (values_subset S O f _)) _ _ ⟨x,⟨hx,rfl⟩,rfl⟩ ⟨z,⟨hz,hO⟩,rfl⟩).trans (hh x hx)
  · intro hh x hx
    apply (setWidth_le_iff _ (values_nonempty S O f x hx)
      (hf.1.mono (values_subset S O f _)) (hf.2.mono (values_subset S O f _)) eps).mpr
    rintro a ⟨u,hu,rfl⟩ b ⟨v,hv,rfl⟩
    exact hh u hu.1 v hv.1 (hv.2.trans hu.2.symm)

theorem pair_le_worstWidth (S : Set A) (hne : S.Nonempty) (O : A→B) (f : A→ℝ)
    (hf : BoundedValues S f) (x z : A) (hx : x∈S) (hz : z∈S) (hO : O z=O x) :
    |f x-f z|≤worstWidth S O f :=
  (worstWidth_pairs_iff S hne O f hf _).mp le_rfl x hx z hz hO

end CommodityClassification.Information

namespace CommodityClassification.Precision.Data
open InputCoordinates
variable {n : ℕ} (d : Precision.Data n) {A : Type*}

theorem general_observation_values (O : Vec n→A) (y : A) :
    Information.values {c | d.Admissible c} O d.normalizedWelfare y=d.observationValues O y := rfl

theorem general_observation_width (O : Vec n→A) :
    Information.worstWidth {c | d.Admissible c} O d.normalizedWelfare=d.observationExAnteWidth O := rfl

theorem general_observation_bounded : Information.BoundedValues {c | d.Admissible c} d.normalizedWelfare := by
  constructor
  · refine ⟨1,?_⟩
    rintro y ⟨c,hc,rfl⟩
    exact (d.normalizedWelfare_bounds c hc).2
  · refine ⟨0,?_⟩
    rintro y ⟨c,hc,rfl⟩
    exact (d.normalizedWelfare_bounds c hc).1

end CommodityClassification.Precision.Data
