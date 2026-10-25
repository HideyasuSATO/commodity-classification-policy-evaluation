module

public import LeanMath.CommodityClassification.PrecisionWelfareBounds

/-! The manuscript's widths for arbitrary observations on the positive parent class. -/
@[expose] public section
noncomputable section
namespace CommodityClassification.Precision.Data
open Matrix InputCoordinates
variable {n g : ℕ} (d : Precision.Data n) {A : Type*}

def observationFiber (O : Vec n → A) (y : A) : Set (Vec n) :=
  {c | d.Admissible c ∧ O c=y}

def observationValues (O : Vec n → A) (y : A) : Set ℝ :=
  d.normalizedWelfare '' d.observationFiber O y

def observationAnswerWidth (O : Vec n → A) (y : A) : ℝ :=
  sSup (d.observationValues O y)-sInf (d.observationValues O y)

def observationReports (O : Vec n → A) : Set A := O '' {c | d.Admissible c}

def observationExAnteWidth (O : Vec n → A) : ℝ :=
  sSup (d.observationAnswerWidth O '' d.observationReports O)

theorem observationValues_nonempty (O : Vec n → A) (c : Vec n) (hc : d.Admissible c) :
    (d.observationValues O (O c)).Nonempty := ⟨_,c,⟨hc,rfl⟩,rfl⟩

theorem observationValues_subset_unit (O : Vec n → A) (y : A) :
    d.observationValues O y ⊆ Set.Icc 0 1 := by
  rintro x ⟨c,hc,rfl⟩
  exact d.normalizedWelfare_bounds c hc.1

theorem observationValues_bddAbove (O : Vec n → A) (y : A) :
    BddAbove (d.observationValues O y) := by
  refine ⟨1,?_⟩
  intro x hx
  exact (d.observationValues_subset_unit O y hx).2

theorem observationValues_bddBelow (O : Vec n → A) (y : A) :
    BddBelow (d.observationValues O y) := by
  refine ⟨0,?_⟩
  intro x hx
  exact (d.observationValues_subset_unit O y hx).1

theorem observationAnswerWidth_bounds (O : Vec n → A) (c : Vec n) (hc : d.Admissible c) :
    0 ≤ d.observationAnswerWidth O (O c) ∧ d.observationAnswerWidth O (O c) ≤ 1 := by
  have hn := d.observationValues_nonempty O c hc
  have hm : d.normalizedWelfare c∈d.observationValues O (O c) := ⟨c,⟨hc,rfl⟩,rfl⟩
  have hl := csInf_le (d.observationValues_bddBelow O (O c)) hm
  have hu := le_csSup (d.observationValues_bddAbove O (O c)) hm
  have h0 : 0 ≤ sInf (d.observationValues O (O c)) :=
    le_csInf hn (fun _ hx => (d.observationValues_subset_unit O (O c) hx).1)
  have h1 : sSup (d.observationValues O (O c)) ≤ 1 :=
    csSup_le hn (fun _ hx => (d.observationValues_subset_unit O (O c) hx).2)
  unfold observationAnswerWidth
  exact ⟨by linarith,by linarith⟩

theorem observation_pair_gap_le_width (O : Vec n → A) (c e : Vec n)
    (hc : d.Admissible c) (he : d.Admissible e) (hO : O e=O c) :
    |d.normalizedWelfare c-d.normalizedWelfare e| ≤ d.observationAnswerWidth O (O c) := by
  have hcm : d.normalizedWelfare c∈d.observationValues O (O c) := ⟨c,⟨hc,rfl⟩,rfl⟩
  have hem : d.normalizedWelfare e∈d.observationValues O (O c) := ⟨e,⟨he,hO⟩,rfl⟩
  have hcl := csInf_le (d.observationValues_bddBelow O (O c)) hcm
  have hcu := le_csSup (d.observationValues_bddAbove O (O c)) hcm
  have hel := csInf_le (d.observationValues_bddBelow O (O c)) hem
  have heu := le_csSup (d.observationValues_bddAbove O (O c)) hem
  unfold observationAnswerWidth
  exact abs_le.mpr ⟨by linarith,by linarith⟩

theorem observation_widths_nonempty (O : Vec n → A) :
    (d.observationAnswerWidth O '' d.observationReports O).Nonempty :=
  ⟨_,O 0,⟨0,d.zero_admissible,rfl⟩,rfl⟩

theorem observation_widths_bddAbove (O : Vec n → A) :
    BddAbove (d.observationAnswerWidth O '' d.observationReports O) := by
  refine ⟨1,?_⟩
  rintro x ⟨y,⟨c,hc,rfl⟩,rfl⟩
  exact (d.observationAnswerWidth_bounds O c hc).2

theorem observationExAnteWidth_bounds (O : Vec n → A) :
    0 ≤ d.observationExAnteWidth O ∧ d.observationExAnteWidth O ≤ 1 := by
  constructor
  · exact (d.observationAnswerWidth_bounds O 0 d.zero_admissible).1.trans
      (le_csSup (d.observation_widths_bddAbove O) ⟨O 0,⟨0,d.zero_admissible,rfl⟩,rfl⟩)
  · apply csSup_le (d.observation_widths_nonempty O)
    rintro x ⟨y,⟨c,hc,rfl⟩,rfl⟩
    exact (d.observationAnswerWidth_bounds O c hc).2

theorem observationExAnteWidth_le_iff (O : Vec n → A) (eps : ℝ) :
    d.observationExAnteWidth O ≤ eps ↔
      ∀c,d.Admissible c → d.observationAnswerWidth O (O c) ≤ eps := by
  constructor
  · intro hh c hc
    exact (le_csSup (d.observation_widths_bddAbove O) ⟨O c,⟨c,hc,rfl⟩,rfl⟩).trans hh
  · intro hh
    apply csSup_le (d.observation_widths_nonempty O)
    rintro x ⟨y,⟨c,hc,rfl⟩,rfl⟩
    exact hh c hc

theorem observation_partition_fiber (P : Partition n g) (J : Vec g) :
    d.observationFiber (d.groupTotal P) J=d.positiveFiber P J := rfl

theorem observation_partition_values (P : Partition n g) (J : Vec g) :
    d.observationValues (d.groupTotal P) J=d.welfareValues P J := rfl

theorem observation_partition_width (P : Partition n g) (J : Vec g) :
    d.observationAnswerWidth (d.groupTotal P) J=d.manuscriptAnswerWidth P J := rfl

theorem observation_partition_exAnte (P : Partition n g) :
    d.observationExAnteWidth (d.groupTotal P)=d.exAnteWidth P := by
  rw [d.exAnteWidth_report_formula]
  rfl

theorem arbitrary_partition_exAnte_le_iff (P : Partition n g) (eps : ℝ) :
    d.exAnteWidth P ≤ eps ↔ ∀c,d.Admissible c → d.manuscriptAnswerWidth P (d.groupTotal P c) ≤ eps := by
  rw [←d.observation_partition_exAnte]
  exact d.observationExAnteWidth_le_iff (d.groupTotal P) eps

theorem arbitrary_partition_pair_lower (P : Partition n g) (c e : Vec n)
    (hc : d.Admissible c) (he : d.Admissible e) (hO : d.groupTotal P e=d.groupTotal P c) :
    |d.normalizedWelfare c-d.normalizedWelfare e| ≤ d.exAnteWidth P := by
  have hh := d.observation_pair_gap_le_width (d.groupTotal P) c e hc he hO
  exact hh.trans ((d.arbitrary_partition_exAnte_le_iff P (d.exAnteWidth P)).mp le_rfl c hc)

end CommodityClassification.Precision.Data
