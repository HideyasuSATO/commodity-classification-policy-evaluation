module

public import LeanMath.CommodityClassification.PrecisionRefinementInformation

/-! Uniform answer and ex ante upper bounds for type-respecting classifications. -/
@[expose] public section
noncomputable section
set_option maxHeartbeats 1500000
namespace CommodityClassification.Precision.Data
open Matrix InputCoordinates
variable {n g h : ℕ} (d : Precision.Data n)

def feasibleWidths (P : Partition n g) : Set ℝ :=
  (fun c => d.manuscriptAnswerWidth P (d.groupTotal P c)) '' {c | d.Admissible c}
def exAnteWidth (P : Partition n g) : ℝ := sSup (d.feasibleWidths P)
def feasibleReports (P : Partition n g) : Set (Vec g) := d.groupTotal P '' {c | d.Admissible c}

theorem feasibleWidths_eq_report_image (P : Partition n g) :
    d.feasibleWidths P=d.manuscriptAnswerWidth P '' d.feasibleReports P := by
  rw [feasibleReports,Set.image_image]
  rfl

theorem exAnteWidth_report_formula (P : Partition n g) :
    d.exAnteWidth P=sSup (d.manuscriptAnswerWidth P '' d.feasibleReports P) := by
  rw [exAnteWidth,d.feasibleWidths_eq_report_image]

theorem typeRespecting_lowerMoment (P : Partition n g) (hP : d.TypeRespecting P) (c : Vec n) :
    (d.theta c)^2≤d.lowerMoment P (d.groupTotal P c) := by
  have hh := d.theta_sq_le_secondMoment (d.meanVector P c)
  rwa [d.meanVector_theta P hP c,d.meanVector_secondMoment] at hh

theorem typeRespecting_answer_upper (P : Partition n g) (hP : d.TypeRespecting P)
    (c : Vec n) (hc : d.Admissible c) : d.manuscriptAnswerWidth P (d.groupTotal P c)≤d.precisionFloor := by
  obtain ⟨e,he,hm⟩ := d.closedFiber_maximum P c hc
  have hb := d.closedFiber_secondMoment_bounds P _ e he
  have hlow := d.typeRespecting_lowerMoment P hP c
  have hx : (d.theta c)^2∈Set.Icc (0:ℝ) 1 := ⟨sq_nonneg _,hlow.trans (hb.1.trans hb.2)⟩
  rw [←d.answerWidth_eq_manuscript P hP c hc,d.answerWidth_formula P hP c e hc he hm,
    d.momentWidth_eq_abs _ _ _ (sq_nonneg _)]
  exact (d.momentWidth_interval_bound _ _ _ _ _ (sq_nonneg _) hx.1 le_rfl
    ⟨hlow,hb.1.trans hb.2⟩ ⟨hlow.trans hb.1,hb.2⟩).trans (d.scalar_envelope_upper _ hx)

theorem feasibleWidths_nonempty (P : Partition n g) : (d.feasibleWidths P).Nonempty :=
  ⟨_,0,d.zero_admissible,rfl⟩

theorem feasibleWidths_bddAbove (P : Partition n g) (hP : d.TypeRespecting P) :
    BddAbove (d.feasibleWidths P) := by
  refine ⟨d.precisionFloor,?_⟩
  rintro z ⟨c,hc,rfl⟩
  exact d.typeRespecting_answer_upper P hP c hc

theorem exAnteWidth_upper (P : Partition n g) (hP : d.TypeRespecting P) :
    d.exAnteWidth P≤d.precisionFloor := by
  apply csSup_le (d.feasibleWidths_nonempty P)
  rintro z ⟨c,hc,rfl⟩
  exact d.typeRespecting_answer_upper P hP c hc

theorem exAnteWidth_le_iff (P : Partition n g) (hP : d.TypeRespecting P) (eps : ℝ) :
    d.exAnteWidth P≤eps ↔ ∀c,d.Admissible c→d.manuscriptAnswerWidth P (d.groupTotal P c)≤eps := by
  constructor
  · intro hh c hc
    exact (le_csSup (d.feasibleWidths_bddAbove P hP) ⟨c,hc,rfl⟩).trans hh
  · intro hh
    apply csSup_le (d.feasibleWidths_nonempty P)
    rintro z ⟨c,hc,rfl⟩
    exact hh c hc

theorem typePartition_exAnte_upper : d.exAnteWidth d.typePartition≤d.precisionFloor :=
  d.exAnteWidth_upper d.typePartition d.typePartition_respecting

theorem refinement_exAnteWidth_le {P : Partition n g} {P0 : Partition n h}
    (R : Refinement P P0) (hP0 : d.TypeRespecting P0) : d.exAnteWidth P≤d.exAnteWidth P0 := by
  apply csSup_le (d.feasibleWidths_nonempty P)
  rintro z ⟨c,hc,rfl⟩
  exact (d.refinement_manuscriptWidth_le R hP0 c hc).trans
    (le_csSup (d.feasibleWidths_bddAbove P0 hP0) ⟨c,hc,rfl⟩)

theorem type_refinement_exAnte_upper {P : Partition n g} (R : Refinement P d.typePartition) :
    d.exAnteWidth P≤d.precisionFloor :=
  (d.refinement_exAnteWidth_le R d.typePartition_respecting).trans d.typePartition_exAnte_upper

end CommodityClassification.Precision.Data
