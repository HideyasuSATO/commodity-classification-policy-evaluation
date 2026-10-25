module

public import LeanMath.CommodityClassification.PrecisionTypePartition

/-! Refinement preserves coarse answers and shrinks their welfare ranges. -/
@[expose] public section
noncomputable section
set_option maxHeartbeats 1400000
namespace CommodityClassification.Precision.Data
open Matrix InputCoordinates
variable {n g h : ℕ} (d : Precision.Data n)
variable {P : Partition n g} {P0 : Partition n h} (R : Refinement P P0)

include R

theorem refinement_typeRespecting (hP0 : d.TypeRespecting P0) : d.TypeRespecting P := by
  obtain ⟨v,hv⟩ := hP0
  refine ⟨fun a => v (R.parent a),?_⟩
  intro i
  rw [hv i,R.compatible i]

theorem refinement_groupTotal (c e : Vec n) (hh : d.groupTotal P c=d.groupTotal P e) :
    d.groupTotal P0 c=d.groupTotal P0 e := by
  have hM : P.report d.w (d.coordinates c)=P.report d.w (d.coordinates e) := by
    ext a j;fin_cases j
    change P.report d.w (d.coordinates c) a 0=P.report d.w (d.coordinates e) a 0
    rw [←d.groupTotal_report,←d.groupTotal_report,hh]
  have h0 := R.report_preserved d.w (d.coordinates c) (d.coordinates e) hM
  ext a
  rw [d.groupTotal_report,d.groupTotal_report,h0]

theorem refinement_positiveFiber (c : Vec n) :
    d.positiveFiber P (d.groupTotal P c)⊆d.positiveFiber P0 (d.groupTotal P0 c) := by
  intro e he
  exact ⟨he.1,d.refinement_groupTotal R e c he.2⟩

theorem refinement_welfareDifferences (c : Vec n) :
    d.welfareDifferences P (d.groupTotal P c)⊆d.welfareDifferences P0 (d.groupTotal P0 c) := by
  rintro r ⟨a,ha,b,hb,hr⟩
  exact ⟨a,d.refinement_positiveFiber R c ha,b,d.refinement_positiveFiber R c hb,hr⟩

theorem refinement_answerWidth_le (hP0 : d.TypeRespecting P0) (c : Vec n) (hc : d.Admissible c) :
    d.answerWidth P (d.groupTotal P c)≤d.answerWidth P0 (d.groupTotal P0 c) := by
  obtain ⟨e,he,hm⟩ := d.closedFiber_maximum P0 c hc
  have hB : BddAbove (d.welfareDifferences P0 (d.groupTotal P0 c)) :=
    ⟨_,(d.welfareDifferences_isLUB P0 hP0 c e hc he hm).1⟩
  apply csSup_le (d.welfareDifferences_nonempty P c hc)
  intro r hr
  exact le_csSup hB (d.refinement_welfareDifferences R c hr)

theorem refinement_manuscriptWidth_le (hP0 : d.TypeRespecting P0) (c : Vec n) (hc : d.Admissible c) :
    d.manuscriptAnswerWidth P (d.groupTotal P c)≤d.manuscriptAnswerWidth P0 (d.groupTotal P0 c) := by
  rw [←d.answerWidth_eq_manuscript P (d.refinement_typeRespecting R hP0) c hc,
    ←d.answerWidth_eq_manuscript P0 hP0 c hc]
  exact d.refinement_answerWidth_le R hP0 c hc

end CommodityClassification.Precision.Data
