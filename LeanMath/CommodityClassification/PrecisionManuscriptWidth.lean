module

public import LeanMath.CommodityClassification.PrecisionSharpWelfareWidth
public import Mathlib.Topology.Instances.ENNReal.Lemmas

/-! Identification with the manuscript's supremum-minus-infimum convention. -/
@[expose] public section
noncomputable section
set_option maxHeartbeats 1400000
namespace CommodityClassification.Precision.Data
open Matrix InputCoordinates
variable {n g : ℕ} (d : Precision.Data n)

def welfareValues (P : Partition n g) (J : Vec g) : Set ℝ :=
  d.normalizedWelfare '' d.positiveFiber P J

def manuscriptAnswerWidth (P : Partition n g) (J : Vec g) : ℝ :=
  sSup (d.welfareValues P J)-sInf (d.welfareValues P J)

theorem welfareValues_nonempty (P : Partition n g) (c : Vec n) (hc : d.Admissible c) :
    (d.welfareValues P (d.groupTotal P c)).Nonempty :=
  ⟨d.normalizedWelfare c,c,⟨hc,rfl⟩,rfl⟩

theorem welfareValues_bounded (P : Partition n g) (hP : d.TypeRespecting P)
    (c : Vec n) (hc : d.Admissible c) : Bornology.IsBounded (d.welfareValues P (d.groupTotal P c)) := by
  obtain ⟨e,he,hm⟩ := d.closedFiber_maximum P c hc
  apply Metric.isBounded_iff.mpr
  refine ⟨d.momentWidth ((d.theta c)^2) (d.lowerMoment P (d.groupTotal P c)) (d.secondMoment e),?_⟩
  rintro x ⟨a,ha,rfl⟩ y ⟨b,hb,rfl⟩
  exact d.closedFiber_welfare_gap_bound P hP c e he hm a b
    ⟨fun i => (ha.1.1 i).le,ha.2⟩ ⟨fun i => (hb.1.1 i).le,hb.2⟩

theorem welfareDifferences_diameter_isLUB (P : Partition n g) (hP : d.TypeRespecting P)
    (c : Vec n) (hc : d.Admissible c) :
    IsLUB (d.welfareDifferences P (d.groupTotal P c)) (Metric.diam (d.welfareValues P (d.groupTotal P c))) := by
  have hB := d.welfareValues_bounded P hP c hc
  constructor
  · rintro r ⟨a,ha,b,hb,rfl⟩
    exact Metric.dist_le_diam_of_mem hB ⟨a,ha,rfl⟩ ⟨b,hb,rfl⟩
  · intro z hz
    apply Metric.diam_le_of_forall_dist_le_of_nonempty (d.welfareValues_nonempty P c hc)
    rintro x ⟨a,ha,rfl⟩ y ⟨b,hb,rfl⟩
    exact hz ⟨a,ha,b,hb,rfl⟩

theorem answerWidth_eq_manuscript (P : Partition n g) (hP : d.TypeRespecting P)
    (c : Vec n) (hc : d.Admissible c) :
    d.answerWidth P (d.groupTotal P c)=d.manuscriptAnswerWidth P (d.groupTotal P c) := by
  change sSup (d.welfareDifferences P (d.groupTotal P c))=_
  rw [(d.welfareDifferences_diameter_isLUB P hP c hc).csSup_eq
    (d.welfareDifferences_nonempty P c hc),Real.diam_eq (d.welfareValues_bounded P hP c hc)]
  rfl

theorem manuscriptAnswerWidth_formula (P : Partition n g) (hP : d.TypeRespecting P)
    (c e : Vec n) (hc : d.Admissible c) (he : e∈d.closedFiber P (d.groupTotal P c))
    (hm : IsMaxOn d.secondMoment (d.closedFiber P (d.groupTotal P c)) e) :
    d.manuscriptAnswerWidth P (d.groupTotal P c)=
      d.lossScale*(d.theta c)^2*|1/d.denominator d.sigma (d.lowerMoment P (d.groupTotal P c)) ((d.theta c)^2)-
        1/d.denominator d.sigma (d.secondMoment e) ((d.theta c)^2)| := by
  rw [←d.answerWidth_eq_manuscript P hP c hc,d.answerWidth_formula P hP c e hc he hm]
  rfl

theorem manuscriptAnswerWidth_zero_load (P : Partition n g) (hP : d.TypeRespecting P)
    (c : Vec n) (hc : d.Admissible c) (ht : d.theta c=0) :
    d.manuscriptAnswerWidth P (d.groupTotal P c)=0 := by
  obtain ⟨e,he,hm⟩ := d.closedFiber_maximum P c hc
  rw [←d.answerWidth_eq_manuscript P hP c hc,d.answerWidth_formula P hP c e hc he hm,ht]
  simp [d.momentWidth_zero_load]

theorem manuscriptAnswerWidth_matching_elasticity (P : Partition n g) (hP : d.TypeRespecting P)
    (c : Vec n) (hc : d.Admissible c) (hs : d.eta=d.sigma) :
    d.manuscriptAnswerWidth P (d.groupTotal P c)=0 := by
  obtain ⟨e,he,hm⟩ := d.closedFiber_maximum P c hc
  rw [←d.answerWidth_eq_manuscript P hP c hc,d.answerWidth_formula P hP c e hc he hm,
    d.momentWidth_matching_elasticity _ _ _ hs]

end CommodityClassification.Precision.Data
