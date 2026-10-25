module

public import LeanMath.CommodityClassification.PrecisionMomentWidth
public import Mathlib.Topology.Order.IsLUB

/-! The exact supremum of welfare discrepancies over the actual positive report fiber. -/
@[expose] public section
noncomputable section
set_option maxHeartbeats 1600000
namespace CommodityClassification.Precision.Data
open Matrix InputCoordinates Filter
open scoped BigOperators Topology
variable {n g : ℕ} (d : Precision.Data n)

def welfareDifferences (P : Partition n g) (J : Vec g) : Set ℝ :=
  {r | ∃a∈d.positiveFiber P J,∃b∈d.positiveFiber P J,|d.normalizedWelfare a-d.normalizedWelfare b|=r}

def answerWidth (P : Partition n g) (J : Vec g) : ℝ := sSup (d.welfareDifferences P J)

def actualWelfareDifferences (P : Partition n g) (J : Vec g) : Set ℝ :=
  {r | ∃a,∃ha : a∈d.positiveFiber P J,∃b,∃hb : b∈d.positiveFiber P J,
    |(d.family.model (d.candidate a ha.1)).lossCoefficient/d.nu-
      (d.family.model (d.candidate b hb.1)).lossCoefficient/d.nu|=r}

theorem lowerMoment_nonneg (P : Partition n g) (J : Vec g) : 0≤d.lowerMoment P J :=
  Finset.sum_nonneg (fun a _ => div_nonneg (sq_nonneg _) (d.groupWeight_pos P a).le)

theorem closedFiber_denominator_positive (P : Partition n g) (J : Vec g) (c : Vec n)
    (hc : c∈d.closedFiber P J) : 0<d.denominator d.sigma (d.secondMoment c) ((d.theta c)^2) :=
  d.denominator_positive_unit _ _ (d.secondMoment_nonneg c)
    (d.closedFiber_secondMoment_bounds P J c hc).2 (sq_nonneg _)

theorem fixed_report_welfare_formula (P : Partition n g) (hP : d.TypeRespecting P)
    (c e : Vec n) (he : d.groupTotal P e=d.groupTotal P c) :
    d.normalizedWelfare e=d.momentValue ((d.theta c)^2) (d.secondMoment e) := by
  rw [d.normalizedWelfare_momentValue,d.same_report_theta P hP e c he]

theorem momentWidth_actual_endpoints (P : Partition n g) (hP : d.TypeRespecting P)
    (c e : Vec n) (he : d.groupTotal P e=d.groupTotal P c) :
    d.momentWidth ((d.theta c)^2) (d.lowerMoment P (d.groupTotal P c)) (d.secondMoment e)=
      |d.normalizedWelfare (d.meanVector P c)-d.normalizedWelfare e| := by
  rw [d.momentWidth_eq_abs _ _ _ (sq_nonneg _),
    d.fixed_report_welfare_formula P hP c e he,
    d.fixed_report_welfare_formula P hP c (d.meanVector P c) (d.meanVector_report P c),
    d.meanVector_secondMoment]

theorem closedFiber_welfare_gap_bound (P : Partition n g) (hP : d.TypeRespecting P)
    (c e : Vec n) (he : e∈d.closedFiber P (d.groupTotal P c))
    (hm : IsMaxOn d.secondMoment (d.closedFiber P (d.groupTotal P c)) e)
    (a b : Vec n) (ha : a∈d.closedFiber P (d.groupTotal P c))
    (hb : b∈d.closedFiber P (d.groupTotal P c)) :
    |d.normalizedWelfare a-d.normalizedWelfare b|≤
      d.momentWidth ((d.theta c)^2) (d.lowerMoment P (d.groupTotal P c)) (d.secondMoment e) := by
  rw [d.fixed_report_welfare_formula P hP c a ha.2,d.fixed_report_welfare_formula P hP c b hb.2]
  exact d.momentWidth_interval_bound _ _ _ _ _ (sq_nonneg _)
    (d.lowerMoment_nonneg P _) (d.closedFiber_secondMoment_bounds P _ e he).2
    ⟨(d.closedFiber_secondMoment_bounds P _ a ha).1,hm ha⟩
    ⟨(d.closedFiber_secondMoment_bounds P _ b hb).1,hm hb⟩

theorem welfareDifferences_nonempty (P : Partition n g) (c : Vec n) (hc : d.Admissible c) :
    (d.welfareDifferences P (d.groupTotal P c)).Nonempty := by
  refine ⟨0,c,⟨hc,rfl⟩,c,⟨hc,rfl⟩,?_⟩
  simp

theorem welfareDifferences_isLUB (P : Partition n g) (hP : d.TypeRespecting P)
    (c e : Vec n) (hc : d.Admissible c) (he : e∈d.closedFiber P (d.groupTotal P c))
    (hm : IsMaxOn d.secondMoment (d.closedFiber P (d.groupTotal P c)) e) :
    IsLUB (d.welfareDifferences P (d.groupTotal P c))
      (d.momentWidth ((d.theta c)^2) (d.lowerMoment P (d.groupTotal P c)) (d.secondMoment e)) := by
  apply isLUB_of_mem_closure
  · rintro r ⟨a,ha,b,hb,rfl⟩
    exact d.closedFiber_welfare_gap_bound P hP c e he hm a b
      ⟨fun i => (ha.1.1 i).le,ha.2⟩ ⟨fun i => (hb.1.1 i).le,hb.2⟩
  · have hcont : ContinuousAt (fun a => |d.normalizedWelfare (d.meanVector P c)-d.normalizedWelfare a|) e :=
      (continuousAt_const.sub (d.normalizedWelfare_continuousAt e
        (d.closedFiber_denominator_positive P _ e he).ne')).abs
    have hmem := mem_closure_image hcont (d.closedFiber_subset_closure_positive P c hc he)
    have hsub : (fun a => |d.normalizedWelfare (d.meanVector P c)-d.normalizedWelfare a|) ''
        d.positiveFiber P (d.groupTotal P c)⊆d.welfareDifferences P (d.groupTotal P c) := by
      rintro r ⟨a,ha,rfl⟩
      exact ⟨d.meanVector P c,⟨d.meanVector_admissible P c hc,d.meanVector_report P c⟩,a,ha,rfl⟩
    rw [d.momentWidth_actual_endpoints P hP c e he.2]
    exact closure_mono hsub hmem

theorem answerWidth_formula (P : Partition n g) (hP : d.TypeRespecting P)
    (c e : Vec n) (hc : d.Admissible c) (he : e∈d.closedFiber P (d.groupTotal P c))
    (hm : IsMaxOn d.secondMoment (d.closedFiber P (d.groupTotal P c)) e) :
    d.answerWidth P (d.groupTotal P c)=
      d.momentWidth ((d.theta c)^2) (d.lowerMoment P (d.groupTotal P c)) (d.secondMoment e) :=
  (d.welfareDifferences_isLUB P hP c e hc he hm).csSup_eq (d.welfareDifferences_nonempty P c hc)

theorem actualWelfareDifferences_eq (P : Partition n g) (J : Vec g) :
    d.actualWelfareDifferences P J=d.welfareDifferences P J := by
  ext r
  constructor
  · rintro ⟨a,ha,b,hb,hr⟩
    rw [d.actual_normalized_coefficient a ha.1,d.actual_normalized_coefficient b hb.1] at hr
    exact ⟨a,ha,b,hb,hr⟩
  · rintro ⟨a,ha,b,hb,hr⟩
    refine ⟨a,ha,b,hb,?_⟩
    rw [d.actual_normalized_coefficient a ha.1,d.actual_normalized_coefficient b hb.1]
    exact hr

theorem actualWelfareDifferences_isLUB (P : Partition n g) (hP : d.TypeRespecting P)
    (c e : Vec n) (hc : d.Admissible c) (he : e∈d.closedFiber P (d.groupTotal P c))
    (hm : IsMaxOn d.secondMoment (d.closedFiber P (d.groupTotal P c)) e) :
    IsLUB (d.actualWelfareDifferences P (d.groupTotal P c))
      (d.momentWidth ((d.theta c)^2) (d.lowerMoment P (d.groupTotal P c)) (d.secondMoment e)) := by
  rw [d.actualWelfareDifferences_eq]
  exact d.welfareDifferences_isLUB P hP c e hc he hm

theorem actual_coefficient_gap_scaled (a b : Vec n) (ha : d.Admissible a) (hb : d.Admissible b) :
    |(d.family.model (d.candidate a ha)).lossCoefficient-(d.family.model (d.candidate b hb)).lossCoefficient|=
      d.nu*|d.normalizedWelfare a-d.normalizedWelfare b| := by
  rw [d.family.candidate_lossCoefficient,d.family.candidate_lossCoefficient]
  change |d.family.coefficient (d.coordinates a)-d.family.coefficient (d.coordinates b)|=_
  rw [d.coefficient_scaled_normalized a ha.2,d.coefficient_scaled_normalized b hb.2,
    ←mul_sub,abs_mul,abs_of_pos d.nu_pos]

end CommodityClassification.Precision.Data
