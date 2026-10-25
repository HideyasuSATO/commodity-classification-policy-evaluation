module

public import LeanMath.CommodityClassification.LiteratureDispersionAlgebra

/-! All rows of the manuscript's precision decision table under their stated scopes. -/
@[expose] public section
noncomputable section
namespace CommodityClassification.Precision.Data
open InputCoordinates Information
variable {n g : ℕ} (d : Precision.Data n) {A : Type*}

def PrecisionGuaranteed (O : Vec n→A) (eps : ℝ) : Prop :=
  ∀c,d.Admissible c→∀e,d.Admissible e→O e=O c→
    |d.normalizedWelfare c-d.normalizedWelfare e|≤eps

theorem precisionGuaranteed_iff_width (O : Vec n→A) (eps : ℝ) :
    d.PrecisionGuaranteed O eps ↔ d.observationExAnteWidth O≤eps := by
  rw [←d.general_observation_width O]
  exact (worstWidth_pairs_iff _ ⟨0,d.zero_admissible⟩ _ _ d.general_observation_bounded eps).symm

theorem precisionGuaranteed_iff_partition_width (P : Partition n g) (eps : ℝ) :
    d.PrecisionGuaranteed (d.groupTotal P) eps ↔ d.exAnteWidth P≤eps := by
  rw [d.precisionGuaranteed_iff_width,d.observation_partition_exAnte]

theorem table_type_totals (eps : ℝ) (h : d.precisionFloor≤eps) :
    d.PrecisionGuaranteed (d.groupTotal d.typePartition) eps :=
  (d.precisionGuaranteed_iff_partition_width _ eps).mpr (d.typePartition_exAnte_upper.trans h)

theorem table_capacity_totals (P : Partition n g) (hP : d.TypeRespecting P)
    (eps : ℝ) (h : min d.precisionFloor (d.capacityMultiplier*d.totalCapacity P)≤eps) :
    d.PrecisionGuaranteed (d.groupTotal P) eps :=
  (d.precisionGuaranteed_iff_partition_width P eps).mpr ((d.exAnte_capacity_certificate P hP).trans h)

theorem table_all_partitions_failure (P : Partition n g) (eps : ℝ)
    (h : eps<d.coarseLowerWidth g) : ¬d.PrecisionGuaranteed (d.groupTotal P) eps := by
  rw [d.precisionGuaranteed_iff_partition_width]
  exact d.all_partition_failure P eps h

theorem table_conditional_precision (P : Partition n g) (c : Vec n) (hc : d.Admissible c)
    (eps : ℝ) : d.manuscriptAnswerWidth P (d.groupTotal P c)≤eps ↔
      ∀a∈d.welfareValues P (d.groupTotal P c),∀b∈d.welfareValues P (d.groupTotal P c),|a-b|≤eps := by
  exact setWidth_le_iff _ (d.welfareValues_nonempty P c hc)
    (d.observationValues_bddAbove (d.groupTotal P) _) (d.observationValues_bddBelow (d.groupTotal P) _) eps

theorem table_conditional_sharp_test (P : Partition n g) (hP : d.TypeRespecting P)
    (c e : Vec n) (hc : d.Admissible c) (he : e∈d.closedFiber P (d.groupTotal P c))
    (hm : IsMaxOn d.secondMoment (d.closedFiber P (d.groupTotal P c)) e) (eps : ℝ) :
    d.manuscriptAnswerWidth P (d.groupTotal P c)≤eps ↔
    d.lossScale*(d.theta c)^2*|1/d.denominator d.sigma (d.lowerMoment P (d.groupTotal P c)) ((d.theta c)^2)-
      1/d.denominator d.sigma (d.secondMoment e) ((d.theta c)^2)|≤eps := by
  rw [d.manuscriptAnswerWidth_formula P hP c e hc he hm]

theorem table_moment_exact : d.PrecisionGuaranteed d.momentReport 0 :=
  (d.precisionGuaranteed_iff_width _ 0).mpr d.momentReport_exAnte_zero.le

theorem table_half_width_prediction (O : Vec n→A) (eps : ℝ) :
    d.PrecisionGuaranteed O eps ↔ ∃a : A→ℝ,
      ∀c,d.Admissible c→|a (O c)-d.normalizedWelfare c|≤eps/2 := by
  rw [d.precisionGuaranteed_iff_width,d.width_tolerance_iff_prediction]

theorem table_matching_elasticities (h : d.eta=d.sigma) :
    d.PrecisionGuaranteed (d.groupTotal d.typePartition) 0 := by
  apply d.table_type_totals
  exact (d.precisionFloor_matching h).le

theorem table_largest_products (k : ℕ) (eps : ℝ) (h : d.capacityMultiplier*d.tailSales k≤eps) :
    ∃S : Finset (Fin n),S.card=min k n ∧ ∃g,∃P : Partition n g,
      d.IsIsolationPartition S P ∧ g≤min k n+2 ∧ d.PrecisionGuaranteed (d.groupTotal P) eps := by
  obtain ⟨S,hs,g,P,hP,hg,hw⟩ := d.largest_isolation_guarantee k eps h
  exact ⟨S,hs,g,P,hP,hg,(d.precisionGuaranteed_iff_partition_width P eps).mpr
    ((d.arbitrary_partition_exAnte_le_iff P eps).mpr hw)⟩

theorem table_residual_information {B : Type*} (theta : ℝ) (ht : theta≠0)
    (hs : d.eta≠d.sigma) (O : Vec n→B) :
    d.FixedThetaIdentified theta O d.normalizedWelfare ↔
      d.FixedThetaIdentified theta O d.secondMoment :=
  d.fixed_theta_information_iff theta ht hs O

end CommodityClassification.Precision.Data

namespace CommodityClassification.Information
theorem bounds_alone_straddle_tolerance (L U eps : ℝ) (hL : L≤eps) (hU : eps<U) :
    (∃x∈Set.Icc L U,x≤eps) ∧ (∃x∈Set.Icc L U,eps<x) :=
  ⟨⟨L,⟨le_rfl,hL.trans hU.le⟩,hL⟩,⟨U,⟨hL.trans hU.le,le_rfl⟩,hU⟩⟩
end CommodityClassification.Information
