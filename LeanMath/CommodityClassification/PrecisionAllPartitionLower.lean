module

public import LeanMath.CommodityClassification.PrecisionFixedLoadPath

/-! The finite-N ex ante lower bound for every classification, including mixed types. -/
@[expose] public section
noncomputable section
set_option maxHeartbeats 1600000
namespace CommodityClassification.Precision.Data
open Matrix InputCoordinates Filter
open scoped BigOperators Topology
variable {n g : ℕ} (d : Precision.Data n)

def coarseMoment (m : ℕ) : ℝ := max d.criticalExposure (1-d.coarseSales m)
def coarseLowerWidth (m : ℕ) : ℝ := d.momentWidth d.criticalExposure d.criticalExposure (d.coarseMoment m)

theorem coarseMoment_bounds (m : ℕ) : d.coarseMoment m∈Set.Icc d.criticalExposure 1 := by
  exact ⟨le_max_left _ _,max_le d.criticalExposure_mem.2.le (by
    have hh := (d.largestSales_bounds (m+1)).1
    unfold coarseSales
    linarith)⟩

theorem coarseLowerWidth_nonneg (m : ℕ) : 0≤d.coarseLowerWidth m :=
  d.momentWidth_nonneg _ _ _ d.criticalExposure_mem.1.le

theorem coarseLowerWidth_manuscript (m : ℕ) :
    d.coarseLowerWidth m=d.lossScale*d.criticalExposure*
      |(d.denominator d.sigma (d.coarseMoment m) d.criticalExposure)⁻¹-
        (d.denominator d.sigma d.criticalExposure d.criticalExposure)⁻¹| := by
  unfold coarseLowerWidth momentWidth
  rw [one_div,one_div,abs_sub_comm]

theorem coarseLowerWidth_le_floor (m : ℕ) : d.coarseLowerWidth m≤d.precisionFloor := by
  unfold coarseLowerWidth
  rw [d.momentWidth_eq_abs _ _ _ d.criticalExposure_mem.1.le]
  exact (d.momentWidth_interval_bound _ _ 1 _ _ d.criticalExposure_mem.1.le
    d.criticalExposure_mem.1.le le_rfl ⟨le_rfl,d.criticalExposure_mem.2.le⟩
    (d.coarseMoment_bounds m)).trans (d.scalar_envelope_upper _ ⟨d.criticalExposure_mem.1.le,
      d.criticalExposure_mem.2.le⟩)

theorem coarseLowerWidth_matching (m : ℕ) (hs : d.eta=d.sigma) : d.coarseLowerWidth m=0 :=
  d.momentWidth_matching_elasticity _ _ _ hs

theorem classification_lower_vertex (P : Partition n g) :
    ∃e,e∈d.closedFiber P (d.groupTotal P d.criticalInputs) ∧
      d.theta e=d.theta d.criticalInputs ∧
      d.coarseLowerWidth g≤|d.normalizedWelfare d.criticalInputs-d.normalizedWelfare e| := by
  obtain ⟨e,he,_,ht,hj,hq⟩ := d.classification_vertex_concentration P d.criticalInputs
    (fun i => (d.criticalInputs_admissible.1 i).le)
  have hclosed : e∈d.closedFiber P (d.groupTotal P d.criticalInputs) := ⟨he.1.1,hj⟩
  have hlow := d.theta_sq_le_secondMoment e
  rw [ht,d.criticalInputs_theta_sq] at hlow
  have hhigh := (d.closedFiber_secondMoment_bounds P _ e hclosed).2
  have hqm : d.coarseMoment g≤d.secondMoment e := max_le hlow hq
  have hbound := d.momentWidth_interval_bound d.criticalExposure d.criticalExposure
    (d.secondMoment e) d.criticalExposure (d.coarseMoment g)
    d.criticalExposure_mem.1.le d.criticalExposure_mem.1.le hhigh
    ⟨le_rfl,hlow⟩ ⟨(d.coarseMoment_bounds g).1,hqm⟩
  refine ⟨e,hclosed,ht,?_⟩
  rw [normalizedWelfare_momentValue,normalizedWelfare_momentValue,ht,
    d.criticalInputs_theta_sq,d.criticalInputs_secondMoment]
  rw [coarseLowerWidth,d.momentWidth_eq_abs _ _ _ d.criticalExposure_mem.1.le]
  rwa [d.momentWidth_eq_abs _ _ _ d.criticalExposure_mem.1.le] at hbound

theorem all_partition_lower (P : Partition n g) : d.coarseLowerWidth g≤d.exAnteWidth P := by
  obtain ⟨e,he,_,hl⟩ := d.classification_lower_vertex P
  exact hl.trans (d.fixedLoadPath_pair_lower P e he)

theorem all_partition_failure (P : Partition n g) (eps : ℝ) (hε : eps<d.coarseLowerWidth g) :
    ¬d.exAnteWidth P≤eps := not_le.mpr (hε.trans_le (d.all_partition_lower P))

theorem all_partition_positive_witness (P : Partition n g) (eps : ℝ)
    (hε : eps<d.coarseLowerWidth g) :
    ∃e,d.Admissible e ∧ d.groupTotal P e=d.groupTotal P d.criticalInputs ∧
      d.theta e=d.theta d.criticalInputs ∧
      eps < |d.normalizedWelfare d.criticalInputs-d.normalizedWelfare e| := by
  obtain ⟨e,he,hθ,hl⟩ := d.classification_lower_vertex P
  have hlim : Tendsto
      (fun t : ℝ => |d.normalizedWelfare d.criticalInputs-d.normalizedWelfare (d.fixedLoadPath e t)|)
      (𝓝[<] (1:ℝ)) (𝓝 |d.normalizedWelfare d.criticalInputs-d.normalizedWelfare e|) :=
    (tendsto_const_nhds.sub (d.fixedLoadPath_welfare_limit P e he)).abs
  have hgap : ∀ᶠt : ℝ in 𝓝[<] (1:ℝ),
      eps < |d.normalizedWelfare d.criticalInputs-d.normalizedWelfare (d.fixedLoadPath e t)| :=
    hlim.eventually (eventually_gt_nhds (hε.trans_le hl))
  have h0 : ∀ᶠt : ℝ in 𝓝[<] (1:ℝ),0≤t :=
    (eventually_ge_nhds (by norm_num : (0:ℝ)<1)).filter_mono nhdsWithin_le_nhds
  have hex : ∀ᶠt : ℝ in 𝓝[<] (1:ℝ),0≤t ∧ t<1 ∧
      eps < |d.normalizedWelfare d.criticalInputs-d.normalizedWelfare (d.fixedLoadPath e t)| := by
    filter_upwards [h0,self_mem_nhdsWithin,hgap] with t ht ht1 hg
    exact ⟨ht,ht1,hg⟩
  obtain ⟨t,ht,ht1,hg⟩ := hex.exists
  exact ⟨d.fixedLoadPath e t,d.fixedLoadPath_admissible P e he t ht ht1,
    d.fixedLoadPath_report P e he.2 t,d.fixedLoadPath_theta e hθ t,hg⟩

theorem all_partition_actual_witness (P : Partition n g) (eps : ℝ)
    (hε : eps<d.coarseLowerWidth g) :
    ∃e,∃he : d.Admissible e,d.groupTotal P e=d.groupTotal P d.criticalInputs ∧
      d.theta e=d.theta d.criticalInputs ∧
      eps < |(d.family.model (d.candidate d.criticalInputs d.criticalInputs_admissible)).lossCoefficient/d.nu-
        (d.family.model (d.candidate e he)).lossCoefficient/d.nu| := by
  obtain ⟨e,he,hj,ht,hg⟩ := d.all_partition_positive_witness P eps hε
  refine ⟨e,he,hj,ht,?_⟩
  rwa [d.actual_normalized_coefficient,d.actual_normalized_coefficient]

end CommodityClassification.Precision.Data
