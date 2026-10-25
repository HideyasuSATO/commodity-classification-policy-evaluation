module

public import LeanMath.CommodityClassification.PrecisionInteriorScalarWitness

/-! Uniformly positive indistinguishable technologies across diffuse economies. -/
@[expose] public section
noncomputable section
set_option maxHeartbeats 1800000
namespace CommodityClassification.Precision.Data
open InputCoordinates Filter
open scoped Topology
variable {n g : ℕ} (d : Precision.Data n)

theorem coarseMoment_tendsto {N : ℕ → ℕ} (E : ∀j,Precision.Data (N j)) (m : ℕ → ℕ)
    (hm : Tendsto (fun j => (E j).coarseSales (m j)) atTop (𝓝 0)) :
    Tendsto (fun j => (E j).coarseMoment (m j)) atTop (𝓝 1) := by
  have hh := squeeze_zero (fun j => ((E j).coarseMoment_deficit (m j)).1)
    (fun j => ((E j).coarseMoment_deficit (m j)).2) hm
  have hout : Tendsto (fun j => 1-(1-(E j).coarseMoment (m j))) atTop (𝓝 ((1:ℝ)-0)) :=
    tendsto_const_nhds.sub hh
  simpa only [sub_sub_cancel,sub_zero] using hout

theorem interpolatedWidth_coarse_tendsto {N : ℕ → ℕ} (E : ∀j,Precision.Data (N j)) (m : ℕ → ℕ)
    (hη : ∀j,(E j).eta=d.eta) (hα : ∀j,(E j).alpha=d.alpha)
    (hβ : ∀j,(E j).beta=d.beta) (hσ : ∀j,(E j).sigma=d.sigma)
    (hm : Tendsto (fun j => (E j).coarseSales (m j)) atTop (𝓝 0))
    (t : ℝ) (ht : 0≤t) (ht1 : t≤1) :
    Tendsto (fun j => (E j).interpolatedWidth t ((E j).coarseMoment (m j))) atTop
      (𝓝 (d.interpolatedWidth t 1)) := by
  have hb := d.interpolatedMoment_bounds t 1 ht ht1 ⟨d.criticalExposure_mem.2.le,le_rfl⟩
  have hK := d.denominator_positive_unit (d.interpolatedMoment t 1) d.criticalExposure
    (d.criticalExposure_mem.1.le.trans hb.1) hb.2 d.criticalExposure_mem.1.le
  have hlim := (d.interpolatedWidth_continuousAt t 1 hK.ne').tendsto.comp (coarseMoment_tendsto E m hm)
  convert hlim using 1
  funext j
  exact (E j).interpolatedWidth_parameters_eq d (hη j) (hα j) (hβ j) (hσ j) t _

theorem finite_uniform_share_witness (P : Partition n g) (t : ℝ) (ht : 0≤t) (ht1 : t<1) :
    ∃c,d.Admissible c ∧ d.groupTotal P c=d.groupTotal P d.criticalInputs ∧
      d.theta c=d.theta d.criticalInputs ∧
      (∀i j,d.shareFloor t≤d.inputs d.criticalInputs i j ∧ d.shareFloor t≤d.inputs c i j) ∧
      d.interpolatedWidth t (d.coarseMoment g)≤|d.normalizedWelfare d.criticalInputs-d.normalizedWelfare c| := by
  obtain ⟨e,he,_,hθ,hj,hq⟩ := d.classification_vertex_concentration P d.criticalInputs
    (fun i => (d.criticalInputs_admissible.1 i).le)
  have hclosed : e∈d.closedFiber P (d.groupTotal P d.criticalInputs) := ⟨he.1.1,hj⟩
  have hlo := d.theta_sq_le_secondMoment e
  rw [hθ,d.criticalInputs_theta_sq] at hlo
  have hhi := (d.closedFiber_secondMoment_bounds P _ e hclosed).2
  have hqm : d.coarseMoment g≤d.secondMoment e := max_le hlo hq
  have hQ := d.interpolatedMoment_bounds t (d.secondMoment e) ht ht1.le ⟨hlo,hhi⟩
  have hq0 := (d.interpolatedMoment_bounds t (d.coarseMoment g) ht ht1.le (d.coarseMoment_bounds g)).1
  have hq1 : d.interpolatedMoment t (d.coarseMoment g)≤d.interpolatedMoment t (d.secondMoment e) := by
    unfold interpolatedMoment
    nlinarith [mul_nonneg (sq_nonneg t) (sub_nonneg.mpr hqm)]
  refine ⟨d.fixedLoadPath e t,d.fixedLoadPath_admissible P e hclosed t ht ht1,
    d.fixedLoadPath_report P e hj t,d.fixedLoadPath_theta e hθ t,?_,?_⟩
  · intro i j
    exact ⟨d.criticalInputs_share_lower t ht i j,d.fixedLoadPath_share_lower e he.1.1 t ht ht1.le i j⟩
  · rw [normalizedWelfare_momentValue,normalizedWelfare_momentValue,d.fixedLoadPath_theta e hθ,
      d.criticalInputs_theta_sq,d.criticalInputs_secondMoment,d.fixedLoadPath_secondMoment e hθ]
    change d.interpolatedWidth t (d.coarseMoment g)≤
      |d.momentValue d.criticalExposure d.criticalExposure-
        d.momentValue d.criticalExposure (d.interpolatedMoment t (d.secondMoment e))|
    rw [←d.momentWidth_eq_abs _ _ _ d.criticalExposure_mem.1.le,interpolatedWidth,
      d.momentWidth_eq_abs _ _ _ d.criticalExposure_mem.1.le]
    exact d.momentWidth_interval_bound _ _ _ _ _ d.criticalExposure_mem.1.le
      d.criticalExposure_mem.1.le hQ.2 ⟨le_rfl,hQ.1⟩ ⟨hq0,hq1⟩

theorem uniform_positive_witnesses {N : ℕ → ℕ} (E : ∀j,Precision.Data (N j)) (m : ℕ → ℕ)
    (hη : ∀j,(E j).eta=d.eta) (hα : ∀j,(E j).alpha=d.alpha)
    (hβ : ∀j,(E j).beta=d.beta) (hσ : ∀j,(E j).sigma=d.sigma)
    (hm : Tendsto (fun j => (E j).coarseSales (m j)) atTop (𝓝 0))
    (eps : ℝ) (hε : eps<d.precisionFloor) :
    ∃t δ : ℝ,0≤t ∧ t<1 ∧ δ=d.shareFloor t ∧ 0<δ ∧
      ∀ᶠj in atTop,∀P : Partition (N j) (m j),∃c,(E j).Admissible c ∧
        (E j).groupTotal P c=(E j).groupTotal P (E j).criticalInputs ∧
        (E j).theta c=(E j).theta (E j).criticalInputs ∧
        (∀i a,δ≤(E j).inputs (E j).criticalInputs i a ∧ δ≤(E j).inputs c i a) ∧
        eps < |(E j).normalizedWelfare (E j).criticalInputs-(E j).normalizedWelfare c| := by
  obtain ⟨t,ht,ht1,hδ,hgap⟩ := d.exists_interior_fraction eps hε
  refine ⟨t,d.shareFloor t,ht,ht1,rfl,hδ,?_⟩
  have hg := (d.interpolatedWidth_coarse_tendsto E m hη hα hβ hσ hm t ht ht1.le).eventually
    (eventually_gt_nhds hgap)
  filter_upwards [hg] with j hj
  intro P
  obtain ⟨c,hc,hrep,hload,hshares,hval⟩ := (E j).finite_uniform_share_witness P t ht ht1
  refine ⟨c,hc,hrep,hload,?_,hj.trans_le hval⟩
  rwa [(E j).shareFloor_parameters_eq d (hη j) (hα j) (hσ j) t] at hshares

theorem uniform_actual_witnesses {N : ℕ → ℕ} (E : ∀j,Precision.Data (N j)) (m : ℕ → ℕ)
    (hη : ∀j,(E j).eta=d.eta) (hα : ∀j,(E j).alpha=d.alpha)
    (hβ : ∀j,(E j).beta=d.beta) (hσ : ∀j,(E j).sigma=d.sigma)
    (hm : Tendsto (fun j => (E j).coarseSales (m j)) atTop (𝓝 0))
    (eps : ℝ) (hε : eps<d.precisionFloor) :
    ∃δ : ℝ,0<δ ∧ ∀ᶠj in atTop,∀P : Partition (N j) (m j),
      ∃c,∃hc : (E j).Admissible c,
        (E j).groupTotal P c=(E j).groupTotal P (E j).criticalInputs ∧
        (E j).theta c=(E j).theta (E j).criticalInputs ∧
        (∀i a,δ≤(E j).inputs (E j).criticalInputs i a ∧ δ≤(E j).inputs c i a) ∧
        eps < |((E j).family.model ((E j).candidate (E j).criticalInputs
            (E j).criticalInputs_admissible)).lossCoefficient/(E j).nu-
          ((E j).family.model ((E j).candidate c hc)).lossCoefficient/(E j).nu| := by
  obtain ⟨_,δ,_,_,_,hδ,hh⟩ := d.uniform_positive_witnesses E m hη hα hβ hσ hm eps hε
  refine ⟨δ,hδ,?_⟩
  filter_upwards [hh] with j hj
  intro P
  obtain ⟨c,hc,hrep,hload,hshares,hgap⟩ := hj P
  refine ⟨c,hc,hrep,hload,hshares,?_⟩
  rwa [(E j).actual_normalized_coefficient,(E j).actual_normalized_coefficient]

end CommodityClassification.Precision.Data
