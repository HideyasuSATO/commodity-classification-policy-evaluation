module

public import LeanMath.CommodityClassification.PrecisionUniformShareBounds

/-! Choose the interior interpolation fraction before the product count or partition. -/
@[expose] public section
noncomputable section
set_option maxHeartbeats 1500000
namespace CommodityClassification.Precision.Data
open InputCoordinates Filter
open scoped Topology
variable {n : ℕ} (d : Precision.Data n)

def interpolatedMoment (t q : ℝ) : ℝ := d.criticalExposure+t^2*(q-d.criticalExposure)
def interpolatedWidth (t q : ℝ) : ℝ :=
  d.momentWidth d.criticalExposure d.criticalExposure (d.interpolatedMoment t q)

theorem interpolatedMoment_bounds (t q : ℝ) (ht : 0≤t) (ht1 : t≤1)
    (hq : q∈Set.Icc d.criticalExposure 1) :
    d.interpolatedMoment t q∈Set.Icc d.criticalExposure 1 := by
  have hs : t^2≤1 := by nlinarith
  have hp := mul_nonneg (sq_nonneg t) (sub_nonneg.mpr hq.1)
  have hu := mul_le_mul_of_nonneg_right hs (sub_nonneg.mpr hq.1)
  unfold interpolatedMoment
  exact ⟨by linarith,by nlinarith [hq.2]⟩

theorem momentWidth_continuousAt_right (x q0 q : ℝ)
    (hK : d.denominator d.sigma q x≠0) : ContinuousAt (d.momentWidth x q0) q := by
  have hd : Continuous (fun z => d.denominator d.sigma z x) := by unfold denominator;fun_prop
  exact continuousAt_const.mul ((continuousAt_const.sub
    (continuousAt_const.div hd.continuousAt hK)).abs)

theorem interpolatedWidth_continuousAt (t q : ℝ)
    (hK : d.denominator d.sigma (d.interpolatedMoment t q) d.criticalExposure≠0) :
    ContinuousAt (fun z => d.interpolatedWidth t z) q := by
  have hM : Continuous (d.interpolatedMoment t) := by unfold interpolatedMoment;fun_prop
  exact (d.momentWidth_continuousAt_right _ _ _ hK).comp hM.continuousAt

theorem interpolatedWidth_to_floor :
    Tendsto (fun t => d.interpolatedWidth t 1) (𝓝[<] (1:ℝ)) (𝓝 d.precisionFloor) := by
  have hK := d.denominator_positive_unit 1 d.criticalExposure (by norm_num) le_rfl
    d.criticalExposure_mem.1.le
  have hM : Continuous (fun t => d.interpolatedMoment t 1) := by unfold interpolatedMoment;fun_prop
  have he : d.interpolatedMoment 1 1=1 := by unfold interpolatedMoment;ring
  have hC := (d.momentWidth_continuousAt_right d.criticalExposure d.criticalExposure 1 hK.ne')
  rw [←he] at hC
  have hcomp : ContinuousAt (fun t : ℝ => d.momentWidth d.criticalExposure d.criticalExposure
      (d.interpolatedMoment t 1)) 1 :=
    hC.comp (f := fun t : ℝ => d.interpolatedMoment t 1) hM.continuousAt
  have hlim := hcomp.tendsto.mono_left
    (nhdsWithin_le_nhds (a := (1:ℝ)) (s := Set.Iio 1))
  simpa only [interpolatedWidth,he,d.scalar_envelope_attains] using hlim

theorem exists_interior_fraction (eps : ℝ) (hε : eps<d.precisionFloor) :
    ∃t : ℝ,0≤t ∧ t<1 ∧ 0<d.shareFloor t ∧ eps<d.interpolatedWidth t 1 := by
  have hg := d.interpolatedWidth_to_floor.eventually (eventually_gt_nhds hε)
  have h0 : ∀ᶠt : ℝ in 𝓝[<] (1:ℝ),0≤t :=
    (eventually_ge_nhds (by norm_num : (0:ℝ)<1)).filter_mono nhdsWithin_le_nhds
  have hh : ∀ᶠt : ℝ in 𝓝[<] (1:ℝ),0≤t ∧ t<1 ∧ eps<d.interpolatedWidth t 1 := by
    filter_upwards [h0,self_mem_nhdsWithin,hg] with t ht ht1 hgap
    exact ⟨ht,ht1,hgap⟩
  obtain ⟨t,ht,ht1,hgap⟩ := hh.exists
  exact ⟨t,ht,ht1,d.shareFloor_pos t ht1,hgap⟩

theorem interpolatedWidth_parameters_eq {n' : ℕ} (e : Precision.Data n')
    (hη : d.eta=e.eta) (hα : d.alpha=e.alpha) (hβ : d.beta=e.beta) (hσ : d.sigma=e.sigma)
    (t q : ℝ) : d.interpolatedWidth t q=e.interpolatedWidth t q := by
  simp only [interpolatedWidth,interpolatedMoment,momentWidth,denominator,lossScale,
    policyShare,nu,totalElasticity]
  rw [d.criticalExposure_parameters_eq e hη hα hσ,hη,hα,hβ,hσ]

end CommodityClassification.Precision.Data
