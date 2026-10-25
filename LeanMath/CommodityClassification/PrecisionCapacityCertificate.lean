module

public import LeanMath.CommodityClassification.PrecisionCapacityScalar

/-! From observable variance capacity to conditional and ex ante welfare guarantees. -/
@[expose] public section
noncomputable section
set_option maxHeartbeats 1600000
namespace CommodityClassification.Precision.Data
open InputCoordinates
variable {n g : ℕ} (d : Precision.Data n)

def capacityMultiplier : ℝ :=
  d.lossScale*|d.eta-d.sigma| * Capacity.chi d.minElasticity d.totalElasticity

theorem minElasticity_le_total : d.minElasticity≤d.totalElasticity := by
  exact (min_le_left d.eta d.sigma).trans (by unfold totalElasticity; linarith [d.halpha])

theorem capacityMultiplier_nonneg : 0≤d.capacityMultiplier :=
  mul_nonneg (mul_nonneg d.lossScale_pos.le (abs_nonneg _))
    (Capacity.chi_pos _ _ d.minElasticity_pos d.minElasticity_le_total).le

theorem denominator_capacity_lower (x Q : ℝ) (hxQ : x≤Q) (hQ : Q≤1) :
    Capacity.factor d.minElasticity d.totalElasticity x≤d.denominator d.sigma Q x := by
  have he : d.denominator d.sigma Q x-Capacity.factor d.minElasticity d.totalElasticity x=
      (d.eta-d.minElasticity)*(Q-x)+(d.sigma-d.minElasticity)*(1-Q) := by
    unfold denominator Capacity.factor totalElasticity
    ring
  have h1 := mul_nonneg (sub_nonneg.mpr (min_le_left d.eta d.sigma)) (sub_nonneg.mpr hxQ)
  have h2 := mul_nonneg (sub_nonneg.mpr (min_le_right d.eta d.sigma)) (sub_nonneg.mpr hQ)
  change 0≤(d.eta-d.minElasticity)*(Q-x) at h1
  change 0≤(d.sigma-d.minElasticity)*(1-Q) at h2
  linarith

theorem momentWidth_capacity_pointwise (x Q0 Q1 C : ℝ) (hx : 0≤x)
    (hxQ : x≤Q0) (hQ : Q0≤Q1) (hQ1 : Q1≤1) (hC : Q1-Q0≤C) :
    d.momentWidth x Q0 Q1≤d.lossScale*|d.eta-d.sigma| * C *
      Capacity.value d.minElasticity d.totalElasticity x := by
  have hf := Capacity.factor_pos _ _ _ d.minElasticity_pos d.minElasticity_le_total hx
  have h0 := d.denominator_capacity_lower x Q0 hxQ (hQ.trans hQ1)
  have h1 := d.denominator_capacity_lower x Q1 (hxQ.trans hQ) hQ1
  have hp0 := hf.trans_le h0
  have hp1 := hf.trans_le h1
  have hv : 0≤Q1-Q0 := sub_nonneg.mpr hQ
  have hfactor : (Capacity.factor d.minElasticity d.totalElasticity x)^2≤
      d.denominator d.sigma Q0 x*d.denominator d.sigma Q1 x := by
    rw [pow_two]
    exact mul_le_mul h0 h1 hf.le hp0.le
  have hn := mul_nonneg (mul_nonneg (mul_nonneg d.lossScale_pos.le hx)
    (abs_nonneg (d.eta-d.sigma))) hv
  have hb := mul_nonneg d.lossScale_pos.le (abs_nonneg (d.eta-d.sigma))
  have hvalue : 0≤Capacity.value d.minElasticity d.totalElasticity x :=
    div_nonneg hx (sq_nonneg _)
  calc
    d.momentWidth x Q0 Q1=
        d.lossScale*x*|d.eta-d.sigma| * (Q1-Q0)/
        (d.denominator d.sigma Q0 x*d.denominator d.sigma Q1 x) :=
      d.momentWidth_fraction x Q0 Q1 hQ hp0 hp1
    _≤d.lossScale*x*|d.eta-d.sigma| * (Q1-Q0)/
        (Capacity.factor d.minElasticity d.totalElasticity x)^2 :=
      div_le_div_of_nonneg_left hn (sq_pos_of_pos hf) hfactor
    _=d.lossScale*|d.eta-d.sigma| * (Q1-Q0)*
        Capacity.value d.minElasticity d.totalElasticity x := by
      unfold Capacity.value
      ring
    _≤d.lossScale*|d.eta-d.sigma| * C *
        Capacity.value d.minElasticity d.totalElasticity x :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hC hb) hvalue

theorem momentWidth_capacity_bound (x Q0 Q1 C : ℝ) (hx : 0≤x)
    (hxQ : x≤Q0) (hQ : Q0≤Q1) (hQ1 : Q1≤1) (hC : Q1-Q0≤C) :
    d.momentWidth x Q0 Q1≤d.capacityMultiplier*C := by
  have hCp : 0≤C := (sub_nonneg.mpr hQ).trans hC
  calc
    d.momentWidth x Q0 Q1≤d.lossScale*|d.eta-d.sigma| * C *
        Capacity.value d.minElasticity d.totalElasticity x :=
      d.momentWidth_capacity_pointwise x Q0 Q1 C hx hxQ hQ hQ1 hC
    _≤d.lossScale*|d.eta-d.sigma| * C * Capacity.chi d.minElasticity d.totalElasticity :=
      mul_le_mul_of_nonneg_left
        (Capacity.value_le_chi _ _ _ d.minElasticity_pos d.minElasticity_le_total
          ⟨hx,hxQ.trans (hQ.trans hQ1)⟩)
        (mul_nonneg (mul_nonneg d.lossScale_pos.le (abs_nonneg _)) hCp)
    _=d.capacityMultiplier*C := by unfold capacityMultiplier; ring

theorem answer_capacity_bound (P : Partition n g) (hP : d.TypeRespecting P)
    (c : Vec n) (hc : d.Admissible c) :
    d.manuscriptAnswerWidth P (d.groupTotal P c)≤d.capacityMultiplier*d.totalCapacity P := by
  obtain ⟨e,he,hm⟩ := d.closedFiber_maximum P c hc
  have hb := d.closedFiber_secondMoment_bounds P _ e he
  rw [←d.answerWidth_eq_manuscript P hP c hc,d.answerWidth_formula P hP c e hc he hm]
  exact d.momentWidth_capacity_bound _ _ _ _ (sq_nonneg _)
    (d.typeRespecting_lowerMoment P hP c) hb.1 hb.2 (d.report_moment_gap_le_capacity P c e he)

theorem exAnte_capacity_bound (P : Partition n g) (hP : d.TypeRespecting P) :
    d.exAnteWidth P≤d.capacityMultiplier*d.totalCapacity P := by
  apply (d.exAnteWidth_le_iff P hP _).mpr
  exact fun c hc => d.answer_capacity_bound P hP c hc

theorem exAnte_capacity_certificate (P : Partition n g) (hP : d.TypeRespecting P) :
    d.exAnteWidth P≤min d.precisionFloor (d.capacityMultiplier*d.totalCapacity P) :=
  le_min (d.exAnteWidth_upper P hP) (d.exAnte_capacity_bound P hP)

theorem capacity_tolerance_guarantee (P : Partition n g) (hP : d.TypeRespecting P)
    (eps : ℝ) (h : min d.precisionFloor (d.capacityMultiplier*d.totalCapacity P)≤eps) :
    ∀c,d.Admissible c→d.manuscriptAnswerWidth P (d.groupTotal P c)≤eps :=
  (d.exAnteWidth_le_iff P hP eps).mp ((d.exAnte_capacity_certificate P hP).trans h)

theorem capacityMultiplier_matching (h : d.eta=d.sigma) : d.capacityMultiplier=0 := by
  simp [capacityMultiplier,h]

end CommodityClassification.Precision.Data
