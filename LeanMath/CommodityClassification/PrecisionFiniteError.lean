module

public import LeanMath.CommodityClassification.PrecisionAllPartitionLower

/-! The explicit finite-sales error between the common lower and upper bounds. -/
@[expose] public section
noncomputable section
set_option maxHeartbeats 1600000
namespace CommodityClassification.Precision.Data
open Matrix InputCoordinates
variable {n : ℕ} (d : Precision.Data n)

def coarseErrorConstant : ℝ :=
  d.lossScale*d.criticalExposure*|d.eta-d.sigma|/d.minElasticity^2

theorem coarseErrorConstant_nonneg : 0≤d.coarseErrorConstant := by
  unfold coarseErrorConstant
  exact div_nonneg (mul_nonneg (mul_nonneg d.lossScale_pos.le d.criticalExposure_mem.1.le)
    (abs_nonneg _)) (sq_nonneg _)

theorem coarseMoment_deficit (m : ℕ) : 0≤1-d.coarseMoment m ∧ 1-d.coarseMoment m≤d.coarseSales m := by
  have hh := le_max_right d.criticalExposure (1-d.coarseSales m)
  change 1-d.coarseSales m≤d.coarseMoment m at hh
  exact ⟨sub_nonneg.mpr (d.coarseMoment_bounds m).2,by linarith⟩

theorem momentWidth_triangle (x a b c : ℝ) (hx : 0≤x) :
    d.momentWidth x a c≤d.momentWidth x a b+d.momentWidth x b c := by
  rw [d.momentWidth_eq_abs _ _ _ hx,d.momentWidth_eq_abs _ _ _ hx,d.momentWidth_eq_abs _ _ _ hx]
  exact abs_sub_le _ _ _

theorem momentWidth_upper_lipschitz (x q : ℝ) (hx : 0≤x) (hq : q∈Set.Icc (0:ℝ) 1) :
    d.momentWidth x q 1≤(d.lossScale*x*|d.eta-d.sigma|/d.minElasticity^2)*(1-q) := by
  have h0 := d.denominator_positive_unit q x hq.1 hq.2 hx
  have h1 := d.denominator_positive_unit 1 x (by norm_num) le_rfl hx
  have ha0 : d.minElasticity≤d.denominator d.sigma q x := d.denominator_lower _ _ _ hq.1 hq.2 hx
  have ha1 : d.minElasticity≤d.denominator d.sigma 1 x := d.denominator_lower _ _ _ (by norm_num) le_rfl hx
  have hp : d.minElasticity^2≤d.denominator d.sigma q x*d.denominator d.sigma 1 x := by
    nlinarith [d.minElasticity_pos,mul_nonneg (sub_nonneg.mpr ha0) (sub_nonneg.mpr ha1)]
  have hn : 0≤d.lossScale*x*|d.eta-d.sigma| * (1-q) := by
    exact mul_nonneg (mul_nonneg (mul_nonneg d.lossScale_pos.le hx) (abs_nonneg _))
      (sub_nonneg.mpr hq.2)
  rw [d.momentWidth_fraction _ _ _ hq.2 h0 h1]
  calc
    _≤(d.lossScale*x*|d.eta-d.sigma| * (1-q))/d.minElasticity^2 :=
      div_le_div_of_nonneg_left hn (sq_pos_of_pos d.minElasticity_pos) hp
    _=_ := by ring

theorem precisionFloor_error_bound (m : ℕ) :
    0≤d.precisionFloor-d.coarseLowerWidth m ∧
      d.precisionFloor-d.coarseLowerWidth m≤d.coarseErrorConstant*d.coarseSales m := by
  refine ⟨sub_nonneg.mpr (d.coarseLowerWidth_le_floor m),?_⟩
  have ht := d.momentWidth_triangle d.criticalExposure d.criticalExposure (d.coarseMoment m) 1
    d.criticalExposure_mem.1.le
  rw [d.scalar_envelope_attains] at ht
  change d.precisionFloor≤d.coarseLowerWidth m+d.momentWidth d.criticalExposure (d.coarseMoment m) 1 at ht
  have hl := d.momentWidth_upper_lipschitz d.criticalExposure (d.coarseMoment m)
    d.criticalExposure_mem.1.le
    ⟨d.criticalExposure_mem.1.le.trans (d.coarseMoment_bounds m).1,(d.coarseMoment_bounds m).2⟩
  change d.momentWidth d.criticalExposure (d.coarseMoment m) 1≤
    d.coarseErrorConstant*(1-d.coarseMoment m) at hl
  have hd := mul_le_mul_of_nonneg_left (d.coarseMoment_deficit m).2 d.coarseErrorConstant_nonneg
  linarith

theorem precisionFloor_error_bound_manuscript (m : ℕ) :
    0≤d.precisionFloor-d.coarseLowerWidth m ∧
      d.precisionFloor-d.coarseLowerWidth m≤
        d.lossScale*d.criticalExposure*|d.eta-d.sigma|/(min d.eta d.sigma)^2*d.coarseSales m :=
  d.precisionFloor_error_bound m

theorem diffuse_sales_failure (P : Partition n g) (eps : ℝ)
    (hε : eps+d.coarseErrorConstant*d.coarseSales g<d.precisionFloor) :
    ¬d.exAnteWidth P≤eps := by
  have hh := (d.precisionFloor_error_bound g).2
  apply d.all_partition_failure P eps
  linarith

end CommodityClassification.Precision.Data
