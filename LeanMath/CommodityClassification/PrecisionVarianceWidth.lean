module

public import LeanMath.CommodityClassification.PrecisionVarianceAlgebra

/-! Exact residual-variance width formulas with denominator positivity from regularity. -/
@[expose] public section
noncomputable section
set_option maxHeartbeats 1400000
namespace CommodityClassification.Precision.Data
open Matrix InputCoordinates
variable {n : ℕ} (d : Precision.Data n)

theorem denominator_increment (x Q0 Q1 : ℝ) :
    d.denominator d.sigma Q1 x=d.denominator d.sigma Q0 x+(d.eta-d.sigma)*(Q1-Q0) := by
  unfold denominator
  ring

theorem momentWidth_fraction (x Q0 Q1 : ℝ) (hQ : Q0≤Q1)
    (h0 : 0<d.denominator d.sigma Q0 x) (h1 : 0<d.denominator d.sigma Q1 x) :
    d.momentWidth x Q0 Q1=d.lossScale*x*|d.eta-d.sigma| * (Q1-Q0)/
      (d.denominator d.sigma Q0 x*d.denominator d.sigma Q1 x) := by
  have he : 1/d.denominator d.sigma Q0 x-1/d.denominator d.sigma Q1 x=
      (d.eta-d.sigma)*(Q1-Q0)/(d.denominator d.sigma Q0 x*d.denominator d.sigma Q1 x) := by
    field_simp [h0.ne',h1.ne']
    unfold denominator
    ring
  rw [momentWidth,he,abs_div,abs_mul,abs_of_nonneg (sub_nonneg.mpr hQ),
    abs_of_pos (mul_pos h0 h1)]
  ring

theorem momentWidth_growing (x Q0 Q1 : ℝ) (hQ : Q0≤Q1) (hm : d.sigma<d.eta)
    (h0 : 0<d.denominator d.sigma Q0 x) (h1 : 0<d.denominator d.sigma Q1 x) :
    d.momentWidth x Q0 Q1=Variance.growing (d.lossScale*x) |d.eta-d.sigma|
      (d.denominator d.sigma Q0 x) (Q1-Q0) := by
  rw [d.momentWidth_fraction x Q0 Q1 hQ h0 h1,d.denominator_increment x Q0 Q1,
    abs_of_pos (sub_pos.mpr hm)]
  rfl

theorem momentWidth_shrinking (x Q0 Q1 : ℝ) (hQ : Q0≤Q1) (hm : d.eta<d.sigma)
    (h0 : 0<d.denominator d.sigma Q0 x) (h1 : 0<d.denominator d.sigma Q1 x) :
    d.momentWidth x Q0 Q1=Variance.shrinking (d.lossScale*x) |d.eta-d.sigma|
      (d.denominator d.sigma Q0 x) (Q1-Q0) := by
  rw [d.momentWidth_fraction x Q0 Q1 hQ h0 h1,abs_of_neg (sub_neg.mpr hm),
    d.denominator_increment x Q0 Q1]
  unfold Variance.shrinking
  ring

theorem variance_shrinking_denominator (x Q0 Q1 : ℝ) (hm : d.eta<d.sigma)
    (h1 : 0<d.denominator d.sigma Q1 x) :
    0<d.denominator d.sigma Q0 x-|d.eta-d.sigma| * (Q1-Q0) := by
  rw [abs_of_neg (sub_neg.mpr hm)]
  have he := d.denominator_increment x Q0 Q1
  linarith

end CommodityClassification.Precision.Data
