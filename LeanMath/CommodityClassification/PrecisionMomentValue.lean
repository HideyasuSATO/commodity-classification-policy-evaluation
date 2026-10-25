module

public import LeanMath.CommodityClassification.PrecisionTypeSales

/-! Exact conditional dependence on the residual supply second moment. -/
@[expose] public section
noncomputable section
set_option maxHeartbeats 1200000
namespace CommodityClassification.Precision.Data
open Matrix InputCoordinates
variable {n : ℕ} (d : Precision.Data n)

def momentValue (x Q : ℝ) : ℝ := 1-d.lossScale*x/d.denominator d.sigma Q x

theorem normalizedWelfare_momentValue (c : Vec n) :
    d.normalizedWelfare c=d.momentValue ((d.theta c)^2) (d.secondMoment c) := rfl

theorem momentValue_difference (x Q0 Q1 : ℝ)
    (h0 : d.denominator d.sigma Q0 x≠0) (h1 : d.denominator d.sigma Q1 x≠0) :
    d.momentValue x Q1-d.momentValue x Q0=
      (d.lossScale*x*(d.eta-d.sigma)*(Q1-Q0))/
        (d.denominator d.sigma Q0 x*d.denominator d.sigma Q1 x) := by
  unfold momentValue
  field_simp [h0,h1]
  unfold denominator
  ring

theorem momentValue_derivative (x Q : ℝ) (hK : d.denominator d.sigma Q x≠0) :
    HasDerivAt (d.momentValue x)
      (d.lossScale*x*(d.eta-d.sigma)/(d.denominator d.sigma Q x)^2) Q := by
  have hd : HasDerivAt (fun r => d.denominator d.sigma r x) (d.eta-d.sigma) Q := by
    convert (((hasDerivAt_id Q).const_mul (d.eta-d.sigma)).const_add d.sigma).add_const (d.alpha*x) using 1
    · ext r;simp only [denominator,id_eq]
    · ring
  have hh := ((hasDerivAt_const Q (d.lossScale*x)).div hd hK).const_sub 1
  convert hh using 1
  · rfl
  · ring

theorem momentValue_eq_iff (x Q0 Q1 : ℝ) (hx : x≠0) (hm : d.eta≠d.sigma)
    (h0 : d.denominator d.sigma Q0 x≠0) (h1 : d.denominator d.sigma Q1 x≠0) :
    d.momentValue x Q0=d.momentValue x Q1 ↔ Q0=Q1 := by
  constructor
  · intro hh
    have hd := d.momentValue_difference x Q0 Q1 h0 h1
    rw [hh,sub_self] at hd
    have he : d.lossScale*x*(d.eta-d.sigma)*(Q1-Q0)=0 :=
      (div_eq_zero_iff).mp hd.symm |>.resolve_right (mul_ne_zero h0 h1)
    have hn : d.lossScale*x*(d.eta-d.sigma)≠0 :=
      mul_ne_zero (mul_ne_zero d.lossScale_pos.ne' hx) (sub_ne_zero.mpr hm)
    have hq := (mul_eq_zero.mp he).resolve_left hn
    exact (sub_eq_zero.mp hq).symm
  · intro hh;rw [hh]

theorem momentValue_increasing (x Q0 Q1 : ℝ) (hx : 0<x) (hm : d.sigma<d.eta)
    (hQ : Q0<Q1) (h0 : 0<d.denominator d.sigma Q0 x)
    (h1 : 0<d.denominator d.sigma Q1 x) : d.momentValue x Q0<d.momentValue x Q1 := by
  have hd := d.momentValue_difference x Q0 Q1 h0.ne' h1.ne'
  have hp : 0<(d.lossScale*x*(d.eta-d.sigma)*(Q1-Q0))/
      (d.denominator d.sigma Q0 x*d.denominator d.sigma Q1 x) :=
    div_pos (mul_pos (mul_pos (mul_pos d.lossScale_pos hx) (sub_pos.mpr hm))
      (sub_pos.mpr hQ)) (mul_pos h0 h1)
  linarith

theorem momentValue_decreasing (x Q0 Q1 : ℝ) (hx : 0<x) (hm : d.eta<d.sigma)
    (hQ : Q0<Q1) (h0 : 0<d.denominator d.sigma Q0 x)
    (h1 : 0<d.denominator d.sigma Q1 x) : d.momentValue x Q1<d.momentValue x Q0 := by
  have hd := d.momentValue_difference x Q0 Q1 h0.ne' h1.ne'
  have hn : (d.lossScale*x*(d.eta-d.sigma)*(Q1-Q0))/
      (d.denominator d.sigma Q0 x*d.denominator d.sigma Q1 x)<0 :=
    div_neg_of_neg_of_pos (mul_neg_of_neg_of_pos
      (mul_neg_of_pos_of_neg (mul_pos d.lossScale_pos hx) (sub_neg.mpr hm))
      (sub_pos.mpr hQ)) (mul_pos h0 h1)
  linarith

end CommodityClassification.Precision.Data
