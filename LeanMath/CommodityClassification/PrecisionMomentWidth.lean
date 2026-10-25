module

public import LeanMath.CommodityClassification.PrecisionFiniteVertices

/-! Exact scalar endpoint bounds, including zero-load and matched-elasticity cases. -/
@[expose] public section
noncomputable section
set_option maxHeartbeats 1200000
namespace CommodityClassification.Precision.Data
open Matrix InputCoordinates
variable {n : ℕ} (d : Precision.Data n)

def momentWidth (x Q0 Q1 : ℝ) : ℝ :=
  d.lossScale*x*|1/d.denominator d.sigma Q0 x-1/d.denominator d.sigma Q1 x|

theorem denominator_positive_unit (Q x : ℝ) (hQ0 : 0≤Q) (hQ1 : Q≤1) (hx : 0≤x) :
    0<d.denominator d.sigma Q x :=
  (lt_min d.heta d.hsigma).trans_le (d.denominator_lower d.sigma Q x hQ0 hQ1 hx)

theorem momentValue_monotone (x : ℝ) (hx : 0≤x) (hm : d.sigma≤d.eta) :
    MonotoneOn (d.momentValue x) (Set.Icc 0 1) := by
  intro a ha b hb hab
  have h0 := d.denominator_positive_unit a x ha.1 ha.2 hx
  have h1 := d.denominator_positive_unit b x hb.1 hb.2 hx
  have hd := d.momentValue_difference x a b h0.ne' h1.ne'
  have hh : 0≤d.lossScale*x*(d.eta-d.sigma)*(b-a)/
      (d.denominator d.sigma a x*d.denominator d.sigma b x) :=
    div_nonneg (mul_nonneg (mul_nonneg (mul_nonneg d.lossScale_pos.le hx)
      (sub_nonneg.mpr hm)) (sub_nonneg.mpr hab)) (mul_pos h0 h1).le
  linarith

theorem momentValue_antitone (x : ℝ) (hx : 0≤x) (hm : d.eta≤d.sigma) :
    AntitoneOn (d.momentValue x) (Set.Icc 0 1) := by
  intro a ha b hb hab
  have h0 := d.denominator_positive_unit a x ha.1 ha.2 hx
  have h1 := d.denominator_positive_unit b x hb.1 hb.2 hx
  have hd := d.momentValue_difference x a b h0.ne' h1.ne'
  have hh : d.lossScale*x*(d.eta-d.sigma)*(b-a)/
      (d.denominator d.sigma a x*d.denominator d.sigma b x)≤0 :=
    div_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonpos_of_nonneg
      (mul_nonpos_of_nonneg_of_nonpos (mul_nonneg d.lossScale_pos.le hx)
        (sub_nonpos.mpr hm)) (sub_nonneg.mpr hab)) (mul_pos h0 h1).le
  linarith

theorem momentWidth_eq_abs (x Q0 Q1 : ℝ) (hx : 0≤x) :
    d.momentWidth x Q0 Q1=|d.momentValue x Q0-d.momentValue x Q1| := by
  have he : d.momentValue x Q0-d.momentValue x Q1=
      d.lossScale*x*(1/d.denominator d.sigma Q1 x-1/d.denominator d.sigma Q0 x) := by
    unfold momentValue
    ring
  rw [he,abs_mul,abs_of_nonneg (mul_nonneg d.lossScale_pos.le hx),abs_sub_comm]
  rfl

theorem momentWidth_interval_bound (x Q0 Q1 a b : ℝ) (hx : 0≤x)
    (hQ0 : 0≤Q0) (hQ1 : Q1≤1) (ha : a∈Set.Icc Q0 Q1) (hb : b∈Set.Icc Q0 Q1) :
    |d.momentValue x a-d.momentValue x b|≤d.momentWidth x Q0 Q1 := by
  have h01 := ha.1.trans ha.2
  have h0 : Q0∈Set.Icc (0:ℝ) 1 := ⟨hQ0,h01.trans hQ1⟩
  have h1 : Q1∈Set.Icc (0:ℝ) 1 := ⟨hQ0.trans h01,hQ1⟩
  have hau : a∈Set.Icc (0:ℝ) 1 := ⟨hQ0.trans ha.1,ha.2.trans hQ1⟩
  have hbu : b∈Set.Icc (0:ℝ) 1 := ⟨hQ0.trans hb.1,hb.2.trans hQ1⟩
  rw [d.momentWidth_eq_abs x Q0 Q1 hx]
  rcases le_total d.sigma d.eta with hm|hm
  · have hf := d.momentValue_monotone x hx hm
    have h0a := hf h0 hau ha.1
    have ha1 := hf hau h1 ha.2
    have h0b := hf h0 hbu hb.1
    have hb1 := hf hbu h1 hb.2
    rw [abs_of_nonpos (sub_nonpos.mpr (hf h0 h1 h01))]
    apply abs_le.mpr
    constructor <;> linarith
  · have hf := d.momentValue_antitone x hx hm
    have h0a := hf h0 hau ha.1
    have ha1 := hf hau h1 ha.2
    have h0b := hf h0 hbu hb.1
    have hb1 := hf hbu h1 hb.2
    rw [abs_of_nonneg (sub_nonneg.mpr (hf h0 h1 h01))]
    apply abs_le.mpr
    constructor <;> linarith

theorem momentWidth_nonneg (x Q0 Q1 : ℝ) (hx : 0≤x) : 0≤d.momentWidth x Q0 Q1 :=
  mul_nonneg (mul_nonneg d.lossScale_pos.le hx) (abs_nonneg _)

theorem momentWidth_zero_load (Q0 Q1 : ℝ) : d.momentWidth 0 Q0 Q1=0 := by simp [momentWidth]

theorem momentWidth_matching_elasticity (x Q0 Q1 : ℝ) (hm : d.eta=d.sigma) :
    d.momentWidth x Q0 Q1=0 := by simp [momentWidth,denominator,hm]

theorem momentWidth_equal_endpoints (x Q : ℝ) : d.momentWidth x Q Q=0 := by simp [momentWidth]

theorem theta_continuous : Continuous d.theta := by unfold theta;fun_prop

theorem normalizedWelfare_continuousAt (c : Vec n)
    (hK : d.denominator d.sigma (d.secondMoment c) ((d.theta c)^2)≠0) :
    ContinuousAt d.normalizedWelfare c := by
  have hd : Continuous (fun e : Vec n => d.denominator d.sigma (d.secondMoment e) ((d.theta e)^2)) := by
    unfold denominator
    exact ((continuous_const.add ((continuous_const.mul d.secondMoment_continuous))).add
      (continuous_const.mul (d.theta_continuous.pow 2)))
  exact continuousAt_const.sub
    ((continuousAt_const.mul (d.theta_continuous.continuousAt.pow 2)).div hd.continuousAt hK)

end CommodityClassification.Precision.Data
