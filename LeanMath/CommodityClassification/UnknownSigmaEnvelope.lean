module

public import LeanMath.CommodityClassification.UnknownSigmaConditionalWidth

/-! The printed odds transformation and square-completion bound for unknown substitution. -/
@[expose] public section
noncomputable section
set_option maxHeartbeats 2400000
namespace CommodityClassification.Precision.Envelope

theorem sigma_square_identity (l u t : ℝ) (hl : 0≤l) (hu : 0≤u) :
    (l+t)*(u+t)-(Real.sqrt l+Real.sqrt u)^2*t=(t-Real.sqrt (l*u))^2 := by
  rw [Real.sqrt_mul hl]
  ring_nf
  rw [Real.sq_sqrt hl,Real.sq_sqrt hu]
  ring

theorem sigma_rational_bound (l u A B y : ℝ) (hl : 0<l) (hlu : l≤u)
    (hA : 0<A) (hB : 0≤B) (hy : 0≤y) :
    B*y*(u-l)/((l+A*y)*(u+A*y))≤bound l u A B := by
  have hu := hl.trans_le hlu
  have hly := add_pos_of_pos_of_nonneg hl (mul_nonneg hA.le hy)
  have huy := add_pos_of_pos_of_nonneg hu (mul_nonneg hA.le hy)
  have hc := cap_pos l u A hl hu hA
  have hs := sigma_square_identity l u (A*y) hl.le hu.le
  have hh : A*(Real.sqrt l+Real.sqrt u)^2*y≤(l+A*y)*(u+A*y) := by
    nlinarith [sq_nonneg (A*y-Real.sqrt (l*u))]
  have hm := mul_le_mul_of_nonneg_left hh (mul_nonneg hB (sub_nonneg.mpr hlu))
  rw [bound,div_le_div_iff₀ (mul_pos hly huy) hc]
  nlinarith [hm]

end CommodityClassification.Precision.Envelope

namespace CommodityClassification.Precision.Data
open InputCoordinates
variable {n : ℕ} (d : Precision.Data n)

def sigmaOddsExposure (c : Vec n) : ℝ := (d.theta c)^2/(1-d.secondMoment c)
def sigmaOddsMoment (c : Vec n) : ℝ := d.secondMoment c/(1-d.secondMoment c)
def sigmaFloor (l u : ℝ) : ℝ := d.policyShare*(Real.sqrt u-Real.sqrt l)/(Real.sqrt u+Real.sqrt l)

theorem sigmaOdds_bounds (c : Vec n) (hc : d.Admissible c) :
    0≤d.sigmaOddsExposure c ∧ d.sigmaOddsExposure c≤d.sigmaOddsMoment c := by
  have hr := (sub_pos.mpr (d.secondMoment_lt_one c hc)).le
  exact ⟨div_nonneg (sq_nonneg _) hr,
    div_le_div_of_nonneg_right (d.theta_sq_le_secondMoment c) hr⟩

theorem sigma_denominator_odds (s : ℝ) (c : Vec n) (hc : d.Admissible c) :
    d.denominator s (d.secondMoment c) ((d.theta c)^2)=
      (1-d.secondMoment c)*(s+d.eta*d.sigmaOddsMoment c+d.alpha*d.sigmaOddsExposure c) := by
  have hr := (sub_pos.mpr (d.secondMoment_lt_one c hc)).ne'
  unfold denominator sigmaOddsMoment sigmaOddsExposure
  field_simp [hr]
  ring

theorem sigma_odds_factor_pos (s : ℝ) (hs : 0<s) (c : Vec n) (hc : d.Admissible c) :
    0<s+d.eta*d.sigmaOddsMoment c+d.alpha*d.sigmaOddsExposure c := by
  have hy := d.sigmaOdds_bounds c hc
  exact add_pos_of_pos_of_nonneg
    (add_pos_of_pos_of_nonneg hs (mul_nonneg d.heta.le (hy.1.trans hy.2)))
    (mul_nonneg d.halpha hy.1)

theorem sigmaConditionalWidth_odds (l u : ℝ) (hl : 0<l) (hlu : l≤u)
    (c : Vec n) (hc : d.Admissible c) :
    d.sigmaConditionalWidth l u c=
      d.lossScale*d.sigmaOddsExposure c*(u-l)/
        ((l+d.eta*d.sigmaOddsMoment c+d.alpha*d.sigmaOddsExposure c)*
          (u+d.eta*d.sigmaOddsMoment c+d.alpha*d.sigmaOddsExposure c)) := by
  have hr := (sub_pos.mpr (d.secondMoment_lt_one c hc)).ne'
  have hlp := (d.sigma_odds_factor_pos l hl c hc).ne'
  have hup := (d.sigma_odds_factor_pos u (hl.trans_le hlu) c hc).ne'
  rw [d.sigmaConditionalWidth_formula l u hl hlu c hc,
    d.sigma_denominator_odds l c hc,d.sigma_denominator_odds u c hc]
  have hxy : d.sigmaOddsExposure c*(1-d.secondMoment c)=(d.theta c)^2 :=
    div_mul_cancel₀ _ hr
  apply (div_eq_div_iff (mul_ne_zero (mul_ne_zero hr hlp) (mul_ne_zero hr hup))
    (mul_ne_zero hlp hup)).mpr
  rw [←hxy]
  ring

theorem sigmaConditionalWidth_reduced_upper (l u : ℝ) (hl : 0<l) (hlu : l≤u)
    (c : Vec n) (hc : d.Admissible c) :
    d.sigmaConditionalWidth l u c≤d.lossScale*d.sigmaOddsExposure c*(u-l)/
      ((l+d.totalElasticity*d.sigmaOddsExposure c)*(u+d.totalElasticity*d.sigmaOddsExposure c)) := by
  rw [d.sigmaConditionalWidth_odds l u hl hlu c hc]
  have hy := d.sigmaOdds_bounds c hc
  have hly := add_pos_of_pos_of_nonneg hl (mul_nonneg d.totalElasticity_pos.le hy.1)
  have huy := add_pos_of_pos_of_nonneg (hl.trans_le hlu) (mul_nonneg d.totalElasticity_pos.le hy.1)
  have hlo : l+d.totalElasticity*d.sigmaOddsExposure c≤
      l+d.eta*d.sigmaOddsMoment c+d.alpha*d.sigmaOddsExposure c := by
    have hm := mul_le_mul_of_nonneg_left hy.2 d.heta.le
    unfold totalElasticity
    nlinarith
  have hhi : u+d.totalElasticity*d.sigmaOddsExposure c≤
      u+d.eta*d.sigmaOddsMoment c+d.alpha*d.sigmaOddsExposure c := by
    have hm := mul_le_mul_of_nonneg_left hy.2 d.heta.le
    unfold totalElasticity
    nlinarith
  exact div_le_div_of_nonneg_left
    (mul_nonneg (mul_nonneg d.lossScale_pos.le hy.1) (sub_nonneg.mpr hlu))
    (mul_pos hly huy) (mul_le_mul hlo hhi huy.le (hly.le.trans hlo))

theorem sigmaEnvelope_bound_formula (l u : ℝ) (hl : 0<l) (hu : 0<u) :
    Envelope.bound l u d.totalElasticity d.lossScale=d.sigmaFloor l u := by
  rw [lossScale,Envelope.bound_scaled l u _ _ hl hu d.totalElasticity_pos]
  rfl

theorem sigmaConditionalWidth_le_floor (l u : ℝ) (hl : 0<l) (hlu : l≤u)
    (c : Vec n) (hc : d.Admissible c) : d.sigmaConditionalWidth l u c≤d.sigmaFloor l u := by
  apply (d.sigmaConditionalWidth_reduced_upper l u hl hlu c hc).trans
  rw [←d.sigmaEnvelope_bound_formula l u hl (hl.trans_le hlu)]
  exact Envelope.sigma_rational_bound l u _ _ _ hl hlu d.totalElasticity_pos
    d.lossScale_pos.le (d.sigmaOdds_bounds c hc).1

end CommodityClassification.Precision.Data
