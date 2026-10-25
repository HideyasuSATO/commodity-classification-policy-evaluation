module

public import LeanMath.CommodityClassification.UnknownSigmaValueSets

/-! Exact conditional width when inputs are known but common substitution lies in a positive interval. -/
@[expose] public section
noncomputable section
set_option maxHeartbeats 1800000
namespace CommodityClassification.Precision.Data
open InputCoordinates Information
variable {n : ℕ} (d : Precision.Data n)

def sigmaConditionalWidth (l u : ℝ) (c : Vec n) : ℝ := setWidth (d.sigmaValues l u c)

theorem sigma_denominator_pos (s : ℝ) (hs : 0<s) (c : Vec n) (hc : d.Admissible c) :
    0<d.denominator s (d.secondMoment c) ((d.theta c)^2) :=
  (d.withSigma s hs).denominator_positive c hc

theorem sigmaWelfare_difference (l u : ℝ) (hl : 0<l) (hu : 0<u)
    (c : Vec n) (hc : d.Admissible c) :
    d.sigmaWelfare u c-d.sigmaWelfare l c=
      d.lossScale*(d.theta c)^2*(u-l)*(1-d.secondMoment c)/
        (d.denominator l (d.secondMoment c) ((d.theta c)^2)*
          d.denominator u (d.secondMoment c) ((d.theta c)^2)) := by
  have h0 := (d.sigma_denominator_pos l hl c hc).ne'
  have h1 := (d.sigma_denominator_pos u hu c hc).ne'
  unfold sigmaWelfare
  field_simp [h0,h1]
  unfold denominator
  ring

theorem sigmaWelfare_monotone (l u : ℝ) (hl : 0<l) (hlu : l≤u)
    (c : Vec n) (hc : d.Admissible c) : d.sigmaWelfare l c≤d.sigmaWelfare u c := by
  have hh := d.sigmaWelfare_difference l u hl (hl.trans_le hlu) c hc
  have hn : 0≤d.lossScale*(d.theta c)^2*(u-l)*(1-d.secondMoment c)/
      (d.denominator l (d.secondMoment c) ((d.theta c)^2)*
        d.denominator u (d.secondMoment c) ((d.theta c)^2)) :=
    div_nonneg (mul_nonneg (mul_nonneg (mul_nonneg d.lossScale_pos.le (sq_nonneg _))
      (sub_nonneg.mpr hlu)) (sub_pos.mpr (d.secondMoment_lt_one c hc)).le)
      (mul_pos (d.sigma_denominator_pos l hl c hc)
        (d.sigma_denominator_pos u (hl.trans_le hlu) c hc)).le
  linarith

theorem sigmaValues_extrema (l u : ℝ) (hl : 0<l) (hlu : l≤u)
    (c : Vec n) (hc : d.Admissible c) :
    IsLeast (d.sigmaValues l u c) (d.sigmaWelfare l c) ∧
      IsGreatest (d.sigmaValues l u c) (d.sigmaWelfare u c) := by
  constructor
  · refine ⟨⟨l,⟨le_rfl,hlu⟩,rfl⟩,?_⟩
    rintro z ⟨s,hs,rfl⟩
    exact d.sigmaWelfare_monotone l s hl hs.1 c hc
  · refine ⟨⟨u,⟨hlu,le_rfl⟩,rfl⟩,?_⟩
    rintro z ⟨s,hs,rfl⟩
    exact d.sigmaWelfare_monotone s u (hl.trans_le hs.1) hs.2 c hc

theorem sigmaConditionalWidth_endpoints (l u : ℝ) (hl : 0<l) (hlu : l≤u)
    (c : Vec n) (hc : d.Admissible c) :
    d.sigmaConditionalWidth l u c=d.sigmaWelfare u c-d.sigmaWelfare l c := by
  obtain ⟨hmin,hmax⟩ := d.sigmaValues_extrema l u hl hlu c hc
  unfold sigmaConditionalWidth setWidth
  rw [hmax.csSup_eq,hmin.csInf_eq]

theorem sigmaConditionalWidth_formula (l u : ℝ) (hl : 0<l) (hlu : l≤u)
    (c : Vec n) (hc : d.Admissible c) :
    d.sigmaConditionalWidth l u c=
      d.lossScale*(d.theta c)^2*(u-l)*(1-d.secondMoment c)/
        (d.denominator l (d.secondMoment c) ((d.theta c)^2)*
          d.denominator u (d.secondMoment c) ((d.theta c)^2)) := by
  rw [d.sigmaConditionalWidth_endpoints l u hl hlu c hc]
  exact d.sigmaWelfare_difference l u hl (hl.trans_le hlu) c hc

theorem sigma_full_answer_width (l u : ℝ) (c : Vec n) (hc : d.Admissible c) :
    Information.answerWidth (d.sigmaDomain l u) (fun x => d.inputs x.1)
      (fun x => d.sigmaWelfare x.2 x.1) (d.inputs c)=d.sigmaConditionalWidth l u c := by
  unfold Information.answerWidth sigmaConditionalWidth
  rw [d.sigma_full_values l u c hc]

theorem sigma_moment_answer_width (l u : ℝ) (c : Vec n) (hc : d.Admissible c) :
    Information.answerWidth (d.sigmaDomain l u) (fun x => d.momentReport x.1)
      (fun x => d.sigmaWelfare x.2 x.1) (d.momentReport c)=d.sigmaConditionalWidth l u c := by
  rw [←d.sigma_answer_widths_equal l u c hc,d.sigma_full_answer_width l u c hc]

theorem sigmaConditionalWidth_known (l : ℝ) (hl : 0<l) (c : Vec n) (hc : d.Admissible c) :
    d.sigmaConditionalWidth l l c=0 := by
  rw [d.sigmaConditionalWidth_endpoints l l hl le_rfl c hc,sub_self]

theorem sigmaConditionalWidth_zero_load (l u : ℝ) (hl : 0<l) (hlu : l≤u)
    (c : Vec n) (hc : d.Admissible c) (ht : d.theta c=0) :
    d.sigmaConditionalWidth l u c=0 := by
  rw [d.sigmaConditionalWidth_formula l u hl hlu c hc,ht]
  simp

end CommodityClassification.Precision.Data
