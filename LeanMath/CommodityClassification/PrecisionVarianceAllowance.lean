module

public import LeanMath.CommodityClassification.PrecisionVarianceWidth

/-! The exact printed tolerance criteria for the actual conditional welfare width. -/
@[expose] public section
noncomputable section
set_option maxHeartbeats 1400000
namespace CommodityClassification.Precision.Data
open Matrix InputCoordinates
variable {n g : ℕ} (d : Precision.Data n)
variable (P : Partition n g) (hP : d.TypeRespecting P) (c e : Vec n)
variable (hc : d.Admissible c) (he : e∈d.closedFiber P (d.groupTotal P c))
variable (hm : IsMaxOn d.secondMoment (d.closedFiber P (d.groupTotal P c)) e)

local notation "Q₀" => d.lowerMoment P (d.groupTotal P c)
local notation "Q₁" => d.secondMoment e
local notation "x" => (d.theta c)^2
local notation "k₀" => d.denominator d.sigma Q₀ x
local notation "h" => |d.eta-d.sigma|
local notation "V" => Q₁-Q₀

include he in
theorem answer_endpoint_denominators :
    0≤Q₀ ∧ Q₀≤Q₁ ∧ Q₁≤1 ∧ 0<k₀ ∧ 0<d.denominator d.sigma Q₁ x := by
  have hb := d.closedFiber_secondMoment_bounds P _ e he
  have hl := d.lowerMoment_nonneg P (d.groupTotal P c)
  exact ⟨hl,hb.1,hb.2,d.denominator_positive_unit _ _ hl (hb.1.trans hb.2) (sq_nonneg _),
    d.denominator_positive_unit _ _ (d.secondMoment_nonneg e) hb.2 (sq_nonneg _)⟩

include hP hc he hm

theorem answer_width_growing (hs : d.sigma<d.eta) :
    d.manuscriptAnswerWidth P (d.groupTotal P c)=Variance.growing (d.lossScale*x) h k₀ V := by
  have hb := d.answer_endpoint_denominators P c e he
  rw [←d.answerWidth_eq_manuscript P hP c hc,d.answerWidth_formula P hP c e hc he hm]
  exact d.momentWidth_growing x Q₀ Q₁ hb.2.1 hs hb.2.2.2.1 hb.2.2.2.2

theorem answer_width_shrinking (hs : d.eta<d.sigma) :
    d.manuscriptAnswerWidth P (d.groupTotal P c)=Variance.shrinking (d.lossScale*x) h k₀ V := by
  have hb := d.answer_endpoint_denominators P c e he
  rw [←d.answerWidth_eq_manuscript P hP c hc,d.answerWidth_formula P hP c e hc he hm]
  exact d.momentWidth_shrinking x Q₀ Q₁ hb.2.1 hs hb.2.2.2.1 hb.2.2.2.2

theorem answer_variance_growing_iff (eps : ℝ) (hs : d.sigma<d.eta)
    (hA : eps*k₀<d.lossScale*x) :
    d.manuscriptAnswerWidth P (d.groupTotal P c)≤eps ↔
      V≤eps*k₀^2/(h*(d.lossScale*x-eps*k₀)) := by
  have hb := d.answer_endpoint_denominators P c e he
  rw [d.answer_width_growing P hP c e hc he hm hs]
  exact Variance.growing_iff _ _ _ _ _ (abs_pos.mpr (sub_ne_zero.mpr (ne_of_gt hs)))
    hb.2.2.2.1 (sub_nonneg.mpr hb.2.1) hA

theorem answer_variance_growing_all_pass (eps : ℝ) (heps : 0≤eps) (hs : d.sigma<d.eta)
    (hA : d.lossScale*x≤eps*k₀) : d.manuscriptAnswerWidth P (d.groupTotal P c)≤eps := by
  have hb := d.answer_endpoint_denominators P c e he
  rw [d.answer_width_growing P hP c e hc he hm hs]
  exact Variance.growing_all_pass _ _ _ _ _ (abs_nonneg _) hb.2.2.2.1
    (sub_nonneg.mpr hb.2.1) heps hA

theorem answer_variance_shrinking_iff (eps : ℝ) (heps : 0≤eps) (hs : d.eta<d.sigma)
    (hx : 0<x) : d.manuscriptAnswerWidth P (d.groupTotal P c)≤eps ↔
      V≤eps*k₀^2/(h*(d.lossScale*x+eps*k₀)) := by
  have hb := d.answer_endpoint_denominators P c e he
  rw [d.answer_width_shrinking P hP c e hc he hm hs]
  exact Variance.shrinking_iff _ _ _ _ _ (mul_pos d.lossScale_pos hx)
    (abs_pos.mpr (sub_ne_zero.mpr (ne_of_lt hs))) hb.2.2.2.1 heps
    (d.variance_shrinking_denominator x Q₀ Q₁ hs hb.2.2.2.2)

theorem answer_zero_variance_pass (eps : ℝ) (heps : 0≤eps) (hV : Q₁=Q₀) :
    d.manuscriptAnswerWidth P (d.groupTotal P c)≤eps := by
  rw [←d.answerWidth_eq_manuscript P hP c hc,d.answerWidth_formula P hP c e hc he hm,
    hV,d.momentWidth_equal_endpoints]
  exact heps

theorem answer_zero_tolerance_iff (hx : 0<x) (hs : d.eta≠d.sigma) :
    d.manuscriptAnswerWidth P (d.groupTotal P c)≤0 ↔ Q₀=Q₁ := by
  have hb := d.answer_endpoint_denominators P c e he
  have hz (t : ℝ) : |t|≤0 ↔ t=0 := by
    constructor
    · intro ht
      exact abs_eq_zero.mp (le_antisymm ht (abs_nonneg t))
    · intro ht
      rw [ht,abs_zero]
  rw [←d.answerWidth_eq_manuscript P hP c hc,d.answerWidth_formula P hP c e hc he hm,
    d.momentWidth_eq_abs _ _ _ (sq_nonneg _),hz,sub_eq_zero]
  exact d.momentValue_eq_iff x Q₀ Q₁ hx.ne' hs hb.2.2.2.1.ne' hb.2.2.2.2.ne'

end CommodityClassification.Precision.Data
