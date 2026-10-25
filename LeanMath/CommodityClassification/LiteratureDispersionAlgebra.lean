module

public import LeanMath.CommodityClassification.AllAnswerMeanPreservation

/-! The manuscript's factor-share substitution; no identification of market structures. -/
@[expose] public section
noncomputable section
namespace CommodityClassification.Precision.Data
open Matrix InputCoordinates
open scoped BigOperators
variable {n : ℕ} (d : Precision.Data n)

def shareDispersion (c : Vec n) : ℝ :=
  (∑i,d.w i*((1+c i)/2-(1/2:ℝ))^2)/((1/2:ℝ)*(1-1/2))

def substitutionMixture (c : Vec n) : ℝ :=
  d.sigma+(d.eta-d.sigma)*d.shareDispersion c

theorem first_factor_share (c : Vec n) (i : Fin n) :
    d.inputs c i 0=(1+c i)/2 := by simp [inputs]

theorem admissible_first_factor_share (c : Vec n) (hc : d.Admissible c) (i : Fin n) :
    0<d.inputs c i 0 ∧ d.inputs c i 0<1 := by
  rw [d.first_factor_share]
  have h := abs_lt.mp (hc.1 i)
  constructor <;> linarith

theorem aggregate_first_factor_share (c : Vec n) (hc : d.Admissible c) :
    (∑i,d.w i*d.inputs c i 0)=1/2 := by
  simp only [d.first_factor_share]
  calc
    _=((∑i,d.w i)+(∑i,d.w i*c i))/2 := by
      rw [←Finset.sum_add_distrib,Finset.sum_div]
      apply Finset.sum_congr rfl
      intro i _
      ring
    _=1/2 := by rw [d.sum_w,hc.2];norm_num

theorem shareDispersion_eq_secondMoment (c : Vec n) :
    d.shareDispersion c=d.secondMoment c := by
  have hn : (∑i,d.w i*((1+c i)/2-(1/2:ℝ))^2)=d.secondMoment c/4 := by
    rw [secondMoment,Finset.sum_div]
    apply Finset.sum_congr rfl
    intro i _
    ring
  unfold shareDispersion
  rw [hn]
  ring

theorem substitutionMixture_formula (c : Vec n) :
    d.substitutionMixture c=d.sigma+(d.eta-d.sigma)*d.secondMoment c := by
  rw [substitutionMixture,d.shareDispersion_eq_secondMoment]

theorem substitutionMixture_eq_denominator (c : Vec n) (ha : d.alpha=0) (x : ℝ) :
    d.substitutionMixture c=d.denominator d.sigma (d.secondMoment c) x := by
  rw [d.substitutionMixture_formula,denominator,ha]
  ring

theorem substitutionMixture_common_range (c : Vec n) (ha : d.alpha=0) (heta : 1<d.eta) :
    1<d.eta ∧ d.substitutionMixture c=
      d.denominator d.sigma (d.secondMoment c) ((d.theta c)^2) :=
  ⟨heta,d.substitutionMixture_eq_denominator c ha _⟩

theorem normalizedWelfare_mixture_formula (c : Vec n) (ha : d.alpha=0) :
    d.normalizedWelfare c=1-d.lossScale*(d.theta c)^2/d.substitutionMixture c := by
  rw [d.substitutionMixture_eq_denominator c ha ((d.theta c)^2)]
  rfl

theorem actual_welfare_mixture_formula (c : Vec n) (hc : d.Admissible c) (ha : d.alpha=0) :
    (d.family.model (d.candidate c hc)).lossCoefficient/d.nu=
      1-d.lossScale*(d.theta c)^2/d.substitutionMixture c := by
  rw [d.actual_normalized_coefficient c hc,d.normalizedWelfare_mixture_formula c ha]

end CommodityClassification.Precision.Data
