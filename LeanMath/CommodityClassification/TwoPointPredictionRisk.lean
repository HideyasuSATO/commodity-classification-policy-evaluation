module

public import LeanMath.CommodityClassification.CompatiblePredictionRisk

/-! Equal-weight two-point distributions on actual candidates realize squared pair gaps over four. -/
@[expose] public section
noncomputable section
set_option maxHeartbeats 1800000
namespace CommodityClassification.Information
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal
variable {A : Type*} [MeasurableSpace A] [MeasurableSingletonClass A]

def twoPointPrior (x y : A) : Measure A :=
  (1/2 : ℝ≥0∞) • Measure.dirac x+(1/2 : ℝ≥0∞) • Measure.dirac y

omit [MeasurableSingletonClass A] in
theorem twoPointPrior_probability (x y : A) : IsProbabilityMeasure (twoPointPrior x y) := by
  constructor
  simp [twoPointPrior,Measure.add_apply,Measure.smul_apply]
  rw [←two_mul]
  exact ENNReal.mul_inv_cancel (by norm_num) (by norm_num)

theorem twoPointPrior_memLp (x y : A) (f : A→ℝ) : MemLp f 2 (twoPointPrior x y) := by
  apply memLp_add_measure.mpr
  constructor <;> exact (memLp_dirac (by simp)).smul_measure (by norm_num)

theorem twoPointPrior_integral (x y : A) (f : A→ℝ) :
    (∫z,f z ∂twoPointPrior x y)=(f x+f y)/2 := by
  unfold twoPointPrior
  rw [integral_add_measure
    ((integrable_dirac (by simp)).smul_measure (by norm_num))
    ((integrable_dirac (by simp)).smul_measure (by norm_num)),
    integral_smul_measure,integral_smul_measure,integral_dirac,integral_dirac]
  norm_num
  ring

theorem twoPointPrior_compatible (S : Set A) (f : A→ℝ) (x y : A) (hx : x∈S) (hy : y∈S) :
    CompatiblePrior S f (twoPointPrior x y) := by
  refine ⟨twoPointPrior_probability x y,?_,(twoPointPrior_memLp x y f).aemeasurable⟩
  simp only [twoPointPrior,ae_add_measure_iff]
  constructor
  · apply (Measure.ae_ennreal_smul_measure_iff (by norm_num : (1/2 : ℝ≥0∞)≠0)).mpr
    simpa using hx
  · apply (Measure.ae_ennreal_smul_measure_iff (by norm_num : (1/2 : ℝ≥0∞)≠0)).mpr
    simpa using hy

theorem twoPointPrior_variance (x y : A) (f : A→ℝ) :
    variance f (twoPointPrior x y)=(f x-f y)^2/4 := by
  let := twoPointPrior_probability x y
  rw [variance_eq_sub (twoPointPrior_memLp x y f),twoPointPrior_integral,twoPointPrior_integral]
  simp only [Pi.pow_apply]
  ring

theorem pairRisk_mem (S : Set A) (f : A→ℝ) (x y : A) (hx : x∈S) (hy : y∈S) :
    (f x-f y)^2/4∈compatibleRisks S f :=
  ⟨twoPointPrior x y,twoPointPrior_compatible S f x y hx hy,twoPointPrior_variance x y f⟩

theorem compatibleRisks_nonempty (S : Set A) (hne : S.Nonempty) (f : A→ℝ) :
    (compatibleRisks S f).Nonempty := by
  obtain ⟨x,hx⟩ := hne
  exact ⟨_,pairRisk_mem S f x x hx hx⟩

end CommodityClassification.Information
