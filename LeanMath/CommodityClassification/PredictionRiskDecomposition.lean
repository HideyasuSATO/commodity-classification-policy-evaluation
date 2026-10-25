module

public import LeanMath.CommodityClassification.PrecisionRecoveryRadius
public import Mathlib.Probability.Moments.Variance

/-! The actual quadratic expectation decomposes into squared mean error and variance. -/
@[expose] public section
noncomputable section
namespace CommodityClassification.Information
open MeasureTheory ProbabilityTheory
variable {A : Type*} [MeasurableSpace A] (μ : Measure A) [IsProbabilityMeasure μ]

def predictionRisk (f : A→ℝ) (a : ℝ) : ℝ := ∫x,(a-f x)^2 ∂μ

theorem predictionRisk_decomposition (f : A→ℝ) (hf : MemLp f 2 μ) (a : ℝ) :
    predictionRisk μ f a=(a-∫x,f x ∂μ)^2+variance f μ := by
  have hz : MemLp (fun x => a-f x) 2 μ := (memLp_const a).sub hf
  have hi : (∫x,a-f x ∂μ)=a-∫x,f x ∂μ := by
    rw [integral_sub (integrable_const a) (hf.integrable (by norm_num)),integral_const]
    simp
  have hv := variance_eq_sub hz
  rw [variance_const_sub hf.aestronglyMeasurable a] at hv
  change variance f μ=(∫x,(a-f x)^2 ∂μ)-(∫x,a-f x ∂μ)^2 at hv
  rw [hi] at hv
  unfold predictionRisk
  linarith

theorem predictionRisk_mean (f : A→ℝ) (hf : MemLp f 2 μ) :
    predictionRisk μ f (∫x,f x ∂μ)=variance f μ := by
  rw [predictionRisk_decomposition μ f hf]
  simp

theorem variance_le_predictionRisk (f : A→ℝ) (hf : MemLp f 2 μ) (a : ℝ) :
    variance f μ≤predictionRisk μ f a := by
  rw [predictionRisk_decomposition μ f hf]
  nlinarith [sq_nonneg (a-∫x,f x ∂μ)]

theorem predictionRisk_isLeast (f : A→ℝ) (hf : MemLp f 2 μ) :
    IsLeast (predictionRisk μ f '' Set.univ) (variance f μ) := by
  refine ⟨⟨∫x,f x ∂μ,Set.mem_univ _,predictionRisk_mean μ f hf⟩,?_⟩
  rintro r ⟨a,_,rfl⟩
  exact variance_le_predictionRisk μ f hf a

theorem predictionRisk_minimizer_iff (f : A→ℝ) (hf : MemLp f 2 μ) (a : ℝ) :
    predictionRisk μ f a=variance f μ ↔ a=∫x,f x ∂μ := by
  rw [predictionRisk_decomposition μ f hf]
  constructor
  · intro h
    have hh : (a-∫x,f x ∂μ)^2=0 := by linarith
    exact sub_eq_zero.mp (sq_eq_zero_iff.mp hh)
  · intro h
    simp [h]

end CommodityClassification.Information
