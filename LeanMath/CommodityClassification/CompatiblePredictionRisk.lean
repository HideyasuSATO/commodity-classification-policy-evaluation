module

public import LeanMath.CommodityClassification.PredictionRiskDecomposition

/-! All compatible probability priors obey the width-squared upper bound. -/
@[expose] public section
noncomputable section
namespace CommodityClassification.Information
open MeasureTheory ProbabilityTheory Filter
variable {A : Type*} [MeasurableSpace A]

def CompatiblePrior (S : Set A) (f : A→ℝ) (μ : Measure A) : Prop :=
  IsProbabilityMeasure μ ∧ (∀ᵐ x ∂μ,x∈S) ∧ AEMeasurable f μ

def compatibleRisks (S : Set A) (f : A→ℝ) : Set ℝ :=
  {r | ∃μ : Measure A,CompatiblePrior S f μ ∧ variance f μ=r}

theorem compatible_ae_bounds (S : Set A) (f : A→ℝ) (hf : BoundedValues S f)
    (μ : Measure A) (hμ : CompatiblePrior S f μ) :
    ∀ᵐ x ∂μ,f x∈Set.Icc (sInf (f '' S)) (sSup (f '' S)) := by
  filter_upwards [hμ.2.1] with x hx
  exact ⟨csInf_le hf.2 ⟨x,hx,rfl⟩,le_csSup hf.1 ⟨x,hx,rfl⟩⟩

theorem compatible_memLp (S : Set A) (f : A→ℝ) (hf : BoundedValues S f)
    (μ : Measure A) (hμ : CompatiblePrior S f μ) : MemLp f 2 μ := by
  let : IsProbabilityMeasure μ := hμ.1
  exact memLp_of_bounded (compatible_ae_bounds S f hf μ hμ) hμ.2.2.aestronglyMeasurable 2

theorem compatible_minimum_risk (S : Set A) (f : A→ℝ) (hf : BoundedValues S f)
    (μ : Measure A) (hμ : CompatiblePrior S f μ) :
    IsLeast (predictionRisk μ f '' Set.univ) (variance f μ) := by
  let : IsProbabilityMeasure μ := hμ.1
  exact predictionRisk_isLeast μ f (compatible_memLp S f hf μ hμ)

theorem compatible_risk_upper (S : Set A) (f : A→ℝ) (hf : BoundedValues S f)
    (μ : Measure A) (hμ : CompatiblePrior S f μ) :
    variance f μ≤(setWidth (f '' S))^2/4 := by
  let : IsProbabilityMeasure μ := hμ.1
  have hh := variance_le_sq_of_bounded (compatible_ae_bounds S f hf μ hμ) hμ.2.2
  unfold setWidth
  nlinarith [hh]

theorem compatibleRisks_bddAbove (S : Set A) (f : A→ℝ) (hf : BoundedValues S f) :
    BddAbove (compatibleRisks S f) := by
  refine ⟨(setWidth (f '' S))^2/4,?_⟩
  rintro r ⟨μ,hμ,rfl⟩
  exact compatible_risk_upper S f hf μ hμ

end CommodityClassification.Information
