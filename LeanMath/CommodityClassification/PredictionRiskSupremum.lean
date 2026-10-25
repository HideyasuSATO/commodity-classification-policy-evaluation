module

public import LeanMath.CommodityClassification.SquaredPairRiskSupremum

/-! Minimize risk for each compatible prior, then take its sharp supremum over all priors. -/
@[expose] public section
noncomputable section
namespace CommodityClassification.Information
open MeasureTheory ProbabilityTheory
variable {A : Type*} [MeasurableSpace A] [MeasurableSingletonClass A]

theorem compatibleRisks_isLUB (S : Set A) (hne : S.Nonempty) (f : A→ℝ)
    (hf : BoundedValues S f) : IsLUB (compatibleRisks S f) ((setWidth (f '' S))^2/4) := by
  constructor
  · rintro r ⟨μ,hμ,rfl⟩
    exact compatible_risk_upper S f hf μ hμ
  · intro B hB
    apply (pairRisks_isLUB S hne f hf).2
    rintro r ⟨x,hx,y,hy,rfl⟩
    exact hB (pairRisk_mem S f x y hx hy)

theorem compatibleRisks_supremum (S : Set A) (hne : S.Nonempty) (f : A→ℝ)
    (hf : BoundedValues S f) : sSup (compatibleRisks S f)=(setWidth (f '' S))^2/4 :=
  (compatibleRisks_isLUB S hne f hf).csSup_eq (compatibleRisks_nonempty S hne f)

theorem twoPointRisk_approximate (S : Set A) (hne : S.Nonempty) (f : A→ℝ)
    (hf : BoundedValues S f) (eps : ℝ) (hε : 0<eps) :
    ∃x∈S,∃y∈S,CompatiblePrior S f (twoPointPrior x y) ∧
      (setWidth (f '' S))^2/4-eps<variance f (twoPointPrior x y) := by
  obtain ⟨x,hx,y,hy,he⟩ := pairRisks_approximate S hne f hf eps hε
  exact ⟨x,hx,y,hy,twoPointPrior_compatible S f x y hx hy,
    by rwa [twoPointPrior_variance]⟩

theorem compatible_minimizedRisk_supremum (S : Set A) (hne : S.Nonempty) (f : A→ℝ)
    (hf : BoundedValues S f) :
    sSup {r | ∃μ : Measure A,CompatiblePrior S f μ ∧
      IsLeast (predictionRisk μ f '' Set.univ) r}=(setWidth (f '' S))^2/4 := by
  have hs : {r | ∃μ : Measure A,CompatiblePrior S f μ ∧
      IsLeast (predictionRisk μ f '' Set.univ) r}=compatibleRisks S f := by
    ext r
    constructor
    · rintro ⟨μ,hμ,hr⟩
      exact ⟨μ,hμ,(compatible_minimum_risk S f hf μ hμ).unique hr⟩
    · rintro ⟨μ,hμ,rfl⟩
      exact ⟨μ,hμ,compatible_minimum_risk S f hf μ hμ⟩
  rw [hs,compatibleRisks_supremum S hne f hf]

theorem answer_prior_risk_supremum {B : Type*} (S : Set A) (O : A→B) (f : A→ℝ)
    (hf : BoundedValues S f) (x : A) (hx : x∈S) :
    sSup (compatibleRisks {z | z∈S ∧ O z=O x} f)=(answerWidth S O f (O x))^2/4 := by
  have hsub : f '' {z | z∈S ∧ O z=O x}⊆f '' S := values_subset S O f (O x)
  exact compatibleRisks_supremum {z | z∈S ∧ O z=O x} ⟨x,hx,rfl⟩ f
    ⟨hf.1.mono hsub,hf.2.mono hsub⟩

end CommodityClassification.Information
