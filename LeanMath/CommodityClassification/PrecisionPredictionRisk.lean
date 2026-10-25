module

public import LeanMath.CommodityClassification.PredictionRiskSupremum

/-! The Fisher scalar-risk embedding on the actual economic input fibers. -/
@[expose] public section
noncomputable section
namespace CommodityClassification.Precision.Data
open InputCoordinates Information MeasureTheory ProbabilityTheory
variable {n : ℕ} (d : Precision.Data n) {A : Type*}

theorem normalizedWelfare_measurable : Measurable d.normalizedWelfare := by
  unfold normalizedWelfare denominator theta secondMoment
  fun_prop

theorem observation_prior_compatible (O : Vec n→A) (c : Vec n) (μ : Measure (Vec n))
    [IsProbabilityMeasure μ]
    (hμ : ∀ᵐ e ∂μ,d.Admissible e ∧ O e=O c) :
    CompatiblePrior {e | d.Admissible e ∧ O e=O c} d.normalizedWelfare μ :=
  ⟨inferInstance,hμ,d.normalizedWelfare_measurable.aemeasurable⟩

theorem observation_target_bounded (O : Vec n→A) (c : Vec n) :
    BoundedValues {e | d.Admissible e ∧ O e=O c} d.normalizedWelfare := by
  have hs : d.normalizedWelfare '' {e | d.Admissible e ∧ O e=O c}⊆
      d.normalizedWelfare '' {e | d.Admissible e} := by
    rintro r ⟨e,he,rfl⟩
    exact ⟨e,he.1,rfl⟩
  exact ⟨d.general_observation_bounded.1.mono hs,d.general_observation_bounded.2.mono hs⟩

theorem observation_prior_risk_decomposition (O : Vec n→A) (c : Vec n) (μ : Measure (Vec n))
    [IsProbabilityMeasure μ]
    (hμ : ∀ᵐ e ∂μ,d.Admissible e ∧ O e=O c) (a : ℝ) :
    predictionRisk μ d.normalizedWelfare a=
      (a-∫e,d.normalizedWelfare e ∂μ)^2+variance d.normalizedWelfare μ :=
  predictionRisk_decomposition μ d.normalizedWelfare
    (compatible_memLp _ _ (d.observation_target_bounded O c) μ
      (d.observation_prior_compatible O c μ hμ)) a

theorem observation_prior_risk_supremum (O : Vec n→A) (c : Vec n) (hc : d.Admissible c) :
    sSup (compatibleRisks {e | d.Admissible e ∧ O e=O c} d.normalizedWelfare)=
      (d.observationAnswerWidth O (O c))^2/4 :=
  answer_prior_risk_supremum {e | d.Admissible e} O d.normalizedWelfare
    d.general_observation_bounded c hc

theorem observation_minimizedRisk_supremum (O : Vec n→A) (c : Vec n) (hc : d.Admissible c) :
    sSup {r | ∃μ : Measure (Vec n),
      CompatiblePrior {e | d.Admissible e ∧ O e=O c} d.normalizedWelfare μ ∧
      IsLeast (predictionRisk μ d.normalizedWelfare '' Set.univ) r}=
      (d.observationAnswerWidth O (O c))^2/4 :=
  compatible_minimizedRisk_supremum {e | d.Admissible e ∧ O e=O c}
    ⟨c,hc,rfl⟩ _ (d.observation_target_bounded O c)

end CommodityClassification.Precision.Data
