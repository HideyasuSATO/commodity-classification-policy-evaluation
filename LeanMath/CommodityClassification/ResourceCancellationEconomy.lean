module

public import LeanMath.CommodityClassification.ResourceCancellationResponses

/-! Competitive meaning of the example's welfare and quantity responses. -/
@[expose] public section
noncomputable section
namespace CommodityClassification.ResourceCancellation
open Matrix InputCoordinates

theorem actual_welfare_coefficient (C : family.Candidate) (x z : ℝ)
    (hc : C.val=coordinates x z) :
    (family.model C).lossCoefficient=3051/1000-(24*x/25)^2/(3+18*x^2/5) := by
  rw [family.candidate_lossCoefficient C,hc,coefficient_formula]

theorem competitive_response (C : family.Candidate) (x z s0 c : ℝ)
    (hc : C.val=coordinates x z) (hs : 0<s0) :
    ∃u : ℝ → Vec 1,∃s : ℝ → ℝ,(family.model C).PositiveLocalPath s0 u s ∧
      (∃I : Set ℝ,IsOpen I ∧ 0∈I ∧ ∀t∈I,(family.model C).CompetitiveState
        (family.commonUtility c) Set.univ (family.commonEndowment s0) (t,u t) (s t)) ∧
      HasDerivAt (fun t => fine.valueAggregation e *ᵥ (family.model C).quantities (t,u t))
        (responseFormula x z) 0 := by
  obtain ⟨u,s,hp,he,hd⟩ := family.groupQuantityResponse_competitive_path
    (by norm_num) fine s0 c hs C
  rw [all_candidate_group_response C x z hc] at hd
  exact ⟨u,s,hp,he,hd⟩

theorem example_classification_conclusions :
    family.ReportIdentified fine ∧ ¬family.ParentIdentified ∧
      ¬family.GroupQuantitiesIdentified fine :=
  ⟨fine_identifies_welfare,parent_not_identified,fine_does_not_identify_quantities⟩

theorem equilibrium_counterexample (s0 c : ℝ) (hs : 0<s0) :
    ∃C E : family.Candidate,
      fine.report family.q C.val=fine.report family.q E.val ∧
      (family.model C).lossCoefficient=(family.model E).lossCoefficient ∧
      family.groupQuantityResponse fine C≠family.groupQuantityResponse fine E ∧
      (family.model C).BenchmarkEquilibrium (family.commonUtility c)
        (family.commonEndowment s0) s0 ∧
      (family.model E).BenchmarkEquilibrium (family.commonUtility c)
        (family.commonEndowment s0) s0 := by
  obtain ⟨C,E,hr,hw,hq⟩ := group_quantity_counterexample
  refine ⟨C,E,hr,?_,hq,family.every_candidate_equilibrium hs c C,
    family.every_candidate_equilibrium hs c E⟩
  rw [family.candidate_lossCoefficient C,family.candidate_lossCoefficient E]
  exact hw

end CommodityClassification.ResourceCancellation
