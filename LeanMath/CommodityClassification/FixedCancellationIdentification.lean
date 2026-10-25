module

public import LeanMath.CommodityClassification.FixedCancellationMoments

/-! One identifying answer with varying moments, another nonidentifying answer. -/
@[expose] public section
noncomputable section
set_option maxHeartbeats 2400000
namespace CommodityClassification.FixedCancellation
open Matrix InputCoordinates
open ResourceCancellation (e coordinates fine)

theorem fixed_answer_actual_gain (C : family.Candidate) (z : ℝ)
    (hc : C.val=coordinates (1/10) z) :
    (family.model C).m≠0 ∧
      dotProduct (family.model C).m ((family.model C).K⁻¹ *ᵥ (family.model C).m)=3/2500 := by
  have hp : coordinates (1/10) z∈family.frame.Candidates family.p family.q family.parents family.report := by
    rw [←hc];exact C.property
  constructor
  · rw [(all_candidate_moments C (1/10) z hc).1]
    intro he
    have hz := fixed_answer_affine_positive z hp
    have he0 := congrFun he 0
    norm_num at he0
    linarith
  · have he := family.candidate_lossCoefficient C
    rw [hc,fixed_answer_coefficient z hp] at he
    change dotProduct policy (demand *ᵥ policy)-
      dotProduct (family.model C).m ((family.model C).K⁻¹ *ᵥ (family.model C).m)=
        dotProduct policy (demand *ᵥ policy)-3/2500 at he
    exact sub_right_inj.mp he

theorem fixed_answer_identified :
    family.IdentifiedAt fine (candidate (1/10) 0 (by norm_num) (by norm_num)) := by
  intro C hC
  let CC : ResourceCancellation.family.Candidate := ⟨C,hC.1⟩
  obtain ⟨x,z,hcz⟩ := ResourceCancellation.all_candidates_parameterized CC
  change C=coordinates x z at hcz
  have hr := hC.2
  change fine.report e C=fine.report e (coordinates (1/10) 0) at hr
  rw [hcz] at hr
  have hx := (ResourceCancellation.fine_report_iff x z (1/10) 0).mp hr
  subst x
  have hc : coordinates (1/10) z∈family.frame.Candidates family.p family.q family.parents family.report := by
    rw [←hcz];exact hC.1
  change family.coefficient C=family.coefficient (coordinates (1/10) 0)
  rw [hcz,fixed_answer_coefficient z hc,
    fixed_answer_coefficient 0 (ResourceCancellation.coordinates_candidate (1/10) 0 (by norm_num) (by norm_num))]

theorem moments_vary_on_fixed_answer :
    ∃C E : family.Candidate,
      fine.report e C.val=fine.report e E.val ∧
      family.coefficient C.val=family.coefficient E.val ∧
      (family.model C).m≠(family.model E).m ∧ (family.model C).K≠(family.model E).K := by
  let C := candidate (1/10) 0 (by norm_num) (by norm_num)
  let E := candidate (1/10) (1/10) (by norm_num) (by norm_num)
  refine ⟨C,E,?_,?_,?_,?_⟩
  · exact (ResourceCancellation.fine_report_iff _ _ _ _).mpr rfl
  · change family.coefficient (coordinates (1/10) 0)=family.coefficient (coordinates (1/10) (1/10))
    rw [fixed_answer_coefficient _ C.property,fixed_answer_coefficient _ E.property]
  · rw [(all_candidate_moments C (1/10) 0 rfl).1,
      (all_candidate_moments E (1/10) (1/10) rfl).1]
    intro he; have h := congrFun he 0; norm_num at h
  · rw [(all_candidate_moments C (1/10) 0 rfl).2,
      (all_candidate_moments E (1/10) (1/10) rfl).2]
    intro he; have h := congrFun (congrFun he 0) 0; norm_num at h

theorem other_answer_coefficients_differ :
    family.coefficient (coordinates 0 0)≠family.coefficient (coordinates 0 (1/10)) := by
  rw [coefficient_formula,coefficient_formula]
  norm_num
  intro he
  linarith

theorem other_answer_not_identified :
    ¬family.IdentifiedAt fine (candidate 0 0 (by norm_num) (by norm_num)) := by
  intro h
  let E := candidate 0 (1/10) (by norm_num) (by norm_num)
  have hr : fine.report e E.val=fine.report e (coordinates 0 0) :=
    (ResourceCancellation.fine_report_iff _ _ _ _).mpr rfl
  have he := h E.val ⟨E.property,hr⟩
  exact other_answer_coefficients_differ he.symm

theorem report_not_identified : ¬family.ReportIdentified fine := by
  intro h
  exact other_answer_not_identified (h (candidate 0 0 (by norm_num) (by norm_num)))

theorem cancellation_equilibrium_witnesses (s0 c : ℝ) (hs : 0<s0) :
    ∃C E : family.Candidate,
      fine.report e C.val=fine.report e E.val ∧
      (family.model C).lossCoefficient=(family.model E).lossCoefficient ∧
      (family.model C).m≠(family.model E).m ∧ (family.model C).K≠(family.model E).K ∧
      (family.model C).BenchmarkEquilibrium (family.commonUtility c) (family.commonEndowment s0) s0 ∧
      (family.model E).BenchmarkEquilibrium (family.commonUtility c) (family.commonEndowment s0) s0 := by
  obtain ⟨C,E,hr,hw,hm,hK⟩ := moments_vary_on_fixed_answer
  refine ⟨C,E,hr,?_,hm,hK,family.every_candidate_equilibrium hs c C,
    family.every_candidate_equilibrium hs c E⟩
  rw [family.candidate_lossCoefficient C,family.candidate_lossCoefficient E]
  exact hw

end CommodityClassification.FixedCancellation
