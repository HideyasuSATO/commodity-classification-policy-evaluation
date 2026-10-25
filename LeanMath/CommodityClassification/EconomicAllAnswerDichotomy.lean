module

public import LeanMath.CommodityClassification.EconomicAllAnswerDomain

/-! Lemma B.2 applied to actual economic candidates and reported totals. -/
@[expose] public section
noncomputable section
set_option maxHeartbeats 2400000
namespace CommodityClassification.Equilibrium.BenchmarkFamily
open Matrix
variable {n k g h r s : ℕ} (F : BenchmarkFamily n k h)

theorem report_moments_of_coordinate_preservation (P : InputCoordinates.Partition n g)
    (H : InputCoordinates.HiddenBasis (P.Q F.q) r)
    (H0 : InputCoordinates.HiddenBasis (F.parents.Q F.q) s)
    (J : Mat s r) (hN : H.N = H0.N*J)
    (hc : FixedAnswer.MomentsPreserved (F.answerData F.reference H.N) H0.N J
      (F.frame.FiberDomain F.p H0 F.reference)) : F.ReportMomentsPreserved P := by
  intro C E hreport
  obtain ⟨Y,hY,hEY⟩ := F.frame.candidate_parent_coordinates F.p F.q F.parents F.report
    F.reference F.reference_mem H0 E.val E.property
  obtain ⟨Z,hCZ⟩ := (H.fiber_exists_iff E.val C.val).mp hreport
  have hp : F.reference+H0.N*(Y+J*Z) = C.val := by
    rw [InputCoordinates.hidden_embedding_point F.reference H0.N H.N J hN Y Z,← hEY,← hCZ]
  have hYZ : Y+J*Z ∈ F.frame.FiberDomain F.p H0 F.reference := by
    change F.reference+H0.N*(Y+J*Z) ∈ F.frame.PositiveDomain F.p
    rw [hp]
    exact C.property.1
  have hh := hc Y hY Z hYZ
  change (F.answerData F.reference H.N).m (F.reference+H0.N*(Y+J*Z)) =
      (F.answerData F.reference H.N).m (F.reference+H0.N*Y) ∧
    (F.answerData F.reference H.N).K (F.reference+H0.N*(Y+J*Z)) =
      (F.answerData F.reference H.N).K (F.reference+H0.N*Y) at hh
  rw [hp,← hEY] at hh
  rw [F.candidate_m_answer C F.reference H.N,F.candidate_m_answer E F.reference H.N,
    F.candidate_K_answer C F.reference H.N,F.candidate_K_answer E F.reference H.N]
  exact hh

theorem economic_all_answer_dichotomy
    (hI : ∀j,0<Supply.totalInputs F.q (F.frame.reconstruct F.p F.reference) j)
    (hk : 0<k) (P : InputCoordinates.Partition n g)
    (R : InputCoordinates.Refinement P F.parents) (hc : F.ReportIdentified P) :
    F.ParentIdentified ∨ F.ReportMomentsPreserved P := by
  obtain ⟨r,⟨H⟩⟩ := InputCoordinates.exists_hiddenBasis (P.Q F.q)
  obtain ⟨s,⟨H0⟩⟩ := InputCoordinates.exists_hiddenBasis (F.parents.Q F.q)
  obtain ⟨J,hJ⟩ := R.hidden_embedding F.q H H0
  have hh := F.economic_all_answer_hypotheses hI hk P H H0 J hJ
  have hi := F.report_identification_in_parent_coordinates P H H0 J hJ hc
  rcases FixedAnswer.all_answer_dichotomy _ _ _ _ hh hi with hp|hm
  · exact Or.inl (F.parent_identification_of_coordinate_constancy H0 H.N hp)
  · exact Or.inr (F.report_moments_of_coordinate_preservation P H H0 J hJ hm)

theorem report_moments_identifies (P : InputCoordinates.Partition n g)
    (hm : F.ReportMomentsPreserved P) : F.ReportIdentified P := by
  intro E C hC
  let CC : F.Candidate := ⟨C,hC.1⟩
  obtain ⟨hmom,hK⟩ := hm CC E hC.2
  rw [← F.candidate_lossCoefficient CC,← F.candidate_lossCoefficient E]
  change dotProduct F.b (F.D *ᵥ F.b) - dotProduct (F.model CC).m
      ((F.model CC).K⁻¹ *ᵥ (F.model CC).m) =
    dotProduct F.b (F.D *ᵥ F.b) - dotProduct (F.model E).m
      ((F.model E).K⁻¹ *ᵥ (F.model E).m)
  rw [hmom,hK]

theorem parent_identifies_every_report (P : InputCoordinates.Partition n g)
    (hp : F.ParentIdentified) : F.ReportIdentified P := by
  intro E C hC
  exact (hp ⟨C,hC.1⟩).trans (hp E).symm

theorem economic_all_answer_identification_iff
    (hI : ∀j,0<Supply.totalInputs F.q (F.frame.reconstruct F.p F.reference) j)
    (P : InputCoordinates.Partition n g) (R : InputCoordinates.Refinement P F.parents) :
    F.ReportIdentified P ↔ F.ParentIdentified ∨ F.ReportMomentsPreserved P := by
  constructor
  · intro hc
    rcases Nat.eq_zero_or_pos k with hk|hk
    · subst k
      left
      intro C
      rw [coefficient_zero_relative,coefficient_zero_relative]
    · exact F.economic_all_answer_dichotomy hI hk P R hc
  · rintro (hp|hm)
    · exact F.parent_identifies_every_report P hp
    · exact F.report_moments_identifies P hm

theorem economic_all_answer_identification_iff_of_goods
    (hn : 0<n) (P : InputCoordinates.Partition n g)
    (R : InputCoordinates.Refinement P F.parents) :
    F.ReportIdentified P ↔ F.ParentIdentified ∨ F.ReportMomentsPreserved P :=
  F.economic_all_answer_identification_iff (F.total_positive_of_goods hn) P R

end CommodityClassification.Equilibrium.BenchmarkFamily
