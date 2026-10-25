module

public import LeanMath.CommodityClassification.EconomicAllAnswerDichotomy
public import LeanMath.CommodityClassification.SeparateMomentSufficiency
public import LeanMath.CommodityClassification.ParentKernelFactorization

/-! Observable linear restrictions on a report's unobserved directions. -/
@[expose] public section
noncomputable section
set_option maxHeartbeats 2400000
namespace CommodityClassification.Equilibrium.BenchmarkFamily
open Matrix
variable {n k g h r s : ℕ} (F : BenchmarkFamily n k h)

def LinearReportRestrictions (N : Mat n r) : Prop :=
  N.transpose *ᵥ (F.D *ᵥ F.b)=0 ∧
    ∃ Γ : Mat h r,Regularity.adjustedDemand F.p F.q F.D F.sigma * N = F.parents.Q F.q * Γ ∧
      F.report.transpose * Γ=0

theorem report_moments_in_parent_coordinates (P : InputCoordinates.Partition n g)
    (H : InputCoordinates.HiddenBasis (P.Q F.q) r)
    (H0 : InputCoordinates.HiddenBasis (F.parents.Q F.q) s)
    (J : Mat s r) (hN : H.N = H0.N*J) (hc : F.ReportMomentsPreserved P) :
    FixedAnswer.MomentsPreserved (F.answerData F.reference H.N) H0.N J
      (F.frame.FiberDomain F.p H0 F.reference) := by
  intro Y hY Z hZ
  have hCY := F.frame.parent_coordinate_candidate F.p F.q F.parents F.report
    F.reference F.reference_mem H0 Y hY
  have hCZ := F.frame.parent_coordinate_candidate F.p F.q F.parents F.report
    F.reference F.reference_mem H0 (Y+J*Z) hZ
  let CY : F.Candidate := ⟨F.reference+H0.N*Y,hCY⟩
  let CZ : F.Candidate := ⟨F.reference+H0.N*(Y+J*Z),hCZ⟩
  have hp := InputCoordinates.hidden_embedding_point F.reference H0.N H.N J hN Y Z
  have hrep : P.report F.q CZ.val = P.report F.q CY.val := by
    change P.report F.q (F.reference+H0.N*(Y+J*Z)) = P.report F.q (F.reference+H0.N*Y)
    rw [hp]
    exact H.report_point _ Z
  have hh := hc CZ CY hrep
  rw [F.candidate_m_answer CZ F.reference H.N,F.candidate_m_answer CY F.reference H.N,
    F.candidate_K_answer CZ F.reference H.N,F.candidate_K_answer CY F.reference H.N] at hh
  exact hh

theorem report_moments_iff_linear_restrictions
    (hI : ∀j,0<Supply.totalInputs F.q (F.frame.reconstruct F.p F.reference) j)
    (hk : 0<k) (P : InputCoordinates.Partition n g)
    (R : InputCoordinates.Refinement P F.parents)
    (H : InputCoordinates.HiddenBasis (P.Q F.q) r) :
    F.ReportMomentsPreserved P ↔ F.LinearReportRestrictions H.N := by
  obtain ⟨s,⟨H0⟩⟩ := InputCoordinates.exists_hiddenBasis (F.parents.Q F.q)
  obtain ⟨J,hJ⟩ := R.hidden_embedding F.q H H0
  have hh := F.economic_all_answer_hypotheses hI hk P H H0 J hJ
  have hf := F.parents.linear_restrictions_factor_iff F.p F.q F.hp F.hq H0
    (Regularity.adjustedDemand F.p F.q F.D F.sigma) hh.parent.L_symmetric
    H.N F.reference F.report F.reference_mem.2
  constructor
  · intro hc
    have hm := F.report_moments_in_parent_coordinates P H H0 J hJ hc
    have he := (FixedAnswer.moments_preserved_iff_linear_coefficients _ _ _ _ hh).mp hm
    exact ⟨he.1,hf.mp ⟨he.2.1,he.2.2⟩⟩
  · rintro ⟨hr,hΓ⟩
    obtain ⟨hA,hS⟩ := hf.mpr hΓ
    have hm := (FixedAnswer.moments_preserved_iff_linear_coefficients _ _ _ _ hh).mpr
      ⟨hr,hA,hS⟩
    exact F.report_moments_of_coordinate_preservation P H H0 J hJ hm

theorem positive_relative_dimension_of_parent_failure (hnc : ¬ F.ParentIdentified) : 0<k := by
  by_contra hk
  have he : k=0 := Nat.eq_zero_of_not_pos hk
  subst k
  apply hnc
  intro C
  rw [coefficient_zero_relative,coefficient_zero_relative]

theorem report_identified_iff_linear_restrictions
    (hI : ∀j,0<Supply.totalInputs F.q (F.frame.reconstruct F.p F.reference) j)
    (P : InputCoordinates.Partition n g) (R : InputCoordinates.Refinement P F.parents)
    (H : InputCoordinates.HiddenBasis (P.Q F.q) r) (hnc : ¬ F.ParentIdentified) :
    F.ReportIdentified P ↔ F.LinearReportRestrictions H.N := by
  rw [F.economic_all_answer_identification_iff hI P R,or_iff_right hnc]
  exact F.report_moments_iff_linear_restrictions hI
    (F.positive_relative_dimension_of_parent_failure hnc) P R H

theorem report_identified_iff_linear_restrictions_of_goods (hn : 0<n)
    (P : InputCoordinates.Partition n g) (R : InputCoordinates.Refinement P F.parents)
    (H : InputCoordinates.HiddenBasis (P.Q F.q) r) (hnc : ¬ F.ParentIdentified) :
    F.ReportIdentified P ↔ F.LinearReportRestrictions H.N :=
  F.report_identified_iff_linear_restrictions (F.total_positive_of_goods hn) P R H hnc

end CommodityClassification.Equilibrium.BenchmarkFamily
