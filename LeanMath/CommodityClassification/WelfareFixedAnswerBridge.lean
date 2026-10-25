module
public import LeanMath.CommodityClassification.CommonBenchmarkFamily
public import LeanMath.CommodityClassification.FixedAnswerComplete
public import LeanMath.CommodityClassification.WelfareExpansionApplication
@[expose] public section
set_option maxHeartbeats 2400000
namespace CommodityClassification.Equilibrium
open Matrix Filter Asymptotics
open scoped BigOperators Topology
variable {n k g r : ℕ}

namespace BenchmarkFamily
variable (F : BenchmarkFamily n k g)

noncomputable def fixedR : Mat k k := Supply.candidateR F.frame F.p F.q F.reference

noncomputable def answerData (C0 : Mat n k) (N : Mat n r) : FixedAnswer.Data n k r :=
  Regularity.fixedAnswerData F.p F.q F.D F.fixedR F.sigma F.b C0 N

/-- Defined on matrices for fiber statements; it is identified with the actual
economic lossCoefficient only for economic candidates below. -/
noncomputable def coefficient (C : Mat n k) : ℝ :=
  dotProduct F.b (F.D *ᵥ F.b) -
    dotProduct (C.transpose *ᵥ (F.D *ᵥ F.b))
      ((Regularity.K F.p F.q F.D F.fixedR F.sigma C)⁻¹ *ᵥ (C.transpose *ᵥ (F.D *ᵥ F.b)))

theorem coefficient_eq_nu_sub_F (C0 C : Mat n k) (N : Mat n r) :
    F.coefficient C=dotProduct F.b (F.D *ᵥ F.b)-(F.answerData C0 N).F C := rfl

theorem coefficient_eq_iff_F_eq (C0 C E : Mat n k) (N : Mat n r) :
    F.coefficient C=F.coefficient E ↔ (F.answerData C0 N).F C=(F.answerData C0 N).F E := by
  rw [F.coefficient_eq_nu_sub_F C0 C N,F.coefficient_eq_nu_sub_F C0 E N]
  exact sub_right_inj

theorem candidate_R_fixed (C : F.Candidate) : (F.model C).R=F.fixedR :=
  Supply.candidate_R_eq F.frame F.parents F.p F.q F.report F.reference C.val F.reference_mem C.property

theorem candidate_K_answer (C : F.Candidate) (C0 : Mat n k) (N : Mat n r) :
    (F.model C).K=(F.answerData C0 N).K C.val := by
  change Regularity.K F.p F.q F.D (F.model C).R F.sigma C.val=_
  rw [F.candidate_R_fixed C]
  rfl

theorem candidate_m_answer (C : F.Candidate) (C0 : Mat n k) (N : Mat n r) :
    (F.model C).m=(F.answerData C0 N).m C.val := rfl

theorem candidate_lossCoefficient (C : F.Candidate) : (F.model C).lossCoefficient=F.coefficient C.val := by
  unfold Model.lossCoefficient
  rw [F.candidate_K_answer C F.reference (0 : Mat n 0)]
  rfl

theorem coefficient_zero_relative (F0 : BenchmarkFamily n 0 g) (C : Mat n 0) :
    F0.coefficient C=dotProduct F0.b (F0.D *ᵥ F0.b) := by
  simp [coefficient,dotProduct]

theorem candidate_total_positive
    (hI : ∀j,0<Supply.totalInputs F.q (F.frame.reconstruct F.p F.reference) j)
    (C : F.Candidate) : ∀j,0<Supply.totalInputs (F.model C).q (F.model C).A j := by
  change ∀j,0<Supply.totalInputs F.q (F.frame.reconstruct F.p C.val) j
  rw [Supply.candidate_total_eq F.frame F.parents F.p F.q F.report F.reference C.val F.reference_mem C.property]
  exact hI

theorem total_positive_of_goods (hn : 0<n) :
    ∀j,0<Supply.totalInputs F.q (F.frame.reconstruct F.p F.reference) j :=
  Supply.totalInputs_pos F.q (F.frame.reconstruct F.p F.reference) hn F.hq F.reference_mem.1

theorem candidate_expansion_with_coefficient
    (hI : ∀j,0<Supply.totalInputs F.q (F.frame.reconstruct F.p F.reference) j)
    (C : F.Candidate) (s0 c : ℝ) (hs : 0<s0) :
    ∃u : ℝ → Vec k,∃s : ℝ → ℝ,(F.model C).PositiveLocalPath s0 u s ∧
      (fun t => (F.model C).welfare (F.commonUtility c) u s 0-
        (F.model C).welfare (F.commonUtility c) u s t-(1/2 : ℝ)*t^2*F.coefficient C.val)
        =o[𝓝 (0 : ℝ)] (fun t : ℝ => t^2) := by
  have hh := (F.model C).quadratic_welfare_expansion
    (Model.ofAffine_demandC1 F.frame F.p F.q C.val F.D F.b F.sigma F.hp F.hw C.property.1)
    F.parents F.report C.property.2 F.hq (F.candidate_total_positive hI C) F.hD F.hsigma
    s0 hs rfl (F.commonUtility c) c Set.univ (by simp) (by intro r _; rfl)
  obtain ⟨u,s,hpath,_,_,hex⟩ := hh
  refine ⟨u,s,hpath,?_⟩
  unfold Model.WelfareExpansion at hex
  rwa [F.candidate_lossCoefficient C] at hex

end BenchmarkFamily
end CommodityClassification.Equilibrium
