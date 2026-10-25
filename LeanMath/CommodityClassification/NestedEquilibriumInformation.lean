module

public import LeanMath.CommodityClassification.NestedMomentAlgebra

/-! Recovery from actual nest reports and weighted residual covariances. -/
@[expose] public section
noncomputable section
set_option maxHeartbeats 800000
namespace CommodityClassification.Equilibrium.BenchmarkFamily
open Matrix InputCoordinates
variable {n k h g : ℕ} (F : BenchmarkFamily n k h)

def nestReportedLoad (G : Partition n g) (DG : Matrix (Fin g) (Fin g) ℝ)
    (β : Vec g) (J : Matrix (Fin g) (Fin k) ℝ) : Vec k :=
  J.transpose *ᵥ (diagonal (fun a => (G.sales F.p F.q a)⁻¹) *ᵥ (DG *ᵥ β))

def nestReportedK (G : Partition n g) (η : Vec g) (hη : ∀a,0<η a)
    (DG : Matrix (Fin g) (Fin g) ℝ) (J : Matrix (Fin g) (Fin k) ℝ)
    (V : Matrix (Fin k) (Fin k) ℝ) : Matrix (Fin k) (Fin k) ℝ :=
  F.sigma • F.fixedR+J.transpose*(F.nestData G η hη).meanAdjustment DG F.sigma*J+V

def nestReportedCoefficient (G : Partition n g) (η : Vec g) (hη : ∀a,0<η a)
    (DG : Matrix (Fin g) (Fin g) ℝ) (β : Vec g) (J : Matrix (Fin g) (Fin k) ℝ)
    (V : Matrix (Fin k) (Fin k) ℝ) : ℝ :=
  dotProduct β (DG *ᵥ β)-dotProduct (F.nestReportedLoad G DG β J)
    ((F.nestReportedK G η hη DG J V)⁻¹ *ᵥ F.nestReportedLoad G DG β J)

theorem nested_candidate_m (G : Partition n g) (η : Vec g) (hη : ∀a,0<η a)
    (DG : Matrix (Fin g) (Fin g) ℝ) (β : Vec g)
    (hD : F.D=(F.nestData G η hη).demandMatrix DG)
    (hb : F.b=(F.nestData G η hη).proportionalPolicy β) (C : F.Candidate) :
    (F.model C).m=F.nestReportedLoad G DG β (G.report F.q C.val) := by
  change C.val.transpose *ᵥ (F.D *ᵥ F.b)=_
  rw [hD,hb]
  exact (F.nestData G η hη).nest_m_decomposition DG β C.val

theorem nested_candidate_K (G : Partition n g) (η : Vec g) (hη : ∀a,0<η a)
    (DG : Matrix (Fin g) (Fin g) ℝ)
    (hD : F.D=(F.nestData G η hη).demandMatrix DG) (C : F.Candidate) :
    (F.model C).K=F.nestReportedK G η hη DG (G.report F.q C.val)
      ((F.nestData G η hη).covarianceCorrection C.val F.sigma) := by
  change Regularity.K F.p F.q F.D (F.model C).R F.sigma C.val=_
  rw [F.candidate_R_fixed,hD]
  exact (F.nestData G η hη).nest_K_decomposition DG F.fixedR F.sigma C.val

theorem nested_coefficient_recovery (G : Partition n g) (η : Vec g) (hη : ∀a,0<η a)
    (DG : Matrix (Fin g) (Fin g) ℝ) (β : Vec g)
    (hD : F.D=(F.nestData G η hη).demandMatrix DG)
    (hb : F.b=(F.nestData G η hη).proportionalPolicy β)
    (C : Matrix (Fin n) (Fin k) ℝ) :
    F.coefficient C=F.nestReportedCoefficient G η hη DG β (G.report F.q C)
      ((F.nestData G η hη).covarianceCorrection C F.sigma) := by
  have hK : Regularity.K F.p F.q F.D F.fixedR F.sigma C=
      F.nestReportedK G η hη DG (G.report F.q C)
        ((F.nestData G η hη).covarianceCorrection C F.sigma) := by
    rw [hD]
    exact (F.nestData G η hη).nest_K_decomposition DG F.fixedR F.sigma C
  unfold coefficient
  rw [hK,hD,hb,(F.nestData G η hη).proportional_policy_energy,
    (F.nestData G η hη).nest_m_decomposition]
  rfl

theorem nested_actual_coefficient_recovery (G : Partition n g) (η : Vec g) (hη : ∀a,0<η a)
    (DG : Matrix (Fin g) (Fin g) ℝ) (β : Vec g)
    (hD : F.D=(F.nestData G η hη).demandMatrix DG)
    (hb : F.b=(F.nestData G η hη).proportionalPolicy β) (C : F.Candidate) :
    (F.model C).lossCoefficient=F.nestReportedCoefficient G η hη DG β (G.report F.q C.val)
      ((F.nestData G η hη).covarianceCorrection C.val F.sigma) := by
  rw [F.candidate_lossCoefficient,F.nested_coefficient_recovery G η hη DG β hD hb]

theorem nested_information_sufficient (G : Partition n g) (η : Vec g) (hη : ∀a,0<η a)
    (DG : Matrix (Fin g) (Fin g) ℝ) (β : Vec g)
    (hD : F.D=(F.nestData G η hη).demandMatrix DG)
    (hb : F.b=(F.nestData G η hη).proportionalPolicy β) (C E : F.Candidate)
    (hJ : G.report F.q C.val=G.report F.q E.val)
    (hV : (F.nestData G η hη).covarianceCorrection C.val F.sigma=
      (F.nestData G η hη).covarianceCorrection E.val F.sigma) :
    (F.model C).m=(F.model E).m ∧ (F.model C).K=(F.model E).K ∧
      (F.model C).lossCoefficient=(F.model E).lossCoefficient := by
  rw [F.nested_candidate_m G η hη DG β hD hb C,F.nested_candidate_m G η hη DG β hD hb E,
    F.nested_candidate_K G η hη DG hD C,F.nested_candidate_K G η hη DG hD E,
    F.nested_actual_coefficient_recovery G η hη DG β hD hb C,
    F.nested_actual_coefficient_recovery G η hη DG β hD hb E,hJ,hV]
  exact ⟨rfl,rfl,rfl⟩

theorem nested_matching_reports_sufficient (G : Partition n g) (η : Vec g) (hη : ∀a,0<η a)
    (DG : Matrix (Fin g) (Fin g) ℝ) (β : Vec g)
    (hD : F.D=(F.nestData G η hη).demandMatrix DG)
    (hb : F.b=(F.nestData G η hη).proportionalPolicy β) (hmatch : ∀a,η a=F.sigma) :
    F.ReportMomentsPreserved G ∧ F.ReportIdentified G := by
  have hm : F.ReportMomentsPreserved G := by
    intro C E hJ
    have hV : (F.nestData G η hη).covarianceCorrection C.val F.sigma=
        (F.nestData G η hη).covarianceCorrection E.val F.sigma := by
      rw [(F.nestData G η hη).covarianceCorrection_matching C.val F.sigma hmatch,
        (F.nestData G η hη).covarianceCorrection_matching E.val F.sigma hmatch]
    have hh := F.nested_information_sufficient G η hη DG β hD hb C E hJ hV
    exact ⟨hh.1,hh.2.1⟩
  exact ⟨hm,F.report_moments_identifies G hm⟩

theorem nested_reported_zero_coefficient (G : Partition n g) (η : Vec g) (hη : ∀a,0<η a)
    (DG : Matrix (Fin g) (Fin g) ℝ) (β : Vec g)
    (hD : F.D=(F.nestData G η hη).demandMatrix DG)
    (hb : F.b=(F.nestData G η hη).proportionalPolicy β)
    (C : Matrix (Fin n) (Fin k) ℝ)
    (hm : F.nestReportedLoad G DG β (G.report F.q C)=0) :
    F.coefficient C=dotProduct β (DG *ᵥ β) := by
  rw [F.nested_coefficient_recovery G η hη DG β hD hb]
  simp only [nestReportedCoefficient,hm,Matrix.mulVec_zero,dotProduct_zero,sub_zero]

theorem nested_fixed_answer_zero_load (G : Partition n g) (η : Vec g) (hη : ∀a,0<η a)
    (DG : Matrix (Fin g) (Fin g) ℝ) (β : Vec g)
    (hD : F.D=(F.nestData G η hη).demandMatrix DG)
    (hb : F.b=(F.nestData G η hη).proportionalPolicy β) (C0 : F.Candidate)
    (hm : (F.model C0).m=0) : F.IdentifiedAt G C0 := by
  have hz : F.nestReportedLoad G DG β (G.report F.q C0.val)=0 := by
    rw [←F.nested_candidate_m G η hη DG β hD hb C0]
    exact hm
  intro C hC
  have hzC : F.nestReportedLoad G DG β (G.report F.q C)=0 := by rw [hC.2];exact hz
  rw [F.nested_reported_zero_coefficient G η hη DG β hD hb C hzC,
    F.nested_reported_zero_coefficient G η hη DG β hD hb C0.val hz]

end CommodityClassification.Equilibrium.BenchmarkFamily
