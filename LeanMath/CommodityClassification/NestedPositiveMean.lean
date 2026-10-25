module

public import LeanMath.CommodityClassification.NestedMeanExchange

/-! Parent nonidentification supplies a positive reporting mean with nonzero load. -/
@[expose] public section
noncomputable section
set_option maxHeartbeats 1000000
namespace CommodityClassification.Equilibrium.BenchmarkFamily
open Matrix InputCoordinates
variable {n k h g r : ℕ} (F : BenchmarkFamily n k h)

theorem candidate_model_K_posDef (hn : 0<n) (C : F.Candidate) : (F.model C).K.PosDef := by
  change (Regularity.K F.p F.q F.D (F.model C).R F.sigma C.val).PosDef
  rw [F.candidate_R_fixed]
  exact Regularity.candidate_K_posDef F.frame F.parents F.p F.q F.report F.reference C.val
    F.D F.sigma F.hp F.hq F.hw (F.total_positive_of_goods hn) F.reference_mem C.property F.hD F.hsigma

theorem exists_nonzero_load_of_parent_failure (hnc : ¬F.ParentIdentified) :
    ∃C : F.Candidate,(F.model C).m≠0 := by
  obtain ⟨C,hC⟩ := F.exists_nonzero_response_of_parent_failure hnc
  refine ⟨C,?_⟩
  intro hm
  apply hC
  simp only [responseY,hm,Matrix.mulVec_zero]

def reportingMean (P : Partition n r) (RP : Refinement P F.parents) (C : F.Candidate) : F.Candidate :=
  ⟨P.mean F.p F.q C.val,(F.frame.mean_candidate F.p F.q F.hp F.hq RP F.report C.val C.property).1⟩

theorem reportingMean_report (P : Partition n r) (RP : Refinement P F.parents) (C : F.Candidate) :
    P.report F.q (F.reportingMean P RP C).val=P.report F.q C.val :=
  P.mean_report F.p F.q F.hp F.hq C.val

theorem reportingMean_fixed (P : Partition n r) (RP : Refinement P F.parents) (C : F.Candidate) :
    P.mean F.p F.q (F.reportingMean P RP C).val=(F.reportingMean P RP C).val := by
  ext i l
  change F.p i/P.sales F.p F.q (P.group i)*P.report F.q (F.reportingMean P RP C).val (P.group i) l=
    F.p i/P.sales F.p F.q (P.group i)*P.report F.q C.val (P.group i) l
  rw [F.reportingMean_report]

theorem nested_reportingMean_load (G : Partition n g) (η : Vec g) (hη : ∀a,0<η a)
    (DG : Mat g g) (β : Vec g)
    (hD : F.D=(F.nestData G η hη).demandMatrix DG)
    (hb : F.b=(F.nestData G η hη).proportionalPolicy β)
    (P : Partition n r) (RP : Refinement P F.parents) (RG : Refinement P G) (C : F.Candidate) :
    (F.model (F.reportingMean P RP C)).m=(F.model C).m := by
  rw [F.nested_candidate_m G η hη DG β hD hb,F.nested_candidate_m G η hη DG β hD hb]
  rw [RG.report_preserved F.q _ _ (F.reportingMean_report P RP C)]

theorem exists_nested_nonzero_mean (G : Partition n g) (η : Vec g) (hη : ∀a,0<η a)
    (DG : Mat g g) (β : Vec g)
    (hD : F.D=(F.nestData G η hη).demandMatrix DG)
    (hb : F.b=(F.nestData G η hη).proportionalPolicy β)
    (P : Partition n r) (RP : Refinement P F.parents) (RG : Refinement P G)
    (hnc : ¬F.ParentIdentified) :
    ∃C0 : F.Candidate,P.mean F.p F.q C0.val=C0.val ∧ (F.model C0).m≠0 := by
  obtain ⟨C,hm⟩ := F.exists_nonzero_load_of_parent_failure hnc
  refine ⟨F.reportingMean P RP C,F.reportingMean_fixed P RP C,?_⟩
  rw [F.nested_reportingMean_load G η hη DG β hD hb P RP RG C]
  exact hm

end CommodityClassification.Equilibrium.BenchmarkFamily
