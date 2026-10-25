module

public import LeanMath.CommodityClassification.AllAnswerReportEmbedding

/-! All-answer hypotheses discharged by actual economic report candidates. -/
@[expose] public section
noncomputable section
set_option maxHeartbeats 2400000
namespace CommodityClassification.Equilibrium.BenchmarkFamily
open Matrix
variable {n k g h r s : ℕ} (F : BenchmarkFamily n k h)

def ReportIdentified (P : InputCoordinates.Partition n g) : Prop :=
  ∀ C0 : F.Candidate, F.IdentifiedAt P C0

def ParentIdentified : Prop :=
  ∀ C : F.Candidate, F.coefficient C.val = F.coefficient F.reference

def ReportMomentsPreserved (P : InputCoordinates.Partition n g) : Prop :=
  ∀ C E : F.Candidate, P.report F.q C.val = P.report F.q E.val →
    (F.model C).m = (F.model E).m ∧ (F.model C).K = (F.model E).K

theorem economic_all_answer_hypotheses
    (hI : ∀j,0<Supply.totalInputs F.q (F.frame.reconstruct F.p F.reference) j)
    (hk : 0<k) (P : InputCoordinates.Partition n g)
    (H : InputCoordinates.HiddenBasis (P.Q F.q) r)
    (H0 : InputCoordinates.HiddenBasis (F.parents.Q F.q) s)
    (J : Mat s r) (hN : H.N = H0.N*J) :
    FixedAnswer.AllAnswerHypotheses (F.answerData F.reference H.N) H0.N J
      (F.frame.FiberDomain F.p H0 F.reference) := by
  exact ⟨F.economic_B1_hypotheses hI hk F.parents (InputCoordinates.Refinement.refl F.parents)
    F.referenceCandidate H0,H.independent,hN⟩

theorem report_identification_in_parent_coordinates (P : InputCoordinates.Partition n g)
    (H : InputCoordinates.HiddenBasis (P.Q F.q) r)
    (H0 : InputCoordinates.HiddenBasis (F.parents.Q F.q) s)
    (J : Mat s r) (hN : H.N = H0.N*J) (hc : F.ReportIdentified P) :
    FixedAnswer.AllAnswersIdentified (F.answerData F.reference H.N) H0.N J
      (F.frame.FiberDomain F.p H0 F.reference) := by
  intro Y hY Z hZ
  have hCY := F.frame.parent_coordinate_candidate F.p F.q F.parents F.report
    F.reference F.reference_mem H0 Y hY
  have hCZ := F.frame.parent_coordinate_candidate F.p F.q F.parents F.report
    F.reference F.reference_mem H0 (Y+J*Z) hZ
  have hp := InputCoordinates.hidden_embedding_point F.reference H0.N H.N J hN Y Z
  apply (F.coefficient_eq_iff_F_eq F.reference _ _ H.N).mp
  apply hc ⟨F.reference+H0.N*Y,hCY⟩
  refine ⟨hCZ,?_⟩
  change P.report F.q (F.reference+H0.N*(Y+J*Z)) = P.report F.q (F.reference+H0.N*Y)
  rw [hp]
  exact H.report_point _ Z

theorem parent_identification_of_coordinate_constancy
    (H : InputCoordinates.HiddenBasis (F.parents.Q F.q) s) (N : Mat n r)
    (hc : ((F.answerData F.reference N).withDirections H.N).ConstantOn
      (F.frame.FiberDomain F.p H F.reference)) : F.ParentIdentified := by
  intro C
  obtain ⟨Y,hY,hCY⟩ := F.frame.candidate_parent_coordinates F.p F.q F.parents F.report
    F.reference F.reference_mem H C.val C.property
  apply (F.coefficient_eq_iff_F_eq F.reference C.val F.reference N).mpr
  rw [hCY]
  exact hc Y hY

end CommodityClassification.Equilibrium.BenchmarkFamily
