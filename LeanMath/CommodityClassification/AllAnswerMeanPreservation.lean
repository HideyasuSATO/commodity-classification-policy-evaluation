module

public import LeanMath.CommodityClassification.ReportMeanInverseFormula

/-! Identification at all reports is equivalent to preservation under the actual positive reporting mean. -/
@[expose] public section
noncomputable section
namespace CommodityClassification.Equilibrium.BenchmarkFamily
open Matrix InputCoordinates
variable {n k h g : ℕ} (F : BenchmarkFamily n k h)

theorem reportIdentified_iff_candidate_pairs (P : Partition n g) :
    F.ReportIdentified P ↔ ∀C E : F.Candidate,
      P.report F.q C.val=P.report F.q E.val→F.coefficient C.val=F.coefficient E.val := by
  constructor
  · intro h C E hr
    exact h E C.val ⟨C.property,hr⟩
  · intro h C0 C hC
    exact h ⟨C,hC.1⟩ C0 hC.2

theorem reportingMean_same_report (P : Partition n g) (RP : Refinement P F.parents)
    (C E : F.Candidate) (hr : P.report F.q C.val=P.report F.q E.val) :
    (F.reportingMean P RP C).val=(F.reportingMean P RP E).val := by
  change P.mean F.p F.q C.val=P.mean F.p F.q E.val
  rw [P.mean_eq_lift,P.mean_eq_lift,hr]

theorem reportIdentified_iff_mean_preservation (P : Partition n g) (RP : Refinement P F.parents) :
    F.ReportIdentified P ↔ ∀C : F.Candidate,
      F.coefficient C.val=F.coefficient (F.reportingMean P RP C).val := by
  rw [F.reportIdentified_iff_candidate_pairs]
  constructor
  · intro h C
    exact h C (F.reportingMean P RP C) (F.reportingMean_report P RP C).symm
  · intro h C E hr
    calc
      F.coefficient C.val=F.coefficient (F.reportingMean P RP C).val := h C
      _=F.coefficient (F.reportingMean P RP E).val := congrArg F.coefficient (F.reportingMean_same_report P RP C E hr)
      _=F.coefficient E.val := (h E).symm

theorem inverseXi_mean_candidate (P : Partition n g) (RP : Refinement P F.parents)
    (C : Mat n k) (hc : C∈F.frame.Candidates F.p F.q F.parents F.report) :
    P.inverseXiReportLift F.p F.q*((P.Q F.q).transpose*C)∈
      F.frame.Candidates F.p F.q F.parents F.report ∧
    P.report F.q (P.inverseXiReportLift F.p F.q*((P.Q F.q).transpose*C))=P.report F.q C := by
  rw [←P.mean_inverseXi_formula F.p F.q F.hp F.hq C]
  exact F.frame.mean_candidate F.p F.q F.hp F.hq RP F.report C hc

theorem reportIdentified_iff_inverseXi_preservation (P : Partition n g) (RP : Refinement P F.parents) :
    F.ReportIdentified P ↔ ∀C∈F.frame.Candidates F.p F.q F.parents F.report,
      F.coefficient C=F.coefficient (P.inverseXiReportLift F.p F.q*((P.Q F.q).transpose*C)) := by
  rw [F.reportIdentified_iff_mean_preservation P RP]
  constructor
  · intro hh C hc
    rw [←P.mean_inverseXi_formula F.p F.q F.hp F.hq C]
    exact hh ⟨C,hc⟩
  · intro hh C
    have he := hh C.val C.property
    rw [←P.mean_inverseXi_formula F.p F.q F.hp F.hq C.val] at he
    exact he

theorem reportIdentified_iff_actual_mean_coefficient (P : Partition n g) (RP : Refinement P F.parents) :
    F.ReportIdentified P ↔ ∀C : F.Candidate,
      (F.model C).lossCoefficient=(F.model (F.reportingMean P RP C)).lossCoefficient := by
  simp only [F.candidate_lossCoefficient]
  exact F.reportIdentified_iff_mean_preservation P RP

end CommodityClassification.Equilibrium.BenchmarkFamily
