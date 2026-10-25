module

public import LeanMath.CommodityClassification.AnswerCoordinateExistence
public import LeanMath.CommodityClassification.EconomicAllAnswerDichotomy

/-! Observable parent-mean criterion and the parent-identification exception. -/
@[expose] public section
noncomputable section
namespace CommodityClassification.Equilibrium.BenchmarkFamily
open Matrix InputCoordinates
variable {n k h g r s : ℕ} (F : BenchmarkFamily n k h)

/-- This expression uses only the known parent report, prices and quantities. -/
def parentMean : Mat n k := fun i j =>
  F.p i / F.parents.sales F.p F.q (F.parents.group i) * F.report (F.parents.group i) j

theorem parentMean_eq_mean (C : F.Candidate) :
    F.parentMean=F.parents.mean F.p F.q C.val := by
  unfold parentMean Partition.mean
  rw [C.property.2]

theorem parentMean_formula (i : Fin n) (j : Fin k) :
    F.parentMean i j = F.p i * F.report (F.parents.group i) j /
      (∑ a ∈ F.parents.cell (F.parents.group i), F.q a * F.p a) := by
  rw [parentMean,Partition.sales_apply]
  ring

theorem parentMean_candidate : F.parentMean∈F.frame.Candidates F.p F.q F.parents F.report := by
  rw [F.parentMean_eq_mean F.referenceCandidate]
  exact F.frame.parent_mean_candidate F.parents F.p F.q F.hp F.hq F.report
    F.reference F.reference_mem

def parentMeanCandidate : F.Candidate := ⟨F.parentMean,F.parentMean_candidate⟩

theorem parentMean_positive : InputCoordinates.Positive (F.frame.reconstruct F.p F.parentMean) :=
  F.parentMean_candidate.1

theorem parentMean_report : F.parents.report F.q F.parentMean=F.report :=
  F.parentMean_candidate.2

theorem fixedR_observable :
    F.fixedR=Supply.candidateR F.frame F.p F.q F.parentMean :=
  (Supply.candidate_R_eq F.frame F.parents F.p F.q F.report F.reference F.parentMean
    F.reference_mem F.parentMean_candidate).symm

theorem parentAnswerData_observable (N : Mat n r) :
    F.answerData F.parentMean N = Regularity.fixedAnswerData F.p F.q F.D
      (Supply.candidateR F.frame F.p F.q F.parentMean) F.sigma F.b F.parentMean N := by
  unfold answerData
  rw [F.fixedR_observable]

theorem parentIdentified_iff_identifiedAt (C0 : F.Candidate) :
    F.ParentIdentified ↔ F.IdentifiedAt F.parents C0 := by
  constructor
  · intro hp C hC
    exact (hp ⟨C,hC.1⟩).trans (hp C0).symm
  · intro hp C
    have hC := hp C.val ⟨C.property,C.property.2.trans C0.property.2.symm⟩
    have href := hp F.reference ⟨F.reference_mem,F.reference_mem.2.trans C0.property.2.symm⟩
    exact hC.trans href.symm

theorem parentIdentified_all_reports (hp : F.ParentIdentified)
    (P : Partition n g) : F.ReportIdentified P := by
  intro C0 C hC
  exact (hp ⟨C,hC.1⟩).trans (hp C0).symm

theorem parentIdentified_iff_parent_report :
    F.ParentIdentified ↔ F.ReportIdentified F.parents := by
  constructor
  · exact fun hp => F.parentIdentified_all_reports hp F.parents
  · intro hp
    exact (F.parentIdentified_iff_identifiedAt F.referenceCandidate).mpr (hp F.referenceCandidate)

theorem observable_parent_test
    (hI : ∀j,0<Supply.totalInputs F.q (F.frame.reconstruct F.p F.reference) j)
    (hk : 0<k) (H : HiddenBasis (F.parents.Q F.q) r) :
    F.ParentIdentified ↔ (F.answerData F.parentMean H.N).CongruenceCriterion :=
  (F.parentIdentified_iff_identifiedAt F.parentMeanCandidate).trans
    (F.identifiedAt_iff_congruence hI hk F.parents (Refinement.refl F.parents)
      F.parentMeanCandidate H)

theorem observable_parent_test_of_goods (hn : 0<n) (hk : 0<k)
    (H : HiddenBasis (F.parents.Q F.q) r) :
    F.ParentIdentified ↔ (F.answerData F.parentMean H.N).CongruenceCriterion :=
  F.observable_parent_test (F.total_positive_of_goods hn) hk H

theorem parent_test_basis_independent (hn : 0<n) (hk : 0<k)
    (H : HiddenBasis (F.parents.Q F.q) r) (G : HiddenBasis (F.parents.Q F.q) s) :
    (F.answerData F.parentMean H.N).CongruenceCriterion ↔
      (F.answerData F.parentMean G.N).CongruenceCriterion :=
  (F.observable_parent_test_of_goods hn hk H).symm.trans
    (F.observable_parent_test_of_goods hn hk G)

theorem parent_test_zero_load (hn : 0<n) (hk : 0<k)
    (H : HiddenBasis (F.parents.Q F.q) r)
    (hm : (F.answerData F.parentMean H.N).m₀=0) :
    F.ParentIdentified ↔ (F.answerData F.parentMean H.N).r_N=0 := by
  rw [F.observable_parent_test_of_goods hn hk H]
  simp only [FixedAnswer.Data.CongruenceCriterion,hm,true_and,ne_eq,not_true_eq_false,
    false_and,or_false]

theorem parent_identified_no_hidden (H : HiddenBasis (F.parents.Q F.q) 0) :
    F.ParentIdentified :=
  (F.parentIdentified_iff_identifiedAt F.referenceCandidate).mpr
    (F.identifiedAt_no_hidden F.parents (Refinement.refl F.parents) F.referenceCandidate H)

theorem parent_identified_zero_relative (F0 : BenchmarkFamily n 0 h) : F0.ParentIdentified := by
  intro C
  rw [coefficient_zero_relative,coefficient_zero_relative]

end CommodityClassification.Equilibrium.BenchmarkFamily
