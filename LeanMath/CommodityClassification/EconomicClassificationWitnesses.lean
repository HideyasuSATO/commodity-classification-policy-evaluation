module

public import LeanMath.CommodityClassification.FixedAnswerFailureDirections
public import LeanMath.CommodityClassification.ExactCommodityPairRule

/-! Failed classifications have arbitrarily close, observationally equal economies. -/
@[expose] public section
noncomputable section
namespace CommodityClassification.Equilibrium.BenchmarkFamily
open Matrix Filter InputCoordinates
open scoped Topology
variable {n k h g r : ℕ} (F : BenchmarkFamily n k h)

def SameObservationWitness (P : Partition n g) (C E : F.Candidate) (s0 c : ℝ) : Prop :=
  P.report F.q C.val=P.report F.q E.val ∧
  P.report F.q (F.model C).A=P.report F.q (F.model E).A ∧
  (F.model C).lossCoefficient≠(F.model E).lossCoefficient ∧
  (F.model C).BenchmarkEquilibrium (F.commonUtility c) (F.commonEndowment s0) s0 ∧
  (F.model E).BenchmarkEquilibrium (F.commonUtility c) (F.commonEndowment s0) s0

theorem failed_answer_direction_witness (hn : 0<n) (hk : 0<k)
    (P : Partition n g) (R : Refinement P F.parents) (H : HiddenBasis (P.Q F.q) r)
    (C0 : F.Candidate) (hfail : ¬F.IdentifiedAt P C0)
    (s0 c : ℝ) (hs : 0<s0) :
    ∃Z : Mat r k,∀V : Set ℝ,V∈𝓝 0 →
      ∃t∈V,t≠0 ∧ ∃C : F.Candidate,C.val=C0.val+H.N*(t • Z) ∧
        F.SameObservationWitness P C C0 s0 c := by
  let a := F.answerData C0.val H.N
  let U := F.frame.FiberDomain F.p H C0.val
  have hh := F.economic_B1_hypotheses (F.total_positive_of_goods hn) hk P R C0 H
  have hf : ¬a.CongruenceCriterion := fun hc => hfail
    ((F.identifiedAt_iff_congruence (F.total_positive_of_goods hn) hk P R C0 H).mpr hc)
  obtain ⟨Z,hZ⟩ := a.failure_has_change_direction U hh hf
  refine ⟨Z,?_⟩
  intro V hV
  obtain ⟨t,ht,ht0,htU,hne⟩ := a.admissibleChanges_nonzero U Z hZ V hV
  have hreport := H.report_point C0.val (t • Z)
  have hC : C0.val+H.N*(t • Z)∈F.frame.Candidates F.p F.q F.parents F.report :=
    ⟨htU,(R.report_preserved F.q _ _ hreport).trans C0.property.2⟩
  let C : F.Candidate := ⟨C0.val+H.N*(t • Z),hC⟩
  refine ⟨t,ht,ht0,C,rfl,hreport,?_,?_,F.every_candidate_equilibrium hs c C,
    F.every_candidate_equilibrium hs c C0⟩
  · change P.report F.q (F.frame.reconstruct F.p C.val)=
      P.report F.q (F.frame.reconstruct F.p C0.val)
    rw [P.report_reconstruct,P.report_reconstruct]
    exact congrArg (F.frame.reconstruct (P.sales F.p F.q))
      (show P.report F.q C.val=P.report F.q C0.val from hreport)
  · rw [F.candidate_lossCoefficient C,F.candidate_lossCoefficient C0]
    intro he
    exact hne ((F.coefficient_eq_iff_F_eq C0.val C.val C0.val H.N).mp he)

theorem pair_failure_direction_witness (hn : 0<n)
    (P : Partition n g) (R : Refinement P F.parents) (hnc : ¬F.ParentIdentified)
    (hpair : ¬F.PairRule P) (s0 c : ℝ) (hs : 0<s0) :
    ∃r,∃H : HiddenBasis (P.Q F.q) r,∃C0 : F.Candidate,∃Z : Mat r k,
      ∀V : Set ℝ,V∈𝓝 0 → ∃t∈V,t≠0 ∧ ∃C : F.Candidate,
        C.val=C0.val+H.N*(t • Z) ∧ F.SameObservationWitness P C C0 s0 c := by
  have hf : ¬F.ReportIdentified P :=
    fun hp => hpair ((F.exact_commodity_pair_rule_of_goods hn P R hnc).mp hp)
  obtain ⟨C0,hf⟩ := not_forall.mp hf
  obtain ⟨r,⟨H⟩⟩ := exists_hiddenBasis (P.Q F.q)
  obtain ⟨Z,hZ⟩ := F.failed_answer_direction_witness hn
    (F.positive_relative_dimension_of_parent_failure hnc) P R H C0 hf s0 c hs
  exact ⟨r,H,C0,Z,hZ⟩

theorem pair_failure_common_benchmark_witness (hn : 0<n)
    (P : Partition n g) (R : Refinement P F.parents) (hnc : ¬F.ParentIdentified)
    (hpair : ¬F.PairRule P) (s0 c : ℝ) (hs : 0<s0) :
    ∃C E : F.Candidate,F.SameObservationWitness P C E s0 c := by
  obtain ⟨r,H,E,Z,hZ⟩ := F.pair_failure_direction_witness hn P R hnc hpair s0 c hs
  obtain ⟨t,_,_,C,_,hw⟩ := hZ Set.univ (Filter.univ_mem)
  exact ⟨C,E,hw⟩

theorem unequal_attributes_common_benchmark_witness (hn : 0<n)
    (P : Partition n g) (R : Refinement P F.parents) (hnc : ¬F.ParentIdentified)
    (i j : Fin n) (hij : P.group i=P.group j) (hattr : ¬F.SamePolicyAttributes i j)
    (s0 c : ℝ) (hs : 0<s0) :
    ∃C E : F.Candidate,F.SameObservationWitness P C E s0 c :=
  F.pair_failure_common_benchmark_witness hn P R hnc (fun hp => hattr (hp i j hij)) s0 c hs

end CommodityClassification.Equilibrium.BenchmarkFamily
