module
public import LeanMath.CommodityClassification.WelfareFixedAnswerBridge
@[expose] public section
set_option maxHeartbeats 2400000
namespace CommodityClassification.Equilibrium.BenchmarkFamily
open Matrix Filter
open scoped BigOperators Topology
variable {n k g h r : ℕ} (F : BenchmarkFamily n k h)

/-- Identification conditional on one fixed realized answer. -/
def IdentifiedAt (P : InputCoordinates.Partition n g) (C0 : F.Candidate) : Prop :=
  ∀C∈F.frame.FixedFiber F.p F.q F.parents F.report P C0.val,
    F.coefficient C=F.coefficient C0.val

theorem coefficient_fiber_constancy_iff (P : InputCoordinates.Partition n g)
    (refineP : InputCoordinates.Refinement P F.parents) (C0 : F.Candidate)
    (H : InputCoordinates.HiddenBasis (P.Q F.q) r) :
    F.IdentifiedAt P C0 ↔
      (F.answerData C0.val H.N).ConstantOn (F.frame.FiberDomain F.p H C0.val) := by
  constructor
  · intro hc Z hZ
    apply (F.coefficient_eq_iff_F_eq C0.val _ C0.val H.N).mp
    apply hc
    rw [F.frame.fixedFiber_eq_image F.p F.q refineP F.report C0.val C0.property H]
    exact ⟨Z,hZ,rfl⟩
  · intro hc C hC
    rw [F.frame.fixedFiber_eq_image F.p F.q refineP F.report C0.val C0.property H] at hC
    obtain ⟨Z,hZ,rfl⟩ := hC
    apply (F.coefficient_eq_iff_F_eq C0.val _ C0.val H.N).mpr
    exact hc Z hZ

theorem economic_B1_hypotheses
    (hI : ∀j,0<Supply.totalInputs F.q (F.frame.reconstruct F.p F.reference) j)
    (hk : 0<k) (P : InputCoordinates.Partition n g)
    (refineP : InputCoordinates.Refinement P F.parents) (C0 : F.Candidate)
    (H : InputCoordinates.HiddenBasis (P.Q F.q) r) :
    (F.answerData C0.val H.N).Hypotheses (F.frame.FiberDomain F.p H C0.val) := by
  have hR := Supply.candidate_R_posDef F.frame F.p F.q F.reference F.hw hI
  have hL := F.hD.isHermitian.sub
    (((Regularity.xi_posDef F.p F.q F.hp F.hq).smul F.hsigma).isHermitian)
  have hbase : (F.sigma • F.fixedR).transpose=F.sigma • F.fixedR :=
    (hR.smul F.hsigma).isHermitian.isSymm
  have hL' : (Regularity.adjustedDemand F.p F.q F.D F.sigma).transpose=
      Regularity.adjustedDemand F.p F.q F.D F.sigma := hL.isSymm
  refine ⟨hk,hbase,hL',H.independent,F.frame.fiberDomain_open F.p H C0.val,
    F.frame.fiberDomain_zero F.p H C0.val C0.property.1,?_⟩
  apply Regularity.fixedAnswer_K_posDef_on F.frame F.parents F.p F.q F.report F.reference
    C0.val F.D F.sigma F.b H.N _ F.hp F.hq F.hw hI F.reference_mem F.hD F.hsigma
  intro Z hZ
  exact ⟨hZ,(refineP.report_preserved F.q _ _ (H.report_point C0.val Z)).trans C0.property.2⟩

theorem identifiedAt_iff_congruence
    (hI : ∀j,0<Supply.totalInputs F.q (F.frame.reconstruct F.p F.reference) j)
    (hk : 0<k) (P : InputCoordinates.Partition n g)
    (refineP : InputCoordinates.Refinement P F.parents) (C0 : F.Candidate)
    (H : InputCoordinates.HiddenBasis (P.Q F.q) r) :
    F.IdentifiedAt P C0 ↔ (F.answerData C0.val H.N).CongruenceCriterion := by
  rw [F.coefficient_fiber_constancy_iff P refineP C0 H]
  exact FixedAnswer.lemmaB1_local _ _ (F.economic_B1_hypotheses hI hk P refineP C0 H)

theorem identifiedAt_zero_load_iff
    (hI : ∀j,0<Supply.totalInputs F.q (F.frame.reconstruct F.p F.reference) j)
    (hk : 0<k) (P : InputCoordinates.Partition n g)
    (refineP : InputCoordinates.Refinement P F.parents) (C0 : F.Candidate)
    (H : InputCoordinates.HiddenBasis (P.Q F.q) r)
    (hm : (F.answerData C0.val H.N).m₀=0) :
    F.IdentifiedAt P C0 ↔ (F.answerData C0.val H.N).r_N=0 := by
  rw [F.coefficient_fiber_constancy_iff P refineP C0 H]
  exact FixedAnswer.zeroLoad_constantOn_iff _ _ (F.economic_B1_hypotheses hI hk P refineP C0 H) hm

theorem congruence_global_coefficient
    (hI : ∀j,0<Supply.totalInputs F.q (F.frame.reconstruct F.p F.reference) j)
    (hk : 0<k) (P : InputCoordinates.Partition n g)
    (refineP : InputCoordinates.Refinement P F.parents) (C0 : F.Candidate)
    (H : InputCoordinates.HiddenBasis (P.Q F.q) r)
    (hc : (F.answerData C0.val H.N).CongruenceCriterion) :
    ∀Z,(F.answerData C0.val H.N).K ((F.answerData C0.val H.N).point Z) |>.PosDef →
      F.coefficient (C0.val+H.N*Z)=F.coefficient C0.val := by
  intro Z hZ
  apply (F.coefficient_eq_iff_F_eq C0.val _ C0.val H.N).mpr
  exact FixedAnswer.lemmaB1_global _ _ (F.economic_B1_hypotheses hI hk P refineP C0 H) hc Z hZ

theorem identifiedAt_no_hidden (P : InputCoordinates.Partition n g)
    (refineP : InputCoordinates.Refinement P F.parents) (C0 : F.Candidate)
    (H : InputCoordinates.HiddenBasis (P.Q F.q) 0) : F.IdentifiedAt P C0 := by
  intro C hC
  rw [F.frame.fixedFiber_zeroDim F.p F.q refineP F.report C0.val C0.property H] at hC
  rw [Set.mem_singleton_iff.mp hC]

theorem identifiedAt_zero_relative (F0 : BenchmarkFamily n 0 h)
    (P : InputCoordinates.Partition n g) (C0 : F0.Candidate) : F0.IdentifiedAt P C0 := by
  intro C _
  rw [coefficient_zero_relative,coefficient_zero_relative]

/-- Failure gives two positive economies with the SAME reported answer and
the SAME endowment and utility, and unequal actual welfare coefficients. -/
theorem failure_same_benchmark_witness
    (hI : ∀j,0<Supply.totalInputs F.q (F.frame.reconstruct F.p F.reference) j)
    (hk : 0<k) (P : InputCoordinates.Partition n g)
    (refineP : InputCoordinates.Refinement P F.parents) (C0 : F.Candidate)
    (H : InputCoordinates.HiddenBasis (P.Q F.q) r)
    (hfail : ¬(F.answerData C0.val H.N).CongruenceCriterion)
    (s0 c : ℝ) (hs : 0<s0) :
    ∃C : F.Candidate,P.report F.q C.val=P.report F.q C0.val ∧
      (F.model C).lossCoefficient≠(F.model C0).lossCoefficient ∧
      (F.model C).BenchmarkEquilibrium (F.commonUtility c) (F.commonEndowment s0) s0 ∧
      (F.model C0).BenchmarkEquilibrium (F.commonUtility c) (F.commonEndowment s0) s0 := by
  classical
  have hn : ¬F.IdentifiedAt P C0 := fun hh => hfail ((F.identifiedAt_iff_congruence hI hk P refineP C0 H).mp hh)
  unfold IdentifiedAt at hn
  push Not at hn
  obtain ⟨C,hC,hne⟩ := hn
  refine ⟨⟨C,hC.1⟩,hC.2,?_,F.every_candidate_equilibrium hs c ⟨C,hC.1⟩,
    F.every_candidate_equilibrium hs c C0⟩
  rw [F.candidate_lossCoefficient ⟨C,hC.1⟩,F.candidate_lossCoefficient C0]
  exact hne

end CommodityClassification.Equilibrium.BenchmarkFamily
