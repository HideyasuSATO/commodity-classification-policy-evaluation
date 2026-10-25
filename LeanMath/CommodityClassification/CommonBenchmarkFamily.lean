module
public import LeanMath.CommodityClassification.CommonBenchmarkEquilibrium
@[expose] public section
set_option maxHeartbeats 2400000
namespace CommodityClassification.Equilibrium
open Matrix Filter
open scoped BigOperators Topology

/-- Fixed primitives and an explicit witness of candidate nonemptiness. No
equilibrium or consumer/firm optimality is included among these fields. -/
structure BenchmarkFamily (n k g : ℕ) where
  frame : InputCoordinates.Frame k
  p : Vec n
  q : Vec n
  b : Vec n
  D : Mat n n
  sigma : ℝ
  parents : InputCoordinates.Partition n g
  report : Mat g k
  reference : Mat n k
  reference_mem : reference ∈ frame.Candidates p q parents report
  hp : ∀i,0<p i
  hq : ∀i,0<q i
  hw : ∀j,0<frame.w j
  ha0 : ∀j,0<frame.a0 j
  hD : D.PosDef
  hsigma : 0<sigma

namespace BenchmarkFamily
variable {n k g : ℕ} (F : BenchmarkFamily n k g)

def Candidate := {C : Mat n k // C ∈ F.frame.Candidates F.p F.q F.parents F.report}

noncomputable def model (C : F.Candidate) : Model n k :=
  Model.ofAffine F.frame F.p F.q C.val F.D F.b F.sigma F.hp F.hw C.property.1

def referenceCandidate : F.Candidate := ⟨F.reference,F.reference_mem⟩

noncomputable def commonEndowment (s0 : ℝ) : Vec (k+1) :=
  (F.frame.reconstruct F.p F.reference).transpose *ᵥ F.q+s0 • F.frame.a0

noncomputable def commonUtility (c : ℝ) : Vec n → ℝ := benchmarkUtility F.p F.q F.D c

theorem candidate_total_inputs (C : F.Candidate) :
    (F.model C).A.transpose *ᵥ F.q=(F.frame.reconstruct F.p F.reference).transpose *ᵥ F.q := by
  have hh := Supply.candidate_total_eq F.frame F.parents F.p F.q F.report F.reference C.val
    F.reference_mem C.property
  ext j
  have hj := congrFun hh j
  simpa [Supply.totalInputs,Matrix.mulVec,Matrix.transpose,dotProduct,mul_comm,model,
    Model.ofAffine,Model.A] using hj

theorem candidate_endowment (C : F.Candidate) (s0 : ℝ) :
    (F.model C).endowment s0=F.commonEndowment s0 := by
  change (F.model C).A.transpose *ᵥ F.q+s0 • F.frame.a0=_
  rw [F.candidate_total_inputs C]
  rfl

theorem commonEndowment_positive {s0 : ℝ} (hs : 0<s0) : ∀j,0<F.commonEndowment s0 j := by
  rw [←F.candidate_endowment F.referenceCandidate s0]
  exact (F.model F.referenceCandidate).endowment_positive (fun i => (F.hq i).le) F.ha0 hs

theorem commonUtility_value (c : ℝ) : F.commonUtility c F.q=c :=
  benchmarkUtility_value F.p F.q F.D c

theorem commonUtility_derivative (c : ℝ) :
    HasFDerivAt (F.commonUtility c) (CESCost.weightedLinear F.p) F.q :=
  benchmarkUtility_derivative_base F.p F.q F.D F.hD c

theorem commonUtility_hessian :
    HasFDerivAt (benchmarkGradient F.p F.q F.D) (-matCLM F.D⁻¹) F.q :=
  benchmarkGradient_derivative F.p F.q F.D F.q

theorem commonUtility_strictConcave (c : ℝ) : StrictConcaveOn ℝ Set.univ (F.commonUtility c) :=
  benchmarkUtility_strictConcave F.p F.q F.D F.hD c

theorem commonUtility_positive_marginals :
    ∀ᶠ r in 𝓝 F.q,(∀i,0<r i) ∧ ∀i,0<benchmarkGradient F.p F.q F.D r i :=
  benchmarkUtility_marginals_positive_near F.p F.q F.D F.hp F.hq

theorem candidate_utility_compatible (C : F.Candidate) (c : ℝ) :
    (F.model C).UtilityCompatible (F.commonUtility c) := by
  apply (F.model C).quadratic_utility_compatible F.hD rfl (F.commonUtility c) c Set.univ
    (by simp)
  intro r _
  rfl

theorem candidate_demand_implemented (C : F.Candidate) (c : ℝ) (v : Vec n) :
    ∀r : Vec n,F.commonUtility c r-dotProduct v r ≤
      F.commonUtility c ((F.model C).demand v)-dotProduct v ((F.model C).demand v) :=
  fun r => benchmarkUtility_surplus_maximum F.p F.q v r F.D F.hD c

theorem candidate_demand_derivative (C : F.Candidate) :
    HasFDerivAt (F.model C).demand (-matCLM F.D) F.p := (F.model C).demand_deriv

theorem every_candidate_equilibrium {s0 : ℝ} (hs : 0<s0) (c : ℝ) (C : F.Candidate) :
    (F.model C).BenchmarkEquilibrium (F.commonUtility c) (F.commonEndowment s0) s0 := by
  rw [←F.candidate_endowment C s0]
  exact (F.model C).benchmark_equilibrium F.hD F.hsigma F.hq (fun j => (F.ha0 j).le) hs c

/-- Common objects are existentially chosen before all supply candidates. -/
theorem common_benchmark_exists {s0 : ℝ} (hs : 0<s0) (c : ℝ) :
    ∃abar : Vec (k+1), ∃utility : Vec n → ℝ,
      (∀j,0<abar j) ∧ utility F.q=c ∧
      HasFDerivAt utility (CESCost.weightedLinear F.p) F.q ∧
      StrictConcaveOn ℝ Set.univ utility ∧
      ∀C : F.Candidate,(F.model C).BenchmarkEquilibrium utility abar s0 ∧
        (F.model C).UtilityCompatible utility := by
  exact ⟨F.commonEndowment s0,F.commonUtility c,F.commonEndowment_positive hs,
    F.commonUtility_value c,F.commonUtility_derivative c,F.commonUtility_strictConcave c,
    fun C => ⟨F.every_candidate_equilibrium hs c C,F.candidate_utility_compatible C c⟩⟩

theorem same_benchmark_budget (C E : F.Candidate) (s0 : ℝ) :
    (F.model C).householdIncome (F.commonEndowment s0) 0 =
      (F.model E).householdIncome (F.commonEndowment s0) 0 ∧
    dotProduct F.p F.q+s0=dotProduct F.frame.w (F.commonEndowment s0) := by
  constructor
  · simp [Model.householdIncome,Model.taxTransfer,model,Model.ofAffine]
  · rw [←F.candidate_endowment C s0]
    exact (F.model C).benchmark_budget s0

theorem common_local_utility (utility : Vec n → ℝ) (c s0 : ℝ) (U : Set (Vec n))
    (hq : F.q∈U) (hmatch : ∀r∈U,utility r=F.commonUtility c r) :
    ∀r∈U,∀z : ℝ,dotProduct F.p r+z≤dotProduct F.frame.w (F.commonEndowment s0) →
      utility r+z≤utility F.q+s0 := by
  exact matching_utility_benchmark_household F.p F.q F.D F.hD utility c s0 _ U hq hmatch
    (F.same_benchmark_budget F.referenceCandidate F.referenceCandidate s0).2

end BenchmarkFamily
end CommodityClassification.Equilibrium
