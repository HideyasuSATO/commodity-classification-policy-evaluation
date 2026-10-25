module

public import LeanMath.CommodityClassification.CompositePriceResponse

/-! Competitive local paths in the genuine reduced economy, with actual welfare. -/
@[expose] public section
noncomputable section
set_option maxHeartbeats 1200000
namespace CommodityClassification.Equilibrium.BenchmarkFamily
open Matrix InputCoordinates Filter Asymptotics
open scoped Topology
variable {n k h g : ℕ} (F : BenchmarkFamily n k h)

theorem composite_competitive_path (P : Partition n g) (β : Vec g) (C : F.Candidate)
    (hn : 0<n) (s0 c : ℝ) (hs : 0<s0) :
    let E := F.compositeModel P β C
    ∃u : ℝ → Vec k,∃s : ℝ → ℝ,E.PositiveLocalPath s0 u s ∧
      (∃I : Set ℝ,IsOpen I ∧ 0∈I ∧ ∀t∈I,E.CompetitiveState (F.compositeUtility P c)
        Set.univ (F.commonEndowment s0) (t,u t) (s t)) ∧
      HasDerivAt u E.zSolution 0 ∧ HasDerivAt s E.sSolution 0 ∧
      HasDerivAt (fun t => E.quantities (t,u t)) E.qSolution 0 ∧
      E.WelfareExpansion (F.compositeUtility P c) u s := by
  let E := F.compositeModel P β C
  have hh := E.quadratic_competitive_implementation (F.compositeModel_demandC1 P β C)
    (Partition.singleton g) ((Partition.singleton g).report E.q E.C) rfl
    (P.sales_pos F.p F.q F.hp F.hq) (F.compositeModel_total_positive P β C hn)
    (F.composite_groupDemand_posDef P) F.hsigma (fun j => (F.ha0 j).le) s0 hs rfl
    (F.compositeUtility P c) c Set.univ (by simp) (by intro r _;rfl)
  obtain ⟨u,s,hp,hcomp,hu,hs',hq,hw⟩ := hh
  refine ⟨u,s,hp,?_,hu,hs',hq,hw⟩
  change ∃I : Set ℝ,IsOpen I ∧ 0∈I ∧ ∀t∈I,(F.compositeModel P β C).CompetitiveState
    (F.compositeUtility P c) Set.univ ((F.compositeModel P β C).endowment s0) (t,u t) (s t) at hcomp
  rwa [F.compositeModel_endowment P β C s0] at hcomp

def matchedModel (P : Partition n g) (B : Mat g g)
    (hD : F.D=F.sigma • Supply.xi F.p F.q+P.Q F.q*B*(P.Q F.q).transpose)
    (C : F.Candidate) : Model n k :=
  F.nestedModel P (fun _ => F.sigma) (fun _ => F.hsigma) (P.groupDemand F.p F.D)
    (F.composite_demand_recovery P B hD) C

def matchedUtility (P : Partition n g) (c : ℝ) : Vec n → ℝ :=
  (F.nestData P (fun _ => F.sigma) (fun _ => F.hsigma)).nestedUtility (P.groupDemand F.p F.D) c

theorem matched_actual_implementation (P : Partition n g) (B : Mat g g)
    (hD : F.D=F.sigma • Supply.xi F.p F.q+P.Q F.q*B*(P.Q F.q).transpose)
    (C : F.Candidate) (hn : 0<n) (s0 c : ℝ) (hs : 0<s0) :
    (F.matchedModel P B hD C).BenchmarkEquilibrium (F.matchedUtility P c)
      (F.commonEndowment s0) s0 ∧
    ∃u : ℝ → Vec k,∃s : ℝ → ℝ,(F.matchedModel P B hD C).PositiveLocalPath s0 u s ∧
      (∃I : Set ℝ,IsOpen I ∧ 0∈I ∧ ∀t∈I,(F.matchedModel P B hD C).CompetitiveState
        (F.matchedUtility P c) {x | ∀i,0≤x i} (F.commonEndowment s0) (t,u t) (s t)) ∧
      HasDerivAt u (F.model C).zSolution 0 ∧
      HasDerivAt (fun t => (F.matchedModel P B hD C).quantities (t,u t)) (F.model C).qSolution 0 ∧
      (F.matchedModel P B hD C).WelfareExpansion (F.matchedUtility P c) u s := by
  have hh := F.nested_candidate_implementation P (fun _ => F.sigma) (fun _ => F.hsigma)
    (P.groupDemand F.p F.D) (F.composite_demand_recovery P B hD)
    (F.composite_groupDemand_posDef P) hn C s0 c hs
  obtain ⟨hb,u,s,hp,_,hq,hw,hcomp⟩ := hh
  have hu := ((F.matchedModel P B hD C).positive_path_solution
    (F.candidate_model_K_posDef hn C) s0 u s hp).1
  exact ⟨hb,u,s,hp,hcomp,hu,hq,hw⟩

end CommodityClassification.Equilibrium.BenchmarkFamily
