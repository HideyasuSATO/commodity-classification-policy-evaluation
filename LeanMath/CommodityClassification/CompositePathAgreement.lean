module

public import LeanMath.CommodityClassification.CompositeCompetitivePaths

/-! Paired genuine equilibria: common first-order responses and actual welfare coefficient. -/
@[expose] public section
noncomputable section
set_option maxHeartbeats 1600000
namespace CommodityClassification.Equilibrium.BenchmarkFamily
open Matrix InputCoordinates Filter Asymptotics
open scoped Topology
variable {n k h g : ℕ} (F : BenchmarkFamily n k h)

structure CompositePathAgreement (P : Partition n g) (B : Mat g g) (β : Vec g)
    (hD : F.D=F.sigma • Supply.xi F.p F.q+P.Q F.q*B*(P.Q F.q).transpose)
    (C : F.Candidate) (s0 c : ℝ)
    (u : ℝ → Vec k) (s : ℝ → ℝ) (v : ℝ → Vec k) (t : ℝ → ℝ) : Prop where
  original_path : (F.matchedModel P B hD C).PositiveLocalPath s0 u s
  reduced_path : (F.compositeModel P β C).PositiveLocalPath s0 v t
  original_competitive : ∃I : Set ℝ,IsOpen I ∧ 0∈I ∧ ∀a∈I,
    (F.matchedModel P B hD C).CompetitiveState (F.matchedUtility P c)
      {x | ∀i,0≤x i} (F.commonEndowment s0) (a,u a) (s a)
  reduced_competitive : ∃I : Set ℝ,IsOpen I ∧ 0∈I ∧ ∀a∈I,
    (F.compositeModel P β C).CompetitiveState (F.compositeUtility P c)
      Set.univ (F.commonEndowment s0) (a,v a) (t a)
  original_relative_price : HasDerivAt u (F.model C).zSolution 0
  reduced_relative_price : HasDerivAt v (F.model C).zSolution 0
  original_factor_price : HasDerivAt (fun a => (F.matchedModel P B hD C).currentPrice (u a))
    (F.frame.V *ᵥ (F.model C).zSolution) 0
  reduced_factor_price : HasDerivAt (fun a => (F.compositeModel P β C).currentPrice (v a))
    (F.frame.V *ᵥ (F.model C).zSolution) 0
  original_group_quantity : HasDerivAt
    (fun a => P.valueAggregation F.p *ᵥ (F.matchedModel P B hD C).quantities (a,u a))
    (F.groupQuantityResponse P C) 0
  reduced_quantity : HasDerivAt (fun a => (F.compositeModel P β C).quantities (a,v a))
    (F.groupQuantityResponse P C) 0
  original_group_price : HasDerivAt
    (fun a => (F.nestData P (fun _ => F.sigma) (fun _ => F.hsigma)).priceMap
      ((F.matchedModel P B hD C).prices (a,u a)))
    (β+F.compositeCoordinates P C *ᵥ (F.model C).zSolution) 0
  reduced_group_price : HasDerivAt (fun a => (F.compositeModel P β C).prices (a,v a))
    (β+F.compositeCoordinates P C *ᵥ (F.model C).zSolution) 0
  original_welfare :
    (fun a => (F.matchedModel P B hD C).welfare (F.matchedUtility P c) u s 0-
      (F.matchedModel P B hD C).welfare (F.matchedUtility P c) u s a-
      (1/2 : ℝ)*a^2*(F.model C).lossCoefficient)=o[𝓝 (0 : ℝ)] (fun a : ℝ => a^2)
  reduced_welfare :
    (fun a => (F.compositeModel P β C).welfare (F.compositeUtility P c) v t 0-
      (F.compositeModel P β C).welfare (F.compositeUtility P c) v t a-
      (1/2 : ℝ)*a^2*(F.model C).lossCoefficient)=o[𝓝 (0 : ℝ)] (fun a : ℝ => a^2)

theorem local_composite_path_agreement (P : Partition n g) (B : Mat g g) (β : Vec g)
    (hD : F.D=F.sigma • Supply.xi F.p F.q+P.Q F.q*B*(P.Q F.q).transpose)
    (hb : F.b=P.Q F.p *ᵥ β) (C : F.Candidate) (hn : 0<n)
    (s0 c : ℝ) (hs : 0<s0) :
    (F.matchedModel P B hD C).BenchmarkEquilibrium (F.matchedUtility P c)
      (F.commonEndowment s0) s0 ∧
    (F.compositeModel P β C).BenchmarkEquilibrium (F.compositeUtility P c)
      (F.commonEndowment s0) s0 ∧
    ∃u : ℝ → Vec k,∃s : ℝ → ℝ,∃v : ℝ → Vec k,∃t : ℝ → ℝ,
      F.CompositePathAgreement P B β hD C s0 c u s v t := by
  obtain ⟨hbase,u,s,hp,hcomp,hu,hq,hw⟩ := F.matched_actual_implementation P B hD C hn s0 c hs
  obtain ⟨v,t,hpG,hcompG,hv,_,hqG,hwG⟩ := F.composite_competitive_path P β C hn s0 c hs
  rw [F.compositeModel_zSolution P B β hD hb C] at hv
  rw [F.compositeModel_qSolution P B β hD hb C] at hqG
  have hq' := (matCLM (P.valueAggregation F.p)).hasFDerivAt.comp_hasDerivAt (0 : ℝ) hq
  have hwG' :
      (fun a => (F.compositeModel P β C).welfare (F.compositeUtility P c) v t 0-
        (F.compositeModel P β C).welfare (F.compositeUtility P c) v t a-
        (1/2 : ℝ)*a^2*(F.model C).lossCoefficient)=o[𝓝 (0 : ℝ)] (fun a : ℝ => a^2) := by
    unfold Model.WelfareExpansion at hwG
    rwa [F.compositeModel_lossCoefficient P B β hD hb C] at hwG
  refine ⟨hbase,F.compositeModel_benchmark P β C s0 c hs,u,s,v,t,?_⟩
  refine ⟨hp,hpG,hcomp,hcompG,hu,hv,?_,?_,?_,hqG,?_,?_,hw,hwG'⟩
  · exact (F.matchedModel P B hD C).factor_price_path_derivative u _ hp.price_base hu
  · exact (F.compositeModel P β C).factor_price_path_derivative v _ hpG.price_base hv
  · simpa only [matCLM_apply,Function.comp_def,groupQuantityResponse] using hq'
  · exact F.composite_index_path_derivative P β hb C u _ hp.price_base hu
  · exact (F.compositeModel P β C).consumer_price_path_derivative v _ hpG.price_base hv

theorem composite_outer_utility_calibration (P : Partition n g) (c : ℝ) :
    HasFDerivAt (F.compositeUtility P c) (CESCost.weightedLinear (fun _ => 1)) (P.sales F.p F.q) ∧
    HasFDerivAt (benchmarkGradient (fun _ => 1) (P.sales F.p F.q) (P.groupDemand F.p F.D))
      (-matCLM (P.groupDemand F.p F.D)⁻¹) (P.sales F.p F.q) :=
  ⟨benchmarkUtility_derivative_base _ _ _ (F.composite_groupDemand_posDef P) c,
    benchmarkGradient_derivative _ _ _ _⟩

end CommodityClassification.Equilibrium.BenchmarkFamily
