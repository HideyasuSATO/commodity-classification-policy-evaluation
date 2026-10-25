module

public import LeanMath.CommodityClassification.StrongQuantitySufficiency
public import LeanMath.CommodityClassification.LocalCompetitiveImplementation

/-! The group derivative and competitive implementation refer to the same path. -/
@[expose] public section
noncomputable section
namespace CommodityClassification.Equilibrium.BenchmarkFamily
open Matrix InputCoordinates
variable {n k h g : ℕ} (F : BenchmarkFamily n k h)

theorem groupQuantityResponse_competitive_path (hn : 0<n) (P : Partition n g)
    (s0 c : ℝ) (hs : 0<s0) (C : F.Candidate) :
    ∃u : ℝ → Vec k,∃s : ℝ → ℝ,(F.model C).PositiveLocalPath s0 u s ∧
      (∃I : Set ℝ,IsOpen I ∧ 0∈I ∧ ∀t∈I,(F.model C).CompetitiveState
        (F.commonUtility c) Set.univ (F.commonEndowment s0) (t,u t) (s t)) ∧
      HasDerivAt (fun t => P.valueAggregation F.p *ᵥ (F.model C).quantities (t,u t))
        (F.groupQuantityResponse P C) 0 := by
  obtain ⟨u,s,hpath,hcomp,_,_,hq,_⟩ :=
    F.candidate_competitive_implementation (F.total_positive_of_goods hn) s0 c hs C
  refine ⟨u,s,hpath,hcomp,?_⟩
  have hd := (matCLM (P.valueAggregation F.p)).hasFDerivAt.comp_hasDerivAt (0 : ℝ) hq
  simpa only [matCLM_apply,Function.comp_def,groupQuantityResponse] using hd

end CommodityClassification.Equilibrium.BenchmarkFamily
