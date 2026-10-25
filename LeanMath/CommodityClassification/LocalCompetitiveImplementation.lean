module
public import LeanMath.CommodityClassification.LocalCompetitiveState
@[expose] public section
set_option maxHeartbeats 2400000
namespace CommodityClassification.Equilibrium
open Matrix Filter Asymptotics
open scoped BigOperators Topology
variable {n k g : ℕ}
namespace Model
variable (E : Model n k)

/-- Same actual constructed paths: local clearing/uniqueness, full competitive
certificate over U, derivatives and two-sided welfare expansion. -/
theorem quadratic_competitive_implementation (h : E.DemandC1)
    (P : InputCoordinates.Partition n g) (J : Mat g k) (hr : P.report E.q E.C=J)
    (hq : ∀i,0<E.q i) (hI : ∀j,0<Supply.totalInputs E.q E.A j)
    (hD : E.D.PosDef) (hσ : 0<E.sigma) (ha : ∀j,0≤E.frame.a0 j)
    (s0 : ℝ) (hs : 0<s0) (haff : E.demand=affineDemand E.p E.q E.D)
    (utility : Vec n → ℝ) (c : ℝ) (U : Set (Vec n)) (hU : U∈𝓝 E.q)
    (hm : ∀r∈U,utility r=c+quadraticUtility E.p E.D (r-E.q)) :
    ∃u : ℝ → Vec k,∃s : ℝ → ℝ,E.PositiveLocalPath s0 u s ∧
      (∃I : Set ℝ,IsOpen I ∧ 0∈I ∧ ∀t∈I,E.CompetitiveState utility U (E.endowment s0) (t,u t) (s t)) ∧
      HasDerivAt u E.zSolution 0 ∧ HasDerivAt s E.sSolution 0 ∧
      HasDerivAt (fun t => E.quantities (t,u t)) E.qSolution 0 ∧ E.WelfareExpansion utility u s := by
  let hK := E.K_posDef P J hr hq hI hD hσ
  have hd := E.constructed_path_derivatives h P J hr hq hI hD hσ s0
  have hw := E.constructed_quadratic_welfare h hK hq s0 hs hD haff utility c U hU hm
  refine ⟨E.localPricePath h hK s0,E.localNumerairePath h hK s0,
    E.constructed_positive_path h hK hq s0 hs,
    E.quadratic_neighborhood_competitive hσ ha s0 utility U _ _ hw,
    hd.1,hd.2.1,hd.2.2,?_⟩
  exact E.constructed_welfare_expansion h P J hr hq hI hD hσ s0 hs utility
    (E.quadratic_utility_compatible hD haff utility c U hU hm)

end Model
namespace BenchmarkFamily
variable (F : BenchmarkFamily n k g)

/-- Fixed common utility/endowment before all candidates. Each candidate's
own constructed policy path is a competitive equilibrium on a neighborhood. -/
theorem candidate_competitive_implementation
    (hI : ∀j,0<Supply.totalInputs F.q (F.frame.reconstruct F.p F.reference) j)
    (s0 c : ℝ) (hs : 0<s0) (C : F.Candidate) :
    ∃u : ℝ → Vec k,∃s : ℝ → ℝ,(F.model C).PositiveLocalPath s0 u s ∧
      (∃I : Set ℝ,IsOpen I ∧ 0∈I ∧ ∀t∈I,(F.model C).CompetitiveState
        (F.commonUtility c) Set.univ (F.commonEndowment s0) (t,u t) (s t)) ∧
      HasDerivAt u (F.model C).zSolution 0 ∧ HasDerivAt s (F.model C).sSolution 0 ∧
      HasDerivAt (fun t => (F.model C).quantities (t,u t)) (F.model C).qSolution 0 ∧
      (fun t => (F.model C).welfare (F.commonUtility c) u s 0-
        (F.model C).welfare (F.commonUtility c) u s t-(1/2 : ℝ)*t^2*F.coefficient C.val)
        =o[𝓝 (0 : ℝ)] (fun t : ℝ => t^2) := by
  have hh := (F.model C).quadratic_competitive_implementation
    (Model.ofAffine_demandC1 F.frame F.p F.q C.val F.D F.b F.sigma F.hp F.hw C.property.1)
    F.parents F.report C.property.2 F.hq (F.candidate_total_positive hI C) F.hD F.hsigma
    (fun j => (F.ha0 j).le) s0 hs rfl (F.commonUtility c) c Set.univ (by simp) (by intro r _; rfl)
  obtain ⟨u,s,hpath,hcomp,hu,hs',hq,hw⟩ := hh
  refine ⟨u,s,hpath,?_,hu,hs',hq,?_⟩
  · rwa [F.candidate_endowment C s0] at hcomp
  · unfold Model.WelfareExpansion at hw
    rwa [F.candidate_lossCoefficient C] at hw

end BenchmarkFamily
end CommodityClassification.Equilibrium
