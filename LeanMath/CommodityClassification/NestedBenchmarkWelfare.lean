module

public import LeanMath.CommodityClassification.NestedEquilibriumModel

/-! The original nested utility supports the common benchmark and actual expansion. -/
@[expose] public section
noncomputable section
set_option maxHeartbeats 1000000
namespace CommodityClassification.Equilibrium.BenchmarkFamily
open Matrix InputCoordinates Filter
open scoped Topology
variable {n k h g : ℕ} (F : BenchmarkFamily n k h)
  (G : Partition n g) (η : Vec g) (hη : ∀a,0<η a)
  (DG : Mat g g) (hDG : DG.PosDef) (hD : F.D=(F.nestData G η hη).demandMatrix DG)

include hDG

theorem nested_benchmark_surplus (c : ℝ) :
    IsMaxOn (fun x => (F.nestData G η hη).nestedUtility DG c x-dotProduct F.p x)
      {x | ∀i,0≤x i} F.q := by
  have hh := ((F.nestData G η hη).quadratic_nested_optimal_near DG hDG c).self_of_nhds
  have ho := hh.2.2
  rw [DemandNests.Data.quadratic_nested_benchmark] at ho
  exact ho

theorem nested_candidate_benchmark (C : F.Candidate) (s0 c : ℝ) (hs : 0<s0) :
    (F.nestedModel G η hη DG hD C).BenchmarkEquilibrium
      ((F.nestData G η hη).nestedUtility DG c) (F.commonEndowment s0) s0 := by
  let E := F.nestedModel G η hη DG hD C
  have he : E.endowment s0=F.commonEndowment s0 := F.nestedModel_common_endowment G η hη DG hD C s0
  rw [←he]
  have hn := E.numeraire_production_certificate (fun j => (F.ha0 j).le) (u := 0)
    (by rw [E.currentPrice_zero]; exact F.hw) hs.le
  simp only [E.currentPrice_zero] at hn
  refine ⟨F.hq,hs,?_,?_,?_,hn.1,hn.2.2.2,hn.2.2.1,rfl,E.benchmark_budget s0,?_⟩
  · intro i
    exact (E.benchmark_production_certificate F.hsigma i (F.hq i).le).1
  · intro i
    exact (E.benchmark_production_certificate F.hsigma i (F.hq i).le).2.2.2.2
  · intro i
    exact (E.benchmark_production_certificate F.hsigma i (F.hq i).le).2.2.2.1
  · intro r hr z _ hb
    have ho := F.nested_benchmark_surplus G η hη DG hDG c hr
    change (F.nestData G η hη).nestedUtility DG c r-dotProduct F.p r ≤
      (F.nestData G η hη).nestedUtility DG c F.q-dotProduct F.p F.q at ho
    have hbudget := E.benchmark_budget s0
    change dotProduct F.p F.q+s0=dotProduct F.frame.w (E.endowment s0) at hbudget
    change dotProduct F.p r+z≤dotProduct F.frame.w (E.endowment s0) at hb
    change (F.nestData G η hη).nestedUtility DG c r+z≤(F.nestData G η hη).nestedUtility DG c F.q+s0
    linarith

theorem nested_candidate_welfare_expansion (hn : 0<n) (C : F.Candidate) (s0 c : ℝ) (hs : 0<s0) :
    let E := F.nestedModel G η hη DG hD C
    ∃u : ℝ → Vec k,∃s : ℝ → ℝ,E.PositiveLocalPath s0 u s ∧
      E.WelfareNeighborhood s0 ((F.nestData G η hη).nestedUtility DG c) u s ∧
      HasDerivAt (fun t => E.quantities (t,u t)) E.qSolution 0 ∧
      E.WelfareExpansion ((F.nestData G η hη).nestedUtility DG c) u s := by
  exact (F.nestedModel G η hη DG hD C).economic_welfare_expansion
    (F.nestedModel_demandC1 G η hη DG hD C) F.parents F.report C.property.2 F.hq
    (F.candidate_total_positive (F.total_positive_of_goods hn) C) F.hD F.hsigma s0 hs
    _ (F.nestedModel_utility_compatible G η hη DG hD C hDG c)

end CommodityClassification.Equilibrium.BenchmarkFamily
