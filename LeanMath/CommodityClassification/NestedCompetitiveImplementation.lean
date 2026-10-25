module

public import LeanMath.CommodityClassification.NestedBenchmarkWelfare
public import LeanMath.CommodityClassification.SurplusCompetitivePath

/-! Actual nested preferences, firms, rebate and welfare along the same GE path. -/
@[expose] public section
noncomputable section
set_option maxHeartbeats 1200000
namespace CommodityClassification.Equilibrium.BenchmarkFamily
open Matrix InputCoordinates Filter
open scoped Topology
variable {n k h g : ℕ} (F : BenchmarkFamily n k h)
  (G : Partition n g) (η : Vec g) (hη : ∀a,0<η a)
  (DG : Mat g g) (hD : F.D=(F.nestData G η hη).demandMatrix DG)

def NestedImplementation (C : F.Candidate) (s0 c : ℝ) : Prop :=
  let E := F.nestedModel G η hη DG hD C
  let utility := (F.nestData G η hη).nestedUtility DG c
  E.BenchmarkEquilibrium utility (F.commonEndowment s0) s0 ∧
    ∃u : ℝ → Vec k,∃s : ℝ → ℝ,E.PositiveLocalPath s0 u s ∧
      E.WelfareNeighborhood s0 utility u s ∧
      HasDerivAt (fun t => E.quantities (t,u t)) E.qSolution 0 ∧
      E.WelfareExpansion utility u s ∧
      ∃I : Set ℝ,IsOpen I ∧ 0∈I ∧ ∀t∈I,
        E.CompetitiveState utility {x | ∀i,0≤x i} (F.commonEndowment s0) (t,u t) (s t)

theorem nested_candidate_implementation (hDG : DG.PosDef) (hn : 0<n)
    (C : F.Candidate) (s0 c : ℝ) (hs : 0<s0) :
    F.NestedImplementation G η hη DG hD C s0 c := by
  let E := F.nestedModel G η hη DG hD C
  let d := F.nestData G η hη
  obtain ⟨u,s,hp,hw,hq,hexp⟩ := F.nested_candidate_welfare_expansion G η hη DG hDG hD hn C s0 c hs
  have ho : ∀ᶠr in 𝓝 E.p,E.demand r∈{x | ∀i,0≤x i} ∧ ∀x∈{x | ∀i,0≤x i},
      d.nestedUtility DG c x-dotProduct r x≤
        d.nestedUtility DG c (E.demand r)-dotProduct r (E.demand r) := by
    filter_upwards [d.quadratic_nested_optimal_near DG hDG c] with r hr
    exact ⟨fun i => (hr.2.1 i).le,fun x hx => hr.2.2 hx⟩
  have hc := E.positive_path_competitive_of_surplus F.hsigma (fun j => (F.ha0 j).le)
    (d.nestedUtility DG c) {x | ∀i,0≤x i} s0 u s hp ho
  rw [F.nestedModel_common_endowment G η hη DG hD C s0] at hc
  exact ⟨F.nested_candidate_benchmark G η hη DG hDG hD C s0 c hs,u,s,hp,hw,hq,hexp,hc⟩

end CommodityClassification.Equilibrium.BenchmarkFamily
