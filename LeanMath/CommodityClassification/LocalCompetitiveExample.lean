module
public import LeanMath.CommodityClassification.LocalCompetitiveImplementation
public import LeanMath.CommodityClassification.WelfareBridgeExample
@[expose] public section
namespace CommodityClassification.Equilibrium.Example
open Matrix Filter Asymptotics Supply.Example
open scoped Topology

theorem concrete_competitive_implementation :
    ∃u : ℝ → Vec 1,∃s : ℝ → ℝ,model.PositiveLocalPath 1 u s ∧
      (∃I : Set ℝ,IsOpen I ∧ 0∈I ∧ ∀t∈I,
        model.CompetitiveState utility Set.univ ![3/2,3/2] (t,u t) (s t)) ∧
      HasDerivAt u ![-1/4] 0 ∧ HasDerivAt s 1 0 ∧
      HasDerivAt (fun t => model.quantities (t,u t)) ![-7/8,-1/8] 0 ∧
      (fun t => model.welfare utility u s 0-model.welfare utility u s t-(7/16 : ℝ)*t^2)
        =o[𝓝 (0 : ℝ)] (fun t : ℝ => t^2) := by
  have ha : ∀j,0≤model.frame.a0 j := by
    intro j; fin_cases j <;> norm_num [model,Model.ofAffine,frame]
  have hh := model.quadratic_competitive_implementation model_demandC1 parent 0 model_report
    ones_pos model_total_pos Matrix.PosDef.one (by norm_num [model,Model.ofAffine]) ha
    1 (by norm_num) rfl utility 0 Set.univ (by simp) (by intro r _; simp only [utility,zero_add]; rfl)
  obtain ⟨u,s,hpath,hcomp,hu,hs,hq,hw⟩ := hh
  have he : model.endowment 1 = ![3/2,3/2] :=
    (family.candidate_endowment (familyPath (1/2) (by norm_num) (by norm_num)) 1).trans family_endowment
  rw [he] at hcomp
  refine ⟨u,s,hpath,hcomp,?_,?_,?_,?_⟩
  · simpa only [concrete_solution.2.1] using hu
  · simpa only [concrete_solution.2.2] using hs
  · simpa only [concrete_solution.1] using hq
  · unfold Model.WelfareExpansion at hw
    rw [concrete_lossCoefficient] at hw
    convert hw using 1
    funext t
    ring

end CommodityClassification.Equilibrium.Example
