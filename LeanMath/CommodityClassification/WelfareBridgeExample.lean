module
public import LeanMath.CommodityClassification.EconomicFixedAnswerCriterion
public import LeanMath.CommodityClassification.CommonBenchmarkExample
@[expose] public section
namespace CommodityClassification.Equilibrium.Example
open Matrix Supply.Example
open scoped BigOperators

theorem bridge_coefficient_half : family.coefficient (path (1/2))=7/8 := by
  calc
    family.coefficient (path (1/2)) = model.lossCoefficient :=
      (family.candidate_lossCoefficient (familyPath (1/2) (by norm_num) (by norm_num))).symm
    _ = 7/8 := concrete_lossCoefficient

theorem bridge_coefficient_one : family.coefficient (path 1)=1 := by
  have hp : path 1=0 := by rw [path_exposure]; ext i j; fin_cases i <;> fin_cases j <;> norm_num
  rw [hp]
  norm_num [BenchmarkFamily.coefficient,family,dotProduct,ones,Fin.sum_univ_succ]

theorem bridge_distinct_welfare_same_report :
    parent.report ones (path (1/2))=parent.report ones (path 1) ∧
    family.coefficient (path (1/2))≠family.coefficient (path 1) := by
  rw [path_report,path_report,bridge_coefficient_half,bridge_coefficient_one]
  norm_num

theorem bridge_parent_not_identified :
    ¬family.IdentifiedAt parent (familyPath (1/2) (by norm_num) (by norm_num)) := by
  intro hh
  have hmem : path 1 ∈ frame.FixedFiber ones ones parent 0 parent (path (1/2)) :=
    ⟨path_mem (by norm_num) (by norm_num),by rw [path_report,path_report]⟩
  have he := hh (path 1) hmem
  change family.coefficient (path 1)=family.coefficient (path (1/2)) at he
  rw [bridge_coefficient_half,bridge_coefficient_one] at he
  norm_num at he

end CommodityClassification.Equilibrium.Example
