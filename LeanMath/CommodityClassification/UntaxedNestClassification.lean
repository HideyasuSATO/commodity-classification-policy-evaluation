module

public import LeanMath.CommodityClassification.UntaxedNestInformation

/-! The successful three-cell report splits the untaxed nest. -/
@[expose] public section
noncomputable section
set_option maxHeartbeats 1500000
namespace CommodityClassification.UntaxedNest
open Matrix InputCoordinates

def splitUntaxed : Partition 4 3 where
  group := ![0,0,1,2]
  onto := by intro a;fin_cases a;exact ⟨0,rfl⟩;exact ⟨2,rfl⟩;exact ⟨3,rfl⟩

def splitTaxed : Partition 4 3 where
  group := ![0,1,2,2]
  onto := by intro a;fin_cases a;exact ⟨0,rfl⟩;exact ⟨1,rfl⟩;exact ⟨2,rfl⟩

def nests_parent : Refinement nests parent where
  parent := fun _ => 0
  compatible := by intro i;rfl

def splitUntaxed_nests : Refinement splitUntaxed nests where
  parent := ![0,1,1]
  compatible := by intro i;fin_cases i <;> rfl

def splitTaxed_nests : Refinement splitTaxed nests where
  parent := ![0,0,1]
  compatible := by intro i;fin_cases i <;> rfl

theorem parent_not_identified : ¬family.ParentIdentified := by
  intro hi
  have hh := hi (candidate (1/4) (by norm_num))
  change family.coefficient (coordinates (1/4))=family.coefficient (coordinates 0) at hh
  rw [printed_coefficients.1,printed_coefficients.2.1] at hh
  norm_num at hh

theorem split_untaxed_identifies_all_answers : family.ReportIdentified splitUntaxed := by
  apply (family.nested_report_identification_iff nests eta eta_pos outerD beta demand_eq_nested
    policy_eq_nested nests_parent splitUntaxed splitUntaxed_nests parent_not_identified).mpr
  intro i j hne hij
  fin_cases i <;> fin_cases j <;>
    norm_num [splitUntaxed,nests,SeparableFour.fine,eta,family] at *

theorem split_taxed_not_identifies_all_answers : ¬family.ReportIdentified splitTaxed := by
  intro hi
  have hh := (family.nested_report_identification_iff nests eta eta_pos outerD beta demand_eq_nested
    policy_eq_nested nests_parent splitTaxed splitTaxed_nests parent_not_identified).mp hi
  have hc := hh 2 3 (by decide) rfl
  norm_num [eta,nests,SeparableFour.fine,family] at hc

end CommodityClassification.UntaxedNest
