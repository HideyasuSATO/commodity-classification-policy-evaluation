module

public import LeanMath.CommodityClassification.UntaxedNestClassification

/-! Printed positive pair in the original nested competitive economy. -/
@[expose] public section
noncomputable section
set_option maxHeartbeats 1500000
namespace CommodityClassification.UntaxedNest
open Matrix InputCoordinates

theorem family_demand_eq : family.D=(family.nestData nests eta eta_pos).demandMatrix outerD :=
  demand_eq_nested

theorem common_endowment_formula (s0 : ℝ) : family.commonEndowment s0=![1/2+s0/2,1/2+s0/2] := by
  change (Supply.Example.frame.reconstruct prices (coordinates 0)).transpose *ᵥ quantities+
    s0 • Supply.Example.frame.a0=_
  rw [reconstruct_inputs]
  ext j;fin_cases j <;>
    norm_num [Matrix.add_apply,Pi.add_apply,Pi.smul_apply,smul_eq_mul,Matrix.mulVec,
      Matrix.transpose_apply,dotProduct,inputs,coordinates,quantities,Supply.Example.frame,Fin.sum_univ_succ] <;> ring

theorem candidate_original_nested_implementation (t : ℝ) (ht : |t|≤1/4) (s0 c : ℝ) (hs : 0<s0) :
    family.NestedImplementation nests eta eta_pos outerD family_demand_eq (candidate t ht) s0 c :=
  family.nested_candidate_implementation nests eta eta_pos outerD family_demand_eq
    outerD_posDef (by norm_num) (candidate t ht) s0 c hs

theorem printed_original_nested_pair (s0 c : ℝ) (hs : 0<s0) :
    family.NestedSameObservationWitness nests eta eta_pos outerD family_demand_eq nests
      (candidate (1/4) (by norm_num)) (candidate 0 (by norm_num)) s0 c := by
  let C := candidate (1/4) (by norm_num)
  let E := candidate 0 (by norm_num)
  have hr : nests.report quantities C.val=nests.report quantities E.val := by
    change nests.report quantities (coordinates (1/4))=nests.report quantities (coordinates 0)
    rw [nest_report,nest_report]
  refine ⟨hr,?_,?_,candidate_original_nested_implementation _ _ s0 c hs,
    candidate_original_nested_implementation _ _ s0 c hs⟩
  · change nests.report quantities (Supply.Example.frame.reconstruct prices C.val)=
      nests.report quantities (Supply.Example.frame.reconstruct prices E.val)
    rw [nests.report_reconstruct,nests.report_reconstruct,hr]
  · rw [family.nestedModel_lossCoefficient,family.nestedModel_lossCoefficient]
    change family.coefficient (coordinates (1/4))≠family.coefficient (coordinates 0)
    rw [printed_coefficients.1,printed_coefficients.2.1]
    norm_num

theorem printed_original_coefficient_difference :
    (family.nestedModel nests eta eta_pos outerD family_demand_eq (candidate (1/4) (by norm_num))).lossCoefficient-
      (family.nestedModel nests eta eta_pos outerD family_demand_eq (candidate 0 (by norm_num))).lossCoefficient=1/2112 := by
  rw [family.nestedModel_lossCoefficient,family.nestedModel_lossCoefficient]
  exact printed_coefficients.2.2

end CommodityClassification.UntaxedNest
