module

public import LeanMath.CommodityClassification.ResourceCancellationIdentification

/-! Actual group responses and their variation across hidden supply structures. -/
@[expose] public section
noncomputable section
set_option maxHeartbeats 2400000
namespace CommodityClassification.ResourceCancellation
open Matrix InputCoordinates

def responseFormula (x z : ℝ) : Vec 2 :=
  ![-229/100+(16*x/5+z/5)*((24*x/25)/(3+18*x^2/5)),
    -133/200+(-16*x/5+z/10)*((24*x/25)/(3+18*x^2/5))]

theorem all_candidate_responseY (C : family.Candidate) (x z : ℝ)
    (hc : C.val=coordinates x z) :
    family.responseY C=![(24*x/25)/(3+18*x^2/5)] := by
  unfold Equilibrium.BenchmarkFamily.responseY
  rw [all_candidate_m C x z hc,all_candidate_K C x z hc]
  have hh := congrArg (fun M : Mat 1 1 => M *ᵥ (![24*x/25] : Vec 1))
    (scalar_inverse (3+18*x^2/5))
  refine hh.trans ?_
  ext i; fin_cases i
  simp [Matrix.mulVec,dotProduct,div_eq_mul_inv]
  ring

theorem all_candidate_group_response (C : family.Candidate) (x z : ℝ)
    (hc : C.val=coordinates x z) :
    family.groupQuantityResponse fine C=responseFormula x z := by
  rw [family.groupQuantityResponse_formula,all_candidate_responseY C x z hc,hc]
  change -(fine.valueAggregation e *ᵥ (demand *ᵥ policy))+
    (fine.valueAggregation e*demand*coordinates x z) *ᵥ ![(24*x/25)/(3+18*x^2/5)]=_
  rw [demand_policy,demand_entries]
  ext i
  fin_cases i <;>
    norm_num [responseFormula,Partition.valueAggregation,Partition.Q,fine,e,coordinates,visible,hidden,
      Matrix.mulVec,Matrix.mul_apply,transpose_apply,dotProduct,Fin.sum_univ_succ] <;> ring_nf <;> simp

theorem response_formula_difference (x z t : ℝ) :
    responseFormula x z-responseFormula x t=
      ((z-t)*((24*x/25)/(3+18*x^2/5))) • (![1/5,1/10] : Vec 2) := by
  ext i
  fin_cases i <;> simp [responseFormula] <;> ring

theorem response_formula_derivative (x z : ℝ) :
    HasDerivAt (responseFormula x)
      (((24*x/25)/(3+18*x^2/5)) • (![1/5,1/10] : Vec 2)) z := by
  have hf : responseFormula x = fun t => responseFormula x 0+
      t • (((24*x/25)/(3+18*x^2/5)) • (![1/5,1/10] : Vec 2)) := by
    funext t i
    fin_cases i <;> simp [responseFormula] <;> ring
  rw [hf]
  convert
    ((hasDerivAt_id z).smul_const (((24*x/25)/(3+18*x^2/5)) •
      (![1/5,1/10] : Vec 2))).const_add (responseFormula x 0) using 1 <;> simp

theorem response_formula_ne (x z t : ℝ) (hx : x≠0) (hz : z≠t) :
    responseFormula x z≠responseFormula x t := by
  intro he
  have hd := response_formula_difference x z t
  rw [he,sub_self] at hd
  have h0 := congrFun hd 0
  have hk : 3+18*x^2/5≠0 := ne_of_gt (moment_K_positive x)
  have hy : (24*x/25)/(3+18*x^2/5)≠0 := div_ne_zero (by exact div_ne_zero (mul_ne_zero (by norm_num) hx) (by norm_num)) hk
  have hn : (z-t)*((24*x/25)/(3+18*x^2/5))*(1/5)≠0 :=
    mul_ne_zero (mul_ne_zero (sub_ne_zero.mpr hz) hy) (by norm_num)
  exact hn (by simpa [smul_eq_mul] using h0.symm)

theorem group_quantity_counterexample :
    ∃C E : family.Candidate,
      fine.report family.q C.val=fine.report family.q E.val ∧
      family.coefficient C.val=family.coefficient E.val ∧
      family.groupQuantityResponse fine C≠family.groupQuantityResponse fine E := by
  let C := candidate (1/8) 0 (by norm_num) (by norm_num)
  let E := candidate (1/8) (1/8) (by norm_num) (by norm_num)
  refine ⟨C,E,?_,?_,?_⟩
  · exact (fine_report_iff _ _ _ _).mpr rfl
  · change family.coefficient (coordinates (1/8) 0)=family.coefficient (coordinates (1/8) (1/8))
    rw [coefficient_formula,coefficient_formula]
  · rw [all_candidate_group_response C (1/8) 0 rfl,
      all_candidate_group_response E (1/8) (1/8) rfl]
    exact response_formula_ne _ _ _ (by norm_num) (by norm_num)

theorem fine_does_not_identify_quantities : ¬family.GroupQuantitiesIdentified fine := by
  intro h
  obtain ⟨C,E,he,_,hne⟩ := group_quantity_counterexample
  exact hne (h C E he)

end CommodityClassification.ResourceCancellation
