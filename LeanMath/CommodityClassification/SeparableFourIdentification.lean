module

public import LeanMath.CommodityClassification.SeparableFourMoments

/-! Failure when elasticities differ, full-domain success when they match. -/
@[expose] public section
noncomputable section
set_option maxHeartbeats 2400000
namespace CommodityClassification.SeparableFour
open Matrix InputCoordinates

theorem mismatched_coefficients (η : ℝ) (hη : 0<η) (hη1 : η≠1) (a t : ℝ)
    (ha : |a|<1/4) (ht : |t|<1/4) (ha0 : a≠0) (ht0 : t≠0) :
    (family η hη).coefficient (coordinates a 0)≠
      (family η hη).coefficient (coordinates a t) := by
  rw [coefficient_formula,coefficient_formula]
  intro he
  have hk0 := ne_of_gt (moment_K_positive η hη a 0 ha (by norm_num))
  have hkt := ne_of_gt (moment_K_positive η hη a t ha ht)
  have hn : (-η*a/2)^2≠0 := pow_ne_zero _
    (div_ne_zero (mul_ne_zero (neg_ne_zero.mpr (ne_of_gt hη)) ha0) (by norm_num))
  have hratio := sub_right_inj.mp he
  have heK := mul_left_cancel₀ hn ((div_eq_div_iff hk0 hkt).mp hratio)
  have hnonzero : (η-1)*t^2≠0 := mul_ne_zero (sub_ne_zero.mpr hη1) (pow_ne_zero _ ht0)
  apply hnonzero
  nlinarith [heK]

theorem mismatched_equilibrium_pair (η : ℝ) (hη : 0<η) (hη1 : η≠1)
    (a t s0 c : ℝ) (ha : |a|<1/4) (ht : |t|<1/4)
    (ha0 : a≠0) (ht0 : t≠0) (hs : 0<s0) :
    ∃C E : (family η hη).Candidate,
      fine.report quantities C.val=fine.report quantities E.val ∧
      ((family η hη).model C).lossCoefficient≠((family η hη).model E).lossCoefficient ∧
      ((family η hη).model C).BenchmarkEquilibrium ((family η hη).commonUtility c)
        ((family η hη).commonEndowment s0) s0 ∧
      ((family η hη).model E).BenchmarkEquilibrium ((family η hη).commonUtility c)
        ((family η hη).commonEndowment s0) s0 := by
  let C := candidate η hη a 0 ha (by norm_num)
  let E := candidate η hη a t ha ht
  refine ⟨C,E,?_,?_,(family η hη).every_candidate_equilibrium hs c C,
    (family η hη).every_candidate_equilibrium hs c E⟩
  · change fine.report quantities (coordinates a 0)=fine.report quantities (coordinates a t)
    rw [fine_report,fine_report]
  · rw [(family η hη).candidate_lossCoefficient C,(family η hη).candidate_lossCoefficient E]
    exact mismatched_coefficients η hη hη1 a t ha ht ha0 ht0

theorem mismatched_not_identified (η : ℝ) (hη : 0<η) (hη1 : η≠1) :
    ¬(family η hη).ReportIdentified fine := by
  intro hi
  obtain ⟨C,E,hr,hw,_,_⟩ := mismatched_equilibrium_pair η hη hη1 (1/8) (1/8) 1 0
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  apply hw
  rw [(family η hη).candidate_lossCoefficient C,(family η hη).candidate_lossCoefficient E]
  exact hi E C.val ⟨C.property,hr⟩

theorem matching_m_report (C : Mat 4 1) :
    C.transpose *ᵥ (demand 1 *ᵥ policy)=
      fun j => fine.report quantities C 0 j+2*fine.report quantities C 1 j := by
  ext j; fin_cases j
  change (∑l : Fin 4,C l 0*(demand 1 *ᵥ policy) l)=
    (∑l : Fin 4,(if fine.group l=0 then quantities l else 0)*C l 0)+
      2*(∑l : Fin 4,(if fine.group l=1 then quantities l else 0)*C l 0)
  norm_num [demand,Matrix.mulVec_diagonal,policy,fine,quantities,Fin.sum_univ_succ]
  ring

theorem matching_K_constant (C : Mat 4 1) :
    Regularity.K prices quantities (demand 1) (family 1 (by norm_num)).fixedR 1 C=
      (family 1 (by norm_num)).fixedR := by
  have hL : Regularity.adjustedDemand prices quantities (demand 1) 1=0 := by
    rw [Regularity.adjustedDemand,demand_xi]
    simp
  rw [Regularity.K,hL]
  simp

theorem matching_preserves_moments : (family 1 (by norm_num)).ReportMomentsPreserved fine := by
  intro C E he
  constructor
  · change C.val.transpose *ᵥ (demand 1 *ᵥ policy)=E.val.transpose *ᵥ (demand 1 *ᵥ policy)
    rw [matching_m_report,matching_m_report]
    change fine.report quantities C.val=fine.report quantities E.val at he
    rw [he]
  · rw [(family 1 (by norm_num)).candidate_K_answer C (coordinates 0 0) (0 : Mat 4 0),
      (family 1 (by norm_num)).candidate_K_answer E (coordinates 0 0) (0 : Mat 4 0)]
    change Regularity.K prices quantities (demand 1) (family 1 (by norm_num)).fixedR 1 C.val=
      Regularity.K prices quantities (demand 1) (family 1 (by norm_num)).fixedR 1 E.val
    rw [matching_K_constant,matching_K_constant]

theorem matching_identifies_all_answers : (family 1 (by norm_num)).ReportIdentified fine :=
  (family 1 (by norm_num)).report_moments_identifies fine matching_preserves_moments

end CommodityClassification.SeparableFour
