module
import LeanMath.CommodityClassification.CostInputConnection
import LeanMath.CommodityClassification.CheckInputCoordinatesAndReports
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum

open CommodityClassification.CESCost Matrix
open scoped BigOperators
namespace CommodityClassification.CESCost.Audit

noncomputable def asymmetricData : Data 2 where
  p := 5
  w0 := ![1,2]
  a := ![1,2]
  p_pos := by norm_num
  w0_pos := by intro j; fin_cases j <;> norm_num
  a_pos := by intro j; fin_cases j <;> norm_num
  cost_identity := by norm_num [dotProduct, Fin.sum_univ_succ]

example : asymmetricData.share 0 = 1/5 ∧ asymmetricData.share 1 = 4/5 := by
  norm_num [Data.share, asymmetricData]

example (σ : ℝ) : asymmetricData.hessian σ =
    ![![-4*σ/5, 2*σ/5], ![2*σ/5, -σ/5]] := by
  ext j l
  fin_cases j <;> fin_cases l <;> norm_num [Data.hessian, asymmetricData] <;> ring

example : HasFDerivAt (asymmetricData.cost 1) (weightedLinear asymmetricData.a)
    asymmetricData.w0 := asymmetricData.hasFDerivAt_cost_benchmark 1

example (u v : Vec 2) :
    fderiv ℝ (fun w => fderiv ℝ (asymmetricData.cost 2) w v) asymmetricData.w0 u =
      2*(dotProduct asymmetricData.a u*dotProduct asymmetricData.a v/5 -
        ∑ j, (asymmetricData.a j/asymmetricData.w0 j)*u j*v j) :=
  asymmetricData.cost_second_derivative 2 u v

example : ¬ Nonempty (Data 0) := by
  rintro ⟨d⟩
  have hh := d.cost_identity
  simp [dotProduct] at hh
  linarith [d.p_pos]

end CommodityClassification.CESCost.Audit
set_option pp.universes false

#check @CommodityClassification.CESCost.positivePrices_open
#print axioms CommodityClassification.CESCost.positivePrices_open

#check @CommodityClassification.CESCost.Data.benchmark_mem
#print axioms CommodityClassification.CESCost.Data.benchmark_mem

#check @CommodityClassification.CESCost.Data.share_pos
#print axioms CommodityClassification.CESCost.Data.share_pos

#check @CommodityClassification.CESCost.Data.share_sum
#print axioms CommodityClassification.CESCost.Data.share_sum

#check @CommodityClassification.CESCost.Data.share_over_w0
#print axioms CommodityClassification.CESCost.Data.share_over_w0

#check @CommodityClassification.CESCost.Data.p_share_over_w0
#print axioms CommodityClassification.CESCost.Data.p_share_over_w0

#check @CommodityClassification.CESCost.Data.ratio_pos
#print axioms CommodityClassification.CESCost.Data.ratio_pos

#check @CommodityClassification.CESCost.Data.ratio_benchmark
#print axioms CommodityClassification.CESCost.Data.ratio_benchmark

#check @CommodityClassification.CESCost.weightedLinear_apply
#print axioms CommodityClassification.CESCost.weightedLinear_apply

#check @CommodityClassification.CESCost.weightedLinear_single
#print axioms CommodityClassification.CESCost.weightedLinear_single

#check @CommodityClassification.CESCost.Data.cost_eq_cobb
#print axioms CommodityClassification.CESCost.Data.cost_eq_cobb

#check @CommodityClassification.CESCost.Data.cost_eq_ces
#print axioms CommodityClassification.CESCost.Data.cost_eq_ces

#check @CommodityClassification.CESCost.Data.powerSum_pos
#print axioms CommodityClassification.CESCost.Data.powerSum_pos

#check @CommodityClassification.CESCost.Data.powerSum_benchmark
#print axioms CommodityClassification.CESCost.Data.powerSum_benchmark

#check @CommodityClassification.CESCost.Data.logSum_benchmark
#print axioms CommodityClassification.CESCost.Data.logSum_benchmark

#check @CommodityClassification.CESCost.Data.ces_benchmark
#print axioms CommodityClassification.CESCost.Data.ces_benchmark

#check @CommodityClassification.CESCost.Data.cobb_benchmark
#print axioms CommodityClassification.CESCost.Data.cobb_benchmark

#check @CommodityClassification.CESCost.Data.cost_benchmark
#print axioms CommodityClassification.CESCost.Data.cost_benchmark

#check @CommodityClassification.CESCost.Data.hasFDerivAt_ratio
#print axioms CommodityClassification.CESCost.Data.hasFDerivAt_ratio

#check @CommodityClassification.CESCost.Data.ratio_contDiffAt
#print axioms CommodityClassification.CESCost.Data.ratio_contDiffAt

#check @CommodityClassification.CESCost.Data.powerSum_contDiffAt
#print axioms CommodityClassification.CESCost.Data.powerSum_contDiffAt

#check @CommodityClassification.CESCost.Data.ces_contDiffAt
#print axioms CommodityClassification.CESCost.Data.ces_contDiffAt

#check @CommodityClassification.CESCost.Data.logSum_contDiffAt
#print axioms CommodityClassification.CESCost.Data.logSum_contDiffAt

#check @CommodityClassification.CESCost.Data.cobb_contDiffAt
#print axioms CommodityClassification.CESCost.Data.cobb_contDiffAt

#check @CommodityClassification.CESCost.Data.cost_contDiffAt
#print axioms CommodityClassification.CESCost.Data.cost_contDiffAt

#check @CommodityClassification.CESCost.Data.hasFDerivAt_powerSum
#print axioms CommodityClassification.CESCost.Data.hasFDerivAt_powerSum

#check @CommodityClassification.CESCost.Data.powerDeriv_benchmark
#print axioms CommodityClassification.CESCost.Data.powerDeriv_benchmark

#check @CommodityClassification.CESCost.Data.hasFDerivAt_ces
#print axioms CommodityClassification.CESCost.Data.hasFDerivAt_ces

#check @CommodityClassification.CESCost.Data.ces_partial
#print axioms CommodityClassification.CESCost.Data.ces_partial

#check @CommodityClassification.CESCost.Data.hasFDerivAt_ces_benchmark
#print axioms CommodityClassification.CESCost.Data.hasFDerivAt_ces_benchmark

#check @CommodityClassification.CESCost.Data.hasFDerivAt_cesGradient_benchmark
#print axioms CommodityClassification.CESCost.Data.hasFDerivAt_cesGradient_benchmark

#check @CommodityClassification.CESCost.Data.hasFDerivAt_ces_partial_benchmark
#print axioms CommodityClassification.CESCost.Data.hasFDerivAt_ces_partial_benchmark

#check @CommodityClassification.CESCost.Data.hasFDerivAt_logSum
#print axioms CommodityClassification.CESCost.Data.hasFDerivAt_logSum

#check @CommodityClassification.CESCost.Data.logDeriv_benchmark
#print axioms CommodityClassification.CESCost.Data.logDeriv_benchmark

#check @CommodityClassification.CESCost.Data.hasFDerivAt_cobb
#print axioms CommodityClassification.CESCost.Data.hasFDerivAt_cobb

#check @CommodityClassification.CESCost.Data.cobb_partial
#print axioms CommodityClassification.CESCost.Data.cobb_partial

#check @CommodityClassification.CESCost.Data.hasFDerivAt_cobb_benchmark
#print axioms CommodityClassification.CESCost.Data.hasFDerivAt_cobb_benchmark

#check @CommodityClassification.CESCost.Data.hasFDerivAt_cobbGradient_benchmark
#print axioms CommodityClassification.CESCost.Data.hasFDerivAt_cobbGradient_benchmark

#check @CommodityClassification.CESCost.Data.hasFDerivAt_cobb_partial_benchmark
#print axioms CommodityClassification.CESCost.Data.hasFDerivAt_cobb_partial_benchmark

#check @CommodityClassification.CESCost.Data.hasFDerivAt_cost_benchmark
#print axioms CommodityClassification.CESCost.Data.hasFDerivAt_cost_benchmark

#check @CommodityClassification.CESCost.Data.cost_first_derivative
#print axioms CommodityClassification.CESCost.Data.cost_first_derivative

#check @CommodityClassification.CESCost.Data.cost_gradient
#print axioms CommodityClassification.CESCost.Data.cost_gradient

#check @CommodityClassification.CESCost.Data.hasFDerivAt_cost_partial_benchmark
#print axioms CommodityClassification.CESCost.Data.hasFDerivAt_cost_partial_benchmark

#check @CommodityClassification.CESCost.Data.cost_mixed_derivative
#print axioms CommodityClassification.CESCost.Data.cost_mixed_derivative

#check @CommodityClassification.CESCost.Data.hessian_manuscript
#print axioms CommodityClassification.CESCost.Data.hessian_manuscript

#check @CommodityClassification.CESCost.clm_apply_eq_sum
#print axioms CommodityClassification.CESCost.clm_apply_eq_sum

#check @CommodityClassification.CESCost.fderiv_eq_sum_partials
#print axioms CommodityClassification.CESCost.fderiv_eq_sum_partials

#check @CommodityClassification.CESCost.Data.hasFDerivAt_cost_directional_benchmark
#print axioms CommodityClassification.CESCost.Data.hasFDerivAt_cost_directional_benchmark

#check @CommodityClassification.CESCost.Data.cost_second_derivative
#print axioms CommodityClassification.CESCost.Data.cost_second_derivative

#check @CommodityClassification.CESCost.Data.cost_second_derivative_symmetric
#print axioms CommodityClassification.CESCost.Data.cost_second_derivative_symmetric

#check @CommodityClassification.CESCost.input_cost_shares
#print axioms CommodityClassification.CESCost.input_cost_shares

#check @CommodityClassification.CESCost.input_cost_formulas
#print axioms CommodityClassification.CESCost.input_cost_formulas

#check @CommodityClassification.CESCost.coordinate_cost_inputs
#print axioms CommodityClassification.CESCost.coordinate_cost_inputs

#check @CommodityClassification.CESCost.coordinate_cost_shares
#print axioms CommodityClassification.CESCost.coordinate_cost_shares

#check @CommodityClassification.CESCost.coordinate_cost_formulas
#print axioms CommodityClassification.CESCost.coordinate_cost_formulas

#print axioms CommodityClassification.CESCost.Audit.asymmetricData
