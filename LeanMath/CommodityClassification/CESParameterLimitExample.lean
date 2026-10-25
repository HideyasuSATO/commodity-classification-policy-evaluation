module
public import LeanMath.CommodityClassification.CostParameterLimitConnection
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.NormNum
@[expose] public section
namespace CommodityClassification.CESCost.ParameterLimitExample
open Matrix Filter
open scoped BigOperators Topology

noncomputable def data : Data 2 where
  p := 5
  w0 := ![1,2]
  a := ![1,2]
  p_pos := by norm_num
  w0_pos := by intro j; fin_cases j <;> norm_num
  a_pos := by intro j; fin_cases j <;> norm_num
  cost_identity := by norm_num [dotProduct,Fin.sum_univ_succ]

def currentPrices : Vec 2 := ![2,2]

theorem currentPrices_positive : currentPrices ∈ PositivePrices 2 := by
  intro j; fin_cases j <;> norm_num [currentPrices]

theorem currentPrices_ne_benchmark : currentPrices ≠ data.w0 := by
  intro h
  have hh := congrFun h 0
  norm_num [currentPrices,data] at hh

theorem cobb_value : data.cobb currentPrices = 5 * Real.exp (Real.log 2 / 5) := by
  unfold Data.cobb Data.logSum
  norm_num [data,currentPrices,Data.share,Data.ratio,Fin.sum_univ_succ,div_eq_mul_inv,mul_comm]

theorem raw_ces_one_value : data.ces 1 currentPrices = 5 := data.ces_at_one currentPrices

theorem cobb_gt_raw_at_one : data.ces 1 currentPrices < data.cobb currentPrices := by
  rw [raw_ces_one_value,cobb_value]
  have he : 1 < Real.exp (Real.log 2 / 5) :=
    Real.one_lt_exp_iff.mpr (div_pos (Real.log_pos (by norm_num)) (by norm_num))
  linarith

theorem off_benchmark_limit :
    Tendsto (fun σ => data.ces σ currentPrices) (𝓝[≠] (1:ℝ))
      (𝓝 (5 * Real.exp (Real.log 2 / 5))) := by
  rw [← cobb_value]
  exact data.ces_tendsto_cobb currentPrices_positive

theorem filled_cost_continuous : ContinuousAt (fun σ => data.cost σ currentPrices) 1 :=
  data.cost_parameter_continuousAt_one currentPrices_positive

end CommodityClassification.CESCost.ParameterLimitExample
