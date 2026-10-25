module
public import LeanMath.CommodityClassification.CESCostDefinitions
public import Mathlib.Analysis.Calculus.Deriv.Slope
@[expose] public section
set_option maxHeartbeats 1200000
namespace CommodityClassification.CESCost
open Matrix Filter
open scoped BigOperators Topology
variable {f : ℕ}

noncomputable def Data.parameterSum (d : Data f) (w : Vec f) (t : ℝ) : ℝ :=
  ∑ j, d.share j * Real.exp (Real.log (d.ratio w j) * t)

theorem Data.factor_nonempty (d : Data f) : 0 < f := by
  by_contra hf
  have hf0 : f=0 := Nat.eq_zero_of_not_pos hf
  subst f
  have hh := d.share_sum
  simp at hh

theorem Data.parameterSum_zero (d : Data f) (w : Vec f) : d.parameterSum w 0 = 1 := by
  simp [Data.parameterSum,d.share_sum]

theorem Data.powerSum_eq_parameterSum (d : Data f) {w : Vec f}
    (hw : w ∈ PositivePrices f) (σ : ℝ) : d.powerSum σ w = d.parameterSum w (1-σ) := by
  unfold Data.powerSum Data.parameterSum
  apply Finset.sum_congr rfl
  intro j hj
  rw [Real.rpow_def_of_pos (d.ratio_pos hw j)]

theorem Data.parameterSum_pos (d : Data f) {w : Vec f}
    (hw : w ∈ PositivePrices f) (t : ℝ) : 0 < d.parameterSum w t := by
  have hh := d.powerSum_pos (1-t) hw
  simpa [d.powerSum_eq_parameterSum hw] using hh

theorem Data.hasDerivAt_parameterSum_zero (d : Data f) (w : Vec f) :
    HasDerivAt (d.parameterSum w) (d.logSum w) 0 := by
  have h (j : Fin f) := (((hasDerivAt_id (0:ℝ)).const_mul
    (Real.log (d.ratio w j))).exp).const_mul (d.share j)
  convert! HasDerivAt.fun_sum (u := Finset.univ) (fun j _ => h j) using 1
  simp [Data.logSum]

theorem Data.hasDerivAt_log_parameterSum_zero (d : Data f) (w : Vec f) :
    HasDerivAt (fun t => Real.log (d.parameterSum w t)) (d.logSum w) 0 := by
  simpa [d.parameterSum_zero] using
    (d.hasDerivAt_parameterSum_zero w).log (by rw [d.parameterSum_zero]; norm_num)

theorem Data.tendsto_log_parameter_quotient (d : Data f) (w : Vec f) :
    Tendsto (fun t => Real.log (d.parameterSum w t)/t) (𝓝[≠] (0:ℝ)) (𝓝 (d.logSum w)) := by
  simpa [d.parameterSum_zero,smul_eq_mul,div_eq_mul_inv,mul_comm] using
    (d.hasDerivAt_log_parameterSum_zero w).tendsto_slope_zero

theorem Data.ces_eq_parameter_exp (d : Data f) {w : Vec f}
    (hw : w ∈ PositivePrices f) (σ : ℝ) :
    d.ces σ w = d.p * Real.exp (Real.log (d.parameterSum w (1-σ))/(1-σ)) := by
  rw [Data.ces,Real.rpow_def_of_pos (d.powerSum_pos σ hw),d.powerSum_eq_parameterSum hw]
  congr 2
  ring

theorem one_sub_tendsto_punctured :
    Tendsto (fun σ : ℝ => 1-σ) (𝓝[≠] (1:ℝ)) (𝓝[≠] (0:ℝ)) := by
  apply tendsto_nhdsWithin_iff.mpr
  refine ⟨?_,?_⟩
  · simpa using (tendsto_const_nhds.sub (tendsto_id.mono_left nhdsWithin_le_nhds) :
      Tendsto (fun σ : ℝ => 1-σ) (𝓝[≠] (1:ℝ)) (𝓝 (1-1)))
  · filter_upwards [self_mem_nhdsWithin] with σ hσ
    simpa only [Set.mem_compl_iff,Set.mem_singleton_iff,sub_ne_zero] using Ne.symm hσ

theorem Data.ces_tendsto_cobb (d : Data f) {w : Vec f} (hw : w ∈ PositivePrices f) :
    Tendsto (fun σ => d.ces σ w) (𝓝[≠] (1:ℝ)) (𝓝 (d.cobb w)) := by
  have hh := ((d.tendsto_log_parameter_quotient w).comp one_sub_tendsto_punctured).rexp.const_mul d.p
  simpa only [Function.comp_def,← d.ces_eq_parameter_exp hw,Data.cobb] using hh

theorem Data.ces_at_one (d : Data f) (w : Vec f) : d.ces 1 w = d.p := by
  simp [Data.ces]

theorem Data.cost_parameter_continuousAt_one (d : Data f) {w : Vec f}
    (hw : w ∈ PositivePrices f) : ContinuousAt (fun σ => d.cost σ w) 1 := by
  apply continuousAt_iff_punctured_nhds.mpr
  have hh := d.ces_tendsto_cobb hw
  have heq : (fun σ => d.ces σ w) =ᶠ[𝓝[≠] (1:ℝ)] (fun σ => d.cost σ w) := by
    filter_upwards [self_mem_nhdsWithin] with σ hσ
    have hne : σ≠1 := hσ
    simp [Data.cost,hne]
  simpa [Data.cost] using hh.congr' heq

theorem Data.cost_tendsto_cobb (d : Data f) {w : Vec f} (hw : w ∈ PositivePrices f) :
    Tendsto (fun σ => d.cost σ w) (𝓝 (1:ℝ)) (𝓝 (d.cobb w)) := by
  simpa [Data.cost] using (d.cost_parameter_continuousAt_one hw).tendsto

theorem Data.cobb_eq_product (d : Data f) {w : Vec f} (hw : w ∈ PositivePrices f) :
    d.cobb w = d.p * ∏ j, (d.ratio w j) ^ (d.share j) := by
  rw [Data.cobb,Data.logSum,Real.exp_sum]
  congr 1
  apply Finset.prod_congr rfl
  intro j hj
  rw [Real.rpow_def_of_pos (d.ratio_pos hw j),mul_comm]

end CommodityClassification.CESCost
