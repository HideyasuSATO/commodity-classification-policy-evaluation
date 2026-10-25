module
public import LeanMath.CommodityClassification.CostDerivativeIntegration
@[expose] public section
set_option maxHeartbeats 1600000
namespace CommodityClassification.CESCost
open Matrix Filter
open scoped BigOperators Topology
variable {f : ℕ}

theorem Data.ratio_smul (d : Data f) (a : ℝ) (w : Vec f) (j : Fin f) :
    d.ratio (a • w) j = a * d.ratio w j := by
  simp only [Data.ratio, Pi.smul_apply, smul_eq_mul]
  ring

theorem Data.powerSum_smul (d : Data f) (σ a : ℝ) (ha : 0 < a)
    {w : Vec f} (hw : w ∈ PositivePrices f) :
    d.powerSum σ (a • w) = a ^ (1-σ) * d.powerSum σ w := by
  simp only [Data.powerSum, d.ratio_smul, Real.mul_rpow ha.le (d.ratio_pos hw _).le,
    Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem Data.ces_smul (d : Data f) (σ : ℝ) (hσ : σ ≠ 1) (a : ℝ) (ha : 0 < a)
    {w : Vec f} (hw : w ∈ PositivePrices f) :
    d.ces σ (a • w) = a * d.ces σ w := by
  have ht : 1-σ ≠ 0 := sub_ne_zero.mpr (Ne.symm hσ)
  rw [Data.ces, d.powerSum_smul σ a ha hw,
    Real.mul_rpow (Real.rpow_nonneg ha.le _) (d.powerSum_pos σ hw).le,
    ←Real.rpow_mul ha.le]
  rw [show (1-σ)*(1/(1-σ)) = 1 by field_simp, Real.rpow_one]
  simp only [Data.ces]
  ring

theorem Data.logSum_smul (d : Data f) (a : ℝ) (ha : 0 < a)
    {w : Vec f} (hw : w ∈ PositivePrices f) :
    d.logSum (a • w) = Real.log a + d.logSum w := by
  simp only [Data.logSum, d.ratio_smul, Real.log_mul ha.ne' (d.ratio_pos hw _).ne',
    mul_add, Finset.sum_add_distrib, ←Finset.sum_mul, d.share_sum, one_mul]

theorem Data.cobb_smul (d : Data f) (a : ℝ) (ha : 0 < a)
    {w : Vec f} (hw : w ∈ PositivePrices f) :
    d.cobb (a • w) = a * d.cobb w := by
  rw [Data.cobb, d.logSum_smul a ha hw, Real.exp_add, Real.exp_log ha]
  simp only [Data.cobb]
  ring

theorem Data.cost_smul (d : Data f) (σ a : ℝ) (ha : 0 < a)
    {w : Vec f} (hw : w ∈ PositivePrices f) :
    d.cost σ (a • w) = a * d.cost σ w := by
  by_cases hσ : σ = 1
  · rw [d.cost_eq_cobb hσ]; exact d.cobb_smul a ha hw
  · rw [d.cost_eq_ces hσ]; exact d.ces_smul σ hσ a ha hw

/-- Every continuous linear functional equals its coordinate dot product. -/
theorem clm_eq_weighted (L : Vec f →L[ℝ] ℝ) :
    L = weightedLinear (fun j => L (Pi.single j 1)) := by
  ext v
  rw [weightedLinear_apply]
  simpa only [dotProduct, mul_comm] using clm_apply_eq_sum L v

theorem Data.hasFDerivAt_cost_current (d : Data f) (σ : ℝ) {w : Vec f}
    (hw : w ∈ PositivePrices f) :
    HasFDerivAt (d.cost σ) (weightedLinear (fun j => pricePartial (d.cost σ) j w)) w := by
  have hd := ((d.cost_contDiffAt σ hw).differentiableAt (by simp)).hasFDerivAt
  rw [clm_eq_weighted (fderiv ℝ (d.cost σ) w)] at hd
  exact hd

theorem Data.cost_euler (d : Data f) (σ : ℝ) {w : Vec f}
    (hw : w ∈ PositivePrices f) :
    d.cost σ w = dotProduct (fun j => pricePartial (d.cost σ) j w) w := by
  have hs : HasDerivAt (fun a : ℝ => a • w) w 1 := by
    simpa using (hasDerivAt_id (1 : ℝ)).smul_const w
  have hd : HasFDerivAt (d.cost σ)
      (weightedLinear (fun j => pricePartial (d.cost σ) j w)) ((1 : ℝ) • w) := by
    simpa using d.hasFDerivAt_cost_current σ hw
  have hc := hd.comp_hasDerivAt (1 : ℝ) hs
  have hh : (fun a : ℝ => d.cost σ (a • w)) =ᶠ[𝓝 1] (fun a => a*d.cost σ w) := by
    filter_upwards [isOpen_Ioi.mem_nhds (show (1 : ℝ) ∈ Set.Ioi 0 by norm_num)] with a ha
    exact d.cost_smul σ a ha hw
  have hlin := (hasDerivAt_id (1 : ℝ)).mul_const (d.cost σ w)
  have heq := (hc.congr_of_eventuallyEq hh.symm).unique hlin
  simpa only [weightedLinear_apply, one_mul] using heq.symm

end CommodityClassification.CESCost
