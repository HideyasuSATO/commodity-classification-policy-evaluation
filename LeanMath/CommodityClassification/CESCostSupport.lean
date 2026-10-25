module
public import LeanMath.CommodityClassification.CESPowerMean
public import Mathlib.Analysis.MeanInequalities
@[expose] public section
set_option maxHeartbeats 2400000
namespace CommodityClassification.CESCost
open Matrix
open scoped BigOperators
variable {f : ℕ}

theorem Data.cost_pos (d : Data f) (σ : ℝ) {w : Vec f}
    (hw : w ∈ PositivePrices f) : 0 < d.cost σ w := by
  unfold Data.cost Data.cobb Data.ces
  split
  · exact mul_pos d.p_pos (Real.exp_pos _)
  · exact mul_pos d.p_pos (Real.rpow_pos_of_pos (d.powerSum_pos σ hw) _)

theorem Data.cost_partial_pos (d : Data f) (σ : ℝ) {w : Vec f}
    (hw : w ∈ PositivePrices f) (j : Fin f) : 0 < pricePartial (d.cost σ) j w := by
  by_cases hs : σ=1
  · rw [d.cost_eq_cobb hs, d.cobb_partial hw, Data.cobbGradient]
    exact mul_pos (mul_pos (d.a_pos j) (Real.exp_pos _))
      (Real.rpow_pos_of_pos (d.ratio_pos hw j) _)
  · rw [d.cost_eq_ces hs, d.ces_partial σ hs hw, Data.cesGradient]
    exact mul_pos (mul_pos (d.a_pos j) (Real.rpow_pos_of_pos (d.powerSum_pos σ hw) _))
      (Real.rpow_pos_of_pos (d.ratio_pos hw j) _)

theorem Data.ces_support (d : Data f) {σ : ℝ} (hs : 0 < σ) (hs1 : σ≠1)
    {v w : Vec f} (hv : v ∈ PositivePrices f) (hw : w ∈ PositivePrices f) :
    d.ces σ v ≤ dotProduct (fun j => d.cesGradient σ j w) v := by
  let S := d.powerSum σ w
  have hS : 0 < S := d.powerSum_pos σ hw
  let t := fun j => d.share j * d.ratio w j^(1-σ) / S
  let x := fun j => d.ratio v j / d.ratio w j
  have ht : ∀j, 0 ≤ t j := fun j => (div_pos
    (mul_pos (d.share_pos j) (Real.rpow_pos_of_pos (d.ratio_pos hw j) _)) hS).le
  have ht1 : ∑j, t j=1 := by
    simp only [t, div_eq_mul_inv, ←Finset.sum_mul]
    exact mul_inv_cancel₀ hS.ne'
  have hx : ∀j, 0 < x j := fun j => div_pos (d.ratio_pos hv j) (d.ratio_pos hw j)
  have hm := power_mean_le_arithmetic t x ht ht1 hx
    (show 1-σ<1 by linarith) (sub_ne_zero.mpr hs1.symm)
  have hsum : d.powerSum σ v = S * ∑j,t j*x j^(1-σ) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl; intro j _
    dsimp [t,x]
    rw [Real.div_rpow (d.ratio_pos hv j).le (d.ratio_pos hw j).le]
    field_simp [hS.ne', (Real.rpow_pos_of_pos (d.ratio_pos hw j) (1-σ)).ne']
  have hcv : d.ces σ v = d.ces σ w * (∑j,t j*x j^(1-σ))^(1/(1-σ)) := by
    rw [Data.ces, hsum, Real.mul_rpow hS.le (Finset.sum_nonneg
      (fun j _ => mul_nonneg (ht j) (Real.rpow_nonneg (hx j).le _)))]
    dsimp [Data.ces, S]
    ring
  have hterm (j : Fin f) : d.ces σ w * (t j*x j) = d.cesGradient σ j w * v j := by
    dsimp [t,x,Data.ces,Data.cesGradient]
    rw [Real.rpow_sub_one hS.ne', show -σ=(1-σ)-1 by ring,
      Real.rpow_sub_one (d.ratio_pos hw j).ne']
    dsimp [Data.share,Data.ratio]
    field_simp [d.p_pos.ne', (d.w0_pos j).ne', (hw j).ne', hS.ne']
    dsimp [S]
    ring
  rw [hcv]
  calc
    _ ≤ d.ces σ w * (∑j,t j*x j) := mul_le_mul_of_nonneg_left hm
      (mul_pos d.p_pos (Real.rpow_pos_of_pos hS _)).le
    _ = dotProduct (fun j => d.cesGradient σ j w) v := by
      rw [Finset.mul_sum]; exact Finset.sum_congr rfl (fun j _ => hterm j)

theorem Data.cobb_support (d : Data f) {v w : Vec f}
    (hv : v ∈ PositivePrices f) (hw : w ∈ PositivePrices f) :
    d.cobb v ≤ dotProduct (fun j => d.cobbGradient j w) v := by
  let x := fun j => d.ratio v j / d.ratio w j
  have hx : ∀j, 0<x j := fun j => div_pos (d.ratio_pos hv j) (d.ratio_pos hw j)
  have hm := Real.geom_mean_le_arith_mean_weighted Finset.univ d.share x
    (fun j _ => (d.share_pos j).le) d.share_sum (fun j _ => (hx j).le)
  have he : Real.exp (∑j,d.share j*Real.log (x j)) ≤ ∑j,d.share j*x j := by
    rw [Real.exp_sum]
    convert hm using 1
    apply Finset.prod_congr rfl; intro j _
    rw [Real.rpow_def_of_pos (hx j), mul_comm]
  have hl : d.logSum v = d.logSum w + ∑j,d.share j*Real.log (x j) := by
    simp only [Data.logSum, x, Real.log_div (d.ratio_pos hv _).ne' (d.ratio_pos hw _).ne',
      mul_sub, Finset.sum_sub_distrib]
    ring
  have hterm (j : Fin f) : d.cobb w * (d.share j*x j) = d.cobbGradient j w * v j := by
    dsimp [Data.cobb,Data.cobbGradient,x]
    rw [Real.rpow_neg_one]
    dsimp [Data.share,Data.ratio]
    field_simp [d.p_pos.ne', (d.w0_pos j).ne', (hw j).ne']
  calc
    d.cobb v = d.cobb w * Real.exp (∑j,d.share j*Real.log (x j)) := by
      rw [Data.cobb,hl,Real.exp_add]; dsimp [Data.cobb]; ring
    _ ≤ d.cobb w * (∑j,d.share j*x j) := mul_le_mul_of_nonneg_left he
      (mul_pos d.p_pos (Real.exp_pos _)).le
    _ = _ := by rw [Finset.mul_sum]; exact Finset.sum_congr rfl (fun j _ => hterm j)

theorem Data.cost_support (d : Data f) {σ : ℝ} (hs : 0 < σ)
    {v w : Vec f} (hv : v ∈ PositivePrices f) (hw : w ∈ PositivePrices f) :
    d.cost σ v ≤ dotProduct (fun j => pricePartial (d.cost σ) j w) v := by
  by_cases hs1 : σ=1
  · simpa only [d.cost_eq_cobb hs1, d.cobb_partial hw] using d.cobb_support hv hw
  · simpa only [d.cost_eq_ces hs1, d.ces_partial σ hs1 hw] using d.ces_support hs hs1 hv hw

theorem Data.cost_support_affine (d : Data f) {σ : ℝ} (hs : 0 < σ)
    {v w : Vec f} (hv : v ∈ PositivePrices f) (hw : w ∈ PositivePrices f) :
    d.cost σ v ≤ d.cost σ w + dotProduct (fun j => pricePartial (d.cost σ) j w) (v-w) := by
  rw [dotProduct_sub, d.cost_euler σ hw]
  simpa only [add_sub_cancel] using d.cost_support hs hv hw

end CommodityClassification.CESCost
