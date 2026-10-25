module
public import LeanMath.CommodityClassification.CESCostDefinitions
@[expose] public section
set_option maxHeartbeats 1200000
namespace CommodityClassification.CESCost
open Matrix Filter
open scoped BigOperators Topology
variable {f : ℕ}

noncomputable def Data.powerDeriv (d : Data f) (σ : ℝ) (w : Vec f) : Vec f →L[ℝ] ℝ :=
  ∑ j, (d.share j * (1-σ) * d.ratio w j ^ (-σ) / d.w0 j) • ContinuousLinearMap.proj j

theorem Data.hasFDerivAt_powerSum (d : Data f) (σ : ℝ) {w : Vec f}
    (hw : w ∈ PositivePrices f) : HasFDerivAt (d.powerSum σ) (d.powerDeriv σ w) w := by
  have h (j : Fin f) := ((d.hasFDerivAt_ratio w j).rpow_const
    (Or.inl (d.ratio_pos hw j).ne') (p := 1-σ)).const_mul (d.share j)
  have hh := HasFDerivAt.fun_sum (u := Finset.univ) (fun j _ => h j)
  convert! hh using 1
  ext u
  simp only [Data.powerDeriv, _root_.sum_apply, _root_.smul_apply,
    ContinuousLinearMap.proj_apply, smul_eq_mul]
  apply Finset.sum_congr rfl
  intro j hj
  rw [show (1-σ)-1 = -σ by ring]
  simp only [div_eq_mul_inv]
  ring

theorem Data.powerDeriv_benchmark (d : Data f) (σ : ℝ) :
    d.powerDeriv σ d.w0 = ((1-σ)/d.p) • weightedLinear d.a := by
  ext u
  simp only [Data.powerDeriv, d.ratio_benchmark, Real.one_rpow, mul_one,
    _root_.sum_apply, _root_.smul_apply,
    ContinuousLinearMap.proj_apply, smul_eq_mul, weightedLinear_apply, dotProduct,
    Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  rw [show d.share j*(1-σ)/d.w0 j = (1-σ)*(d.share j/d.w0 j) by ring,
    d.share_over_w0]
  ring

noncomputable def Data.cesDeriv (d : Data f) (σ : ℝ) (w : Vec f) : Vec f →L[ℝ] ℝ :=
  (d.p * (1/(1-σ) * d.powerSum σ w ^ (1/(1-σ)-1))) • d.powerDeriv σ w

theorem Data.hasFDerivAt_ces (d : Data f) (σ : ℝ) {w : Vec f}
    (hw : w ∈ PositivePrices f) : HasFDerivAt (d.ces σ) (d.cesDeriv σ w) w := by
  convert!
    ((d.hasFDerivAt_powerSum σ hw).rpow_const (Or.inl (d.powerSum_pos σ hw).ne')
      (p := 1/(1-σ))).const_mul d.p using 1
  ext u
  simp [Data.cesDeriv, smul_smul]

noncomputable def Data.cesGradient (d : Data f) (σ : ℝ) (j : Fin f) (w : Vec f) : ℝ :=
  d.a j * d.powerSum σ w ^ (1/(1-σ)-1) * d.ratio w j ^ (-σ)

theorem Data.ces_partial (d : Data f) (σ : ℝ) (hσ : σ ≠ 1) {w : Vec f}
    (hw : w ∈ PositivePrices f) (j : Fin f) : pricePartial (d.ces σ) j w = d.cesGradient σ j w := by
  have ht : 1-σ ≠ 0 := sub_ne_zero.mpr (Ne.symm hσ)
  rw [pricePartial, (d.hasFDerivAt_ces σ hw).fderiv]
  have hs : d.powerDeriv σ w (Pi.single j 1) =
      d.share j * (1-σ) * d.ratio w j ^ (-σ) / d.w0 j :=
    weightedLinear_single (fun l => d.share l * (1-σ) * d.ratio w l ^ (-σ) / d.w0 l) j
  simp only [Data.cesDeriv, _root_.smul_apply, smul_eq_mul, hs, Data.cesGradient, Data.share]
  field_simp [ht, d.p_pos.ne', (d.w0_pos j).ne']

theorem Data.hasFDerivAt_ces_benchmark (d : Data f) (σ : ℝ) (hσ : σ ≠ 1) :
    HasFDerivAt (d.ces σ) (weightedLinear d.a) d.w0 := by
  have ht : 1-σ ≠ 0 := sub_ne_zero.mpr (Ne.symm hσ)
  convert! d.hasFDerivAt_ces σ d.benchmark_mem using 1
  ext u
  simp [Data.cesDeriv, d.powerDeriv_benchmark, smul_smul]
  field_simp [ht, d.p_pos.ne']

theorem Data.hasFDerivAt_cesGradient_benchmark (d : Data f) (σ : ℝ) (hσ : σ ≠ 1)
    (j : Fin f) : HasFDerivAt (d.cesGradient σ j) (d.hessianRow σ j) d.w0 := by
  have ht : 1-σ ≠ 0 := sub_ne_zero.mpr (Ne.symm hσ)
  have hS := (d.hasFDerivAt_powerSum σ d.benchmark_mem).rpow_const
    (Or.inl (d.powerSum_pos σ d.benchmark_mem).ne') (p := 1/(1-σ)-1)
  have hR := (d.hasFDerivAt_ratio d.w0 j).rpow_const
    (Or.inl (d.ratio_pos d.benchmark_mem j).ne') (p := -σ)
  convert! (hS.const_mul (d.a j)).mul hR using 1
  ext u
  simp [Data.hessianRow, d.powerDeriv_benchmark, smul_smul]
  field_simp [ht, d.p_pos.ne', (d.w0_pos j).ne']
  ring

theorem Data.hasFDerivAt_ces_partial_benchmark (d : Data f) (σ : ℝ) (hσ : σ ≠ 1)
    (j : Fin f) : HasFDerivAt (pricePartial (d.ces σ) j) (d.hessianRow σ j) d.w0 := by
  apply (d.hasFDerivAt_cesGradient_benchmark σ hσ j).congr_of_eventuallyEq
  filter_upwards [positivePrices_open.mem_nhds d.benchmark_mem] with w hw
  exact d.ces_partial σ hσ hw j

end CommodityClassification.CESCost
