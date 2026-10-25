module
public import LeanMath.CommodityClassification.CESCostDefinitions
@[expose] public section
set_option maxHeartbeats 1200000
namespace CommodityClassification.CESCost
open Matrix Filter
open scoped BigOperators Topology
variable {f : ℕ}

noncomputable def Data.logDeriv (d : Data f) (w : Vec f) : Vec f →L[ℝ] ℝ :=
  ∑ j, (d.share j * (d.ratio w j)⁻¹ / d.w0 j) • ContinuousLinearMap.proj j

theorem Data.hasFDerivAt_logSum (d : Data f) {w : Vec f}
    (hw : w ∈ PositivePrices f) : HasFDerivAt d.logSum (d.logDeriv w) w := by
  have h (j : Fin f) := ((d.hasFDerivAt_ratio w j).log
    (d.ratio_pos hw j).ne').const_mul (d.share j)
  have hh := HasFDerivAt.fun_sum (u := Finset.univ) (fun j _ => h j)
  convert! hh using 1
  ext u
  simp only [Data.logDeriv, _root_.sum_apply, _root_.smul_apply,
    ContinuousLinearMap.proj_apply, smul_eq_mul]
  apply Finset.sum_congr rfl
  intro j hj
  simp only [div_eq_mul_inv]
  ring

theorem Data.logDeriv_benchmark (d : Data f) :
    d.logDeriv d.w0 = (1/d.p) • weightedLinear d.a := by
  ext u
  simp only [Data.logDeriv, d.ratio_benchmark, inv_one, mul_one,
    _root_.sum_apply, _root_.smul_apply,
    ContinuousLinearMap.proj_apply, smul_eq_mul, weightedLinear_apply, dotProduct,
    Finset.mul_sum, d.share_over_w0]
  apply Finset.sum_congr rfl
  intro j hj
  ring

noncomputable def Data.cobbDeriv (d : Data f) (w : Vec f) : Vec f →L[ℝ] ℝ :=
  (d.p * Real.exp (d.logSum w)) • d.logDeriv w

theorem Data.hasFDerivAt_cobb (d : Data f) {w : Vec f}
    (hw : w ∈ PositivePrices f) : HasFDerivAt d.cobb (d.cobbDeriv w) w := by
  convert! (d.hasFDerivAt_logSum hw).exp.const_mul d.p using 1
  ext u
  simp [Data.cobbDeriv, smul_smul]

noncomputable def Data.cobbGradient (d : Data f) (j : Fin f) (w : Vec f) : ℝ :=
  d.a j * Real.exp (d.logSum w) * d.ratio w j ^ (- (1 : ℝ))

theorem Data.cobb_partial (d : Data f) {w : Vec f}
    (hw : w ∈ PositivePrices f) (j : Fin f) : pricePartial d.cobb j w = d.cobbGradient j w := by
  rw [pricePartial, (d.hasFDerivAt_cobb hw).fderiv]
  have hs : d.logDeriv w (Pi.single j 1) = d.share j * (d.ratio w j)⁻¹ / d.w0 j :=
    weightedLinear_single (fun l => d.share l * (d.ratio w l)⁻¹ / d.w0 l) j
  simp only [Data.cobbDeriv, _root_.smul_apply, smul_eq_mul, hs, Data.cobbGradient, Data.share,
    Real.rpow_neg_one]
  field_simp [d.p_pos.ne', (d.w0_pos j).ne']

theorem Data.hasFDerivAt_cobb_benchmark (d : Data f) :
    HasFDerivAt d.cobb (weightedLinear d.a) d.w0 := by
  convert! d.hasFDerivAt_cobb d.benchmark_mem using 1
  ext u
  simp [Data.cobbDeriv, d.logDeriv_benchmark, smul_smul]
  field_simp [d.p_pos.ne']

theorem Data.hasFDerivAt_cobbGradient_benchmark (d : Data f) (j : Fin f) :
    HasFDerivAt (d.cobbGradient j) (d.hessianRow 1 j) d.w0 := by
  have hL := (d.hasFDerivAt_logSum d.benchmark_mem).exp
  have hR := (d.hasFDerivAt_ratio d.w0 j).rpow_const
    (Or.inl (d.ratio_pos d.benchmark_mem j).ne') (p := -(1 : ℝ))
  convert! (hL.const_mul (d.a j)).mul hR using 1
  ext u
  simp [Data.hessianRow, d.logDeriv_benchmark, smul_smul]
  field_simp [d.p_pos.ne', (d.w0_pos j).ne']
  ring

theorem Data.hasFDerivAt_cobb_partial_benchmark (d : Data f) (j : Fin f) :
    HasFDerivAt (pricePartial d.cobb j) (d.hessianRow 1 j) d.w0 := by
  apply (d.hasFDerivAt_cobbGradient_benchmark j).congr_of_eventuallyEq
  filter_upwards [positivePrices_open.mem_nhds d.benchmark_mem] with w hw
  exact d.cobb_partial hw j

end CommodityClassification.CESCost
