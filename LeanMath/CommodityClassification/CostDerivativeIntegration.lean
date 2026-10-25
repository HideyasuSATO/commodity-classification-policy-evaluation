module
public import LeanMath.CommodityClassification.CESCostDerivatives
public import LeanMath.CommodityClassification.CobbDouglasCostDerivatives
@[expose] public section
set_option maxHeartbeats 1200000
namespace CommodityClassification.CESCost
open Matrix Filter
open scoped BigOperators Topology
variable {f : ℕ}

theorem Data.hasFDerivAt_cost_benchmark (d : Data f) (σ : ℝ) :
    HasFDerivAt (d.cost σ) (weightedLinear d.a) d.w0 := by
  by_cases hσ : σ = 1
  · rw [d.cost_eq_cobb hσ]
    exact d.hasFDerivAt_cobb_benchmark
  · rw [d.cost_eq_ces hσ]
    exact d.hasFDerivAt_ces_benchmark σ hσ

theorem Data.cost_first_derivative (d : Data f) (σ : ℝ) (u : Vec f) :
    fderiv ℝ (d.cost σ) d.w0 u = dotProduct d.a u := by
  rw [d.hasFDerivAt_cost_benchmark σ |>.fderiv, weightedLinear_apply]

theorem Data.cost_gradient (d : Data f) (σ : ℝ) (j : Fin f) :
    pricePartial (d.cost σ) j d.w0 = d.a j := by
  simp [pricePartial, (d.hasFDerivAt_cost_benchmark σ).fderiv]

theorem Data.hasFDerivAt_cost_partial_benchmark (d : Data f) (σ : ℝ) (j : Fin f) :
    HasFDerivAt (pricePartial (d.cost σ) j) (d.hessianRow σ j) d.w0 := by
  by_cases hσ : σ = 1
  · rw [d.cost_eq_cobb hσ, hσ]
    exact d.hasFDerivAt_cobb_partial_benchmark j
  · rw [d.cost_eq_ces hσ]
    exact d.hasFDerivAt_ces_partial_benchmark σ hσ j

theorem Data.cost_mixed_derivative (d : Data f) (σ : ℝ) (j l : Fin f) :
    pricePartial (pricePartial (d.cost σ) j) l d.w0 = d.hessian σ j l := by
  rw [pricePartial, (d.hasFDerivAt_cost_partial_benchmark σ j).fderiv]
  simp [Data.hessianRow, Data.hessian, Pi.single_apply]
  split_ifs <;> ring

theorem Data.hessian_manuscript (d : Data f) (σ : ℝ) :
    d.hessian σ = σ • (d.p⁻¹ • vecMulVec d.a d.a - diagonal (fun j => d.a j / d.w0 j)) := by
  ext j l
  simp [Data.hessian, diagonal_apply, vecMulVec, div_eq_mul_inv,
    mul_comm]

theorem clm_apply_eq_sum (T : Vec f →L[ℝ] ℝ) (v : Vec f) :
    T v = ∑ j, v j * T (Pi.single j 1) := by
  have hv : v = ∑ j, v j • Pi.single j (1 : ℝ) := by
    ext l
    simp [Pi.single_apply]
  conv_lhs => rw [hv]
  simp

theorem fderiv_eq_sum_partials (g : Vec f → ℝ) (w v : Vec f) :
    fderiv ℝ g w v = ∑ j, v j * pricePartial g j w := clm_apply_eq_sum _ v

theorem Data.hasFDerivAt_cost_directional_benchmark (d : Data f) (σ : ℝ) (v : Vec f) :
    HasFDerivAt (fun w => fderiv ℝ (d.cost σ) w v)
      (∑ j, v j • d.hessianRow σ j) d.w0 := by
  have hh := HasFDerivAt.fun_sum (u := Finset.univ)
    (fun j _ => (d.hasFDerivAt_cost_partial_benchmark σ j).const_mul (v j))
  simpa only [fderiv_eq_sum_partials] using hh

theorem Data.cost_second_derivative (d : Data f) (σ : ℝ) (u v : Vec f) :
    fderiv ℝ (fun w => fderiv ℝ (d.cost σ) w v) d.w0 u =
      σ * (dotProduct d.a u * dotProduct d.a v / d.p -
        ∑ j, (d.a j / d.w0 j) * u j * v j) := by
  rw [(d.hasFDerivAt_cost_directional_benchmark σ v).fderiv]
  simp only [Data.hessianRow, _root_.sum_apply,
    _root_.smul_apply, _root_.sub_apply,
    ContinuousLinearMap.proj_apply, smul_eq_mul, weightedLinear_apply]
  simp only [mul_sub, Finset.sum_sub_distrib]
  rw [Finset.mul_sum]
  congr 1
  · calc
      _ = ∑ j, (σ * dotProduct d.a u / d.p) * (d.a j * v j) := by
        apply Finset.sum_congr rfl
        intro j hj
        ring
      _ = (σ * dotProduct d.a u / d.p) * dotProduct d.a v := by
        rw [← Finset.mul_sum]
        rfl
      _ = _ := by ring
  · apply Finset.sum_congr rfl
    intro j hj
    ring

theorem Data.cost_second_derivative_symmetric (d : Data f) (σ : ℝ) (u v : Vec f) :
    fderiv ℝ (fun w => fderiv ℝ (d.cost σ) w v) d.w0 u =
      fderiv ℝ (fun w => fderiv ℝ (d.cost σ) w u) d.w0 v := by
  rw [d.cost_second_derivative, d.cost_second_derivative]
  have hs : (∑ j, (d.a j/d.w0 j)*u j*v j) = ∑ j, (d.a j/d.w0 j)*v j*u j := by
    apply Finset.sum_congr rfl
    intro j hj
    ring
  rw [hs]
  ring

end CommodityClassification.CESCost
