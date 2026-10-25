module
public import LeanMath.CommodityClassification.CostHomogeneity
public import Mathlib.Analysis.Convex.SpecificFunctions.Basic
@[expose] public section
set_option maxHeartbeats 1600000
namespace CommodityClassification.CESCost
open scoped BigOperators

theorem negative_power_tangent {x r : ℝ} (hx : 0 < x) (hr : r < 0) :
    1 + r * (x - 1) ≤ x ^ r := by
  have h := one_add_mul_self_le_rpow_one_add
    (show -1 ≤ x⁻¹ - 1 by linarith [inv_pos.mpr hx]) (show 1 ≤ 1-r by linarith)
  rw [show 1 + (x⁻¹-1) = x⁻¹ by ring] at h
  have hp : x * (x⁻¹) ^ (1-r) = x ^ r := by
    rw [Real.inv_rpow hx.le, ← Real.rpow_neg hx.le]
    rw [show -(1-r) = r-1 by ring, Real.rpow_sub_one hx.ne']
    field_simp
  have hh := mul_le_mul_of_nonneg_left h hx.le
  rw [hp] at hh
  have he : x * (1 + (1-r)*(x⁻¹-1)) = 1+r*(x-1) := by
    field_simp
    ring
  rwa [he] at hh

theorem power_mean_le_arithmetic {f : ℕ} (t x : Fin f → ℝ)
    (ht : ∀j, 0 ≤ t j) (ht1 : ∑j, t j = 1) (hx : ∀j, 0 < x j)
    {r : ℝ} (hr : r < 1) (hr0 : r ≠ 0) :
    (∑j, t j * x j ^ r) ^ (1/r) ≤ ∑j, t j * x j := by
  let A := ∑j, t j*x j
  have hA : 0 < A := by
    have hex : ∃j, 0 < t j := by
      by_contra! hn
      have hz : ∑j, t j = 0 := Finset.sum_eq_zero (fun j _ => le_antisymm (hn j) (ht j))
      linarith
    obtain ⟨j,hj⟩ := hex
    exact Finset.sum_pos' (fun i _ => mul_nonneg (ht i) (hx i).le)
      ⟨j, Finset.mem_univ j, mul_pos hj (hx j)⟩
  let z := fun j => x j / A
  have hz : ∀j, 0 < z j := fun j => div_pos (hx j) hA
  have hz1 : ∑j, t j*z j = 1 := by
    simp only [z, div_eq_mul_inv, ←mul_assoc, ← Finset.sum_mul]
    exact mul_inv_cancel₀ hA.ne'
  have hsum : ∑j, t j*(1+r*(z j-1)) = 1 := by
    calc
      _ = (∑j, t j) + r*((∑j, t j*z j)-(∑j,t j)) := by
        simp only [mul_sub, Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl; intro j _; ring
      _ = 1 := by rw [ht1,hz1]; ring
  have hscale : ∑j, t j*x j^r = A^r * ∑j,t j*z j^r := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl; intro j _
    rw [show x j = A*z j by dsimp [z]; field_simp, Real.mul_rpow hA.le (hz j).le]
    ring
  rw [hscale, Real.mul_rpow (Real.rpow_nonneg hA.le _) (Finset.sum_nonneg
    (fun j _ => mul_nonneg (ht j) (Real.rpow_nonneg (hz j).le _))),
    ←Real.rpow_mul hA.le, show r*(1/r)=1 by field_simp, Real.rpow_one]
  change A * (∑i, t i*z i^r)^(1/r) ≤ A
  suffices hh : (∑i, t i*z i^r)^(1/r) ≤ 1 by nlinarith
  rcases lt_or_gt_of_ne hr0 with hn | hp
  · apply Real.rpow_le_one_of_one_le_of_nonpos _ (div_nonpos_of_nonneg_of_nonpos zero_le_one hn.le)
    rw [←hsum]
    exact Finset.sum_le_sum (fun j _ => mul_le_mul_of_nonneg_left
      (negative_power_tangent (hz j) hn) (ht j))
  · apply Real.rpow_le_one (Finset.sum_nonneg
      (fun j _ => mul_nonneg (ht j) (Real.rpow_nonneg (hz j).le _))) _ (by positivity)
    rw [←hsum]
    apply Finset.sum_le_sum; intro j _
    apply mul_le_mul_of_nonneg_left _ (ht j)
    have h := rpow_one_add_le_one_add_mul_self
      (show -1 ≤ z j-1 by linarith [hz j]) hp.le hr.le
    rwa [show 1+(z j-1) = z j by ring] at h

end CommodityClassification.CESCost
