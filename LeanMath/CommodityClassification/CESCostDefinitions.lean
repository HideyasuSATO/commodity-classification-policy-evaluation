module

public import LeanMath.CommodityClassification.InputCoordinates
public import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
public import Mathlib.Analysis.Calculus.FDeriv.Pi
public import Mathlib.Analysis.Calculus.FDeriv.Add
public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Ring

/-! CES cost data. Only current prices are differentiated; all fields are fixed. -/
@[expose] public section
set_option maxHeartbeats 800000
namespace CommodityClassification.CESCost
open Matrix Filter
open scoped BigOperators Topology
abbrev Vec (f : ℕ) := Fin f → ℝ
abbrev Mat (f g : ℕ) := Matrix (Fin f) (Fin g) ℝ
variable {f : ℕ}

structure Data (f : ℕ) where
  p : ℝ
  w0 : Vec f
  a : Vec f
  p_pos : 0 < p
  w0_pos : ∀ j, 0 < w0 j
  a_pos : ∀ j, 0 < a j
  cost_identity : dotProduct a w0 = p

def PositivePrices (f : ℕ) : Set (Vec f) := {w | ∀ j, 0 < w j}

theorem positivePrices_open : IsOpen (PositivePrices f) := by
  simp only [PositivePrices, Set.ofPred_forall]
  exact isOpen_iInter_of_finite (fun j => isOpen_lt continuous_const (continuous_apply j))

theorem Data.benchmark_mem (d : Data f) : d.w0 ∈ PositivePrices f := d.w0_pos

noncomputable def Data.share (d : Data f) (j : Fin f) : ℝ := d.w0 j * d.a j / d.p
noncomputable def Data.ratio (d : Data f) (w : Vec f) (j : Fin f) : ℝ := w j / d.w0 j

theorem Data.share_pos (d : Data f) (j : Fin f) : 0 < d.share j :=
  div_pos (mul_pos (d.w0_pos j) (d.a_pos j)) d.p_pos

theorem Data.share_sum (d : Data f) : ∑ j, d.share j = 1 := by
  simp only [Data.share, div_eq_mul_inv, ← Finset.sum_mul]
  have hh : (∑ j, d.w0 j * d.a j) = d.p := by
    simpa [dotProduct, mul_comm] using d.cost_identity
  rw [hh, mul_inv_cancel₀ d.p_pos.ne']

theorem Data.share_over_w0 (d : Data f) (j : Fin f) :
    d.share j / d.w0 j = d.a j / d.p := by
  unfold Data.share
  field_simp [(d.w0_pos j).ne', d.p_pos.ne']

theorem Data.p_share_over_w0 (d : Data f) (j : Fin f) :
    d.p * (d.share j / d.w0 j) = d.a j := by
  rw [d.share_over_w0]
  field_simp [d.p_pos.ne']

theorem Data.ratio_pos (d : Data f) {w : Vec f} (hw : w ∈ PositivePrices f) (j : Fin f) :
    0 < d.ratio w j := div_pos (hw j) (d.w0_pos j)

@[simp] theorem Data.ratio_benchmark (d : Data f) (j : Fin f) : d.ratio d.w0 j = 1 :=
  div_self (d.w0_pos j).ne'

noncomputable def weightedLinear (v : Vec f) : Vec f →L[ℝ] ℝ :=
  ∑ j, v j • ContinuousLinearMap.proj j

@[simp] theorem weightedLinear_apply (v u : Vec f) : weightedLinear v u = dotProduct v u := by
  simp [weightedLinear, dotProduct]

@[simp] theorem weightedLinear_single (v : Vec f) (j : Fin f) :
    weightedLinear v (Pi.single j 1) = v j := by
  simp only [weightedLinear_apply, dotProduct_single, mul_one]

noncomputable def Data.powerSum (d : Data f) (σ : ℝ) (w : Vec f) : ℝ :=
  ∑ j, d.share j * (d.ratio w j) ^ (1-σ)
noncomputable def Data.ces (d : Data f) (σ : ℝ) (w : Vec f) : ℝ :=
  d.p * d.powerSum σ w ^ (1/(1-σ))
noncomputable def Data.logSum (d : Data f) (w : Vec f) : ℝ :=
  ∑ j, d.share j * Real.log (d.ratio w j)
noncomputable def Data.cobb (d : Data f) (w : Vec f) : ℝ := d.p * Real.exp (d.logSum w)
noncomputable def Data.cost (d : Data f) (σ : ℝ) (w : Vec f) : ℝ :=
  if σ = 1 then d.cobb w else d.ces σ w

theorem Data.cost_eq_cobb (d : Data f) {σ : ℝ} (hσ : σ = 1) : d.cost σ = d.cobb := by
  funext w
  simp [Data.cost, hσ]

theorem Data.cost_eq_ces (d : Data f) {σ : ℝ} (hσ : σ ≠ 1) : d.cost σ = d.ces σ := by
  funext w
  simp [Data.cost, hσ]

theorem Data.powerSum_pos (d : Data f) (σ : ℝ) {w : Vec f} (hw : w ∈ PositivePrices f) :
    0 < d.powerSum σ w := by
  have hn : Finset.univ.Nonempty (α := Fin f) := by
    by_contra hh
    have hz : (∑ j, d.share j) = 0 := Finset.sum_eq_zero (fun j hj => False.elim (hh ⟨j, hj⟩))
    linarith [d.share_sum]
  exact Finset.sum_pos (fun j _ => mul_pos (d.share_pos j)
    (Real.rpow_pos_of_pos (d.ratio_pos hw j) _)) hn

@[simp] theorem Data.powerSum_benchmark (d : Data f) (σ : ℝ) : d.powerSum σ d.w0 = 1 := by
  simp only [Data.powerSum, d.ratio_benchmark, Real.one_rpow, mul_one, d.share_sum]
@[simp] theorem Data.logSum_benchmark (d : Data f) : d.logSum d.w0 = 0 := by
  simp [Data.logSum]
@[simp] theorem Data.ces_benchmark (d : Data f) (σ : ℝ) : d.ces σ d.w0 = d.p := by
  simp [Data.ces]
@[simp] theorem Data.cobb_benchmark (d : Data f) : d.cobb d.w0 = d.p := by simp [Data.cobb]
@[simp] theorem Data.cost_benchmark (d : Data f) (σ : ℝ) : d.cost σ d.w0 = d.p := by
  simp [Data.cost]

theorem Data.hasFDerivAt_ratio (d : Data f) (w : Vec f) (j : Fin f) :
    HasFDerivAt (fun v => d.ratio v j)
      ((d.w0 j)⁻¹ • (ContinuousLinearMap.proj j : Vec f →L[ℝ] ℝ)) w := by
  have h : HasFDerivAt (𝕜 := ℝ) (fun v : Vec f => v j) (ContinuousLinearMap.proj j) w :=
    hasFDerivAt_apply (𝕜 := ℝ) j w
  simpa [Data.ratio, div_eq_mul_inv] using h.mul_const (d.w0 j)⁻¹

theorem Data.ratio_contDiffAt (d : Data f) (w : Vec f) (j : Fin f) :
    ContDiffAt ℝ ⊤ (fun v => d.ratio v j) w := by
  unfold Data.ratio
  fun_prop

theorem Data.powerSum_contDiffAt (d : Data f) (σ : ℝ) {w : Vec f}
    (hw : w ∈ PositivePrices f) : ContDiffAt ℝ ⊤ (d.powerSum σ) w := by
  unfold Data.powerSum
  apply ContDiffAt.sum; intro j hj
  exact contDiffAt_const.mul ((d.ratio_contDiffAt w j).rpow_const_of_ne (d.ratio_pos hw j).ne')

theorem Data.ces_contDiffAt (d : Data f) (σ : ℝ) {w : Vec f}
    (hw : w ∈ PositivePrices f) : ContDiffAt ℝ ⊤ (d.ces σ) w := by
  exact contDiffAt_const.mul ((d.powerSum_contDiffAt σ hw).rpow_const_of_ne (d.powerSum_pos σ hw).ne')

theorem Data.logSum_contDiffAt (d : Data f) {w : Vec f}
    (hw : w ∈ PositivePrices f) : ContDiffAt ℝ ⊤ d.logSum w := by
  unfold Data.logSum
  apply ContDiffAt.sum; intro j hj
  exact contDiffAt_const.mul ((d.ratio_contDiffAt w j).log (d.ratio_pos hw j).ne')

theorem Data.cobb_contDiffAt (d : Data f) {w : Vec f}
    (hw : w ∈ PositivePrices f) : ContDiffAt ℝ ⊤ d.cobb w :=
  contDiffAt_const.mul (d.logSum_contDiffAt hw).exp

theorem Data.cost_contDiffAt (d : Data f) (σ : ℝ) {w : Vec f}
    (hw : w ∈ PositivePrices f) : ContDiffAt ℝ ⊤ (d.cost σ) w := by
  by_cases hσ : σ=1
  · rw [d.cost_eq_cobb hσ]
    exact d.cobb_contDiffAt hw
  · rw [d.cost_eq_ces hσ]
    exact d.ces_contDiffAt σ hw

noncomputable def pricePartial (g : Vec f → ℝ) (j : Fin f) (w : Vec f) : ℝ :=
  fderiv ℝ g w (Pi.single j 1)

noncomputable def Data.hessian (d : Data f) (σ : ℝ) : Mat f f :=
  fun j l => σ * (d.a j * d.a l / d.p - if j=l then d.a j / d.w0 j else 0)

noncomputable def Data.hessianRow (d : Data f) (σ : ℝ) (j : Fin f) : Vec f →L[ℝ] ℝ :=
  (σ*d.a j/d.p) • weightedLinear d.a - (σ*d.a j/d.w0 j) • ContinuousLinearMap.proj j

end CommodityClassification.CESCost
