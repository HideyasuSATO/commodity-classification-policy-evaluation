module

public import LeanMath.CommodityClassification.RobustPolicyError

/-! The precise relative normalization bounds, including the reverse-triangle lower bound. -/
@[expose] public section
noncomputable section
set_option maxHeartbeats 2000000
namespace CommodityClassification.Robust
open Matrix Equilibrium
variable {n : ℕ}

def energyNorm (D : Mat n n) (b : Vec n) : ℝ := Real.sqrt (dotProduct b (D *ᵥ b))
def normalizationLower (δ τ : ℝ) : ℝ := (1-δ)*(1-τ)^2
def normalizationUpper (δ τ : ℝ) : ℝ := (1+δ)*(1+τ)^2

theorem energyNorm_nonneg (D : Mat n n) (b : Vec n) : 0≤energyNorm D b := Real.sqrt_nonneg _

theorem energyNorm_sq (D : Mat n n) (hD : D.PosSemidef) (b : Vec n) :
    (energyNorm D b)^2=dotProduct b (D *ᵥ b) := by
  apply Real.sq_sqrt
  simpa only [star_trivial] using hD.dotProduct_mulVec_nonneg b

theorem energyNorm_neg (D : Mat n n) (b : Vec n) : energyNorm D (-b)=energyNorm D b := by
  simp [energyNorm,Matrix.mulVec_neg]

theorem energyNorm_triangle (D : Mat n n) (hD : D.PosSemidef) (x y : Vec n) :
    energyNorm D (x+y)≤energyNorm D x+energyNorm D y := by
  have hx := energyNorm_sq D hD x
  have hy := energyNorm_sq D hD y
  have hxy := energyNorm_sq D hD (x+y)
  have hnormx := energyNorm_nonneg D x
  have hnormy := energyNorm_nonneg D y
  have hnormxy := energyNorm_nonneg D (x+y)
  have hcross := semidefinite_cross_bound D hD x y (energyNorm D x) (energyNorm D y)
    hnormx hnormy hx.ge hy.ge
  have hcross' := (le_abs_self (dotProduct x (D *ᵥ y))).trans hcross
  rw [semidefinite_add_expansion D hD x y] at hxy
  nlinarith

theorem energyNorm_reverse (D : Mat n n) (hD : D.PosSemidef) (x y : Vec n) :
    energyNorm D x≤energyNorm D (x+y)+energyNorm D y := by
  have hh := energyNorm_triangle D hD (x+y) (-y)
  simpa only [add_neg_cancel_right,energyNorm_neg] using hh

theorem reference_energy_bounds (D0 : Mat n n) (hD0 : D0.PosSemidef) (b b0 : Vec n)
    (τ : ℝ) (hτ : 0≤τ) (hτ1 : τ≤1)
    (hh : dotProduct (b-b0) (D0 *ᵥ (b-b0))≤τ^2*dotProduct b0 (D0 *ᵥ b0)) :
    (1-τ)^2*dotProduct b0 (D0 *ᵥ b0)≤dotProduct b (D0 *ᵥ b) ∧
      dotProduct b (D0 *ᵥ b)≤(1+τ)^2*dotProduct b0 (D0 *ᵥ b0) := by
  have hs0 := energyNorm_sq D0 hD0 b0
  have hsb := energyNorm_sq D0 hD0 b
  have hsh := energyNorm_sq D0 hD0 (b-b0)
  have hn0 := energyNorm_nonneg D0 b0
  have hnb := energyNorm_nonneg D0 b
  have hnh := energyNorm_nonneg D0 (b-b0)
  have hprod := mul_nonneg hτ hn0
  have hnormh : energyNorm D0 (b-b0)≤τ*energyNorm D0 b0 := by nlinarith
  have he : b0+(b-b0)=b := by abel
  have hu := energyNorm_triangle D0 hD0 b0 (b-b0)
  have hl := energyNorm_reverse D0 hD0 b0 (b-b0)
  rw [he] at hu hl
  have hlow : (1-τ)*energyNorm D0 b0≤energyNorm D0 b := by nlinarith
  have hhigh : energyNorm D0 b≤(1+τ)*energyNorm D0 b0 := by nlinarith
  have hlow0 : 0≤(1-τ)*energyNorm D0 b0 := mul_nonneg (sub_nonneg.mpr hτ1) hn0
  have hhigh0 : 0≤(1+τ)*energyNorm D0 b0 := mul_nonneg (by linarith) hn0
  have hl2 := mul_le_mul hlow hlow hlow0 hnb
  have hu2 := mul_le_mul hhigh hhigh hnb hhigh0
  constructor <;> nlinarith

theorem normalization_bounds (D D0 : Mat n n) (hD0 : D0.PosSemidef) (b b0 : Vec n)
    (δ τ : ℝ) (hδ : 0≤δ) (hδ1 : δ≤1) (hτ : 0≤τ) (hτ1 : τ≤1)
    (hlo : (D-(1-δ) • D0).PosSemidef) (hhi : ((1+δ) • D0-D).PosSemidef)
    (hh : dotProduct (b-b0) (D0 *ᵥ (b-b0))≤τ^2*dotProduct b0 (D0 *ᵥ b0)) :
    normalizationLower δ τ*dotProduct b0 (D0 *ᵥ b0)≤dotProduct b (D *ᵥ b) ∧
      dotProduct b (D *ᵥ b)≤normalizationUpper δ τ*dotProduct b0 (D0 *ᵥ b0) := by
  have hb := reference_energy_bounds D0 hD0 b b0 τ hτ hτ1 hh
  have hl := loewner_quadratic_lower D D0 (1-δ) hlo b
  have hu := loewner_quadratic_upper D D0 (1+δ) hhi b
  have hlo' := mul_le_mul_of_nonneg_left hb.1 (sub_nonneg.mpr hδ1)
  have hhi' := mul_le_mul_of_nonneg_left hb.2 (show 0≤1+δ by linarith)
  unfold normalizationLower normalizationUpper
  constructor <;> nlinarith

theorem normalization_factors_positive (δ τ : ℝ) (hδ : 0≤δ) (hδ1 : δ<1)
    (hτ : 0≤τ) (hτ1 : τ<1) : 0<normalizationLower δ τ ∧ 0<normalizationUpper δ τ := by
  exact ⟨mul_pos (sub_pos.mpr hδ1) (sq_pos_of_pos (sub_pos.mpr hτ1)),
    mul_pos (by linarith) (sq_pos_of_pos (by linarith))⟩

end CommodityClassification.Robust
