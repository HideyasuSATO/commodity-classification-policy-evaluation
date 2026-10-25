module

public import LeanMath.CommodityClassification.SupplyDemandSeparatingDirection
public import Mathlib.Analysis.Asymptotics.Ring

/-! The actual cubic-order remainder in the small-demand genericity argument. -/
@[expose] public section
noncomputable section
namespace CommodityClassification.Genericity
open Matrix FixedAnswer Filter Asymptotics
open scoped Topology
variable {k : ℕ}

local instance (a b : ℕ) : NormedAddCommGroup (Mat a b) :=
  inferInstanceAs (NormedAddCommGroup (Fin a → Fin b → ℝ))
local instance (a b : ℕ) : NormedSpace ℝ (Mat a b) :=
  inferInstanceAs (NormedSpace ℝ (Fin a → Fin b → ℝ))

def smallInverseEnergy (T H : Mat k k) (v : Vec k) (r : ℝ) : ℝ :=
  dotProduct v ((T+r • H)⁻¹ *ᵥ v)

theorem smallInverseEnergy_derivative (T H : Mat k k) (v : Vec k) (hT : T.PosDef) :
    HasDerivAt (smallInverseEnergy T H v)
      (-dotProduct (T⁻¹ *ᵥ v) (H *ᵥ (T⁻¹ *ᵥ v))) 0 := by
  unfold smallInverseEnergy
  have hA : HasDerivAt (fun r : ℝ => T+r • H) H 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const H).const_add T
  have ht : (T+(0 : ℝ) • H).PosDef := by simpa using hT
  simpa only [smallInverseEnergy,zero_smul,add_zero,zero_dotProduct,mul_zero,zero_sub] using
    hasDerivAt_inverseEnergy hA (hasDerivAt_const (0 : ℝ) v) ht

theorem smallInverseEnergy_first_order (T H : Mat k k) (v : Vec k) (hT : T.PosDef) :
    (fun r => smallInverseEnergy T H v r-dotProduct v (T⁻¹ *ᵥ v))
      =O[𝓝 (0 : ℝ)] (fun r : ℝ => r) := by
  simpa only [smallInverseEnergy,zero_smul,add_zero,sub_zero] using
    (smallInverseEnergy_derivative T H v hT).isBigO_sub

theorem smallInverseEnergy_cubic_remainder (T H : Mat k k) (v : Vec k) (hT : T.PosDef) :
    (fun r => r^2*smallInverseEnergy T H v r-r^2*dotProduct v (T⁻¹ *ᵥ v))
      =O[𝓝 (0 : ℝ)] (fun r : ℝ => r^3) := by
  have hh := (isBigO_refl (fun r : ℝ => r^2) (𝓝 (0 : ℝ))).mul
    (smallInverseEnergy_first_order T H v hT)
  convert hh using 1 <;> funext r <;> ring

theorem smallInverseEnergy_continuous (T H : Mat k k) (v : Vec k) (hT : T.PosDef) :
    ContinuousAt (smallInverseEnergy T H v) 0 :=
  (smallInverseEnergy_derivative T H v hT).continuousAt

theorem smallInverseEnergy_separation (T1 T0 H1 H0 : Mat k k) (v1 v0 : Vec k)
    (hT1 : T1.PosDef) (hT0 : T0.PosDef)
    (hneq : dotProduct v1 (T1⁻¹ *ᵥ v1)≠dotProduct v0 (T0⁻¹ *ᵥ v0)) :
    ∀ᶠ r : ℝ in 𝓝 0,r≠0 →
      r^2*smallInverseEnergy T1 H1 v1 r≠r^2*smallInverseEnergy T0 H0 v0 r := by
  have h0 : smallInverseEnergy T1 H1 v1 0-smallInverseEnergy T0 H0 v0 0≠0 := by
    simpa only [smallInverseEnergy,zero_smul,add_zero,sub_ne_zero] using hneq
  have hn := ((smallInverseEnergy_continuous T1 H1 v1 hT1).sub
    (smallInverseEnergy_continuous T0 H0 v0 hT0)).eventually_ne h0
  filter_upwards [hn] with r hr hr0
  exact fun he => hr (sub_eq_zero.mpr ((mul_left_cancel₀ (pow_ne_zero _ hr0)) he))

end CommodityClassification.Genericity
