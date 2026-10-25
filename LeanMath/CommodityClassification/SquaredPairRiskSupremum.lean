module

public import LeanMath.CommodityClassification.TwoPointPredictionRisk

/-! Squared pair risks have the width-squared sharp supremum, without attained endpoints. -/
@[expose] public section
noncomputable section
set_option maxHeartbeats 1800000
namespace CommodityClassification.Information
variable {A : Type*}

def pairRisks (S : Set A) (f : A→ℝ) : Set ℝ :=
  {r | ∃x∈S,∃y∈S,(f x-f y)^2/4=r}

theorem pairRisks_zero (S : Set A) (hne : S.Nonempty) (f : A→ℝ) : 0∈pairRisks S f := by
  obtain ⟨x,hx⟩ := hne
  exact ⟨x,hx,x,hx,by simp⟩

theorem pairRisks_upper (S : Set A) (hne : S.Nonempty) (f : A→ℝ) (hf : BoundedValues S f)
    (x y : A) (hx : x∈S) (hy : y∈S) : (f x-f y)^2/4≤(setWidth (f '' S))^2/4 := by
  have hW := setWidth_nonneg _ (hne.image f) hf.1 hf.2
  have hh := pair_le_setWidth (f '' S) hf.1 hf.2 _ _ ⟨x,hx,rfl⟩ ⟨y,hy,rfl⟩
  have hm := mul_nonneg (sub_nonneg.mpr hh) (add_nonneg hW (abs_nonneg (f x-f y)))
  nlinarith [sq_abs (f x-f y)]

theorem pairRisks_isLUB (S : Set A) (hne : S.Nonempty) (f : A→ℝ) (hf : BoundedValues S f) :
    IsLUB (pairRisks S f) ((setWidth (f '' S))^2/4) := by
  constructor
  · rintro r ⟨x,hx,y,hy,rfl⟩
    exact pairRisks_upper S hne f hf x y hx hy
  · intro B hB
    have hB0 : 0≤B := hB (pairRisks_zero S hne f)
    have hW0 := setWidth_nonneg _ (hne.image f) hf.1 hf.2
    have hW : setWidth (f '' S)≤2*Real.sqrt B := by
      apply (setWidth_le_iff _ (hne.image f) hf.1 hf.2 _).mpr
      rintro a ⟨x,hx,rfl⟩ b ⟨y,hy,rfl⟩
      have hh := hB (show (f x-f y)^2/4∈pairRisks S f from ⟨x,hx,y,hy,rfl⟩)
      nlinarith [sq_abs (f x-f y),abs_nonneg (f x-f y),Real.sq_sqrt hB0,Real.sqrt_nonneg B]
    have hm := mul_nonneg (sub_nonneg.mpr hW)
      (add_nonneg (mul_nonneg (by norm_num : (0:ℝ)≤2) (Real.sqrt_nonneg B)) hW0)
    nlinarith [Real.sq_sqrt hB0]

theorem pairRisks_approximate (S : Set A) (hne : S.Nonempty) (f : A→ℝ) (hf : BoundedValues S f)
    (eps : ℝ) (hε : 0<eps) :
    ∃x∈S,∃y∈S,(setWidth (f '' S))^2/4-eps<(f x-f y)^2/4 := by
  by_contra h
  push Not at h
  have hu : (setWidth (f '' S))^2/4-eps∈upperBounds (pairRisks S f) := by
    rintro r ⟨x,hx,y,hy,rfl⟩
    exact h x hx y hy
  have hh := (pairRisks_isLUB S hne f hf).2 hu
  linarith

end CommodityClassification.Information
