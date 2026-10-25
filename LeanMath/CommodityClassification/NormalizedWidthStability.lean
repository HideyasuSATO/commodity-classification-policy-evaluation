module

public import LeanMath.CommodityClassification.ObservationWidthTransform

/-! Exact self-normalized width bounds under uniform coefficient error. -/
@[expose] public section
noncomputable section
set_option maxHeartbeats 1800000
namespace CommodityClassification.Information
variable {A B : Type*}

theorem self_normalized_width_comparison (S : Set A) (hne : S.Nonempty) (O : A→B)
    (f f0 : A→ℝ) (hf0 : BoundedValues S f0)
    (e ν0 ν alo ahi : ℝ) (hν0 : 0<ν0) (hν : 0<ν) (ha : 0<alo) (hb : 0<ahi)
    (hlo : alo*ν0≤ν) (hhi : ν≤ahi*ν0)
    (he : ∀x∈S,|f x-f0 x|≤e*ν0) :
    max (worstWidth S O (fun x => f0 x/ν0)-2*e) 0/ahi≤worstWidth S O (fun x => f x/ν) ∧
      worstWidth S O (fun x => f x/ν)≤(worstWidth S O (fun x => f0 x/ν0)+2*e)/alo := by
  have hf := boundedValues_uniform_error S f f0 hf0 (e*ν0) he
  have herr := worstWidth_uniform_comparison S hne O f f0 hf0 (e*ν0) he
  have hW := worstWidth_nonneg S hne O f hf
  rw [worstWidth_div S hne O f hf ν hν,worstWidth_div S hne O f0 hf0 ν0 hν0]
  constructor
  · by_cases hpos : 0≤worstWidth S O f0/ν0-2*e
    · rw [max_eq_left hpos]
      have hnum : 0≤worstWidth S O f0-2*e*ν0 := by
        have hh := mul_nonneg hpos hν0.le
        have heq : (worstWidth S O f0/ν0-2*e)*ν0=worstWidth S O f0-2*e*ν0 := by
          field_simp
        rwa [heq] at hh
      calc
        (worstWidth S O f0/ν0-2*e)/ahi=(worstWidth S O f0-2*e*ν0)/(ahi*ν0) := by
          field_simp
        _≤(worstWidth S O f0-2*e*ν0)/ν := div_le_div_of_nonneg_left hnum hν hhi
        _≤worstWidth S O f/ν := div_le_div_of_nonneg_right (by nlinarith [herr.1]) hν.le
    · rw [max_eq_right (le_of_not_ge hpos),zero_div]
      exact div_nonneg hW hν.le
  · have hnum : 0≤worstWidth S O f0+2*e*ν0 := by nlinarith [herr.2]
    calc
      worstWidth S O f/ν≤(worstWidth S O f0+2*e*ν0)/ν :=
        div_le_div_of_nonneg_right (by nlinarith [herr.2]) hν.le
      _≤(worstWidth S O f0+2*e*ν0)/(alo*ν0) :=
        div_le_div_of_nonneg_left hnum (mul_pos ha hν0) hlo
      _=(worstWidth S O f0/ν0+2*e)/alo := by
        field_simp

end CommodityClassification.Information
