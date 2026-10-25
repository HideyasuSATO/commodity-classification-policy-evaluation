module

public import LeanMath.CommodityClassification.GeneralObservationWidth

/-! Positive scaling and uniform-error transport for an arbitrary fixed observation map. -/
@[expose] public section
noncomputable section
set_option maxHeartbeats 1600000
namespace CommodityClassification.Information
variable {A B : Type*}

theorem boundedValues_smul (S : Set A) (f : A→ℝ) (hf : BoundedValues S f)
    (a : ℝ) (ha : 0≤a) : BoundedValues S (fun x => a*f x) := by
  obtain ⟨u,hu⟩ := hf.1
  obtain ⟨l,hl⟩ := hf.2
  constructor
  · refine ⟨a*u,?_⟩
    rintro y ⟨x,hx,rfl⟩
    exact mul_le_mul_of_nonneg_left (hu ⟨x,hx,rfl⟩) ha
  · refine ⟨a*l,?_⟩
    rintro y ⟨x,hx,rfl⟩
    exact mul_le_mul_of_nonneg_left (hl ⟨x,hx,rfl⟩) ha

theorem worstWidth_smul (S : Set A) (hne : S.Nonempty) (O : A→B) (f : A→ℝ)
    (hf : BoundedValues S f) (a : ℝ) (ha : 0<a) :
    worstWidth S O (fun x => a*f x)=a*worstWidth S O f := by
  have hscaled := boundedValues_smul S f hf a ha.le
  apply le_antisymm
  · apply (worstWidth_pairs_iff S hne O _ hscaled _).mpr
    intro x hx z hz hO
    rw [←mul_sub,abs_mul,abs_of_pos ha]
    exact mul_le_mul_of_nonneg_left (pair_le_worstWidth S hne O f hf x z hx hz hO) ha.le
  · have hh : worstWidth S O f≤worstWidth S O (fun x => a*f x)/a := by
      apply (worstWidth_pairs_iff S hne O f hf _).mpr
      intro x hx z hz hO
      have hp := pair_le_worstWidth S hne O (fun x => a*f x) hscaled x z hx hz hO
      rw [←mul_sub,abs_mul,abs_of_pos ha] at hp
      apply (le_div_iff₀ ha).mpr
      nlinarith
    have hp := (le_div_iff₀ ha).mp hh
    nlinarith

theorem worstWidth_div (S : Set A) (hne : S.Nonempty) (O : A→B) (f : A→ℝ)
    (hf : BoundedValues S f) (a : ℝ) (ha : 0<a) :
    worstWidth S O (fun x => f x/a)=worstWidth S O f/a := by
  simpa only [div_eq_mul_inv,mul_comm] using worstWidth_smul S hne O f hf a⁻¹ (inv_pos.mpr ha)

theorem boundedValues_uniform_error (S : Set A) (f f0 : A→ℝ) (hf0 : BoundedValues S f0)
    (e : ℝ) (he : ∀x∈S,|f x-f0 x|≤e) : BoundedValues S f := by
  obtain ⟨u,hu⟩ := hf0.1
  obtain ⟨l,hl⟩ := hf0.2
  constructor
  · refine ⟨u+e,?_⟩
    rintro y ⟨x,hx,rfl⟩
    have hp := (abs_le.mp (he x hx)).2
    have hb := hu ⟨x,hx,rfl⟩
    linarith
  · refine ⟨l-e,?_⟩
    rintro y ⟨x,hx,rfl⟩
    have hp := (abs_le.mp (he x hx)).1
    have hb := hl ⟨x,hx,rfl⟩
    linarith

theorem worstWidth_uniform_upper (S : Set A) (hne : S.Nonempty) (O : A→B)
    (f f0 : A→ℝ) (hf0 : BoundedValues S f0) (e : ℝ) (he : ∀x∈S,|f x-f0 x|≤e) :
    worstWidth S O f≤worstWidth S O f0+2*e := by
  have hf := boundedValues_uniform_error S f f0 hf0 e he
  apply (worstWidth_pairs_iff S hne O f hf _).mpr
  intro x hx z hz hO
  have hp := pair_le_worstWidth S hne O f0 hf0 x z hx hz hO
  have h1 := abs_sub_le (f x) (f0 x) (f z)
  have h2 := abs_sub_le (f0 x) (f0 z) (f z)
  have hxerr := he x hx
  have hzerr := he z hz
  rw [abs_sub_comm (f z) (f0 z)] at hzerr
  linarith

theorem worstWidth_uniform_comparison (S : Set A) (hne : S.Nonempty) (O : A→B)
    (f f0 : A→ℝ) (hf0 : BoundedValues S f0) (e : ℝ) (he : ∀x∈S,|f x-f0 x|≤e) :
    worstWidth S O f0-2*e≤worstWidth S O f ∧ worstWidth S O f≤worstWidth S O f0+2*e := by
  have hf := boundedValues_uniform_error S f f0 hf0 e he
  have hrev := worstWidth_uniform_upper S hne O f0 f hf e (fun x hx => by
    simpa only [abs_sub_comm] using he x hx)
  exact ⟨by linarith,worstWidth_uniform_upper S hne O f f0 hf0 e he⟩

end CommodityClassification.Information
