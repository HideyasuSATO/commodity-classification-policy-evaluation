module

public import LeanMath.CommodityClassification.NormalizedWidthStability

/-! Value functions agreeing on the actual candidate domain give identical reports and widths. -/
@[expose] public section
noncomputable section
namespace CommodityClassification.Information
variable {A B : Type*}

theorem values_congr (S : Set A) (O : A→B) (f g : A→ℝ)
    (h : ∀x∈S,f x=g x) (y : B) : values S O f y=values S O g y := by
  apply Set.image_congr
  intro x hx
  exact h x hx.1

theorem worstWidth_congr (S : Set A) (O : A→B) (f g : A→ℝ)
    (h : ∀x∈S,f x=g x) : worstWidth S O f=worstWidth S O g := by
  unfold worstWidth answerWidth
  simp only [values_congr S O f g h]

theorem boundedValues_congr (S : Set A) (f g : A→ℝ)
    (h : ∀x∈S,f x=g x) : BoundedValues S f ↔ BoundedValues S g := by
  have he : f '' S=g '' S := Set.image_congr h
  unfold BoundedValues
  rw [he]

end CommodityClassification.Information
