module
public import LeanMath.CommodityClassification.CESProduction
@[expose] public section
namespace CommodityClassification.Production
open Matrix
open scoped BigOperators
variable {f : ℕ}
abbrev Vec (f : ℕ) := Fin f → ℝ

/-- Nonnegative-output fixed-input technology with free input disposal. -/
def FixedFeasible (a : Vec f) (y : ℝ) (x : Vec f) : Prop :=
  0 ≤ y ∧ (∀j, 0 ≤ x j) ∧ ∀j, y*a j ≤ x j

theorem fixed_iff {a x : Vec f} {y : ℝ} (ha : ∀j, 0 ≤ a j) :
    FixedFeasible a y x ↔ 0 ≤ y ∧ ∀j, y*a j ≤ x j := by
  constructor
  · intro h; exact ⟨h.1,h.2.2⟩
  · rintro ⟨hy,hx⟩
    exact ⟨hy,fun j => (mul_nonneg hy (ha j)).trans (hx j),hx⟩

theorem fixed_zero (a : Vec f) : FixedFeasible a 0 0 := by
  refine ⟨le_rfl, fun j => le_rfl, ?_⟩; intro j; simp

theorem fixed_scale {a x : Vec f} {y s : ℝ} (h : FixedFeasible a y x) (hs : 0 ≤ s) :
    FixedFeasible a (s*y) (s • x) := by
  refine ⟨mul_nonneg hs h.1, fun j => mul_nonneg hs (h.2.1 j), ?_⟩
  intro j
  simpa only [Pi.smul_apply,smul_eq_mul,mul_assoc] using mul_le_mul_of_nonneg_left (h.2.2 j) hs

theorem fixed_add {a x u : Vec f} {y z : ℝ} (h : FixedFeasible a y x) (h' : FixedFeasible a z u) :
    FixedFeasible a (y+z) (x+u) := by
  refine ⟨add_nonneg h.1 h'.1, fun j => add_nonneg (h.2.1 j) (h'.2.1 j), ?_⟩
  intro j
  simpa only [add_mul,Pi.add_apply] using add_le_add (h.2.2 j) (h'.2.2 j)

theorem fixed_convex (a : Vec f) : Convex ℝ {p : ℝ × Vec f | FixedFeasible a p.1 p.2} := by
  intro z hz u hu s t hs ht hst
  exact fixed_add (fixed_scale hz hs) (fixed_scale hu ht)

theorem fixed_disposal {a x u : Vec f} {y z : ℝ} (ha : ∀j, 0 ≤ a j)
    (h : FixedFeasible a y x) (hz : 0 ≤ z) (hzy : z ≤ y) (hxu : ∀j, x j ≤ u j) :
    FixedFeasible a z u :=
  ⟨hz, fun j => (h.2.1 j).trans (hxu j), fun j =>
    (mul_le_mul_of_nonneg_right hzy (ha j)).trans ((h.2.2 j).trans (hxu j))⟩

theorem fixed_plan {a : Vec f} (ha : ∀j, 0 ≤ a j) {y : ℝ} (hy : 0 ≤ y) :
    FixedFeasible a y (y • a) := ⟨hy,fun j => mul_nonneg hy (ha j),fun _ => le_rfl⟩

theorem fixed_cost_lower {a x w : Vec f} {y : ℝ} (hw : ∀j, 0 ≤ w j)
    (h : FixedFeasible a y x) : y*dotProduct a w ≤ dotProduct w x := by
  calc
    _ = dotProduct w (y • a) := by rw [dotProduct_smul, smul_eq_mul,dotProduct_comm]
    _ ≤ _ := Finset.sum_le_sum (fun j _ => mul_le_mul_of_nonneg_left (h.2.2 j) (hw j))

theorem fixed_cost_isLeast {a w : Vec f} (ha : ∀j, 0 ≤ a j) (hw : ∀j, 0 ≤ w j)
    {y : ℝ} (hy : 0 ≤ y) :
    IsLeast {e : ℝ | ∃x, FixedFeasible a y x ∧ dotProduct w x=e} (y*dotProduct a w) := by
  refine ⟨⟨y • a,fixed_plan ha hy,?_⟩,?_⟩
  · rw [dotProduct_smul,smul_eq_mul,dotProduct_comm]
  · rintro e ⟨x,h,rfl⟩; exact fixed_cost_lower hw h

theorem fixed_profit_nonpos {a w x : Vec f} (hw : ∀j, 0 ≤ w j) {y : ℝ}
    (h : FixedFeasible a y x) : dotProduct a w*y-dotProduct w x ≤ 0 := by
  have hh := fixed_cost_lower hw h
  nlinarith

theorem fixed_profit_zero (a w : Vec f) (y : ℝ) :
    dotProduct a w*y-dotProduct w (y • a) = 0 := by
  rw [dotProduct_smul,smul_eq_mul,dotProduct_comm]; ring

theorem numeraire_certificate {a w : Vec f} (ha : ∀j, 0 ≤ a j) (hw : ∀j, 0 ≤ w j)
    (hn : dotProduct a w=1) {y : ℝ} (hy : 0 ≤ y) :
    FixedFeasible a y (y • a) ∧ dotProduct w (y • a)=y ∧
    (∀z x, FixedFeasible a z x → z-dotProduct w x ≤ 0) ∧
    y-dotProduct w (y • a)=0 := by
  have he : dotProduct w (y • a)=y := by rw [dotProduct_smul,smul_eq_mul,dotProduct_comm,hn,mul_one]
  refine ⟨fixed_plan ha hy, he, ?_, by rw [he]; ring⟩
  intro z x h
  simpa only [hn,one_mul] using fixed_profit_nonpos hw h

end CommodityClassification.Production
