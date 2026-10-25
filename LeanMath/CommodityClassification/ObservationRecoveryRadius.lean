module

public import LeanMath.CommodityClassification.RealSetRecoveryRadius

/-! A single report-dependent midpoint predictor attains half the ex ante width. -/
@[expose] public section
noncomputable section
namespace CommodityClassification.Information
variable {A B : Type*}

def midpointPredictor (S : Set A) (O : A→B) (f : A→ℝ) (y : B) : ℝ :=
  valueMidpoint (values S O f y)

def UniformErrorBound (S : Set A) (O : A→B) (f : A→ℝ) (a : B→ℝ) (r : ℝ) : Prop :=
  ∀x∈S,|a (O x)-f x|≤r

def recoveryRadius (S : Set A) (O : A→B) (f : A→ℝ) : ℝ :=
  sInf {r | ∃a : B→ℝ,UniformErrorBound S O f a r}

theorem midpointPredictor_error (S : Set A) (O : A→B) (f : A→ℝ) (hf : BoundedValues S f)
    (x : A) (hx : x∈S) :
    |midpointPredictor S O f (O x)-f x|≤answerWidth S O f (O x)/2 :=
  midpoint_error_bound _ (hf.1.mono (values_subset S O f _))
    (hf.2.mono (values_subset S O f _)) _ ⟨x,⟨hx,rfl⟩,rfl⟩

theorem midpointPredictor_uniform (S : Set A) (hne : S.Nonempty) (O : A→B) (f : A→ℝ)
    (hf : BoundedValues S f) :
    UniformErrorBound S O f (midpointPredictor S O f) (worstWidth S O f/2) := by
  intro x hx
  apply (midpointPredictor_error S O f hf x hx).trans
  have hh := (worstWidth_le_iff S hne O f hf _).mp le_rfl x hx
  linarith

theorem uniform_error_lower (S : Set A) (hne : S.Nonempty) (O : A→B) (f : A→ℝ)
    (hf : BoundedValues S f) (a : B→ℝ) (r : ℝ) (ha : UniformErrorBound S O f a r) :
    worstWidth S O f/2≤r := by
  have hh : worstWidth S O f≤2*r := by
    apply (worstWidth_pairs_iff S hne O f hf _).mpr
    intro x hx z hz hO
    have h1 := ha x hx
    have h2 := ha z hz
    rw [hO] at h2
    have ht := abs_sub_le (f x) (a (O x)) (f z)
    rw [abs_sub_comm (f x) (a (O x))] at ht
    linarith
  linarith

theorem uniform_error_achievable_iff (S : Set A) (hne : S.Nonempty) (O : A→B) (f : A→ℝ)
    (hf : BoundedValues S f) (r : ℝ) :
    (∃a : B→ℝ,UniformErrorBound S O f a r) ↔ worstWidth S O f≤2*r := by
  constructor
  · rintro ⟨a,ha⟩
    have hh := uniform_error_lower S hne O f hf a r ha
    linarith
  · intro hh
    refine ⟨midpointPredictor S O f,?_⟩
    intro x hx
    have he := midpointPredictor_uniform S hne O f hf x hx
    linarith

theorem uniform_error_isLeast (S : Set A) (hne : S.Nonempty) (O : A→B) (f : A→ℝ)
    (hf : BoundedValues S f) :
    IsLeast {r | ∃a : B→ℝ,UniformErrorBound S O f a r} (worstWidth S O f/2) := by
  refine ⟨⟨midpointPredictor S O f,midpointPredictor_uniform S hne O f hf⟩,?_⟩
  rintro r ⟨a,ha⟩
  exact uniform_error_lower S hne O f hf a r ha

theorem recoveryRadius_eq_half_width (S : Set A) (hne : S.Nonempty) (O : A→B) (f : A→ℝ)
    (hf : BoundedValues S f) : recoveryRadius S O f=worstWidth S O f/2 :=
  (uniform_error_isLeast S hne O f hf).csInf_eq

end CommodityClassification.Information
