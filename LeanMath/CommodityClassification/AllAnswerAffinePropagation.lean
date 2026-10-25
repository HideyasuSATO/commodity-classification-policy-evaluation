module

public import LeanMath.CommodityClassification.AllAnswerLocalConstancy

/-! Affine globalization without assuming connectedness or convexity. -/
@[expose] public section
noncomputable section
namespace CommodityClassification.FixedAnswer
open Matrix Filter
open scoped BigOperators Topology
variable {n k r s : ℕ}

local instance (a b : ℕ) : NormedAddCommGroup (Mat a b) :=
  inferInstanceAs (NormedAddCommGroup (Fin a → Fin b → ℝ))
local instance (a b : ℕ) : NormedSpace ℝ (Mat a b) :=
  inferInstanceAs (NormedSpace ℝ (Fin a → Fin b → ℝ))

theorem matrix_zero_of_right_variations (M : Mat r s) (hk : 0 < k)
    (h : ∀ X : Mat s k, M * X = 0) : M = 0 := by
  let j : Fin k := ⟨0,hk⟩
  ext i a
  have hh := congrFun (congrFun (h (Matrix.single a j 1)) i) j
  simpa [Matrix.mul_apply,Matrix.single,ite_and] using hh

theorem Data.exists_nonzero_load_of_nonconstant (a : Data n k r)
    (U : Mat n s) (Ω : Set (Mat s k)) (h0 : (0:Mat s k) ∈ Ω)
    (hnc : ¬ (a.withDirections U).ConstantOn Ω) :
    ∃ Y ∈ Ω, a.m ((a.withDirections U).point Y) ≠ 0 := by
  by_contra hn
  push Not at hn
  apply hnc
  intro Y hY
  have hm0 : a.m a.C₀ = 0 := by
    simpa only [Data.point,Data.withDirections,Matrix.mul_zero,add_zero] using hn 0 h0
  change a.F ((a.withDirections U).point Y) = a.F a.C₀
  simp only [Data.F,hn Y hY,hm0,mulVec_zero,dotProduct_zero]

theorem AllAnswersIdentified.loading_zero_at_nonzero_load (a : Data n k r)
    (U : Mat n s) (J : Mat s r) (Ω : Set (Mat s k))
    (h : AllAnswerHypotheses a U J Ω) (hc : AllAnswersIdentified a U J Ω)
    (hnc : ¬ (a.withDirections U).ConstantOn Ω)
    (Y : Mat s k) (hY : Y ∈ Ω) (hm : a.m ((a.withDirections U).point Y) ≠ 0) :
    (a.atParent U Y).A_N = 0 := by
  by_contra hA
  exact hnc (hc.parent_constant_of_nonzero_loading a U J Ω h Y hY hm hA)

theorem AllAnswersIdentified.affine_loading_coefficients_zero (a : Data n k r)
    (U : Mat n s) (J : Mat s r) (Ω : Set (Mat s k))
    (h : AllAnswerHypotheses a U J Ω) (hc : AllAnswersIdentified a U J Ω)
    (hnc : ¬ (a.withDirections U).ConstantOn Ω)
    (Y : Mat s k) (hY : Y ∈ Ω) (hm : a.m ((a.withDirections U).point Y) ≠ 0) :
    a.A_N = 0 ∧ a.N.transpose * a.L * U = 0 := by
  have hAY := hc.loading_zero_at_nonzero_load a U J Ω h hnc Y hY hm
  have hS : a.N.transpose * a.L * U = 0 := by
    apply matrix_zero_of_right_variations _ h.parent.relative_dimension_positive
    intro X
    have hz : (fun t : ℝ => (a.atParent U Y).loading a.N
        (((a.atParent U Y).withDirections U).point (t•X))) =ᶠ[𝓝 0]
        (fun _ => (0:Mat r k)) := by
      filter_upwards [a.nonzero_neighborhood_along_parent U Ω h.parent.domain_open Y hY hm X] with t ht
      rw [a.parent_translation U Y (t • X)]
      exact hc.loading_zero_at_nonzero_load a U J Ω h hnc (Y+t•X) ht.1 ht.2
    have hd := (a.atParent U Y).hasDerivAt_loadingAlong a.N U X 0
    exact (hd.congr_of_eventuallyEq hz.symm).unique (hasDerivAt_const 0 (0:Mat r k))
  refine ⟨?_,hS⟩
  change a.N.transpose * a.L * (a.C₀ + U*Y) = 0 at hAY
  rw [Matrix.mul_add,← Matrix.mul_assoc,hS,Matrix.zero_mul,add_zero] at hAY
  exact hAY

theorem AllAnswersIdentified.all_loading_zero (a : Data n k r)
    (U : Mat n s) (J : Mat s r) (Ω : Set (Mat s k))
    (h : AllAnswerHypotheses a U J Ω) (hc : AllAnswersIdentified a U J Ω)
    (hnc : ¬ (a.withDirections U).ConstantOn Ω) :
    ∀ Y : Mat s k, a.loading a.N ((a.withDirections U).point Y) = 0 := by
  obtain ⟨Y0,hY0,hm⟩ := a.exists_nonzero_load_of_nonconstant U Ω h.parent.origin_mem hnc
  obtain ⟨hA,hS⟩ := hc.affine_loading_coefficients_zero a U J Ω h hnc Y0 hY0 hm
  intro Y
  change a.N.transpose * a.L * (a.C₀+U*Y) = 0
  rw [Matrix.mul_add,← Matrix.mul_assoc,hS,Matrix.zero_mul,add_zero]
  exact hA

end CommodityClassification.FixedAnswer
