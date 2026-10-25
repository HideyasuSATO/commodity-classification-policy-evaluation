module

public import LeanMath.CommodityClassification.AllAnswerDichotomy

/-! Separate moment preservation, independently of parent welfare identification. -/
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

theorem Data.first_moment_zero_of_preservation (a : Data n k r)
    (domain : Set (Mat r k)) (h : a.Hypotheses domain)
    (hc : ∀ Z ∈ domain, a.m (a.point Z) = a.m₀) : a.r_N = 0 := by
  apply vector_eq_zero_of_transpose_mulVec_on_open
    h.relative_dimension_positive domain h.domain_open h.origin_mem a.r_N
  intro Z hZ
  have hh := hc Z hZ
  rw [a.m_point] at hh
  exact add_left_cancel (hh.trans (add_zero a.m₀).symm)

theorem Data.loading_zero_of_K_preservation (a : Data n k r)
    (domain : Set (Mat r k)) (h : a.Hypotheses domain)
    (hc : ∀ Z ∈ domain, a.K (a.point Z) = a.K₀) : a.A_N = 0 := by
  have hI : (1 : Mat k k) ≠ 0 := by
    let i : Fin k := ⟨0,h.relative_dimension_positive⟩
    intro he
    have hi := congrFun (congrFun he i) i
    norm_num at hi
  have hAt : a.A_N.transpose = 0 := by
    apply universal_cross_zero a.A_N.transpose (1 : Mat k k) hI
    intro X
    have hcont : Continuous (fun t : ℝ => t • X) := continuous_id.smul continuous_const
    have ht : ∀ᶠ t : ℝ in 𝓝 0, t•X ∈ domain :=
      hcont.continuousAt.preimage_mem_nhds (by
        simpa only [zero_smul] using h.domain_open.mem_nhds h.origin_mem)
    have heq : (fun t : ℝ => a.K (a.point (t•X))) =ᶠ[𝓝 0] (fun _ => a.K₀) :=
      ht.mono (fun _ ht => hc _ ht)
    have hd := a.hasDerivAt_KLine h.L_symmetric X 0
    have he := (hd.congr_of_eventuallyEq heq.symm).unique (hasDerivAt_const 0 a.K₀)
    simpa only [Data.lineA_zero,Matrix.mul_one,Matrix.one_mul,transpose_one,
      transpose_transpose] using he
  simpa only [transpose_transpose,transpose_zero] using congrArg transpose hAt

theorem MomentsPreserved.hidden_moments (a : Data n k r)
    (U : Mat n s) (J : Mat s r) (Ω : Set (Mat s k))
    (hN : a.N=U*J) (hc : MomentsPreserved a U J Ω) (Y : Mat s k) (hY : Y ∈ Ω) :
    ∀ Z ∈ hiddenDomain Ω J Y,
      (a.atParent U Y).m ((a.atParent U Y).point Z) = (a.atParent U Y).m₀ ∧
      (a.atParent U Y).K ((a.atParent U Y).point Z) = (a.atParent U Y).K₀ := by
  intro Z hZ
  rw [a.hidden_translation U J hN Y Z]
  exact hc Y hY Z hZ

theorem MomentsPreserved.loading_zero (a : Data n k r)
    (U : Mat n s) (J : Mat s r) (Ω : Set (Mat s k))
    (h : AllAnswerHypotheses a U J Ω) (hc : MomentsPreserved a U J Ω)
    (Y : Mat s k) (hY : Y ∈ Ω) : (a.atParent U Y).A_N = 0 := by
  apply (a.atParent U Y).loading_zero_of_K_preservation (hiddenDomain Ω J Y)
    (h.hidden_hypotheses a U J Ω Y hY)
  intro Z hZ
  exact (hc.hidden_moments a U J Ω h.inclusion Y hY Z hZ).2

theorem MomentsPreserved.linear_coefficients (a : Data n k r)
    (U : Mat n s) (J : Mat s r) (Ω : Set (Mat s k))
    (h : AllAnswerHypotheses a U J Ω) (hc : MomentsPreserved a U J Ω) :
    a.r_N = 0 ∧ a.A_N = 0 ∧ a.N.transpose * a.L * U = 0 := by
  have h0 := h.parent.origin_mem
  have hA : a.A_N = 0 := by
    simpa only [Data.atParent,Data.atMatrix,Data.point,Data.withDirections,
      Matrix.mul_zero,add_zero,Data.A_N] using hc.loading_zero a U J Ω h 0 h0
  refine ⟨?_,hA,?_⟩
  · apply (a.atParent U 0).first_moment_zero_of_preservation (hiddenDomain Ω J 0)
      (h.hidden_hypotheses a U J Ω 0 h0)
    intro Z hZ
    exact (hc.hidden_moments a U J Ω h.inclusion 0 h0 Z hZ).1
  · apply matrix_zero_of_right_variations _ h.parent.relative_dimension_positive
    intro X
    have hcont : Continuous (fun t : ℝ => t • X) := continuous_id.smul continuous_const
    have ht : ∀ᶠ t : ℝ in 𝓝 0, t•X ∈ Ω :=
      hcont.continuousAt.preimage_mem_nhds (by
        simpa only [zero_smul] using h.parent.domain_open.mem_nhds h0)
    have heq : (fun t : ℝ => a.loading a.N ((a.withDirections U).point (t•X)))
        =ᶠ[𝓝 0] (fun _ => (0:Mat r k)) :=
      ht.mono (fun t ht => hc.loading_zero a U J Ω h (t•X) ht)
    have hd := a.hasDerivAt_loadingAlong a.N U X 0
    exact (hd.congr_of_eventuallyEq heq.symm).unique (hasDerivAt_const 0 (0:Mat r k))

end CommodityClassification.FixedAnswer
