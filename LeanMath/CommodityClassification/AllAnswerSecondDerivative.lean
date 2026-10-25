module

public import LeanMath.CommodityClassification.AllAnswerSchurDerivatives

/-! The second derivative in B.2, including variation of the inverse. -/
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

theorem second_derivative_from_cross {f : ℝ → Mat r r}
    {M : ℝ → Mat r s} {E : ℝ → Mat k r} (B : Mat s s) (X : Mat s k)
    (hB : B.transpose = B) (hM0 : M 0 = 0)
    (hM : HasDerivAt M (-((E 0).transpose * X.transpose * B)) 0)
    (hE : DifferentiableAt ℝ E 0)
    (hfirst : ∀ᶠ t : ℝ in 𝓝 0,
      deriv f t = -(M t * X * E t) - (E t).transpose * X.transpose * (M t).transpose) :
    HasDerivAt (deriv f)
      ((2:ℝ) • ((E 0).transpose * X.transpose * B * X * E 0)) 0 := by
  have hleft := hasDerivAt_matrixMul
    (hasDerivAt_matrixMul hM (hasDerivAt_const 0 X)) hE.hasDerivAt
  have hright := hasDerivAt_matrixMul
    (hasDerivAt_matrixMul (hasDerivAt_transpose hE.hasDerivAt)
      (hasDerivAt_const 0 X.transpose)) (hasDerivAt_transpose hM)
  have hd := hleft.neg.sub hright
  have hc : HasDerivAt
      (fun t => -(M t * X * E t) - (E t).transpose * X.transpose * (M t).transpose)
      ((2:ℝ) • ((E 0).transpose * X.transpose * B * X * E 0)) 0 := by
    apply hd.congr_deriv
    simp only [hM0, Matrix.zero_mul, Matrix.mul_zero, add_zero, zero_add,
      transpose_zero, transpose_neg, transpose_mul, transpose_transpose, hB,
      Matrix.neg_mul, Matrix.mul_neg, neg_neg, sub_neg_eq_add, two_smul,
      Matrix.mul_assoc]
  have heq : deriv f =ᶠ[𝓝 0]
      (fun t => -(M t * X * E t) - (E t).transpose * X.transpose * (M t).transpose) := hfirst
  exact hc.congr_of_eventuallyEq heq

theorem Data.original_cross_second_derivative (a : Data n k r)
    (U : Mat n s) (domain : Set (Mat s k))
    (h : (a.withDirections U).Hypotheses domain) (X : Mat s k)
    (hcross : a.schur a.N U a.C₀ = 0) :
    HasDerivAt
      (deriv (fun t : ℝ => a.schur a.N a.N ((a.withDirections U).point (t • X))))
      ((2:ℝ) • ((a.K₀⁻¹ * a.A_N.transpose).transpose * X.transpose *
        a.schur U U a.C₀ * X * (a.K₀⁻¹ * a.A_N.transpose))) 0 := by
  let c : ℝ → Mat n k := fun t => (a.withDirections U).point (t • X)
  let M : ℝ → Mat r s := fun t => a.schur a.N U (c t)
  let E : ℝ → Mat k r := fun t => (a.K (c t))⁻¹ * (a.loading a.N (c t)).transpose
  have hc0 : c 0 = a.C₀ := by simp [c, Data.point, Data.withDirections]
  have hc0' : (a.withDirections U).point ((0:ℝ) • X) = a.C₀ := hc0
  have hK : a.K₀.PosDef := (a.withDirections U).K₀_posDef domain h
  have hKc : (a.K (c 0)).PosDef := by simpa only [hc0, Data.K₀] using hK
  have hi : (a.K₀⁻¹).transpose = a.K₀⁻¹ := hK.inv.isHermitian.isSymm
  have hB := a.schur_transpose U U a.C₀ h.L_symmetric hK
  have hM0 : M 0 = 0 := by simpa only [M, hc0] using hcross
  have hMd : HasDerivAt M (-(E 0).transpose * X.transpose * a.schur U U a.C₀) 0 := by
    have hd := a.hasDerivAt_schurAlong a.N U U X 0 h.L_symmetric hKc
    apply hd.congr_deriv
    simp only [E, hc0, hc0', hcross, Matrix.zero_mul, neg_zero, zero_sub,
      transpose_mul, transpose_transpose, Matrix.neg_mul,
      Matrix.mul_assoc]
    have hki : ((a.K a.C₀)⁻¹).transpose = (a.K a.C₀)⁻¹ := hi
    rw [hki, hB]
  have hEd : DifferentiableAt ℝ E 0 := by
    have hd := hasDerivAt_matrixMul
      (hasDerivAt_matrixInverse ((a.withDirections U).hasDerivAt_KLine h.L_symmetric X 0)
        ((a.K (c 0)).isUnit_iff_isUnit_det.mp hKc.isUnit))
      (hasDerivAt_transpose (a.hasDerivAt_loadingAlong a.N U X 0))
    exact hd.differentiableAt
  have hfirst : ∀ᶠ t : ℝ in 𝓝 0,
      deriv (fun z => a.schur a.N a.N (c z)) t =
        -(M t * X * E t) - (E t).transpose * X.transpose * (M t).transpose := by
    have hc : Continuous (fun t : ℝ => t • X) := continuous_id.smul continuous_const
    have ht : ∀ᶠ t : ℝ in 𝓝 0, t • X ∈ domain :=
      hc.continuousAt.preimage_mem_nhds (by
        simpa only [zero_smul] using h.domain_open.mem_nhds h.origin_mem)
    filter_upwards [ht] with t ht
    have hkt : (a.K (c t)).PosDef := h.K_posDef _ ht
    have hkit : ((a.K (c t))⁻¹).transpose = (a.K (c t))⁻¹ := hkt.inv.isHermitian.isSymm
    have hd := (a.hasDerivAt_schurAlong a.N a.N U X t h.L_symmetric hkt).deriv
    simpa only [M, E, transpose_mul, transpose_transpose, hkit,
      Matrix.mul_assoc] using hd
  have hd := second_derivative_from_cross (a.schur U U a.C₀) X hB hM0
    (by simpa only [Matrix.neg_mul] using hMd) hEd hfirst
  simpa only [E, hc0, Data.K₀, Data.A_N, Data.loading] using hd

theorem Data.parent_schur_vanishes (a : Data n k r)
    (U : Mat n s) (domain : Set (Mat s k))
    (h : (a.withDirections U).Hypotheses domain) (hA : a.A_N ≠ 0)
    (hz : ∀ X : Mat s k, ∀ᶠ t : ℝ in 𝓝 0,
      a.schur a.N a.N ((a.withDirections U).point (t • X)) = 0) :
    a.schur U U a.C₀ = 0 := by
  have hK : a.K₀.PosDef := (a.withDirections U).K₀_posDef domain h
  have hcross := a.cross_vanishes U h.L_symmetric hK hA hz
  apply universal_quadratic_zero (a.K₀⁻¹ * a.A_N.transpose)
    (a.inverse_loading_ne_zero hK hA) (a.schur U U a.C₀)
    (a.schur_transpose U U a.C₀ h.L_symmetric hK)
  intro X
  have hd := a.original_cross_second_derivative U domain h X hcross
  have heq : (fun t : ℝ => a.schur a.N a.N ((a.withDirections U).point (t • X)))
      =ᶠ[𝓝 0] (fun _ => (0 : Mat r r)) := hz X
  have he : (2:ℝ) • ((a.K₀⁻¹ * a.A_N.transpose).transpose * X.transpose *
      a.schur U U a.C₀ * X * (a.K₀⁻¹ * a.A_N.transpose)) = 0 := by
    rw [← hd.deriv, heq.deriv.deriv_eq]
    have hc : deriv (fun _ : ℝ => (0 : Mat r r)) = (fun _ : ℝ => (0 : Mat r r)) :=
      funext (fun t => deriv_const t _)
    rw [hc]
    exact deriv_const 0 _
  exact (smul_eq_zero.mp he).resolve_left (by norm_num)

end CommodityClassification.FixedAnswer
