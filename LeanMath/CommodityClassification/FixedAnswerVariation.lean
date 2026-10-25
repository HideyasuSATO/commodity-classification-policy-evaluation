module

public import LeanMath.CommodityClassification.FixedAnswerCongruence
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring

/-! First-variation necessity via the quadratic variational inequality. -/
public section
namespace CommodityClassification.FixedAnswer
open Matrix Filter
open scoped BigOperators Topology
variable {n k r : ℕ}

theorem Data.K₀_mul_y₀ (a : Data n k r) (hK : a.K₀.PosDef) :
    a.K₀ *ᵥ a.y₀ = a.m₀ := by
  simp only [Data.y₀, mulVec_mulVec,
    Matrix.mul_nonsing_inv _ (a.K₀.isUnit_iff_isUnit_det.mp hK.isUnit), one_mulVec]

theorem Data.y₀_ne_zero (a : Data n k r) (hK : a.K₀.PosDef) (hm : a.m₀ ≠ 0) :
    a.y₀ ≠ 0 := by
  intro hy
  apply hm
  rw [← a.K₀_mul_y₀ hK, hy, mulVec_zero]

theorem inverseEnergy_variational_bound (K : Mat k k) (hK : K.PosDef) (m y : Vec k) :
    0 ≤ dotProduct m (K⁻¹ *ᵥ m) - 2 * dotProduct m y + dotProduct y (K *ᵥ y) := by
  let z := K⁻¹ *ᵥ m
  have hz : K *ᵥ z = m := by
    simp only [z, mulVec_mulVec, Matrix.mul_nonsing_inv _
      (K.isUnit_iff_isUnit_det.mp hK.isUnit), one_mulVec]
  have hcross := hK.isHermitian.isSymm.dotProduct_mulVec_comm (x := z) (y := y)
  have hnonneg : 0 ≤ dotProduct (y-z) (K *ᵥ (y-z)) := by
    simpa using hK.posSemidef.dotProduct_mulVec_nonneg (y-z)
  simp only [mulVec_sub, dotProduct_sub, sub_dotProduct, hz] at hnonneg hcross
  have hmy := dotProduct_comm y m
  have hmz := dotProduct_comm z m
  change 0 ≤ dotProduct m z - 2 * dotProduct m y + dotProduct y (K *ᵥ y)
  linarith

/-- A scalar quadratic nonnegative around zero has no linear term. -/
theorem quadratic_linear_coefficient_zero (s g : ℝ)
    (h : ∀ᶠ t : ℝ in 𝓝 0, 0 ≤ t*t*s - 2*t*g) : g = 0 := by
  have hc : Continuous (fun t : ℝ => t*s-2*g) :=
    (continuous_id.mul continuous_const).sub continuous_const
  have ht : Tendsto (fun t : ℝ => t*s-2*g) (𝓝 0) (𝓝 (-2*g)) := by
    simpa only [zero_mul, zero_sub, neg_mul] using hc.tendsto (0:ℝ)
  have hpos : 0 ≤ -2*g := ge_of_tendsto (ht.mono_left inf_le_left :
      Tendsto _ (𝓝[>] (0:ℝ)) _) (by
    filter_upwards [h.filter_mono inf_le_left, self_mem_nhdsWithin] with t ht htpos
    have hp : 0 < t := htpos
    apply nonneg_of_mul_nonneg_left (b := t) _ hp
    nlinarith [ht])
  have hneg : -2*g ≤ 0 := le_of_tendsto (ht.mono_left inf_le_left :
      Tendsto _ (𝓝[<] (0:ℝ)) _) (by
    filter_upwards [h.filter_mono inf_le_left, self_mem_nhdsWithin] with t ht htneg
    have hn : t < 0 := htneg
    apply nonpos_of_mul_nonneg_left (b := t) _ hn
    nlinarith [ht])
  linarith

theorem mulVec_surjective_in_matrix (v : Vec k) (hv : v ≠ 0) (u : Vec r) :
    ∃ E : Mat r k, E *ᵥ v = u := by
  have hvv : dotProduct v v ≠ 0 := by
    simpa using hv
  refine ⟨(dotProduct v v)⁻¹ • vecMulVec u v, ?_⟩
  simp only [smul_mulVec, vecMulVec_mulVec, op_smul_eq_smul, smul_smul]
  rw [inv_mul_cancel₀ hvv, one_smul]

theorem Data.variational_gap (a : Data n k r) (hL : a.L.transpose = a.L)
    (hK : a.K₀.PosDef) (Z : Mat r k) :
    a.F a.C₀ - 2 * dotProduct (a.m (a.point Z)) a.y₀ +
      dotProduct a.y₀ (a.K (a.point Z) *ᵥ a.y₀) =
    -2 * dotProduct (Z *ᵥ a.y₀) (a.r_N - a.A_N *ᵥ a.y₀) +
      dotProduct (Z *ᵥ a.y₀) (a.S_NN *ᵥ (Z *ᵥ a.y₀)) := by
  have hy := a.K₀_mul_y₀ hK
  change dotProduct a.m₀ a.y₀ - 2 * dotProduct (a.m (a.point Z)) a.y₀ + _ = _
  rw [a.m_point, a.K_point hL]
  simp only [add_mulVec, ← mulVec_mulVec, add_dotProduct, dotProduct_add, dotProduct_sub, hy]
  rw [dotProduct_comm (Z.transpose *ᵥ a.r_N) a.y₀,
    dotProduct_transpose_mulVec, dotProduct_transpose_mulVec,
    dotProduct_transpose_mulVec, dotProduct_transpose_mulVec]
  have h1 := dotProduct_comm a.y₀ a.m₀
  have h2 := dotProduct_comm a.r_N (Z *ᵥ a.y₀)
  have h3 := dotProduct_comm (a.A_N *ᵥ a.y₀) (Z *ᵥ a.y₀)
  have h4 := dotProduct_comm (a.S_NN *ᵥ (Z *ᵥ a.y₀)) (Z *ᵥ a.y₀)
  linarith

theorem firstMoment_of_constant_nonzero (a : Data n k r) (U : Set (Mat r k))
    (h : a.Hypotheses U) (hc : a.ConstantOn U) (hm : a.m₀ ≠ 0) :
    a.r_N = a.A_N *ᵥ a.y₀ := by
  have hK := a.K₀_posDef U h
  have hy := a.y₀_ne_zero hK hm
  let g := a.r_N - a.A_N *ᵥ a.y₀
  have hg : ∀ E : Mat r k, dotProduct (E *ᵥ a.y₀) g = 0 := by
    intro E
    apply quadratic_linear_coefficient_zero (dotProduct (E *ᵥ a.y₀)
      (a.S_NN *ᵥ (E *ᵥ a.y₀)))
    have hcont : Continuous (fun t : ℝ => t • E) :=
      continuous_pi fun i => continuous_pi fun j => continuous_id.mul continuous_const
    have htU : ∀ᶠ t : ℝ in 𝓝 0, t • E ∈ U :=
      hcont.continuousAt.preimage_mem_nhds (by simpa using h.domain_open.mem_nhds h.origin_mem)
    filter_upwards [htU] with t ht
    have hb := inverseEnergy_variational_bound (a.K (a.point (t • E)))
      (h.K_posDef _ ht) (a.m (a.point (t • E))) a.y₀
    change 0 ≤ a.F (a.point (t • E)) - _ + _ at hb
    rw [hc _ ht, a.variational_gap h.L_symmetric hK] at hb
    simp only [smul_mulVec, mulVec_smul, smul_dotProduct, dotProduct_smul,
      smul_eq_mul] at hb
    change 0 ≤ -2 * (t * dotProduct (E *ᵥ a.y₀) g) +
      t * (t * dotProduct (E *ᵥ a.y₀) (a.S_NN *ᵥ (E *ᵥ a.y₀))) at hb
    nlinarith
  obtain ⟨E,hE⟩ := mulVec_surjective_in_matrix a.y₀ hy g
  have hgg := hg E
  rw [hE] at hgg
  have : g = 0 := by simpa using hgg
  exact sub_eq_zero.mp this

end CommodityClassification.FixedAnswer
