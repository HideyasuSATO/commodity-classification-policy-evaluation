module

public import LeanMath.CommodityClassification.FixedAnswerVariation

/-! Necessity in B.1: stationarity at nearby points and a first-order limit. -/
@[expose] public section
namespace CommodityClassification.FixedAnswer
open Matrix Filter
open scoped BigOperators Topology
variable {n k r : ℕ}

noncomputable def Data.response (a : Data n k r) (Z : Mat r k) : Vec k :=
  (a.K (a.point Z))⁻¹ *ᵥ a.m (a.point Z)

def Data.recenter (a : Data n k r) (Z : Mat r k) : Data n k r :=
  { a with C₀ := a.point Z }

theorem Data.recenter_point (a : Data n k r) (Z E : Mat r k) :
    (a.recenter Z).point E = a.point (Z+E) := by
  simp only [Data.recenter, Data.point, Matrix.mul_add]
  abel

theorem firstMoment_of_constant (a : Data n k r) (U : Set (Mat r k))
    (h : a.Hypotheses U) (hc : a.ConstantOn U) : a.r_N = a.A_N *ᵥ a.y₀ := by
  by_cases hm : a.m₀ = 0
  · have hr := (zeroLoad_constantOn_iff a U h hm).mp hc
    simp only [hr, Data.y₀, hm, mulVec_zero]
  · exact firstMoment_of_constant_nonzero a U h hc hm

theorem firstMoment_at (a : Data n k r) (U : Set (Mat r k))
    (h : a.Hypotheses U) (hc : a.ConstantOn U) (Z : Mat r k) (hZ : Z ∈ U) :
    a.r_N = (a.A_N + a.S_NN * Z) *ᵥ a.response Z := by
  let V : Set (Mat r k) := {E | Z+E ∈ U}
  have hnew : (a.recenter Z).Hypotheses V := by
    refine ⟨h.relative_dimension_positive, h.base_symmetric, h.L_symmetric,
      h.directions_independent, ?_, ?_, ?_⟩
    · exact h.domain_open.preimage (continuous_const.add continuous_id)
    · simpa [V] using hZ
    · intro E hE
      change (a.K ((a.recenter Z).point E)).PosDef
      rw [a.recenter_point]
      exact h.K_posDef _ hE
  have hcnew : (a.recenter Z).ConstantOn V := by
    intro E hE
    change a.F ((a.recenter Z).point E) = a.F (a.point Z)
    rw [a.recenter_point]
    exact (hc _ hE).trans (hc Z hZ).symm
  have hn := firstMoment_of_constant (a.recenter Z) V hnew hcnew
  have hA : (a.recenter Z).A_N = a.A_N + a.S_NN * Z := by
    simp only [Data.recenter, Data.A_N, Data.S_NN, Data.point,
      Matrix.mul_add, Matrix.mul_assoc]
  rw [hA] at hn
  exact hn

theorem Data.K_mul_response (a : Data n k r) (Z : Mat r k)
    (hK : (a.K (a.point Z)).PosDef) :
    a.K (a.point Z) *ᵥ a.response Z = a.m (a.point Z) := by
  simp only [Data.response, mulVec_mulVec, Matrix.mul_nonsing_inv _
    ((a.K (a.point Z)).isUnit_iff_isUnit_det.mp hK.isUnit), one_mulVec]

theorem Data.reduced_response (a : Data n k r) (U : Set (Mat r k))
    (h : a.Hypotheses U) (hc : a.ConstantOn U) (Z : Mat r k) (hZ : Z ∈ U) :
    a.K₀ *ᵥ a.response Z + a.A_N.transpose *ᵥ (Z *ᵥ a.response Z) = a.m₀ := by
  have hr := firstMoment_at a U h hc Z hZ
  have hk := a.K_mul_response Z (h.K_posDef Z hZ)
  have heq : a.K (a.point Z) = a.K₀ + a.A_N.transpose * Z +
      Z.transpose * (a.A_N + a.S_NN * Z) := by
    rw [a.K_point h.L_symmetric]
    simp only [Matrix.mul_add, Matrix.mul_assoc]
    abel
  rw [heq, a.m_point] at hk
  simp only [add_mulVec, ← mulVec_mulVec] at hk
  simp only [add_mulVec, ← mulVec_mulVec] at hr
  rw [← hr] at hk
  exact add_right_cancel hk

theorem Data.residual_response_zero (a : Data n k r) (U : Set (Mat r k))
    (h : a.Hypotheses U) (hc : a.ConstantOn U) (Z : Mat r k) (hZ : Z ∈ U) :
    (a.S_NN - a.A_N * a.K₀⁻¹ * a.A_N.transpose) *ᵥ (Z *ᵥ a.response Z) = 0 := by
  have hK := a.K₀_posDef U h
  have hu := a.K₀.isUnit_iff_isUnit_det.mp hK.isUnit
  have hr0 := firstMoment_of_constant a U h hc
  have hrZ := firstMoment_at a U h hc Z hZ
  have hred := a.reduced_response U h hc Z hZ
  have hy : a.y₀ = a.response Z + a.K₀⁻¹ *ᵥ (a.A_N.transpose *ᵥ (Z *ᵥ a.response Z)) := by
    rw [Data.y₀, ← hred]
    simp only [mulVec_add, mulVec_mulVec, Matrix.nonsing_inv_mul _ hu, one_mulVec]
  rw [hy, mulVec_add] at hr0
  simp only [add_mulVec, ← mulVec_mulVec] at hrZ
  have heq := hr0.symm.trans hrZ
  have hlast := add_left_cancel heq
  simp only [sub_mulVec, ← mulVec_mulVec]
  exact sub_eq_zero.mpr hlast.symm

theorem Data.continuousAt_response_zero (a : Data n k r) (hK : a.K₀.PosDef) :
    ContinuousAt a.response 0 := by
  have hp : Continuous a.point := continuous_const.add (continuous_const.matrix_mul continuous_id)
  have hk : Continuous (fun Z => a.K (a.point Z)) :=
    continuous_const.add ((hp.matrix_transpose.matrix_mul continuous_const).matrix_mul hp)
  have hm : Continuous (fun Z => a.m (a.point Z)) :=
    hp.matrix_transpose.matrix_mulVec continuous_const
  have hi : ContinuousAt (fun M : Mat k k => M⁻¹) a.K₀ := by
    apply continuousAt_matrix_inv
    have hdet : a.K₀.det ≠ 0 := isUnit_iff_ne_zero.mp (a.K₀.isUnit_iff_isUnit_det.mp hK.isUnit)
    rw [Ring.inverse_eq_inv']
    exact continuousAt_inv₀ hdet
  have hi' : ContinuousAt (fun Z => (a.K (a.point Z))⁻¹) 0 := by
    exact hi.comp_of_eq (hk.continuousAt (x := (0 : Mat r k)))
      (by simp [Data.point, Data.K₀])
  have hmul : Continuous (fun p : Mat k k × Vec k => p.1 *ᵥ p.2) :=
    continuous_fst.matrix_mulVec continuous_snd
  exact hmul.continuousAt.comp' (hi'.prodMk hm.continuousAt)

theorem secondMoment_of_constant_nonzero (a : Data n k r) (U : Set (Mat r k))
    (h : a.Hypotheses U) (hc : a.ConstantOn U) (hm : a.m₀ ≠ 0) :
    a.S_NN = a.A_N * a.K₀⁻¹ * a.A_N.transpose := by
  let M := a.S_NN - a.A_N * a.K₀⁻¹ * a.A_N.transpose
  have hK := a.K₀_posDef U h
  have hlim : ∀ E : Mat r k, M *ᵥ (E *ᵥ a.y₀) = 0 := by
    intro E
    have ht : Continuous (fun t : ℝ => t • E) :=
      continuous_pi fun i => continuous_pi fun j => continuous_id.mul continuous_const
    have hresp : ContinuousAt (fun t : ℝ => a.response (t • E)) 0 := by
      exact (a.continuousAt_response_zero hK).comp_of_eq
        (ht.continuousAt (x := (0:ℝ))) (zero_smul ℝ E)
    have hcE : Continuous (fun v : Vec k => M *ᵥ (E *ᵥ v)) :=
      continuous_const.matrix_mulVec (continuous_const.matrix_mulVec continuous_id)
    have hconv : Tendsto (fun t : ℝ => M *ᵥ (E *ᵥ a.response (t • E)))
        (𝓝[≠] 0) (𝓝 (M *ᵥ (E *ᵥ a.y₀))) := by
      have hh := (hcE.continuousAt.comp' hresp).tendsto
      have hh' : Tendsto (fun t : ℝ => M *ᵥ (E *ᵥ a.response (t • E)))
          (𝓝 0) (𝓝 (M *ᵥ (E *ᵥ a.y₀))) := by
        simpa [Data.response, Data.point, Data.y₀, Data.m₀, Data.K₀] using hh
      exact hh'.mono_left inf_le_left
    have htU : ∀ᶠ t : ℝ in 𝓝 0, t • E ∈ U :=
      ht.continuousAt.preimage_mem_nhds (by simpa using h.domain_open.mem_nhds h.origin_mem)
    have heq : ∀ᶠ t : ℝ in 𝓝[≠] 0, M *ᵥ (E *ᵥ a.response (t • E)) = 0 := by
      filter_upwards [htU.filter_mono inf_le_left, self_mem_nhdsWithin] with t htU htne
      have ht0 : t ≠ 0 := htne
      have hz := a.residual_response_zero U h hc (t • E) htU
      change M *ᵥ ((t • E) *ᵥ a.response (t • E)) = 0 at hz
      rw [smul_mulVec, mulVec_smul] at hz
      exact (smul_eq_zero.mp hz).resolve_left ht0
    have heq' : (fun t : ℝ => M *ᵥ (E *ᵥ a.response (t • E))) =ᶠ[𝓝[≠] 0]
        (fun _ => (0 : Vec r)) := heq
    exact tendsto_nhds_unique hconv (Filter.Tendsto.congr' heq'.symm tendsto_const_nhds)
  have hz : ∀ u : Vec r, M *ᵥ u = 0 := by
    intro u
    obtain ⟨E,hE⟩ := mulVec_surjective_in_matrix a.y₀ (a.y₀_ne_zero hK hm) u
    simpa only [hE] using hlim E
  have hM : M = 0 := by
    apply Matrix.ext
    intro i j
    have he := congrFun (hz (Pi.single j 1)) i
    simpa only [mulVec_single_one, col_apply, Pi.zero_apply, Matrix.zero_apply] using he
  exact sub_eq_zero.mp hM

end CommodityClassification.FixedAnswer
