module
public import LeanMath.CommodityClassification.EquilibriumLocalPositivity
@[expose] public section
set_option maxHeartbeats 2400000
namespace CommodityClassification.Equilibrium
open Matrix Filter
open scoped BigOperators Topology ContDiff
variable {n : ℕ}

theorem affineDemand_contDiff (p q : Vec n) (D : Mat n n) :
    ContDiff ℝ ⊤ (affineDemand p q D) := by
  change ContDiff ℝ ⊤ (fun v => q - D *ᵥ (v-p))
  simpa only [Function.comp_def,matCLM_apply,id_eq] using
    contDiff_const.sub ((matCLM D).contDiff.comp (contDiff_id.sub contDiff_const))

noncomputable def quadraticUtility (p : Vec n) (D : Mat n n) (x : Vec n) : ℝ :=
  dotProduct p x - (1/2 : ℝ) * dotProduct x (D⁻¹ *ᵥ x)

noncomputable def quadraticSurplus (p : Vec n) (D : Mat n n) (v x : Vec n) : ℝ :=
  quadraticUtility p D x - dotProduct v x

noncomputable def quadraticChoice (p : Vec n) (D : Mat n n) (v : Vec n) : Vec n := D *ᵥ (p-v)

theorem affineDemand_eq_choice (p q v : Vec n) (D : Mat n n) :
    affineDemand p q D v = q + quadraticChoice p D v := by
  simp only [affineDemand,quadraticChoice,Matrix.mulVec_sub]
  abel

theorem quadraticChoice_foc (p v : Vec n) (D : Mat n n) (hD : D.PosDef) :
    D⁻¹ *ᵥ quadraticChoice p D v = p-v := by
  change D⁻¹ *ᵥ (D *ᵥ (p-v)) = p-v
  rw [Matrix.mulVec_mulVec,(Regularity.inverse_identities D hD).2.2,Matrix.one_mulVec]

theorem quadratic_form_derivative (M : Mat n n) (hM : M.IsSymm) (x : Vec n) :
    HasFDerivAt (fun y => dotProduct y (M *ᵥ y))
      ((2 : ℝ) • CESCost.weightedLinear (M *ᵥ x)) x := by
  have hi : HasFDerivAt (fun y : Vec n => y) (ContinuousLinearMap.id ℝ (Vec n)) x := hasFDerivAt_id x
  have hid (i : Fin n) := hasFDerivAt_pi'.mp hi i
  have hm0 : HasFDerivAt (matCLM M) (matCLM M) x := (matCLM M).hasFDerivAt
  have hm (i : Fin n) := hasFDerivAt_pi'.mp hm0 i
  have hh := HasFDerivAt.fun_sum (u := Finset.univ) (fun i _ => (hid i).mul (hm i))
  change HasFDerivAt (fun y => ∑ i, y i * (M *ᵥ y) i) _ x
  convert hh using 1
  · funext y
    simp only [Pi.mul_apply,matCLM_apply]
  · apply ContinuousLinearMap.ext
    intro v
    simp only [_root_.sum_apply,_root_.add_apply,_root_.smul_apply,smul_eq_mul,
      ContinuousLinearMap.comp_apply,ContinuousLinearMap.proj_apply,
      ContinuousLinearMap.id_apply,matCLM_apply,CESCost.weightedLinear_apply]
    simp only [Finset.sum_add_distrib]
    change 2 * dotProduct (M *ᵥ x) v = dotProduct x (M *ᵥ v) + dotProduct (M *ᵥ x) v
    rw [hM.dotProduct_mulVec_comm, dotProduct_comm v (M *ᵥ x)]
    ring

theorem quadraticUtility_derivative (p : Vec n) (D : Mat n n) (hD : D.PosDef) (x : Vec n) :
    HasFDerivAt (quadraticUtility p D) (CESCost.weightedLinear (p-D⁻¹ *ᵥ x)) x := by
  have hh := (CESCost.weightedLinear p).hasFDerivAt.sub
    ((quadratic_form_derivative D⁻¹ hD.inv.isHermitian.isSymm x).const_mul (1/2 : ℝ))
  convert hh using 1
  · funext y
    simp only [quadraticUtility,Pi.sub_apply,CESCost.weightedLinear_apply]
  · apply ContinuousLinearMap.ext
    intro v
    simp only [_root_.sub_apply,_root_.smul_apply,smul_eq_mul,CESCost.weightedLinear_apply,sub_dotProduct]
    ring

theorem quadraticSurplus_derivative (p v : Vec n) (D : Mat n n) (hD : D.PosDef) (x : Vec n) :
    HasFDerivAt (quadraticSurplus p D v) (CESCost.weightedLinear (p-D⁻¹ *ᵥ x-v)) x := by
  have hh := (quadraticUtility_derivative p D hD x).sub (CESCost.weightedLinear v).hasFDerivAt
  convert hh using 1
  · funext y
    simp only [quadraticSurplus,Pi.sub_apply,CESCost.weightedLinear_apply]
  · apply ContinuousLinearMap.ext
    intro z
    simp only [_root_.sub_apply,CESCost.weightedLinear_apply,sub_dotProduct]

theorem quadraticSurplus_stationary (p v : Vec n) (D : Mat n n) (hD : D.PosDef) :
    HasFDerivAt (quadraticSurplus p D v) (0 : Vec n →L[ℝ] ℝ) (quadraticChoice p D v) := by
  have hh := quadraticSurplus_derivative p v D hD (quadraticChoice p D v)
  have hz : p-D⁻¹ *ᵥ quadraticChoice p D v-v = 0 := by rw [quadraticChoice_foc p v D hD]; abel
  rw [hz] at hh
  convert hh using 1
  apply ContinuousLinearMap.ext
  intro z
  simp [CESCost.weightedLinear_apply]

theorem quadraticSurplus_gap (p v x : Vec n) (D : Mat n n) (hD : D.PosDef) :
    quadraticSurplus p D v (quadraticChoice p D v) - quadraticSurplus p D v x =
      (1/2 : ℝ) * dotProduct (x-quadraticChoice p D v) (D⁻¹ *ᵥ (x-quadraticChoice p D v)) := by
  have hf := quadraticChoice_foc p v D hD
  have hc : dotProduct (quadraticChoice p D v) (D⁻¹ *ᵥ x) =
      dotProduct x (p-v) := by rw [hD.inv.isHermitian.isSymm.dotProduct_mulVec_comm,hf]
  simp only [quadraticSurplus,quadraticUtility,Matrix.mulVec_sub,dotProduct_sub,sub_dotProduct,hf,hc]
  rw [dotProduct_comm x p,dotProduct_comm x v,
    dotProduct_comm (quadraticChoice p D v) p,dotProduct_comm (quadraticChoice p D v) v]
  ring

theorem quadraticSurplus_maximum (p v x : Vec n) (D : Mat n n) (hD : D.PosDef) :
    quadraticSurplus p D v x ≤ quadraticSurplus p D v (quadraticChoice p D v) := by
  have hn := hD.inv.posSemidef.dotProduct_mulVec_nonneg (x-quadraticChoice p D v)
  simp only [star_trivial] at hn
  have hg := quadraticSurplus_gap p v x D hD
  linarith

theorem quadraticSurplus_strict (p v x : Vec n) (D : Mat n n) (hD : D.PosDef)
    (hx : x ≠ quadraticChoice p D v) :
    quadraticSurplus p D v x < quadraticSurplus p D v (quadraticChoice p D v) := by
  have hn := hD.inv.dotProduct_mulVec_pos (sub_ne_zero.mpr hx)
  simp only [star_trivial] at hn
  have hg := quadraticSurplus_gap p v x D hD
  linarith

theorem affineDemand_local (p q : Vec n) (D : Mat n n) (U : Set (Vec n))
    (hU : U ∈ 𝓝 q) : ∀ᶠ v in 𝓝 p, affineDemand p q D v ∈ U := by
  have hc := (affineDemand_contDiff p q D).continuous.continuousAt (x := p)
  rw [ContinuousAt,affineDemand_base] at hc
  exact hc hU

end CommodityClassification.Equilibrium
