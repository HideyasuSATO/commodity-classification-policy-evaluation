module

public import LeanMath.CommodityClassification.UntaxedNestPrimitives

/-! Exact rational coefficients of the untaxed-nest example. -/
@[expose] public section
noncomputable section
set_option maxHeartbeats 2000000
namespace CommodityClassification.UntaxedNest
open Matrix InputCoordinates

theorem moment_m (t : ℝ) : (coordinates t).transpose *ᵥ (demand *ᵥ policy)=![1/8] := by
  ext i;fin_cases i
  change (∑l : Fin 4,coordinates t l 0*(demand *ᵥ policy) l)=1/8
  norm_num [coordinates,demand,policy,Matrix.mulVec,dotProduct,Fin.sum_univ_succ]

theorem moment_K (t : ℝ) :
    Regularity.K prices quantities demand family.fixedR 1 (coordinates t)=![![1+t^2/2]] := by
  rw [Regularity.K,fixed_R]
  ext i j;fin_cases i;fin_cases j
  change (1 : ℝ)*1 + (∑l : Fin 4,(∑r : Fin 4,coordinates t r 0 *
    (demand-1 • Supply.xi prices quantities) r l)*coordinates t l 0)=_
  simp only [Matrix.sub_apply,Matrix.smul_apply,smul_eq_mul]
  norm_num [demand,Supply.xi,prices,quantities,coordinates,Matrix.diagonal,Fin.sum_univ_succ,
    Matrix.sub_apply,Matrix.of_apply]
  ring

theorem nu_exact : dotProduct policy (demand *ᵥ policy)=1/2 := by
  norm_num [demand,policy,Matrix.mulVec,dotProduct,Fin.sum_univ_succ]

theorem coefficient_formula (t : ℝ) :
    family.coefficient (coordinates t)=1/2-(1/8)^2/(1+t^2/2) := by
  change dotProduct policy (demand *ᵥ policy)-dotProduct ((coordinates t).transpose *ᵥ (demand *ᵥ policy))
    ((Regularity.K prices quantities demand family.fixedR 1 (coordinates t))⁻¹ *ᵥ
      ((coordinates t).transpose *ᵥ (demand *ᵥ policy)))=_
  rw [nu_exact,moment_m,moment_K,ResourceCancellation.scalar_inverse]
  simp [dotProduct,Matrix.mulVec,div_eq_mul_inv]
  ring

theorem actual_moments (t : ℝ) (ht : |t|≤1/4) :
    (family.model (candidate t ht)).m=![1/8] ∧
    (family.model (candidate t ht)).K=![![1+t^2/2]] := by
  constructor
  · exact moment_m t
  · change Regularity.K prices quantities demand (family.model (candidate t ht)).R 1 (coordinates t)=_
    rw [family.candidate_R_fixed]
    exact moment_K t

theorem actual_coefficient (t : ℝ) (ht : |t|≤1/4) :
    (family.model (candidate t ht)).lossCoefficient=1/2-(1/8)^2/(1+t^2/2) := by
  rw [family.candidate_lossCoefficient]
  exact coefficient_formula t

theorem printed_coefficients : family.coefficient (coordinates 0)=31/64 ∧
    family.coefficient (coordinates (1/4))=16/33 ∧
    family.coefficient (coordinates (1/4))-family.coefficient (coordinates 0)=1/2112 := by
  rw [coefficient_formula,coefficient_formula]
  norm_num

end CommodityClassification.UntaxedNest
