module

public import LeanMath.CommodityClassification.SeparableFourPrimitives

/-! Exact moments for the four-good example. -/
@[expose] public section
noncomputable section
set_option maxHeartbeats 2400000
namespace CommodityClassification.SeparableFour
open Matrix InputCoordinates

theorem moment_m (η a t : ℝ) :
    (coordinates a t).transpose *ᵥ (demand η *ᵥ policy)=![-η*a/2] := by
  ext i; fin_cases i
  change (∑l : Fin 4,coordinates a t l 0 * ((demand η) *ᵥ policy) l)=_
  norm_num [demand,Matrix.mulVec_diagonal,coordinates,policy,Fin.sum_univ_succ]
  ring

theorem moment_K (η : ℝ) (hη : 0<η) (a t : ℝ) :
    Regularity.K prices quantities (demand η) (family η hη).fixedR 1 (coordinates a t)=
      ![![1+(η-1)*(a^2+t^2/2)]] := by
  rw [Regularity.K,fixed_R]
  ext i j; fin_cases i; fin_cases j
  change (1 : ℝ)*1 +
    (∑l : Fin 4,(∑r : Fin 4,coordinates a t r 0 *
      (demand η-1 • Supply.xi prices quantities) r l)*coordinates a t l 0)=_
  norm_num [demand,Supply.xi,prices,quantities,coordinates,Matrix.diagonal,Fin.sum_univ_succ]
  ring

theorem nu_exact (η : ℝ) : dotProduct policy (demand η *ᵥ policy)=5*η/2 := by
  norm_num [demand,Matrix.mulVec_diagonal,policy,dotProduct,Fin.sum_univ_succ]
  ring

theorem moment_K_positive (η : ℝ) (hη : 0<η) (a t : ℝ)
    (ha : |a|<1/4) (ht : |t|<1/4) : 0<1+(η-1)*(a^2+t^2/2) := by
  have ha2 := sq_lt_sq' (abs_lt.mp ha).1 (abs_lt.mp ha).2
  have ht2 := sq_lt_sq' (abs_lt.mp ht).1 (abs_lt.mp ht).2
  have hs : 0≤a^2+t^2/2 := by positivity
  have hηs : 0≤η*(a^2+t^2/2) := mul_nonneg hη.le hs
  nlinarith

theorem coefficient_formula (η : ℝ) (hη : 0<η) (a t : ℝ) :
    (family η hη).coefficient (coordinates a t)=
      5*η/2-(-η*a/2)^2/(1+(η-1)*(a^2+t^2/2)) := by
  change dotProduct policy (demand η *ᵥ policy)-
    dotProduct ((coordinates a t).transpose *ᵥ (demand η *ᵥ policy))
      ((Regularity.K prices quantities (demand η) (family η hη).fixedR 1 (coordinates a t))⁻¹ *ᵥ
        ((coordinates a t).transpose *ᵥ (demand η *ᵥ policy)))=_
  rw [nu_exact,moment_m,moment_K]
  have hh := congrArg (fun M : Mat 1 1 => (5*η/2)-
    dotProduct (![-η*a/2] : Vec 1) (M *ᵥ ![-η*a/2]))
      (ResourceCancellation.scalar_inverse (1+(η-1)*(a^2+t^2/2)))
  refine hh.trans ?_
  simp [dotProduct,Matrix.mulVec,div_eq_mul_inv]
  ring

theorem actual_coefficient (η : ℝ) (hη : 0<η) (a t : ℝ)
    (ha : |a|<1/4) (ht : |t|<1/4) :
    ((family η hη).model (candidate η hη a t ha ht)).lossCoefficient=
      5*η/2-(-η*a/2)^2/(1+(η-1)*(a^2+t^2/2)) := by
  rw [(family η hη).candidate_lossCoefficient]
  exact coefficient_formula η hη a t

theorem actual_moments (η : ℝ) (hη : 0<η) (a t : ℝ)
    (ha : |a|<1/4) (ht : |t|<1/4) :
    ((family η hη).model (candidate η hη a t ha ht)).m=![-η*a/2] ∧
      ((family η hη).model (candidate η hη a t ha ht)).K=![![1+(η-1)*(a^2+t^2/2)]] := by
  constructor
  · exact moment_m η a t
  · rw [(family η hη).candidate_K_answer (candidate η hη a t ha ht)
      (coordinates 0 0) (0 : Mat 4 0)]
    exact moment_K η hη a t

end CommodityClassification.SeparableFour
