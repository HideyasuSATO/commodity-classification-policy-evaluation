module

public import LeanMath.CommodityClassification.FixedAnswerCongruence
public import Mathlib.Analysis.Calculus.Deriv.Inv
public import Mathlib.Analysis.Calculus.Deriv.Prod
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Calculus.Deriv.Add
public import Mathlib.Tactic.Ring

/-! Componentwise calculus for the original B.1 proof. No B.1 necessity theorem is used. -/
@[expose] public section
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
namespace CommodityClassification.FixedAnswer
open Matrix Filter
open scoped BigOperators Topology
variable {n k r : ℕ}

theorem hasDerivAt_dotProduct {f g : ℝ → Vec k} {f' g' : Vec k} {t : ℝ}
    (hf : HasDerivAt f f' t) (hg : HasDerivAt g g' t) :
    HasDerivAt (fun s => dotProduct (f s) (g s))
      (dotProduct f' (g t) + dotProduct (f t) g') t := by
  simpa only [dotProduct, Finset.sum_add_distrib, Pi.mul_apply] using
    (HasDerivAt.fun_sum (u := Finset.univ) (fun i _ =>
      (hasDerivAt_pi.mp hf i).mul (hasDerivAt_pi.mp hg i)))

theorem hasDerivAt_mulVec {A : ℝ → Mat r k} {v : ℝ → Vec k}
    {A' : Mat r k} {v' : Vec k} {t : ℝ}
    (hA : HasDerivAt A A' t) (hv : HasDerivAt v v' t) :
    HasDerivAt (fun s => A s *ᵥ v s) (A' *ᵥ v t + A t *ᵥ v') t := by
  apply hasDerivAt_pi.mpr
  intro i
  exact hasDerivAt_dotProduct (hasDerivAt_pi.mp hA i) hv

theorem hasDerivAt_matrixMul {A : ℝ → Mat n r} {B : ℝ → Mat r k}
    {A' : Mat n r} {B' : Mat r k} {t : ℝ}
    (hA : HasDerivAt A A' t) (hB : HasDerivAt B B' t) :
    HasDerivAt (fun s => A s * B s) (A' * B t + A t * B') t := by
  apply hasDerivAt_pi.mpr
  intro i
  apply hasDerivAt_pi.mpr
  intro j
  exact hasDerivAt_dotProduct (hasDerivAt_pi.mp hA i)
    (hasDerivAt_pi.mpr (fun l => hasDerivAt_pi.mp (hasDerivAt_pi.mp hB l) j))

theorem hasDerivAt_transpose {A : ℝ → Mat r k} {A' : Mat r k} {t : ℝ}
    (hA : HasDerivAt A A' t) :
    HasDerivAt (fun s => (A s).transpose) A'.transpose t := by
  exact hasDerivAt_pi.mpr (fun i => hasDerivAt_pi.mpr
    (fun j => hasDerivAt_pi.mp (hasDerivAt_pi.mp hA j) i))

theorem differentiableAt_det_entries {A : ℝ → Mat k k} {t : ℝ}
    (hA : ∀ i j, DifferentiableAt ℝ (fun s => A s i j) t) :
    DifferentiableAt ℝ (fun s => (A s).det) t := by
  simp only [Matrix.det_apply']
  fun_prop

theorem differentiableAt_inv_entries {A : ℝ → Mat k k} {t : ℝ}
    (hA : ∀ i j, DifferentiableAt ℝ (fun s => A s i j) t)
    (hu : IsUnit (A t).det) (i j : Fin k) :
    DifferentiableAt ℝ (fun s => (A s)⁻¹ i j) t := by
  have hd := differentiableAt_det_entries hA
  have hadj : DifferentiableAt ℝ (fun s => (A s).adjugate i j) t := by
    simp only [Matrix.adjugate_apply]
    apply differentiableAt_det_entries
    intro u v
    by_cases he : u = j
    · subst u
      simp only [Matrix.updateRow_self]
      exact differentiableAt_const _
    · simpa only [Matrix.updateRow_ne he] using hA u v
  simp only [Matrix.inv_def, Ring.inverse_eq_inv, Matrix.smul_apply, smul_eq_mul]
  exact (hd.inv hu.ne_zero).mul hadj

theorem differentiableAt_inverse_mulVec {A : ℝ → Mat k k} {v : ℝ → Vec k} {t : ℝ}
    (hA : DifferentiableAt ℝ A t) (hv : DifferentiableAt ℝ v t)
    (hu : IsUnit (A t).det) :
    DifferentiableAt ℝ (fun s => (A s)⁻¹ *ᵥ v s) t := by
  apply differentiableAt_pi.mpr
  intro i
  have hai : ∀ j, DifferentiableAt ℝ (fun s => (A s)⁻¹ i j) t :=
    fun j => differentiableAt_inv_entries
      (fun u v => differentiableAt_pi.mp (differentiableAt_pi.mp hA u) v) hu i j
  have hvi : ∀ j, DifferentiableAt ℝ (fun s => v s j) t :=
    differentiableAt_pi.mp hv
  change DifferentiableAt ℝ (fun s => ∑ j, (A s)⁻¹ i j * v s j) t
  exact DifferentiableAt.fun_sum (u := Finset.univ) (fun j _ => (hai j).mul (hvi j))

theorem hasDerivAt_inverse_mulVec {A : ℝ → Mat k k} {v : ℝ → Vec k}
    {A' : Mat k k} {v' : Vec k} {t : ℝ}
    (hA : HasDerivAt A A' t) (hv : HasDerivAt v v' t)
    (hu : IsUnit (A t).det) :
    HasDerivAt (fun s => (A s)⁻¹ *ᵥ v s)
      ((A t)⁻¹ *ᵥ (v' - A' *ᵥ ((A t)⁻¹ *ᵥ v t))) t := by
  let y : ℝ → Vec k := fun s => (A s)⁻¹ *ᵥ v s
  have haEntries : ∀ i j, DifferentiableAt ℝ (fun s => A s i j) t :=
    fun i j => (hasDerivAt_pi.mp (hasDerivAt_pi.mp hA i) j).differentiableAt
  have hy : DifferentiableAt ℝ y t :=
    differentiableAt_inverse_mulVec (A := A) (v := v)
      (differentiableAt_pi.mpr (fun i => differentiableAt_pi.mpr (haEntries i)))
      hv.differentiableAt hu
  have hd := differentiableAt_det_entries haEntries
  have heq : (fun s => A s *ᵥ y s) =ᶠ[𝓝 t] v := by
    filter_upwards [hd.continuousAt.eventually_ne hu.ne_zero] with s hs
    simp only [y, mulVec_mulVec,
      Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr hs), one_mulVec]
  have hprod := hasDerivAt_mulVec hA hy.hasDerivAt
  have hrel : A' *ᵥ y t + A t *ᵥ deriv y t = v' :=
    (hprod.congr_of_eventuallyEq heq.symm).unique hv
  have hsolve : deriv y t = (A t)⁻¹ *ᵥ (v' - A' *ᵥ y t) := by
    have hh : A t *ᵥ deriv y t = v' - A' *ᵥ y t := eq_sub_of_add_eq' hrel
    rw [← hh, mulVec_mulVec, Matrix.nonsing_inv_mul _ hu, one_mulVec]
  exact hy.hasDerivAt.congr_deriv hsolve

theorem hasDerivAt_inverseEnergy {A : ℝ → Mat k k} {v : ℝ → Vec k}
    {A' : Mat k k} {v' : Vec k} {t : ℝ}
    (hA : HasDerivAt A A' t) (hv : HasDerivAt v v' t)
    (hK : (A t).PosDef) :
    HasDerivAt (fun s => dotProduct (v s) ((A s)⁻¹ *ᵥ v s))
      (2 * dotProduct v' ((A t)⁻¹ *ᵥ v t) -
       dotProduct ((A t)⁻¹ *ᵥ v t) (A' *ᵥ ((A t)⁻¹ *ᵥ v t))) t := by
  have hy := hasDerivAt_inverse_mulVec hA hv
    ((A t).isUnit_iff_isUnit_det.mp hK.isUnit)
  apply (hasDerivAt_dotProduct hv hy).congr_deriv
  rw [hK.inv.isHermitian.isSymm.dotProduct_mulVec_comm
    (x := v t) (y := v' - A' *ᵥ ((A t)⁻¹ *ᵥ v t))]
  rw [sub_dotProduct, dotProduct_comm v', dotProduct_comm (A' *ᵥ ((A t)⁻¹ *ᵥ v t))]
  ring

end CommodityClassification.FixedAnswer
