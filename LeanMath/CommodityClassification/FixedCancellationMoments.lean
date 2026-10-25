module

public import LeanMath.CommodityClassification.FixedCancellationPrimitives

/-! Actual fixed-answer example with the same demand and policy at both answers. -/
@[expose] public section
noncomputable section
set_option maxHeartbeats 2400000
namespace CommodityClassification.FixedCancellation
open Matrix InputCoordinates
open ResourceCancellation (e coordinates inputs parent fine)

def family : Equilibrium.BenchmarkFamily 3 1 1 :=
  { ResourceCancellation.family with D:=demand, b:=policy, hD:=demand_posDef }

def candidate (x z : ℝ) (hx : |x|<1/4) (hz : |z|<1/4) : family.Candidate :=
  ⟨coordinates x z,ResourceCancellation.coordinates_candidate x z hx hz⟩

theorem fixed_R : family.fixedR=![![3]] := ResourceCancellation.fixed_R

theorem moment_m (x z : ℝ) : (coordinates x z).transpose *ᵥ (demand *ᵥ policy)=
    ![3*x/5+3*z/1250] := by
  rw [demand_policy,load_entries]
  ext j; fin_cases j
  norm_num [coordinates,ResourceCancellation.visible,ResourceCancellation.hidden,
    Matrix.mulVec,transpose_apply,dotProduct,Fin.sum_univ_succ]
  ring

theorem moment_K (x z : ℝ) :
    Regularity.K e e demand family.fixedR 1 (coordinates x z)=
      ![![3+12*x*z/5+3*z^2/625]] := by
  rw [Regularity.K,Regularity.adjustedDemand,fixed_R,ResourceCancellation.xi_identity]
  simp only [one_smul]
  ext i j; fin_cases i; fin_cases j
  change (1 : ℝ)*3+(∑l : Fin 3,(∑r : Fin 3,coordinates x z r 0 *
    (demand -
      (1 : Matrix (Fin 3) (Fin 3) ℝ)) r l)*coordinates x z l 0)=_
  rw [demand_entries]
  norm_num [coordinates,ResourceCancellation.visible,ResourceCancellation.hidden,
    Matrix.one_apply,Fin.sum_univ_succ]
  ring

theorem fixed_answer_moments (z : ℝ) :
    (coordinates (1/10) z).transpose *ᵥ (demand *ᵥ policy)=![(3/50)*(1+z/25)] ∧
      Regularity.K e e demand family.fixedR 1 (coordinates (1/10) z)=
        ![![3*(1+z/25)^2]] := by
  rw [moment_m,moment_K]
  constructor
  · ext i; fin_cases i; norm_num; ring
  · ext i j; fin_cases i; fin_cases j; norm_num; ring

theorem other_answer_moments (z : ℝ) :
    (coordinates 0 z).transpose *ᵥ (demand *ᵥ policy)=![3*z/1250] ∧
      Regularity.K e e demand family.fixedR 1 (coordinates 0 z)=![![3+3*z^2/625]] := by
  rw [moment_m,moment_K]
  constructor
  · ext i; fin_cases i; norm_num
  · ext i j; fin_cases i; fin_cases j; norm_num

theorem all_candidate_moments (C : family.Candidate) (x z : ℝ) (hc : C.val=coordinates x z) :
    (family.model C).m=![3*x/5+3*z/1250] ∧
      (family.model C).K=![![3+12*x*z/5+3*z^2/625]] := by
  constructor
  · change C.val.transpose *ᵥ (demand *ᵥ policy)=_
    rw [hc,moment_m]
  · rw [family.candidate_K_answer C (coordinates 0 0) (0 : Mat 3 0)]
    change Regularity.K e e demand family.fixedR 1 C.val=_
    rw [hc,moment_K]

theorem coefficient_formula (x z : ℝ) :
    family.coefficient (coordinates x z)=dotProduct policy (demand *ᵥ policy)-
      (3*x/5+3*z/1250)^2/(3+12*x*z/5+3*z^2/625) := by
  change dotProduct policy (demand *ᵥ policy)-
    dotProduct ((coordinates x z).transpose *ᵥ (demand *ᵥ policy))
      ((Regularity.K e e demand family.fixedR 1 (coordinates x z))⁻¹ *ᵥ
        ((coordinates x z).transpose *ᵥ (demand *ᵥ policy)))=_
  rw [moment_m,moment_K]
  have hh := congrArg (fun M : Mat 1 1 => dotProduct policy (demand *ᵥ policy)-
    dotProduct (![3*x/5+3*z/1250] : Vec 1) (M *ᵥ ![3*x/5+3*z/1250]))
      (ResourceCancellation.scalar_inverse (3+12*x*z/5+3*z^2/625))
  refine hh.trans ?_
  simp [dotProduct,Matrix.mulVec,div_eq_mul_inv]
  ring

theorem fixed_answer_affine_positive (z : ℝ)
    (hc : coordinates (1/10) z∈family.frame.Candidates family.p family.q family.parents family.report) :
    0<1+z/25 := by
  have hp := hc.1 0 0
  change 0<Supply.Example.frame.reconstruct e (coordinates (1/10) z) 0 0 at hp
  rw [ResourceCancellation.reconstruct_inputs] at hp
  norm_num [inputs,coordinates,ResourceCancellation.visible,ResourceCancellation.hidden] at hp
  linarith

theorem fixed_answer_coefficient (z : ℝ)
    (hc : coordinates (1/10) z∈family.frame.Candidates family.p family.q family.parents family.report) :
    family.coefficient (coordinates (1/10) z)=dotProduct policy (demand *ᵥ policy)-3/2500 := by
  rw [coefficient_formula]
  have hne : 1+z/25≠0 := ne_of_gt (fixed_answer_affine_positive z hc)
  have hden : 3+12*(1/10 : ℝ)*z/5+3*z^2/625=3*(1+z/25)^2 := by ring
  rw [hden]
  congr 1
  apply (div_eq_iff (mul_ne_zero (by norm_num) (pow_ne_zero _ hne))).mpr
  ring

end CommodityClassification.FixedCancellation
