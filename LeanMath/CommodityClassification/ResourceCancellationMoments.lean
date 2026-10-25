module

public import LeanMath.CommodityClassification.ResourceCancellationSupply

/-! Actual benchmark family and exact welfare moments for arbitrary parameters. -/
@[expose] public section
noncomputable section
set_option maxHeartbeats 2400000
namespace CommodityClassification.ResourceCancellation
open Matrix InputCoordinates Equilibrium

def family : BenchmarkFamily 3 1 1 where
  frame := Supply.Example.frame
  p := e
  q := e
  b := policy
  D := demand
  sigma := 1
  parents := parent
  report := 0
  reference := coordinates 0 0
  reference_mem := coordinates_candidate 0 0 (by norm_num) (by norm_num)
  hp := e_pos
  hq := e_pos
  hw := by intro j; fin_cases j <;> norm_num [Supply.Example.frame]
  ha0 := by intro j; fin_cases j <;> norm_num [Supply.Example.frame]
  hD := demand_posDef
  hsigma := by norm_num

def candidate (x z : ℝ) (hx : |x|<1/4) (hz : |z|<1/4) : family.Candidate :=
  ⟨coordinates x z,coordinates_candidate x z hx hz⟩

theorem fixed_R : family.fixedR=![![3]] := by
  change Supply.knownR Supply.Example.frame.w Supply.Example.frame.V
    (Supply.totalInputs e (Supply.Example.frame.reconstruct e (coordinates 0 0)))=_
  rw [reconstruct_inputs]
  have ht : Supply.totalInputs e (inputs 0 0)=![3/2,3/2] := by
    ext j
    fin_cases j <;> norm_num [Supply.totalInputs,inputs,coordinates,visible,hidden,e,
      Fin.sum_univ_succ]
  rw [ht]
  ext a b
  fin_cases a; fin_cases b
  change (∑ j : Fin 2, (∑ i : Fin 2,
    Supply.Example.frame.V i 0 * (Matrix.diagonal (fun t : Fin 2 => ![3/2,3/2] t /
      Supply.Example.frame.w t)) i j) * Supply.Example.frame.V j 0)=3
  norm_num [Supply.Example.frame,Matrix.diagonal,Fin.sum_univ_succ]

theorem moment_m (x z : ℝ) : (coordinates x z).transpose *ᵥ (demand *ᵥ policy)=![24*x/25] := by
  rw [demand_policy]
  ext a
  fin_cases a
  norm_num [coordinates,visible,hidden,Matrix.mulVec,transpose_apply,dotProduct,Fin.sum_univ_succ]
  ring

theorem moment_K (x z : ℝ) :
    Regularity.K e e demand family.fixedR 1 (coordinates x z)=![![3+18*x^2/5]] := by
  rw [Regularity.K,Regularity.adjustedDemand,fixed_R,xi_identity,demand_entries]
  simp only [one_smul]
  ext a b
  fin_cases a; fin_cases b
  norm_num [coordinates,visible,hidden,Matrix.mul_apply,transpose_apply,Fin.sum_univ_succ,
    Matrix.one_apply,Matrix.smul_apply,smul_eq_mul,of_apply,Pi.smul_apply]
  have hs : ((1 : ℝ) • (![![3]] : InputCoordinates.Mat 1 1)) 0 0=3 := by norm_num
  ring_nf
  exact congrArg (fun t : ℝ => t+x^2*(18/5)) hs

theorem moment_K_positive (x : ℝ) : 0<3+18*x^2/5 := by nlinarith [sq_nonneg x]

theorem candidate_m (x z : ℝ) (hx : |x|<1/4) (hz : |z|<1/4) :
    (family.model (candidate x z hx hz)).m=![24*x/25] := moment_m x z

theorem candidate_K (x z : ℝ) (hx : |x|<1/4) (hz : |z|<1/4) :
    (family.model (candidate x z hx hz)).K=![![3+18*x^2/5]] := by
  rw [family.candidate_K_answer (candidate x z hx hz) family.reference (0 : InputCoordinates.Mat 3 0)]
  exact moment_K x z

theorem common_benchmark (s0 c x z : ℝ) (hs : 0<s0) (hx : |x|<1/4) (hz : |z|<1/4) :
    (family.model (candidate x z hx hz)).BenchmarkEquilibrium
      (family.commonUtility c) (family.commonEndowment s0) s0 :=
  family.every_candidate_equilibrium hs c (candidate x z hx hz)

end CommodityClassification.ResourceCancellation
