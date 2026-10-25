module
public import LeanMath.CommodityClassification.CommonBenchmarkFamily
@[expose] public section
namespace CommodityClassification.Equilibrium.Example
open Matrix Supply.Example
open scoped BigOperators

noncomputable def family : BenchmarkFamily 2 1 1 where
  frame := frame
  p := ones
  q := ones
  b := ![1,0]
  D := 1
  sigma := 1
  parents := parent
  report := 0
  reference := path (1/2)
  reference_mem := path_mem (by norm_num) (by norm_num)
  hp := ones_pos
  hq := ones_pos
  hw := frame_price_pos
  ha0 := by intro j; fin_cases j <;> norm_num [frame]
  hD := Matrix.PosDef.one
  hsigma := by norm_num

noncomputable def familyPath (t : ℝ) (h : 0<t) (h2 : t<2) : family.Candidate := ⟨path t,path_mem h h2⟩

theorem family_endowment : family.commonEndowment 1 = ![3/2,3/2] := by
  change (frame.reconstruct ones (path (1/2))).transpose *ᵥ ones+(1:ℝ) • frame.a0=_
  rw [path_reconstruct]
  ext j
  fin_cases j <;> norm_num [inputs,ones,frame,Matrix.mulVec,Matrix.transpose,dotProduct,Fin.sum_univ_succ]

theorem distinct_candidates :
    familyPath (1/2) (by norm_num) (by norm_num) ≠ familyPath (3/2) (by norm_num) (by norm_num) := by
  intro hh
  have h := congrArg (fun C : family.Candidate => C.val 0 0) hh
  norm_num [familyPath,path_exposure] at h

theorem same_utility_and_endowment (t : ℝ) (h : 0<t) (h2 : t<2) :
    (family.model (familyPath t h h2)).BenchmarkEquilibrium (family.commonUtility 0) ![3/2,3/2] 1 := by
  rw [←family_endowment]
  exact family.every_candidate_equilibrium (by norm_num) 0 (familyPath t h h2)

/-- An explicit one-factor, zero-product edge case. -/
noncomputable def emptyFamily : BenchmarkFamily 0 0 0 where
  frame := {
    w := fun _ => 1
    a0 := fun _ => 1
    V := 0
    normalized := by norm_num [dotProduct,Fin.sum_univ_succ]
    annihilates := by simp
    independent := fun _ _ _ => Subsingleton.elim _ _ }
  p := 0
  q := 0
  b := 0
  D := 1
  sigma := 1
  parents := { group := id, onto := Function.surjective_id }
  report := 0
  reference := 0
  reference_mem := ⟨by intro i; exact Fin.elim0 i,by simp [InputCoordinates.Partition.report]⟩
  hp := by intro i; exact Fin.elim0 i
  hq := by intro i; exact Fin.elim0 i
  hw := by intro j; norm_num
  ha0 := by intro j; norm_num
  hD := Matrix.PosDef.one
  hsigma := by norm_num

theorem empty_family_equilibrium :
    (∀j,0<emptyFamily.commonEndowment 1 j) ∧
    ∀C : emptyFamily.Candidate,(emptyFamily.model C).BenchmarkEquilibrium
      (emptyFamily.commonUtility 0) (emptyFamily.commonEndowment 1) 1 :=
  ⟨emptyFamily.commonEndowment_positive (by norm_num),emptyFamily.every_candidate_equilibrium (by norm_num) 0⟩

end CommodityClassification.Equilibrium.Example
