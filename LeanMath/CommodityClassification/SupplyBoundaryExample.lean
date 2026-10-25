module
public import LeanMath.CommodityClassification.SupplyCandidates
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.NormNum
@[expose] public section
set_option maxHeartbeats 1800000
namespace CommodityClassification.Supply.Example
open Matrix
open scoped BigOperators Topology

noncomputable def frame : InputCoordinates.Frame 1 where
  w := ![1,1]
  a0 := ![1/2,1/2]
  V := ![![1],![-1]]
  normalized := by norm_num [dotProduct, Fin.sum_univ_succ]
  annihilates := by
    ext j; fin_cases j
    norm_num [Matrix.mulVec,dotProduct,Matrix.transpose,Fin.sum_univ_succ]
  independent := by
    intro z y h
    have hh := congrFun h 0
    have hz : z 0 = y 0 := by simpa [Matrix.mulVec, dotProduct, Fin.sum_univ_succ] using hh
    ext j; fin_cases j; exact hz

def parent : InputCoordinates.Partition 2 1 where
  group := fun _ => 0
  onto := by intro j; exact ⟨0,Subsingleton.elim _ _⟩

def ones : Vec 2 := ![1,1]
noncomputable def inputs (t : ℝ) : Mat 2 2 := ![![1-t/2,t/2],![t/2,1-t/2]]
noncomputable def path (t : ℝ) : Mat 2 1 := inputs t * frame.V

theorem path_cost (t : ℝ) : inputs t *ᵥ frame.w = ones := by
  ext i; fin_cases i <;> simp [inputs,frame,ones,Matrix.mulVec,dotProduct,Fin.sum_univ_succ]

theorem path_reconstruct (t : ℝ) : frame.reconstruct ones (path t) = inputs t := by
  rw [← path_cost t]
  exact frame.reconstruct_original (inputs t)

theorem path_exposure (t : ℝ) : path t = ![![1-t],![t-1]] := by
  ext i j
  simp only [path,Matrix.mul_apply,Fin.sum_univ_succ]
  fin_cases i <;> fin_cases j <;> norm_num [inputs,frame] <;> ring

theorem path_report (t : ℝ) : parent.report ones (path t) = 0 := by
  ext i j
  rw [InputCoordinates.Partition.report_apply]
  fin_cases i; fin_cases j
  simp [InputCoordinates.Partition.cell,parent,ones,path_exposure,Fin.sum_univ_succ]

theorem path_total (t : ℝ) : totalInputs ones (inputs t) = ones := by
  ext j; fin_cases j <;> simp [totalInputs,ones,inputs,Fin.sum_univ_succ]

theorem path_positive {t : ℝ} (ht : 0<t) (ht2 : t<2) : InputCoordinates.Positive (inputs t) := by
  intro i j; fin_cases i <;> fin_cases j <;> dsimp [inputs] <;> linarith

theorem path_mem {t : ℝ} (ht : 0<t) (ht2 : t<2) :
    path t ∈ frame.Candidates ones ones parent 0 := by
  refine ⟨?_,path_report t⟩
  change InputCoordinates.Positive (frame.reconstruct ones (path t))
  rw [path_reconstruct]
  exact path_positive ht ht2

theorem path_continuous : Continuous path := by
  unfold path inputs
  fun_prop

theorem boundary_in_actual_closure :
    path 0 ∈ closure (frame.Candidates ones ones parent 0) := by
  have hz : (0:ℝ) ∈ closure (Set.Ioo (0:ℝ) 1) := by
    rw [closure_Ioo (by norm_num : (0:ℝ)≠1)]
    norm_num
  have hm : path 0 ∈ closure (path '' Set.Ioo (0:ℝ) 1) :=
    image_closure_subset_closure_image path_continuous ⟨0,hz,rfl⟩
  apply closure_mono (s := path '' Set.Ioo (0:ℝ) 1) (t := frame.Candidates ones ones parent 0) ?_ hm
  rintro C ⟨t,ht,rfl⟩
  exact path_mem ht.1 (lt_trans ht.2 (by norm_num))

theorem fixed_R : candidateR frame ones ones (path 1) = ![![2]] := by
  unfold candidateR
  rw [path_reconstruct,path_total]
  ext i j
  simp only [knownR,Matrix.mul_apply,Matrix.diagonal_apply,
    Matrix.transpose_apply,Fin.sum_univ_succ]
  fin_cases i; fin_cases j
  norm_num [frame,ones]

theorem path_residual (t : ℝ) :
    residual (candidateR frame ones ones (path 1)) ones ones (path t) = ![![4*t-2*t^2]] := by
  ext i j
  simp only [residual,Matrix.sub_apply,Matrix.mul_apply,xi,Matrix.diagonal_apply,
    Matrix.transpose_apply,Fin.sum_univ_succ]
  rw [fixed_R,path_exposure]
  fin_cases i; fin_cases j
  norm_num [ones]
  ring

theorem interior_positive :
    path 1 ∈ frame.Candidates ones ones parent 0 ∧
    (residual (candidateR frame ones ones (path 1)) ones ones (path 1)).PosDef := by
  refine ⟨path_mem (by norm_num) (by norm_num),?_⟩
  rw [path_residual]
  have hh : (![![4*(1:ℝ)-2*1^2]] : Mat 1 1) = Matrix.diagonal (fun _ => (2:ℝ)) := by
    ext i j; fin_cases i; fin_cases j; norm_num
  rw [hh]
  exact Matrix.PosDef.diagonal (fun _ : Fin 1 => (by norm_num : (0:ℝ)<2))

theorem boundary_zero : residual (candidateR frame ones ones (path 1)) ones ones (path 0) = 0 := by
  rw [path_residual]
  ext i j; fin_cases i; fin_cases j; norm_num

theorem boundary_not_posDef :
    ¬ (residual (candidateR frame ones ones (path 1)) ones ones (path 0)).PosDef := by
  rw [boundary_zero]
  intro h
  have hn : (fun _ : Fin 1 => (1:ℝ)) ≠ 0 := by intro hh; have := congrFun hh 0; norm_num at this
  have hh := h.dotProduct_mulVec_pos hn
  simp at hh

end CommodityClassification.Supply.Example
