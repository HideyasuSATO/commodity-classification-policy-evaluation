module

public import LeanMath.CommodityClassification.ResourceCancellationEconomy

/-! The manuscript's four-good example, with arbitrary positive demand elasticity. -/
@[expose] public section
noncomputable section
set_option maxHeartbeats 2400000
namespace CommodityClassification.SeparableFour
open Matrix InputCoordinates

def prices : Vec 4 := fun _ => 1
def quantities : Vec 4 := fun _ => 1/4
def policy : Vec 4 := ![1,1,2,2]
def demand (η : ℝ) : Matrix (Fin 4) (Fin 4) ℝ := diagonal (fun _ => η/4)
def parent : Partition 4 1 where
  group := fun _ => 0
  onto := by intro a; exact ⟨0,Subsingleton.elim _ _⟩
def fine : Partition 4 2 where
  group := ![0,0,1,1]
  onto := by intro a; fin_cases a; exact ⟨0,rfl⟩; exact ⟨2,rfl⟩
def coordinates (a t : ℝ) : Mat 4 1 := ![![a+t],![a-t],![-a],![-a]]
def inputs (a t : ℝ) : Mat 4 2 := fun i j =>
  if j=0 then (1+coordinates a t i 0)/2 else (1-coordinates a t i 0)/2

theorem demand_posDef (η : ℝ) (hη : 0<η) : (demand η).PosDef := by
  exact Matrix.PosDef.diagonal (fun _ => by positivity)

theorem demand_xi (η : ℝ) : demand η=η • Supply.xi prices quantities := by
  ext i j
  by_cases hij : i=j
  · subst j; simp [demand,Supply.xi,prices,quantities,Matrix.diagonal,Matrix.smul_apply];ring
  · simp [demand,Supply.xi,prices,quantities,Matrix.diagonal,Matrix.smul_apply,hij]

theorem reconstruct_inputs (a t : ℝ) :
    Supply.Example.frame.reconstruct prices (coordinates a t)=inputs a t := by
  have hw : inputs a t *ᵥ Supply.Example.frame.w=prices := by
    ext i
    simp [inputs,Supply.Example.frame,prices,Matrix.mulVec,dotProduct,Fin.sum_univ_succ]
    ring
  have hv : inputs a t*Supply.Example.frame.V=coordinates a t := by
    ext i j
    fin_cases j
    change (∑r : Fin 2,inputs a t i r*Supply.Example.frame.V r 0)=coordinates a t i 0
    simp [inputs,Supply.Example.frame,Fin.sum_univ_succ]
    ring
  rw [←hw,←hv]
  exact Supply.Example.frame.reconstruct_original (inputs a t)

theorem parent_report (a t : ℝ) : parent.report quantities (coordinates a t)=0 := by
  ext i j; fin_cases i; fin_cases j
  change (∑l : Fin 4,quantities l*coordinates a t l 0)=0
  norm_num [quantities,coordinates,Fin.sum_univ_succ]
  ring

theorem fine_report (a t : ℝ) : fine.report quantities (coordinates a t)=![![a/2],![-a/2]] := by
  ext i j
  change (∑l : Fin 4,(if fine.group l=i then quantities l else 0)*coordinates a t l j)=_
  fin_cases i <;> fin_cases j <;>
    norm_num [fine,quantities,coordinates,Fin.sum_univ_succ] <;> ring

theorem inputs_positive (a t : ℝ) (ha : |a|<1/4) (ht : |t|<1/4) : Positive (inputs a t) := by
  obtain ⟨ha0,ha1⟩ := abs_lt.mp ha
  obtain ⟨ht0,ht1⟩ := abs_lt.mp ht
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [inputs,coordinates] <;> linarith

theorem coordinates_candidate (a t : ℝ) (ha : |a|<1/4) (ht : |t|<1/4) :
    coordinates a t∈Supply.Example.frame.Candidates prices quantities parent 0 := by
  refine ⟨?_,parent_report a t⟩
  change Positive (Supply.Example.frame.reconstruct prices (coordinates a t))
  rw [reconstruct_inputs]
  exact inputs_positive a t ha ht

def family (η : ℝ) (hη : 0<η) : Equilibrium.BenchmarkFamily 4 1 1 where
  frame := Supply.Example.frame
  p := prices
  q := quantities
  b := policy
  D := demand η
  sigma := 1
  parents := parent
  report := 0
  reference := coordinates 0 0
  reference_mem := coordinates_candidate 0 0 (by norm_num) (by norm_num)
  hp := by intro i; norm_num [prices]
  hq := by intro i; norm_num [quantities]
  hw := by intro j; fin_cases j <;> norm_num [Supply.Example.frame]
  ha0 := by intro j; fin_cases j <;> norm_num [Supply.Example.frame]
  hD := demand_posDef η hη
  hsigma := by norm_num

def candidate (η : ℝ) (hη : 0<η) (a t : ℝ) (ha : |a|<1/4) (ht : |t|<1/4) :
    (family η hη).Candidate := ⟨coordinates a t,coordinates_candidate a t ha ht⟩

theorem fixed_R (η : ℝ) (hη : 0<η) : (family η hη).fixedR=![![1]] := by
  change Supply.knownR Supply.Example.frame.w Supply.Example.frame.V
    (Supply.totalInputs quantities (Supply.Example.frame.reconstruct prices (coordinates 0 0)))=_
  rw [reconstruct_inputs]
  have hi : Supply.totalInputs quantities (inputs 0 0)=![1/2,1/2] := by
    ext j; fin_cases j <;> norm_num [Supply.totalInputs,inputs,coordinates,quantities,Fin.sum_univ_succ]
  rw [hi]
  ext i j; fin_cases i; fin_cases j
  change (∑r : Fin 2,(∑s : Fin 2,Supply.Example.frame.V s 0 *
    (diagonal (fun k : Fin 2 => ![1/2,1/2] k / Supply.Example.frame.w k)) s r)*
      Supply.Example.frame.V r 0)=1
  norm_num [Supply.Example.frame,Matrix.diagonal,Fin.sum_univ_succ]

end CommodityClassification.SeparableFour
