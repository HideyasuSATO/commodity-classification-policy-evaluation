module

public import LeanMath.CommodityClassification.ResourceCancellationDemand

/-! The resource example's reports and actual positive factor inputs. -/
@[expose] public section
noncomputable section
set_option maxHeartbeats 2400000
namespace CommodityClassification.ResourceCancellation
open Matrix InputCoordinates

def parent : Partition 3 1 where
  group := fun _ => 0
  onto := by intro a; exact ⟨0,Subsingleton.elim _ _⟩

def fine : Partition 3 2 where
  group := ![0,0,1]
  onto := by intro a; fin_cases a; exact ⟨0,rfl⟩; exact ⟨2,rfl⟩

def refinement : Refinement fine parent where
  parent := fun _ => 0
  compatible := by intro i; rfl

def coordinates (x z : ℝ) : Mat 3 1 := fun i _ => x*visible i+z*hidden i

def inputs (x z : ℝ) : Mat 3 2 :=
  fun i j => if j=0 then (1+coordinates x z i 0)/2 else (1-coordinates x z i 0)/2

theorem coordinates_entries (x z : ℝ) : coordinates x z=![![x+z],![x-z],![-2*x]] := by
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [coordinates,visible,hidden] <;> ring

theorem inputs_cost (x z : ℝ) : inputs x z *ᵥ Supply.Example.frame.w=e := by
  ext i
  simp [inputs,Supply.Example.frame,e,Matrix.mulVec,dotProduct,Fin.sum_univ_succ]
  fin_cases i <;> norm_num <;> ring

theorem inputs_exposure (x z : ℝ) : inputs x z*Supply.Example.frame.V=coordinates x z := by
  ext i j
  fin_cases j
  change (∑a : Fin 2,inputs x z i a*Supply.Example.frame.V a 0)=coordinates x z i 0
  simp [inputs,Supply.Example.frame,Fin.sum_univ_succ]
  ring

theorem reconstruct_inputs (x z : ℝ) :
    Supply.Example.frame.reconstruct e (coordinates x z)=inputs x z := by
  rw [←inputs_cost x z,←inputs_exposure x z]
  exact Supply.Example.frame.reconstruct_original (inputs x z)

theorem parent_report (x z : ℝ) : parent.report e (coordinates x z)=0 := by
  ext a j
  fin_cases a; fin_cases j
  norm_num [Partition.report,Partition.Q,parent,e,coordinates,visible,hidden,Matrix.mul_apply,transpose_apply,Fin.sum_univ_succ]
  ring

theorem fine_report (x z : ℝ) : fine.report e (coordinates x z)=![![2*x],![-2*x]] := by
  ext a j
  fin_cases a <;> fin_cases j <;>
    norm_num [Partition.report,Partition.Q,fine,e,coordinates,visible,hidden,Matrix.mul_apply,transpose_apply,Fin.sum_univ_succ] <;> ring

theorem fine_report_iff (x z a c : ℝ) :
    fine.report e (coordinates x z)=fine.report e (coordinates a c) ↔ x=a := by
  rw [fine_report,fine_report]
  constructor
  · intro he
    have hh := congrFun (congrFun he 0) 0
    norm_num at hh
    linarith
  · rintro rfl
    rfl

theorem inputs_positive (x z : ℝ) (hx : |x|<1/4) (hz : |z|<1/4) : Positive (inputs x z) := by
  obtain ⟨hx0,hx1⟩ := abs_lt.mp hx
  obtain ⟨hz0,hz1⟩ := abs_lt.mp hz
  intro i j
  fin_cases i <;> fin_cases j <;>
    norm_num [inputs,coordinates,visible,hidden] <;> linarith

theorem coordinates_candidate (x z : ℝ) (hx : |x|<1/4) (hz : |z|<1/4) :
    coordinates x z∈Supply.Example.frame.Candidates e e parent 0 := by
  refine ⟨?_,parent_report x z⟩
  change Positive (Supply.Example.frame.reconstruct e (coordinates x z))
  rw [reconstruct_inputs]
  exact inputs_positive x z hx hz

theorem group_hidden_demand : fine.valueAggregation e *ᵥ (demand *ᵥ hidden)=![1/5,1/10] := by
  rw [demand_entries]
  ext a
  fin_cases a <;> norm_num [Partition.valueAggregation,Partition.Q,fine,e,hidden,Matrix.mulVec,
    transpose_apply,dotProduct,Fin.sum_univ_succ]

end CommodityClassification.ResourceCancellation
