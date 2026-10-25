module

public import LeanMath.CommodityClassification.PrecisionEnvelopeParameters

/-! The actual balanced two-type report, its means and exact minimum moment. -/
@[expose] public section
noncomputable section
set_option maxHeartbeats 1600000
namespace CommodityClassification.Precision.Data
open Matrix InputCoordinates
open scoped BigOperators
variable {n : ℕ} (d : Precision.Data n)

theorem type_exists (a : ℝ) (ha : 0<d.typeSales a) : ∃i,d.v i=a := by
  by_contra h
  push Not at h
  have hf : Finset.univ.filter (fun i => d.v i=a)=∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro i hi
    exact h i (Finset.mem_filter.mp hi).2
  unfold typeSales at ha
  rw [hf,Finset.sum_empty] at ha
  exact (lt_irrefl 0) ha

def typePartition : Partition n 2 where
  group := fun i => if d.v i=1 then 0 else 1
  onto := by
    intro a
    fin_cases a
    · obtain ⟨i,hi⟩ := d.type_exists 1 (by rw [d.typeSales_half.1];norm_num)
      exact ⟨i,by simp [hi]⟩
    · obtain ⟨i,hi⟩ := d.type_exists (-1) (by rw [d.typeSales_half.2];norm_num)
      exact ⟨i,by norm_num [hi]⟩

theorem typePartition_respecting : d.TypeRespecting d.typePartition := by
  refine ⟨![1,-1],?_⟩
  intro i
  rcases d.type_sign i with hi|hi <;> norm_num [typePartition,hi]

theorem typePartition_cell_zero : d.typePartition.cell 0=Finset.univ.filter (fun i => d.v i=1) := by
  ext i
  simp only [Partition.mem_cell,Finset.mem_filter,Finset.mem_univ,true_and]
  change (if d.v i=1 then (0:Fin 2) else 1)=0 ↔ d.v i=1
  by_cases hi : d.v i=1 <;> simp [hi]

theorem typePartition_cell_one : d.typePartition.cell 1=Finset.univ.filter (fun i => d.v i=-1) := by
  ext i
  simp only [Partition.mem_cell,Finset.mem_filter,Finset.mem_univ,true_and]
  change (if d.v i=1 then (0:Fin 2) else 1)=1 ↔ d.v i=-1
  rcases d.type_sign i with hi|hi <;> norm_num [hi]

theorem typePartition_weights : d.groupWeight d.typePartition=![1/2,1/2] := by
  ext a
  fin_cases a
  · change (∑i∈d.typePartition.cell 0,d.w i)=1/2
    rw [d.typePartition_cell_zero]
    exact d.typeSales_half.1
  · change (∑i∈d.typePartition.cell 1,d.w i)=1/2
    rw [d.typePartition_cell_one]
    exact d.typeSales_half.2

theorem typeInputTotal_sum (c : Vec n) : d.typeInputTotal c 1+d.typeInputTotal c (-1)=∑i,d.w i*c i := by
  simp only [typeInputTotal,Finset.sum_filter,←Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  rcases d.type_sign i with hi|hi <;> rw [hi] <;> norm_num

theorem typePartition_totals (c : Vec n) (hc : ∑i,d.w i*c i=0) :
    d.groupTotal d.typePartition c=![d.theta c/2,-d.theta c/2] := by
  have hsum := d.typeInputTotal_sum c
  rw [hc] at hsum
  have hd := d.type_totals_recover_theta c
  ext a;fin_cases a
  · change (∑i∈d.typePartition.cell 0,d.w i*c i)=d.theta c/2
    rw [d.typePartition_cell_zero]
    change d.typeInputTotal c 1=d.theta c/2
    linarith
  · change (∑i∈d.typePartition.cell 1,d.w i*c i)=-d.theta c/2
    rw [d.typePartition_cell_one]
    change d.typeInputTotal c (-1)=-d.theta c/2
    linarith

theorem typePartition_mean (c : Vec n) (hc : ∑i,d.w i*c i=0) :
    d.meanVector d.typePartition c=fun i => d.theta c*d.v i := by
  ext i
  unfold meanVector
  rw [d.typePartition_totals c hc,d.typePartition_weights]
  rcases d.type_sign i with hi|hi <;> norm_num [typePartition,hi] <;> ring

theorem typePartition_lowerMoment (c : Vec n) (hc : ∑i,d.w i*c i=0) :
    d.lowerMoment d.typePartition (d.groupTotal d.typePartition c)=(d.theta c)^2 := by
  rw [←d.meanVector_secondMoment,d.typePartition_mean c hc]
  unfold secondMoment
  calc
    (∑i,d.w i*(d.theta c*d.v i)^2)=(d.theta c)^2*(∑i,d.w i) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      rw [mul_pow,d.type_square]
      ring
    _=(d.theta c)^2 := by rw [d.sum_w,mul_one]

end CommodityClassification.Precision.Data
