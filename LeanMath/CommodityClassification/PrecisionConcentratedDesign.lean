module

public import LeanMath.CommodityClassification.PrecisionEqualSalesWitness

/-! The distinct concentrated-sales design and its explicit four nonempty groups. -/
@[expose] public section
noncomputable section
set_option maxHeartbeats 2400000
namespace CommodityClassification.Precision.Illustration
open InputCoordinates
open scoped BigOperators

def concentratedSales : Data 32 where
  w i := if i=0 ∨ i=16 then 2/5 else 1/150
  v := types
  hw i := by split_ifs <;> norm_num
  sum_w := by norm_num [Fin.sum_univ_succ]
  type_sign i := by unfold types;split_ifs <;> simp
  type_balance := by norm_num [types,Fin.sum_univ_succ]
  eta := 9/4
  alpha := 9/4
  beta := 1/2
  sigma := 1
  heta := by norm_num
  halpha := by norm_num
  hbeta := by norm_num
  hsigma := by norm_num

def largeProducts : Finset (Fin 32) := {0,16}

def concentratedPartition : Partition 32 4 where
  group i := if i=0 then 0 else if i=16 then 2 else if i.val<16 then 1 else 3
  onto := by
    intro a
    fin_cases a
    · exact ⟨0,by norm_num⟩
    · exact ⟨1,by norm_num⟩
    · exact ⟨16,by norm_num⟩
    · exact ⟨17,by norm_num⟩

theorem concentratedSales_parameters : concentratedSales.HasIllustrationParameters := by
  norm_num [Data.HasIllustrationParameters,concentratedSales]

theorem concentratedPartition_typeRespecting : concentratedSales.TypeRespecting concentratedPartition := by
  refine ⟨fun a => if a.val<2 then 1 else -1,?_⟩
  intro i
  fin_cases i <;> norm_num [concentratedSales,concentratedPartition,types]

theorem concentratedPartition_singletons :
    ∀i∈largeProducts,concentratedPartition.cell (concentratedPartition.group i)={i} := by
  intro i hi
  have hh : i=0 ∨ i=16 := by simpa [largeProducts] using hi
  rcases hh with rfl|rfl <;> ext j <;>
    simp only [Partition.mem_cell,Finset.mem_singleton] <;>
    fin_cases j <;> norm_num [concentratedPartition]

theorem concentratedPartition_remaining (i j : Fin 32) (hi : i∉largeProducts) (hj : j∉largeProducts) :
    concentratedPartition.group i=concentratedPartition.group j ↔
      concentratedSales.typePartition.group i=concentratedSales.typePartition.group j := by
  have hi' : i≠0 ∧ i≠16 := by simpa [largeProducts] using hi
  have hj' : j≠0 ∧ j≠16 := by simpa [largeProducts] using hj
  simp only [concentratedPartition,ite_eq_right hi'.1,ite_eq_right hi'.2,
    ite_eq_right hj'.1,ite_eq_right hj'.2,Data.typePartition,concentratedSales,types]
  split_ifs <;> norm_num at *

theorem concentratedPartition_isolation : concentratedSales.IsIsolationPartition largeProducts concentratedPartition := by
  intro i j
  by_cases hi : i∈largeProducts
  · constructor
    · intro hij
      have hj := (concentratedPartition.mem_cell (concentratedPartition.group i) j).mpr hij.symm
      rw [concentratedPartition_singletons i hi,Finset.mem_singleton] at hj
      rw [hj]
    · intro hij
      have hj := (concentratedSales.isolationLabel_selected largeProducts i j hi).mp hij.symm
      rw [hj]
  · by_cases hj : j∈largeProducts
    · constructor
      · intro hij
        have hi' := (concentratedPartition.mem_cell (concentratedPartition.group j) i).mpr hij
        rw [concentratedPartition_singletons j hj,Finset.mem_singleton] at hi'
        rw [hi']
      · intro hij
        have hi' := (concentratedSales.isolationLabel_selected largeProducts j i hj).mp hij
        rw [hi']
    · exact (concentratedPartition_remaining i j hi hj).trans
        (concentratedSales.isolationLabel_remaining largeProducts i j hi hj).symm

theorem concentrated_residualSales : concentratedSales.residualSales largeProducts=1/5 := by
  norm_num [Data.residualSales,largeProducts,concentratedSales]

theorem concentrated_capacity_bound : concentratedSales.totalCapacity concentratedPartition≤1/5 := by
  rw [←concentrated_residualSales]
  exact concentratedSales.isolation_capacity_bound largeProducts concentratedPartition concentratedPartition_isolation

theorem concentrated_welfare_bound : concentratedSales.exAnteWidth concentratedPartition≤3/112 := by
  have hh := concentratedSales.exAnte_capacity_bound concentratedPartition concentratedPartition_typeRespecting
  have hΛ := (concentratedSales.illustration_constants concentratedSales_parameters).2.2.2.2.2.2
  rw [hΛ] at hh
  nlinarith [concentrated_capacity_bound]

theorem concentrated_all_answers_pass :
    ∀c,concentratedSales.Admissible c→
      concentratedSales.manuscriptAnswerWidth concentratedPartition
        (concentratedSales.groupTotal concentratedPartition c)<1/20 := by
  intro c hc
  have hh := (concentratedSales.exAnteWidth_le_iff concentratedPartition concentratedPartition_typeRespecting _).mp
    concentrated_welfare_bound c hc
  linarith

theorem concentrated_actual_coefficient_bound (c e : Vec 32)
    (hc : concentratedSales.Admissible c) (he : concentratedSales.Admissible e)
    (hJ : concentratedSales.groupTotal concentratedPartition e=concentratedSales.groupTotal concentratedPartition c) :
    |(concentratedSales.family.model (concentratedSales.candidate c hc)).lossCoefficient/concentratedSales.nu-
      (concentratedSales.family.model (concentratedSales.candidate e he)).lossCoefficient/concentratedSales.nu|≤3/112 := by
  rw [concentratedSales.actual_normalized_coefficient,concentratedSales.actual_normalized_coefficient]
  exact (concentratedSales.arbitrary_partition_pair_lower concentratedPartition c e hc he hJ).trans concentrated_welfare_bound

theorem sales_designs_differ : equalSales.w 0≠concentratedSales.w 0 := by
  norm_num [equalSales,concentratedSales]

end CommodityClassification.Precision.Illustration
