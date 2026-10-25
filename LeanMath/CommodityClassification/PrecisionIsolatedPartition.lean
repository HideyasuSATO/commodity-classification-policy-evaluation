module

public import LeanMath.CommodityClassification.PrecisionCapacityCertificate

/-! A genuine finite partition isolating selected products and pooling remaining types. -/
@[expose] public section
noncomputable section
set_option maxHeartbeats 1600000
namespace CommodityClassification.Precision.Data
open InputCoordinates
variable {n g : ℕ} (d : Precision.Data n)

def isolationLabel (S : Finset (Fin n)) (i : Fin n) : {j // j∈S} ⊕ Fin 2 :=
  if h : i∈S then Sum.inl ⟨i,h⟩ else Sum.inr (d.typePartition.group i)

def IsIsolationPartition (S : Finset (Fin n)) (P : Partition n g) : Prop :=
  ∀i j,P.group i=P.group j ↔ d.isolationLabel S i=d.isolationLabel S j

theorem isolationLabel_selected (S : Finset (Fin n)) (i j : Fin n) (hi : i∈S) :
    d.isolationLabel S j=d.isolationLabel S i ↔ j=i := by
  classical
  by_cases hj : j∈S
  · simp [isolationLabel,hi,hj,Subtype.mk.injEq]
  · simp [isolationLabel,hi,hj]
    intro h
    subst j
    exact hj hi

theorem isolationLabel_remaining (S : Finset (Fin n)) (i j : Fin n)
    (hi : i∉S) (hj : j∉S) :
    d.isolationLabel S i=d.isolationLabel S j ↔ d.typePartition.group i=d.typePartition.group j := by
  simp [isolationLabel,hi,hj]

theorem isolation_partition_exists (S : Finset (Fin n)) :
    ∃g,∃P : Partition n g,d.IsIsolationPartition S P := by
  obtain ⟨g,P,hP⟩ := exists_partition_of_setoid (Setoid.ker (d.isolationLabel S))
  exact ⟨g,P,hP⟩

theorem isolation_cell_singleton (S : Finset (Fin n)) (P : Partition n g)
    (hP : d.IsIsolationPartition S P) (i : Fin n) (hi : i∈S) :
    P.cell (P.group i)={i} := by
  ext j
  rw [Partition.mem_cell,Finset.mem_singleton,hP j i]
  exact d.isolationLabel_selected S i j hi

theorem isolation_remaining_cells (S : Finset (Fin n)) (P : Partition n g)
    (hP : d.IsIsolationPartition S P) (i j : Fin n) (hi : i∉S) (hj : j∉S) :
    P.group i=P.group j ↔ d.typePartition.group i=d.typePartition.group j :=
  (hP i j).trans (d.isolationLabel_remaining S i j hi hj)

theorem isolation_refines_types (S : Finset (Fin n)) (P : Partition n g)
    (hP : d.IsIsolationPartition S P) : Nonempty (Refinement P d.typePartition) := by
  classical
  apply (P.refinement_iff d.typePartition).mpr
  intro i j hij
  by_cases hi : i∈S
  · have hji := (d.isolationLabel_selected S i j hi).mp ((hP i j).mp hij).symm
    rw [hji]
  · by_cases hj : j∈S
    · have hij' := (d.isolationLabel_selected S j i hj).mp ((hP i j).mp hij)
      rw [hij']
    · exact (d.isolation_remaining_cells S P hP i j hi hj).mp hij

theorem isolation_typeRespecting (S : Finset (Fin n)) (P : Partition n g)
    (hP : d.IsIsolationPartition S P) : d.TypeRespecting P := by
  obtain ⟨R⟩ := d.isolation_refines_types S P hP
  exact d.refinement_typeRespecting R d.typePartition_respecting

theorem isolation_group_count (S : Finset (Fin n)) (P : Partition n g)
    (hP : d.IsIsolationPartition S P) : g≤S.card+2 := by
  classical
  let f : Fin g→({i // i∈S} ⊕ Fin 2) := fun a => d.isolationLabel S (P.representative a)
  have hf : Function.Injective f := by
    intro a b hab
    have hh := (hP (P.representative a) (P.representative b)).mpr hab
    simpa only [P.representative_group] using hh
  simpa using Fintype.card_le_of_injective f hf

theorem isolation_partition_properties (S : Finset (Fin n)) :
    ∃g,∃P : Partition n g,d.IsIsolationPartition S P ∧ g≤S.card+2 ∧
      d.TypeRespecting P ∧ (∀i∈S,P.cell (P.group i)={i}) ∧
      (∀i∉S,∀j∉S,P.group i=P.group j ↔ d.typePartition.group i=d.typePartition.group j) := by
  obtain ⟨g,P,hP⟩ := d.isolation_partition_exists S
  exact ⟨g,P,hP,d.isolation_group_count S P hP,d.isolation_typeRespecting S P hP,
    d.isolation_cell_singleton S P hP,fun i hi j hj => d.isolation_remaining_cells S P hP i j hi hj⟩

end CommodityClassification.Precision.Data
