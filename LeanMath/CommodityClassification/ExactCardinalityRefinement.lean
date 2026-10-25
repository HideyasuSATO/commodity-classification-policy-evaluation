module

public import LeanMath.CommodityClassification.PrecisionLowerConvergence
public import LeanMath.CommodityClassification.FinitePartitionOrder

/-! Refining an onto finite report to an exact number of nonempty cells. -/
@[expose] public section
noncomputable section
set_option maxHeartbeats 1400000
namespace CommodityClassification.InputCoordinates
variable {n g : ℕ}

theorem Partition.exists_same_cell_pair (P : Partition n g) (hgn : g<n) :
    ∃i j : Fin n,i≠j ∧ P.group i=P.group j := by
  have hn : ¬Function.Injective P.group := by
    intro hi
    have hh := Fintype.card_le_of_injective P.group hi
    simp only [Fintype.card_fin] at hh
    omega
  unfold Function.Injective at hn
  push Not at hn
  obtain ⟨i,j,hij,hne⟩ := hn
  exact ⟨i,j,hne,hij⟩

def Partition.splitProduct (P : Partition n g) (i j : Fin n)
    (hne : i≠j) (hgroup : P.group i=P.group j) : Partition n (g+1) where
  group x := if x=i then 0 else (P.group x).succ
  onto := by
    intro a
    refine Fin.cases ?_ (fun b => ?_) a
    · exact ⟨i,by simp⟩
    · obtain ⟨x,hx⟩ := P.onto b
      by_cases hi : x=i
      · subst x
        exact ⟨j,by simp [Ne.symm hne,←hgroup,hx]⟩
      · exact ⟨x,by simp [hi,hx]⟩

def Partition.splitProduct_refinement (P : Partition n g) (i j : Fin n)
    (hne : i≠j) (hgroup : P.group i=P.group j) : Refinement (P.splitProduct i j hne hgroup) P where
  parent := Fin.cases (P.group i) id
  compatible x := by
    by_cases hx : x=i
    · subst x;simp [Partition.splitProduct]
    · simp [Partition.splitProduct,hx]

theorem Partition.exists_successor_refinement (P : Partition n g) (hgn : g<n) :
    ∃Q : Partition n (g+1),Nonempty (Refinement Q P) := by
  obtain ⟨i,j,hne,hgroup⟩ := P.exists_same_cell_pair hgn
  exact ⟨P.splitProduct i j hne hgroup,⟨P.splitProduct_refinement i j hne hgroup⟩⟩

theorem Partition.exists_exact_refinement (P : Partition n g) (m : ℕ) (hgm : g≤m) (hmn : m≤n) :
    ∃Q : Partition n m,Nonempty (Refinement Q P) := by
  induction m,hgm using Nat.le_induction with
  | base => exact ⟨P,⟨Refinement.refl P⟩⟩
  | succ m hgm ih =>
    obtain ⟨Q,⟨R⟩⟩ := ih (by omega)
    obtain ⟨Q',⟨R'⟩⟩ := Q.exists_successor_refinement (by omega)
    exact ⟨Q',⟨R'.trans R⟩⟩

end CommodityClassification.InputCoordinates

namespace CommodityClassification.Precision.Data
open InputCoordinates
variable {n : ℕ} (d : Precision.Data n)

theorem exact_type_refinement_exists (m : ℕ) (h2 : 2≤m) (hm : m≤n) :
    ∃P : Partition n m,Nonempty (Refinement P d.typePartition) :=
  d.typePartition.exists_exact_refinement m h2 hm

theorem exact_type_partition_exists (m : ℕ) (h2 : 2≤m) (hm : m≤n) :
    ∃P : Partition n m,d.TypeRespecting P ∧ d.exAnteWidth P≤d.precisionFloor := by
  obtain ⟨P,⟨R⟩⟩ := d.exact_type_refinement_exists m h2 hm
  exact ⟨P,d.refinement_typeRespecting R d.typePartition_respecting,d.type_refinement_exAnte_upper R⟩

end CommodityClassification.Precision.Data
