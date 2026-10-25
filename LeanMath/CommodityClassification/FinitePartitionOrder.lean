module

public import LeanMath.CommodityClassification.WeightedExchangeSpanning
public import LeanMath.CommodityClassification.AllAnswerReportEmbedding
public import Mathlib.Data.Fintype.EquivFin
public import Mathlib.Data.Fintype.Quotient

/-! Refinement, finite equivalence classes, and label-independent uniqueness. -/
@[expose] public section
noncomputable section
namespace CommodityClassification.InputCoordinates
variable {n g h t : ℕ}

theorem Partition.refinement_iff (P : Partition n g) (Q : Partition n h) :
    Nonempty (Refinement P Q) ↔ ∀ i j : Fin n,P.group i=P.group j → Q.group i=Q.group j := by
  constructor
  · rintro ⟨R⟩ i j hij
    exact (R.compatible i).trans ((congrArg R.parent hij).trans (R.compatible j).symm)
  · intro hc
    exact ⟨⟨(fun a => Q.group (P.representative a)),
      (fun i => hc i (P.representative (P.group i)) (P.representative_group _).symm)⟩⟩

def Refinement.trans {P : Partition n g} {Q : Partition n h} {R : Partition n t}
    (a : Refinement P Q) (b : Refinement Q R) : Refinement P R :=
  ⟨b.parent ∘ a.parent,fun i => (b.compatible i).trans (congrArg b.parent (a.compatible i))⟩

theorem exists_partition_of_setoid (S : Setoid (Fin n)) :
    ∃ g, ∃ P : Partition n g, ∀ i j : Fin n,P.group i=P.group j ↔ S.r i j := by
  classical
  let : Fintype (Quotient S) := Fintype.ofFinite _
  let e := Fintype.equivFin (Quotient S)
  let P : Partition n (Fintype.card (Quotient S)) :=
    ⟨(fun i => e (Quotient.mk S i)),e.surjective.comp (Quotient.mk_surjective)⟩
  refine ⟨_,P,?_⟩
  intro i j
  change e (Quotient.mk S i)=e (Quotient.mk S j) ↔ S.r i j
  exact e.injective.eq_iff.trans Quotient.eq

theorem Partition.same_cells_of_mutual_refinement (P : Partition n g) (Q : Partition n h)
    (hpq : Nonempty (Refinement P Q)) (hqp : Nonempty (Refinement Q P)) :
    ∀ i j : Fin n,P.group i=P.group j ↔ Q.group i=Q.group j := by
  intro i j
  exact ⟨(P.refinement_iff Q).mp hpq i j,(Q.refinement_iff P).mp hqp i j⟩

theorem Partition.relabeling_of_same_cells (P : Partition n g) (Q : Partition n h)
    (hc : ∀ i j : Fin n,P.group i=P.group j ↔ Q.group i=Q.group j) :
    ∃ e : Fin g ≃ Fin h, ∀ i : Fin n,e (P.group i)=Q.group i := by
  let f : Fin g → Fin h := fun a => Q.group (P.representative a)
  let b : Fin h → Fin g := fun a => P.group (Q.representative a)
  have hf (i : Fin n) : f (P.group i)=Q.group i :=
    (hc _ _).mp (P.representative_group (P.group i))
  have hb (i : Fin n) : b (Q.group i)=P.group i :=
    (hc _ _).mpr (Q.representative_group (Q.group i))
  have hbf : Function.LeftInverse b f := by
    intro a
    change b (Q.group (P.representative a))=a
    rw [hb,P.representative_group]
  have hfb : Function.RightInverse b f := by
    intro a
    change f (P.group (Q.representative a))=a
    rw [hf,Q.representative_group]
  exact ⟨⟨f,b,hbf,hfb⟩,hf⟩

end CommodityClassification.InputCoordinates
