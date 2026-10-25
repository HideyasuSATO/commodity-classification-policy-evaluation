module

public import LeanMath.CommodityClassification.FinitePartitionOrder
public import LeanMath.CommodityClassification.ExactCommodityPairRule

/-! The coarsest successful refinement, with uniqueness independent of labels. -/
@[expose] public section
noncomputable section
namespace CommodityClassification.Equilibrium.BenchmarkFamily
open InputCoordinates
variable {n k h g t : ℕ} (F : BenchmarkFamily n k h)

theorem samePolicyAttributes_refl (i : Fin n) : F.SamePolicyAttributes i i := by
  refine ⟨rfl,?_⟩
  convert (cancellationSpace (F.parents.Q F.q) F.report).zero_mem using 1
  ext a
  simp

theorem samePolicyAttributes_symm {i j : Fin n} (hij : F.SamePolicyAttributes i j) :
    F.SamePolicyAttributes j i := by
  refine ⟨hij.1.symm,?_⟩
  have hz := (cancellationSpace (F.parents.Q F.q) F.report).neg_mem hij.2
  convert hz using 1
  ext a
  simp only [Pi.neg_apply,neg_sub]

theorem samePolicyAttributes_trans {i j l : Fin n}
    (hij : F.SamePolicyAttributes i j) (hjl : F.SamePolicyAttributes j l) :
    F.SamePolicyAttributes i l := by
  refine ⟨hij.1.trans hjl.1,?_⟩
  have hz := (cancellationSpace (F.parents.Q F.q) F.report).add_mem hij.2 hjl.2
  convert hz using 1
  ext a
  simp only [Pi.add_apply,sub_add_sub_cancel]

def policySetoid : Setoid (Fin n) where
  r i j := F.parents.group i=F.parents.group j ∧ F.SamePolicyAttributes i j
  iseqv := ⟨fun i => ⟨rfl,F.samePolicyAttributes_refl i⟩,
    fun hij => ⟨hij.1.symm,F.samePolicyAttributes_symm hij.2⟩,
    fun hij hjl => ⟨hij.1.trans hjl.1,F.samePolicyAttributes_trans hij.2 hjl.2⟩⟩

def CoarsestSuccessful (P : Partition n g) : Prop :=
  Nonempty (Refinement P F.parents) ∧ F.ReportIdentified P ∧
    ∀ (t : ℕ) (Q : Partition n t), Nonempty (Refinement Q F.parents) →
      F.ReportIdentified Q → Nonempty (Refinement Q P)

theorem classification_of_policy_classes (hn : 0<n) (hnc : ¬ F.ParentIdentified)
    (P : Partition n g)
    (hc : ∀ i j : Fin n,P.group i=P.group j ↔
      F.parents.group i=F.parents.group j ∧ F.SamePolicyAttributes i j) :
    F.CoarsestSuccessful P := by
  have hpar : Nonempty (Refinement P F.parents) := (P.refinement_iff F.parents).mpr
    (fun i j hij => ((hc i j).mp hij).1)
  obtain ⟨R⟩ := hpar
  have hp : F.PairRule P := fun i j hij => ((hc i j).mp hij).2
  refine ⟨⟨R⟩,(F.exact_commodity_pair_rule_of_goods hn P R hnc).mpr hp,?_⟩
  rintro t Q ⟨RQ⟩ hQ
  have hpair := (F.exact_commodity_pair_rule_of_goods hn Q RQ hnc).mp hQ
  apply (Q.refinement_iff P).mpr
  intro i j hij
  exact (hc i j).mpr ⟨(Q.refinement_iff F.parents).mp ⟨RQ⟩ i j hij,hpair i j hij⟩

theorem exists_coarsest_successful (hn : 0<n) (hnc : ¬ F.ParentIdentified) :
    ∃ g, ∃ P : Partition n g,
      (∀ i j : Fin n,P.group i=P.group j ↔
        F.parents.group i=F.parents.group j ∧ F.SamePolicyAttributes i j) ∧
      F.CoarsestSuccessful P := by
  obtain ⟨g,P,hc⟩ := exists_partition_of_setoid F.policySetoid
  exact ⟨g,P,hc,F.classification_of_policy_classes hn hnc P hc⟩

theorem reportIdentified_of_refinement (hn : 0<n) (hnc : ¬ F.ParentIdentified)
    (P : Partition n g) (Q : Partition n t) (R : Refinement P F.parents)
    (RQ : Refinement Q P) (hp : F.ReportIdentified P) : F.ReportIdentified Q := by
  apply (F.exact_commodity_pair_rule_of_goods hn Q (RQ.trans R) hnc).mpr
  have hpair := (F.exact_commodity_pair_rule_of_goods hn P R hnc).mp hp
  intro i j hij
  exact hpair i j ((Q.refinement_iff P).mp ⟨RQ⟩ i j hij)

theorem coarsest_successful_characterization (hn : 0<n) (hnc : ¬ F.ParentIdentified)
    (P : Partition n g) (hp : F.CoarsestSuccessful P)
    (Q : Partition n t) (RQ : Refinement Q F.parents) :
    F.ReportIdentified Q ↔ Nonempty (Refinement Q P) := by
  constructor
  · exact hp.2.2 t Q ⟨RQ⟩
  · rintro ⟨R⟩
    obtain ⟨RP⟩ := hp.1
    exact F.reportIdentified_of_refinement hn hnc P Q RP R hp.2.1

theorem coarsest_successful_unique_cells (P : Partition n g) (Q : Partition n t)
    (hp : F.CoarsestSuccessful P) (hq : F.CoarsestSuccessful Q) :
    ∀ i j : Fin n,P.group i=P.group j ↔ Q.group i=Q.group j :=
  P.same_cells_of_mutual_refinement Q (hq.2.2 g P hp.1 hp.2.1) (hp.2.2 t Q hq.1 hq.2.1)

theorem coarsest_successful_unique_relabeling (P : Partition n g) (Q : Partition n t)
    (hp : F.CoarsestSuccessful P) (hq : F.CoarsestSuccessful Q) :
    ∃ e : Fin g ≃ Fin t, ∀ i : Fin n,e (P.group i)=Q.group i :=
  P.relabeling_of_same_cells Q (F.coarsest_successful_unique_cells P Q hp hq)

end CommodityClassification.Equilibrium.BenchmarkFamily
