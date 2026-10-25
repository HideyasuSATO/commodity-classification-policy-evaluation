module

public import LeanMath.CommodityClassification.NestedMatchingPairRule

/-! The unique coarsest successful refinement inside the specified demand nests. -/
@[expose] public section
noncomputable section
set_option maxHeartbeats 600000
namespace CommodityClassification.InputCoordinates
variable {n g t : ℕ}

def Partition.matchingSetoid (G : Partition n g) (η : Fin g → ℝ) (σ : ℝ) : Setoid (Fin n) where
  r i j := G.group i=G.group j ∧ (i=j ∨ η (G.group i)=σ)
  iseqv := ⟨fun _ => ⟨rfl,Or.inl rfl⟩,
    fun hij => ⟨hij.1.symm,hij.2.elim (fun he => Or.inl he.symm)
      (fun he => Or.inr (hij.1 ▸ he))⟩,
    fun hij hjl => ⟨hij.1.trans hjl.1,hij.2.elim
      (fun he => he ▸ hjl.2) (fun he => Or.inr he)⟩⟩

theorem Partition.pair_matching_iff_cells (P : Partition n t) (G : Partition n g)
    (η : Fin g → ℝ) (σ : ℝ) :
    (∀i j : Fin n,i≠j → P.group i=P.group j → η (G.group i)=σ) ↔
      ∀a,1<(P.cell a).card → ∀i∈P.cell a,η (G.group i)=σ := by
  constructor
  · intro hp a ha i hi
    obtain ⟨j,hj,hji⟩ := Finset.exists_mem_ne ha i
    exact hp i j hji.symm (((P.mem_cell a i).mp hi).trans ((P.mem_cell a j).mp hj).symm)
  · intro hc i j hne hg
    have hi : i∈P.cell (P.group i) := (P.mem_cell _ _).mpr rfl
    have hj : j∈P.cell (P.group i) := (P.mem_cell _ _).mpr hg.symm
    exact hc _ (Finset.one_lt_card.mpr ⟨i,hi,j,hj,hne⟩) i hi

end CommodityClassification.InputCoordinates

namespace CommodityClassification.Equilibrium.BenchmarkFamily
open InputCoordinates
variable {n k h g t s : ℕ} (F : BenchmarkFamily n k h)

def CoarsestWithinNests (G : Partition n g) (P : Partition n t) : Prop :=
  Nonempty (Refinement P G) ∧ F.ReportIdentified P ∧
    ∀(s : ℕ) (Q : Partition n s),Nonempty (Refinement Q G) →
      F.ReportIdentified Q → Nonempty (Refinement Q P)

theorem nested_reporting_cells_iff (G : Partition n g) (η : Vec g) (hη : ∀a,0<η a)
    (DG : Matrix (Fin g) (Fin g) ℝ) (β : Vec g)
    (hD : F.D=(F.nestData G η hη).demandMatrix DG)
    (hb : F.b=(F.nestData G η hη).proportionalPolicy β)
    (RG : Refinement G F.parents) (P : Partition n t) (RP : Refinement P G)
    (hnc : ¬F.ParentIdentified) :
    F.ReportIdentified P ↔ ∀a,1<(P.cell a).card → ∀i∈P.cell a,η (G.group i)=F.sigma :=
  (F.nested_report_identification_iff G η hη DG β hD hb RG P RP hnc).trans
    (P.pair_matching_iff_cells G η F.sigma)

theorem nested_coarsest_of_cells (G : Partition n g) (η : Vec g) (hη : ∀a,0<η a)
    (DG : Matrix (Fin g) (Fin g) ℝ) (β : Vec g)
    (hD : F.D=(F.nestData G η hη).demandMatrix DG)
    (hb : F.b=(F.nestData G η hη).proportionalPolicy β)
    (RG : Refinement G F.parents) (hnc : ¬F.ParentIdentified) (P : Partition n t)
    (hc : ∀i j : Fin n,P.group i=P.group j ↔
      G.group i=G.group j ∧ (i=j ∨ η (G.group i)=F.sigma)) :
    F.CoarsestWithinNests G P := by
  obtain ⟨RP⟩ := (P.refinement_iff G).mpr (fun i j hij => ((hc i j).mp hij).1)
  have hP : F.ReportIdentified P :=
    (F.nested_report_identification_iff G η hη DG β hD hb RG P RP hnc).mpr
      (fun i j hne hij => ((hc i j).mp hij).2.resolve_left hne)
  refine ⟨⟨RP⟩,hP,?_⟩
  rintro s Q ⟨RQ⟩ hQ
  have hpair := (F.nested_report_identification_iff G η hη DG β hD hb RG Q RQ hnc).mp hQ
  apply (Q.refinement_iff P).mpr
  intro i j hij
  refine (hc i j).mpr ⟨(Q.refinement_iff G).mp ⟨RQ⟩ i j hij,?_⟩
  by_cases he : i=j
  · exact Or.inl he
  · exact Or.inr (hpair i j he hij)

theorem exists_nested_coarsest (G : Partition n g) (η : Vec g) (hη : ∀a,0<η a)
    (DG : Matrix (Fin g) (Fin g) ℝ) (β : Vec g)
    (hD : F.D=(F.nestData G η hη).demandMatrix DG)
    (hb : F.b=(F.nestData G η hη).proportionalPolicy β)
    (RG : Refinement G F.parents) (hnc : ¬F.ParentIdentified) :
    ∃t,∃P : Partition n t,
      (∀i j : Fin n,P.group i=P.group j ↔
        G.group i=G.group j ∧ (i=j ∨ η (G.group i)=F.sigma)) ∧
      F.CoarsestWithinNests G P := by
  obtain ⟨t,P,hc⟩ := exists_partition_of_setoid (G.matchingSetoid η F.sigma)
  exact ⟨t,P,hc,F.nested_coarsest_of_cells G η hη DG β hD hb RG hnc P hc⟩

theorem nested_coarsest_unique_cells (G : Partition n g) (P : Partition n t) (Q : Partition n s)
    (hP : F.CoarsestWithinNests G P) (hQ : F.CoarsestWithinNests G Q) :
    ∀i j : Fin n,P.group i=P.group j ↔ Q.group i=Q.group j :=
  P.same_cells_of_mutual_refinement Q (hQ.2.2 t P hP.1 hP.2.1) (hP.2.2 s Q hQ.1 hQ.2.1)

theorem nested_coarsest_unique_relabeling (G : Partition n g) (P : Partition n t) (Q : Partition n s)
    (hP : F.CoarsestWithinNests G P) (hQ : F.CoarsestWithinNests G Q) :
    ∃e : Fin t ≃ Fin s,∀i : Fin n,e (P.group i)=Q.group i :=
  P.relabeling_of_same_cells Q (F.nested_coarsest_unique_cells G P Q hP hQ)

theorem nested_coarsest_characterization (G : Partition n g) (P : Partition n t)
    (hP : F.CoarsestWithinNests G P) (RG : Refinement G F.parents)
    (Q : Partition n s) (RQ : Refinement Q G) (hnc : ¬F.ParentIdentified) :
    F.ReportIdentified Q ↔ Nonempty (Refinement Q P) := by
  constructor
  · exact hP.2.2 s Q ⟨RQ⟩
  · rintro ⟨RQP⟩
    obtain ⟨RP⟩ := hP.1
    exact F.reportIdentified_of_refinement (F.goods_pos_of_parent_nonidentified hnc) hnc
      P Q (RP.trans RG) RQP hP.2.1

end CommodityClassification.Equilibrium.BenchmarkFamily
