module

public import LeanMath.CommodityClassification.NestedCompetitiveImplementation

/-! Same-report positive witnesses with original nested utility and actual GE welfare. -/
@[expose] public section
noncomputable section
set_option maxHeartbeats 1200000
namespace CommodityClassification.Equilibrium.BenchmarkFamily
open Matrix InputCoordinates Filter
open scoped Topology
variable {n k h g r : ℕ} (F : BenchmarkFamily n k h)
  (G : Partition n g) (η : Vec g) (hη : ∀a,0<η a)
  (DG : Mat g g) (hD : F.D=(F.nestData G η hη).demandMatrix DG)

def NestedSameObservationWitness (P : Partition n r) (C E : F.Candidate) (s0 c : ℝ) : Prop :=
  P.report F.q C.val=P.report F.q E.val ∧
  P.report F.q (F.nestedModel G η hη DG hD C).A=P.report F.q (F.nestedModel G η hη DG hD E).A ∧
  (F.nestedModel G η hη DG hD C).lossCoefficient≠(F.nestedModel G η hη DG hD E).lossCoefficient ∧
  F.NestedImplementation G η hη DG hD C s0 c ∧
  F.NestedImplementation G η hη DG hD E s0 c

theorem same_report_witness_nested_transfer (hDG : DG.PosDef) (hn : 0<n)
    (P : Partition n r) (C E : F.Candidate) (s0 c : ℝ) (hs : 0<s0)
    (hw : F.SameObservationWitness P C E s0 c) :
    F.NestedSameObservationWitness G η hη DG hD P C E s0 c :=
  ⟨hw.1,hw.2.1,hw.2.2.1,
    F.nested_candidate_implementation G η hη DG hD hDG hn C s0 c hs,
    F.nested_candidate_implementation G η hη DG hD hDG hn E s0 c hs⟩

theorem nested_direct_original_utility_witness (hDG : DG.PosDef) (β : Vec g)
    (hb : F.b=(F.nestData G η hη).proportionalPolicy β)
    (P : Partition n r) (RP : Refinement P F.parents) (RG : Refinement P G)
    (hnc : ¬F.ParentIdentified) (i j : Fin n) (hne : i≠j) (hij : P.group i=P.group j)
    (hmis : η (G.group i)≠F.sigma) (s0 c : ℝ) (hs : 0<s0) :
    ∃C0 : F.Candidate,P.mean F.p F.q C0.val=C0.val ∧ (F.nestedModel G η hη DG hD C0).m≠0 ∧
      ∀V : Set ℝ,V∈𝓝 0 → ∃t∈V,t≠0 ∧ ∃C : F.Candidate,
        C.val=F.pairExchange C0 i j (F.responseY C0) t ∧
          F.NestedSameObservationWitness G η hη DG hD P C C0 s0 c := by
  obtain ⟨C0,hmean,hm,hw⟩ := F.nested_direct_common_benchmark_witness G η hη DG hDG.isHermitian.isSymm β
    hD hb P RP RG hnc i j hne hij hmis s0 c hs
  refine ⟨C0,hmean,hm,?_⟩
  intro V hV
  obtain ⟨t,htV,ht,C,hC,hW⟩ := hw V hV
  exact ⟨t,htV,ht,C,hC,F.same_report_witness_nested_transfer G η hη DG hD hDG
    (F.goods_pos_of_parent_nonidentified hnc) P C C0 s0 c hs hW⟩

end CommodityClassification.Equilibrium.BenchmarkFamily
