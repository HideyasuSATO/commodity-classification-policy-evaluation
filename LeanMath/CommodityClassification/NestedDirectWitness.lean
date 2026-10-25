module

public import LeanMath.CommodityClassification.NestedExchangeWelfare
public import LeanMath.CommodityClassification.EconomicClassificationWitnesses

/-! The printed direct two-product witness, arbitrarily close to a positive mean. -/
@[expose] public section
noncomputable section
set_option maxHeartbeats 1200000
namespace CommodityClassification.Equilibrium.BenchmarkFamily
open Matrix InputCoordinates Filter
open scoped Topology
variable {n k h g r : ℕ} (F : BenchmarkFamily n k h)

theorem pairExchange_small_nonzero (P : Partition n r) (RP : Refinement P F.parents)
    (C0 : F.Candidate) (i j : Fin n) (hij : P.group i=P.group j) (u : Vec k)
    (V : Set ℝ) (hV : V∈𝓝 0) :
    ∃t∈V,t≠0 ∧ F.pairExchange C0 i j u t∈F.frame.Candidates F.p F.q F.parents F.report := by
  have hc := F.pairExchange_candidates P RP C0 i j hij u
  have hn : ∀ᶠt : ℝ in 𝓝[≠] 0,t≠0 := self_mem_nhdsWithin
  have hv : ∀ᶠt : ℝ in 𝓝[≠] 0,t∈V := Filter.Eventually.filter_mono inf_le_left hV
  have hh := hv.and (hn.and (hc.filter_mono inf_le_left))
  exact hh.exists

theorem nested_direct_common_benchmark_witness
    (G : Partition n g) (η : Vec g) (hη : ∀a,0<η a) (DG : Mat g g) (hDG : DG.IsSymm) (β : Vec g)
    (hD : F.D=(F.nestData G η hη).demandMatrix DG)
    (hb : F.b=(F.nestData G η hη).proportionalPolicy β)
    (P : Partition n r) (RP : Refinement P F.parents) (RG : Refinement P G)
    (hnc : ¬F.ParentIdentified) (i j : Fin n) (hne : i≠j) (hij : P.group i=P.group j)
    (hmis : η (G.group i)≠F.sigma) (s0 c : ℝ) (hs : 0<s0) :
    ∃C0 : F.Candidate,P.mean F.p F.q C0.val=C0.val ∧ (F.model C0).m≠0 ∧
      ∀V : Set ℝ,V∈𝓝 0 → ∃t∈V,t≠0 ∧ ∃C : F.Candidate,
        C.val=F.pairExchange C0 i j (F.responseY C0) t ∧ F.SameObservationWitness P C C0 s0 c := by
  obtain ⟨C0,hmean,hm⟩ := F.exists_nested_nonzero_mean G η hη DG β hD hb P RP RG hnc
  refine ⟨C0,hmean,hm,?_⟩
  intro V hV
  obtain ⟨t,htV,ht,hCand⟩ := F.pairExchange_small_nonzero P RP C0 i j hij (F.responseY C0) V hV
  let C : F.Candidate := ⟨F.pairExchange C0 i j (F.responseY C0) t,hCand⟩
  have hr : P.report F.q C.val=P.report F.q C0.val :=
    F.pairExchange_report P C0 i j hij (F.responseY C0) t
  refine ⟨t,htV,ht,C,rfl,hr,?_,?_,F.every_candidate_equilibrium hs c C,
    F.every_candidate_equilibrium hs c C0⟩
  · change P.report F.q (F.frame.reconstruct F.p C.val)=P.report F.q (F.frame.reconstruct F.p C0.val)
    rw [P.report_reconstruct,P.report_reconstruct,hr]
  · exact F.nested_pairExchange_welfare_nonzero (F.goods_pos_of_parent_nonidentified hnc)
      G η hη DG hDG β hD hb P RG C0 C hmean hm i j hne hij hmis t ht rfl

theorem candidate_actual_loss_expansion (hn : 0<n) (C : F.Candidate) (s0 c : ℝ) (hs : 0<s0) :
    ∃u : ℝ → Vec k,∃s : ℝ → ℝ,(F.model C).PositiveLocalPath s0 u s ∧
      (F.model C).WelfareExpansion (F.commonUtility c) u s := by
  obtain ⟨u,s,hp,he⟩ := F.candidate_expansion_with_coefficient (F.total_positive_of_goods hn) C s0 c hs
  refine ⟨u,s,hp,?_⟩
  unfold Model.WelfareExpansion
  rw [F.candidate_lossCoefficient]
  exact he

end CommodityClassification.Equilibrium.BenchmarkFamily
