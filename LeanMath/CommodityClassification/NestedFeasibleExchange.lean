module

public import LeanMath.CommodityClassification.NestedPositiveMean

/-! Small exchanges are actual positive economic candidates with the printed m,K. -/
@[expose] public section
noncomputable section
set_option maxHeartbeats 1000000
namespace CommodityClassification.Equilibrium.BenchmarkFamily
open Matrix InputCoordinates Filter
open scoped Topology
variable {n k h g r : ℕ} (F : BenchmarkFamily n k h)

def pairExchange (C0 : F.Candidate) (i j : Fin n) (u : Vec k) (t : ℝ) : Mat n k :=
  C0.val+t • vecMulVec (weightedExchange F.q i j) u

theorem pairExchange_zero (C0 : F.Candidate) (i j : Fin n) (u : Vec k) :
    F.pairExchange C0 i j u 0=C0.val := by simp only [pairExchange,zero_smul,add_zero]

theorem pairExchange_report (P : Partition n r) (C0 : F.Candidate) (i j : Fin n)
    (hij : P.group i=P.group j) (u : Vec k) (t : ℝ) :
    P.report F.q (F.pairExchange C0 i j u t)=P.report F.q C0.val :=
  P.exchange_report F.q F.hq C0.val i j hij u t

theorem pairExchange_candidates (P : Partition n r) (RP : Refinement P F.parents)
    (C0 : F.Candidate) (i j : Fin n) (hij : P.group i=P.group j) (u : Vec k) :
    ∀ᶠt : ℝ in 𝓝 0,F.pairExchange C0 i j u t∈F.frame.Candidates F.p F.q F.parents F.report := by
  have hc : Continuous (F.pairExchange C0 i j u) := by unfold pairExchange;fun_prop
  have ht := hc.continuousAt.preimage_mem_nhds
    (show F.frame.PositiveDomain F.p∈𝓝 (F.pairExchange C0 i j u 0) from by
      rw [F.pairExchange_zero]
      exact (F.frame.positiveDomain_open F.p).mem_nhds C0.property.1)
  filter_upwards [ht] with t hp
  exact ⟨hp,(RP.report_preserved F.q _ _ (F.pairExchange_report P C0 i j hij u t)).trans C0.property.2⟩

theorem nested_pairExchange_m (G : Partition n g) (η : Vec g) (hη : ∀a,0<η a)
    (DG : Mat g g) (β : Vec g)
    (hD : F.D=(F.nestData G η hη).demandMatrix DG)
    (hb : F.b=(F.nestData G η hη).proportionalPolicy β)
    (C0 C : F.Candidate) (i j : Fin n) (hij : G.group i=G.group j) (u : Vec k) (t : ℝ)
    (hC : C.val=F.pairExchange C0 i j u t) : (F.model C).m=(F.model C0).m := by
  change C.val.transpose *ᵥ (F.D *ᵥ F.b)=C0.val.transpose *ᵥ (F.D *ᵥ F.b)
  rw [hC,hD,hb]
  exact (F.nestData G η hη).exchange_load_preserved DG β C0.val i j hij u t

theorem nested_pairExchange_K (G : Partition n g) (η : Vec g) (hη : ∀a,0<η a)
    (DG : Mat g g) (hDG : DG.IsSymm)
    (hD : F.D=(F.nestData G η hη).demandMatrix DG)
    (P : Partition n r) (RG : Refinement P G) (C0 C : F.Candidate)
    (hmean : P.mean F.p F.q C0.val=C0.val) (i j : Fin n) (hne : i≠j)
    (hij : P.group i=P.group j) (u : Vec k) (t : ℝ)
    (hC : C.val=F.pairExchange C0 i j u t) :
    (F.model C).K=(F.model C0).K+
      ((η (G.group i)-F.sigma)*((F.p i*F.q i)⁻¹+(F.p j*F.q j)⁻¹)*t^2) • vecMulVec u u := by
  have hh := (F.nestData G η hη).mean_exchange_K DG hDG F.sigma F.fixedR P RG C0.val i j hne hij u t
  have hmean' : P.mean (F.nestData G η hη).p (F.nestData G η hη).q C0.val=C0.val := hmean
  rw [hmean'] at hh
  change Regularity.K F.p F.q F.D (F.model C).R F.sigma C.val=
    Regularity.K F.p F.q F.D (F.model C0).R F.sigma C0.val+_
  rw [F.candidate_R_fixed C,F.candidate_R_fixed C0,hC,hD]
  exact hh

end CommodityClassification.Equilibrium.BenchmarkFamily
