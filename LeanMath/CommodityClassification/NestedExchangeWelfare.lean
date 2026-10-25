module

public import LeanMath.CommodityClassification.NestedFeasibleExchange

/-! Exact welfare change of the actual feasible mismatch exchange. -/
@[expose] public section
noncomputable section
set_option maxHeartbeats 1200000
namespace CommodityClassification.Equilibrium.BenchmarkFamily
open Matrix InputCoordinates
variable {n k h g r : ℕ} (F : BenchmarkFamily n k h)

def pairMismatchDelta (G : Partition n g) (η : Vec g) (i j : Fin n) (t : ℝ) : ℝ :=
  (η (G.group i)-F.sigma)*((F.p i*F.q i)⁻¹+(F.p j*F.q j)⁻¹)*t^2

theorem pairMismatchDelta_nonzero (G : Partition n g) (η : Vec g) (i j : Fin n)
    (hm : η (G.group i)≠F.sigma) (t : ℝ) (ht : t≠0) : F.pairMismatchDelta G η i j t≠0 := by
  have hs : 0<(F.p i*F.q i)⁻¹+(F.p j*F.q j)⁻¹ :=
    add_pos (inv_pos.mpr (mul_pos (F.hp i) (F.hq i))) (inv_pos.mpr (mul_pos (F.hp j) (F.hq j)))
  exact mul_ne_zero (mul_ne_zero (sub_ne_zero.mpr hm) hs.ne') (pow_ne_zero _ ht)

theorem nested_pairExchange_welfare_formula (hn : 0<n)
    (G : Partition n g) (η : Vec g) (hη : ∀a,0<η a) (DG : Mat g g) (hDG : DG.IsSymm) (β : Vec g)
    (hD : F.D=(F.nestData G η hη).demandMatrix DG)
    (hb : F.b=(F.nestData G η hη).proportionalPolicy β)
    (P : Partition n r) (RG : Refinement P G) (C0 C : F.Candidate)
    (hmean : P.mean F.p F.q C0.val=C0.val) (i j : Fin n) (hne : i≠j)
    (hij : P.group i=P.group j) (u : Vec k) (t : ℝ)
    (hC : C.val=F.pairExchange C0 i j u t) :
    0<1+F.pairMismatchDelta G η i j t*dotProduct u ((F.model C0).K⁻¹ *ᵥ u) ∧
    (F.model C).lossCoefficient-(F.model C0).lossCoefficient=
      F.pairMismatchDelta G η i j t*(dotProduct u ((F.model C0).K⁻¹ *ᵥ (F.model C0).m))^2/
        (1+F.pairMismatchDelta G η i j t*dotProduct u ((F.model C0).K⁻¹ *ᵥ u)) := by
  have hg : G.group i=G.group j := by rw [RG.compatible,RG.compatible,hij]
  have hm := F.nested_pairExchange_m G η hη DG β hD hb C0 C i j hg u t hC
  have hK : (F.model C).K=(F.model C0).K+F.pairMismatchDelta G η i j t • vecMulVec u u :=
    F.nested_pairExchange_K G η hη DG hDG hD P RG C0 C hmean i j hne hij u t hC
  have hK0 := F.candidate_model_K_posDef hn C0
  have hKt : ((F.model C0).K+F.pairMismatchDelta G η i j t • vecMulVec u u).PosDef := by
    rw [←hK]
    exact F.candidate_model_K_posDef hn C
  refine ⟨RankOne.denominator_pos _ hK0 u _ hKt,?_⟩
  change (dotProduct F.b (F.D *ᵥ F.b)-dotProduct (F.model C).m ((F.model C).K⁻¹ *ᵥ (F.model C).m))-
    (dotProduct F.b (F.D *ᵥ F.b)-dotProduct (F.model C0).m ((F.model C0).K⁻¹ *ᵥ (F.model C0).m))=_
  rw [hm,hK]
  exact RankOne.welfare_change _ hK0 u (F.model C0).m _ _ hKt

theorem nested_pairExchange_welfare_nonzero (hn : 0<n)
    (G : Partition n g) (η : Vec g) (hη : ∀a,0<η a) (DG : Mat g g) (hDG : DG.IsSymm) (β : Vec g)
    (hD : F.D=(F.nestData G η hη).demandMatrix DG)
    (hb : F.b=(F.nestData G η hη).proportionalPolicy β)
    (P : Partition n r) (RG : Refinement P G) (C0 C : F.Candidate)
    (hmean : P.mean F.p F.q C0.val=C0.val) (hm : (F.model C0).m≠0)
    (i j : Fin n) (hne : i≠j) (hij : P.group i=P.group j)
    (hmis : η (G.group i)≠F.sigma) (t : ℝ) (ht : t≠0)
    (hC : C.val=F.pairExchange C0 i j (F.responseY C0) t) :
    (F.model C).lossCoefficient≠(F.model C0).lossCoefficient := by
  obtain ⟨hd,he⟩ := F.nested_pairExchange_welfare_formula hn G η hη DG hDG β hD hb P RG
    C0 C hmean i j hne hij (F.responseY C0) t hC
  have hu : dotProduct (F.responseY C0) (F.responseY C0)≠0 := by
    intro hz
    exact RankOne.inverse_vector_nonzero _ (F.candidate_model_K_posDef hn C0) _ hm
      (dotProduct_self_eq_zero.mp hz)
  apply sub_ne_zero.mp
  rw [he]
  exact div_ne_zero (mul_ne_zero (F.pairMismatchDelta_nonzero G η i j hmis t ht) (pow_ne_zero _ hu)) hd.ne'

end CommodityClassification.Equilibrium.BenchmarkFamily
