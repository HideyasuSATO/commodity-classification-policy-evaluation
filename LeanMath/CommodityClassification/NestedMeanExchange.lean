module

public import LeanMath.CommodityClassification.RankOneConjugateUpdate

/-! The nested exchange has zero load and zero cross term at any cell mean. -/
@[expose] public section
noncomputable section
set_option maxHeartbeats 1000000
namespace CommodityClassification.InputCoordinates
open Matrix
variable {n k r : ℕ}

theorem Partition.exchange_report (P : Partition n r) (q : Vec n) (hq : ∀i,0<q i)
    (C : Mat n k) (i j : Fin n) (hij : P.group i=P.group j) (u : Vec k) (t : ℝ) :
    P.report q (C+t • vecMulVec (weightedExchange q i j) u)=P.report q C := by
  change (P.Q q).transpose*(C+t • vecMulVec (weightedExchange q i j) u)=_
  rw [Matrix.mul_add,Matrix.mul_smul,Matrix.mul_vecMulVec,
    P.weighted_exchange_hidden q hq i j hij,Matrix.zero_vecMulVec,smul_zero,add_zero]
  rfl

theorem Partition.mean_twoSupport_zero (P : Partition n r) (p q : Vec n)
    (hp : ∀i,0<p i) (C : Mat n k) (i j : Fin n) (hij : P.group i=P.group j) (δ : ℝ) :
    (P.mean p q C).transpose *ᵥ twoSupport i j (δ/p i) (δ/p j)=0 := by
  ext l
  simp only [twoSupport,Matrix.mulVec_sub,Matrix.mulVec_single,Pi.sub_apply,
    op_smul_eq_smul,Pi.smul_apply,smul_eq_mul,Matrix.col_apply,
    Matrix.transpose_apply,Partition.mean,Pi.zero_apply,hij]
  field_simp [(hp i).ne',(hp j).ne']
  ring

end CommodityClassification.InputCoordinates

namespace CommodityClassification.DemandNests.Data
open Matrix InputCoordinates
variable {n g k r : ℕ} (d : DemandNests.Data n g)

theorem exchange_load_zero (DG : Mat g g) (β : Vec g) (i j : Fin n)
    (hij : d.partition.group i=d.partition.group j) :
    dotProduct (weightedExchange d.q i j) (d.demandMatrix DG *ᵥ d.proportionalPolicy β)=0 := by
  rw [weighted_exchange_dot]
  exact sub_eq_zero.mpr (d.within_nest_policy_loads DG β i j hij)

theorem mean_exchange_orthogonal (DG : Mat g g) (σ : ℝ) (P : Partition n r)
    (RP : Refinement P d.partition) (C : Mat n k) (i j : Fin n) (hne : i≠j)
    (hij : P.group i=P.group j) :
    (P.mean d.p d.q C).transpose *ᵥ
      (Regularity.adjustedDemand d.p d.q (d.demandMatrix DG) σ *ᵥ weightedExchange d.q i j)=0 := by
  have hg : d.partition.group i=d.partition.group j := by rw [RP.compatible,RP.compatible,hij]
  rw [d.adjusted_exchange DG σ i j hne hg]
  exact P.mean_twoSupport_zero d.p d.q d.hp C i j hij _

theorem exchange_adjusted_quadratic (DG : Mat g g) (σ : ℝ) (i j : Fin n) (hne : i≠j)
    (hij : d.partition.group i=d.partition.group j) :
    dotProduct (weightedExchange d.q i j)
      (Regularity.adjustedDemand d.p d.q (d.demandMatrix DG) σ *ᵥ weightedExchange d.q i j)=
      (d.eta (d.partition.group i)-σ)*((d.p i*d.q i)⁻¹+(d.p j*d.q j)⁻¹) := by
  rw [d.adjusted_exchange DG σ i j hne hij,weighted_exchange_dot,
    twoSupport_at_left i j hne,twoSupport_at_right i j hne]
  field_simp [(d.hp i).ne',(d.hp j).ne',(d.hq i).ne',(d.hq j).ne']
  ring

theorem exchange_load_preserved (DG : Mat g g) (β : Vec g) (C : Mat n k) (i j : Fin n)
    (hij : d.partition.group i=d.partition.group j) (u : Vec k) (t : ℝ) :
    (C+t • vecMulVec (weightedExchange d.q i j) u).transpose *ᵥ
      (d.demandMatrix DG *ᵥ d.proportionalPolicy β)=
      C.transpose *ᵥ (d.demandMatrix DG *ᵥ d.proportionalPolicy β) := by
  simp only [Matrix.transpose_add,Matrix.transpose_smul,Matrix.transpose_vecMulVec,
    Matrix.add_mulVec,Matrix.smul_mulVec,Matrix.vecMulVec_mulVec,d.exchange_load_zero DG β i j hij,
    op_smul_eq_smul,zero_smul,smul_zero,add_zero]

theorem mean_exchange_K (DG : Mat g g) (hDG : DG.IsSymm) (σ : ℝ) (R : Mat k k)
    (P : Partition n r) (RP : Refinement P d.partition) (C : Mat n k)
    (i j : Fin n) (hne : i≠j) (hij : P.group i=P.group j) (u : Vec k) (t : ℝ) :
    Regularity.K d.p d.q (d.demandMatrix DG) R σ
      (P.mean d.p d.q C+t • vecMulVec (weightedExchange d.q i j) u)=
      Regularity.K d.p d.q (d.demandMatrix DG) R σ (P.mean d.p d.q C)+
        ((d.eta (d.partition.group i)-σ)*((d.p i*d.q i)⁻¹+(d.p j*d.q j)⁻¹)*t^2) • vecMulVec u u := by
  have hL : (Regularity.adjustedDemand d.p d.q (d.demandMatrix DG) σ).IsSymm := by
    change (Regularity.adjustedDemand d.p d.q (d.demandMatrix DG) σ).transpose=_
    simp only [Regularity.adjustedDemand,Matrix.transpose_sub,Matrix.transpose_smul,
      (d.demandMatrix_symmetric DG hDG).eq,Supply.xi,Matrix.diagonal_transpose]
  have hg : d.partition.group i=d.partition.group j := by rw [RP.compatible,RP.compatible,hij]
  rw [Regularity.K,RankOne.mean_conjugate_update _ hL _ _ _
    (d.mean_exchange_orthogonal DG σ P RP C i j hne hij),d.exchange_adjusted_quadratic DG σ i j hne hg]
  rw [Regularity.K,add_assoc]
  rw [mul_comm (t^2)]

end CommodityClassification.DemandNests.Data
