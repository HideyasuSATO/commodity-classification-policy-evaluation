module

public import LeanMath.CommodityClassification.NestedExchangeIdentities

/-! Connect actual nested demand to the established all-answer pair theorem. -/
@[expose] public section
noncomputable section
set_option maxHeartbeats 600000
namespace CommodityClassification.Equilibrium.BenchmarkFamily
open Matrix InputCoordinates
variable {n k h g t : ℕ} (F : BenchmarkFamily n k h)

def nestData (G : Partition n g) (η : Vec g) (hη : ∀a,0<η a) : DemandNests.Data n g :=
  ⟨G,F.p,F.q,η,F.hp,F.hq,hη⟩

theorem goods_pos_of_parent_nonidentified (hnc : ¬F.ParentIdentified) : 0<n := by
  by_contra hn
  have hz : n=0 := Nat.eq_zero_of_not_pos hn
  subst n
  apply hnc
  intro C
  have he : C.val=F.reference := Subsingleton.elim _ _
  rw [he]

theorem nested_samePolicyAttributes_iff (G : Partition n g) (η : Vec g) (hη : ∀a,0<η a)
    (DG : Matrix (Fin g) (Fin g) ℝ) (β : Vec g)
    (hD : F.D=(F.nestData G η hη).demandMatrix DG)
    (hb : F.b=(F.nestData G η hη).proportionalPolicy β)
    (RG : Refinement G F.parents) (i j : Fin n) (hne : i≠j) (hgroup : G.group i=G.group j) :
    F.SamePolicyAttributes i j ↔ η (G.group i)=F.sigma := by
  let d := F.nestData G η hη
  have hload : (F.D *ᵥ F.b) i/F.q i=(F.D *ᵥ F.b) j/F.q j := by
    rw [hD,hb]
    exact d.within_nest_policy_loads DG β i j hgroup
  have himage : (fun a => Regularity.adjustedDemand F.p F.q F.D F.sigma a i/F.q i-
      Regularity.adjustedDemand F.p F.q F.D F.sigma a j/F.q j)=
      twoSupport i j ((η (G.group i)-F.sigma)/F.p i) ((η (G.group i)-F.sigma)/F.p j) := by
    rw [←weighted_exchange_image,hD]
    exact d.adjusted_exchange DG F.sigma i j hne hgroup
  have hparent := (G.refinement_iff F.parents).mp ⟨RG⟩ i j hgroup
  unfold SamePolicyAttributes
  rw [himage,twoSupport_common_difference_cancellation_iff F.parents F.p F.q F.hp F.hq
    F.report i j hne hparent,sub_eq_zero]
  exact and_iff_right hload

theorem nested_report_identification_iff (G : Partition n g) (η : Vec g) (hη : ∀a,0<η a)
    (DG : Matrix (Fin g) (Fin g) ℝ) (β : Vec g)
    (hD : F.D=(F.nestData G η hη).demandMatrix DG)
    (hb : F.b=(F.nestData G η hη).proportionalPolicy β)
    (RG : Refinement G F.parents) (P : Partition n t) (RP : Refinement P G)
    (hnc : ¬F.ParentIdentified) :
    F.ReportIdentified P ↔ ∀i j : Fin n,i≠j → P.group i=P.group j → η (G.group i)=F.sigma := by
  rw [F.exact_commodity_pair_rule_of_goods (F.goods_pos_of_parent_nonidentified hnc)
    P (RP.trans RG) hnc]
  constructor
  · intro hp i j hne hg
    exact (F.nested_samePolicyAttributes_iff G η hη DG β hD hb RG i j hne
      ((P.refinement_iff G).mp ⟨RP⟩ i j hg)).mp (hp i j hg)
  · intro hp i j hg
    by_cases he : i=j
    · subst j;exact F.samePolicyAttributes_refl i
    · exact (F.nested_samePolicyAttributes_iff G η hη DG β hD hb RG i j he
        ((P.refinement_iff G).mp ⟨RP⟩ i j hg)).mpr (hp i j he hg)

end CommodityClassification.Equilibrium.BenchmarkFamily
