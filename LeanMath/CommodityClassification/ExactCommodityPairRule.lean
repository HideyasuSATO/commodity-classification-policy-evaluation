module

public import LeanMath.CommodityClassification.WeightedPairRestrictions
public import LeanMath.CommodityClassification.EconomicLinearRestrictions

/-! The actual commodity-pair welfare identification rule of Theorem 1. -/
@[expose] public section
noncomputable section
set_option maxHeartbeats 2400000
namespace CommodityClassification.Equilibrium.BenchmarkFamily
open Matrix
variable {n k g h r : ℕ} (F : BenchmarkFamily n k h)

def SamePolicyAttributes (i j : Fin n) : Prop :=
  (F.D *ᵥ F.b) i/F.q i=(F.D *ᵥ F.b) j/F.q j ∧
    (fun a => (Regularity.adjustedDemand F.p F.q F.D F.sigma) a i/F.q i-
      (Regularity.adjustedDemand F.p F.q F.D F.sigma) a j/F.q j) ∈
      InputCoordinates.cancellationSpace (F.parents.Q F.q) F.report

def PairRule (P : InputCoordinates.Partition n g) : Prop :=
  ∀ i j : Fin n,P.group i=P.group j → F.SamePolicyAttributes i j

theorem linear_restrictions_iff_pair_rule (P : InputCoordinates.Partition n g)
    (H : InputCoordinates.HiddenBasis (P.Q F.q) r) :
    F.LinearReportRestrictions H.N ↔ F.PairRule P := by
  have hd := H.annihilator_pair_iff P F.q (F.D *ᵥ F.b) F.hq
  have hS := H.image_columns_pair_iff P F.q F.hq
    (Regularity.adjustedDemand F.p F.q F.D F.sigma)
    (InputCoordinates.cancellationSpace (F.parents.Q F.q) F.report)
  have hΓ := InputCoordinates.matrix_columns_cancellation_iff (F.parents.Q F.q) F.report
    (Regularity.adjustedDemand F.p F.q F.D F.sigma * H.N)
  constructor
  · rintro ⟨hr,hfactor⟩ i j hij
    exact ⟨hd.mp hr i j hij,hS.mp (hΓ.mpr hfactor) i j hij⟩
  · intro hp
    refine ⟨hd.mpr (fun i j hij => (hp i j hij).1),?_⟩
    apply hΓ.mp
    exact hS.mpr (fun i j hij => (hp i j hij).2)

theorem exact_commodity_pair_rule
    (hI : ∀j,0<Supply.totalInputs F.q (F.frame.reconstruct F.p F.reference) j)
    (P : InputCoordinates.Partition n g) (R : InputCoordinates.Refinement P F.parents)
    (hnc : ¬ F.ParentIdentified) : F.ReportIdentified P ↔ F.PairRule P := by
  obtain ⟨r,⟨H⟩⟩ := InputCoordinates.exists_hiddenBasis (P.Q F.q)
  exact (F.report_identified_iff_linear_restrictions hI P R H hnc).trans
    (F.linear_restrictions_iff_pair_rule P H)

theorem exact_commodity_pair_rule_of_goods (hn : 0<n)
    (P : InputCoordinates.Partition n g) (R : InputCoordinates.Refinement P F.parents)
    (hnc : ¬ F.ParentIdentified) : F.ReportIdentified P ↔ F.PairRule P :=
  F.exact_commodity_pair_rule (F.total_positive_of_goods hn) P R hnc

end CommodityClassification.Equilibrium.BenchmarkFamily
