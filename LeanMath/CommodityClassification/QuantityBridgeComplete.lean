module

public import LeanMath.CommodityClassification.QuantityIdentificationNecessity

/-! Complete eq:bridge: both preservation objectives and the structural form. -/
@[expose] public section
noncomputable section
namespace CommodityClassification.Equilibrium.BenchmarkFamily
open InputCoordinates
variable {n k h g r : ℕ} (F : BenchmarkFamily n k h)

theorem welfare_and_quantities_iff_strong (hn : 0<n) (P : Partition n g)
    (R : Refinement P F.parents) (H : HiddenBasis (P.Q F.q) r)
    (hnc : ¬F.ParentIdentified) :
    (F.ReportIdentified P ∧ F.GroupQuantitiesIdentified P) ↔ F.StrongReportRestrictions H.N :=
  ⟨fun h => F.both_identifications_require_strong hn P R H hnc h.1 h.2,
    F.strong_restrictions_identify_both hn P R H hnc⟩

theorem welfare_and_quantities_iff_policy_demand (hn : 0<n) (P : Partition n g)
    (R : Refinement P F.parents) (H : HiddenBasis (P.Q F.q) r)
    (hnc : ¬F.ParentIdentified) :
    (F.ReportIdentified P ∧ F.GroupQuantitiesIdentified P) ↔ F.PolicyDemandForm P :=
  (F.welfare_and_quantities_iff_strong hn P R H hnc).trans
    (F.strong_report_restrictions_iff_policy_demand P H)

end CommodityClassification.Equilibrium.BenchmarkFamily
