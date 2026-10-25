module

public import LeanMath.CommodityClassification.GroupQuantityResponses

/-! Strong restrictions preserve both actual group responses and welfare. -/
@[expose] public section
noncomputable section
namespace CommodityClassification.Equilibrium.BenchmarkFamily
open Matrix InputCoordinates
variable {n k h g r : ℕ} (F : BenchmarkFamily n k h)

theorem valueAggregation_adjusted_hidden (P : Partition n g) (H : HiddenBasis (P.Q F.q) r) :
    P.valueAggregation F.p*F.D*H.N=
      P.valueAggregation F.p*Regularity.adjustedDemand F.p F.q F.D F.sigma*H.N := by
  have hx : P.valueAggregation F.p*Supply.xi F.p F.q*H.N=0 := by
    rw [P.valueAggregation_xi F.p F.q F.hp,H.annihilates]
  simp only [Regularity.adjustedDemand,Matrix.mul_sub,Matrix.mul_smul,Matrix.sub_mul,Matrix.smul_mul,hx,smul_zero,sub_zero]

theorem valueAggregation_hidden_zero (P : Partition n g) (H : HiddenBasis (P.Q F.q) r)
    (hLN : Regularity.adjustedDemand F.p F.q F.D F.sigma*H.N=0) :
    P.valueAggregation F.p*F.D*H.N=0 := by
  rw [F.valueAggregation_adjusted_hidden P H,Matrix.mul_assoc,hLN,Matrix.mul_zero]

theorem strong_restrictions_linear (N : Mat n r) (hs : F.StrongReportRestrictions N) :
    F.LinearReportRestrictions N := by
  refine ⟨hs.2,0,?_,?_⟩
  · rw [hs.1,Matrix.mul_zero]
  · exact Matrix.mul_zero _

theorem strong_restrictions_moments (hn : 0<n) (P : Partition n g)
    (R : Refinement P F.parents) (H : HiddenBasis (P.Q F.q) r)
    (hnc : ¬F.ParentIdentified) (hs : F.StrongReportRestrictions H.N) :
    F.ReportMomentsPreserved P :=
  (F.report_moments_iff_linear_restrictions (F.total_positive_of_goods hn)
    (F.positive_relative_dimension_of_parent_failure hnc) P R H).mpr
    (F.strong_restrictions_linear H.N hs)

theorem strong_restrictions_identify_quantities (hn : 0<n) (P : Partition n g)
    (R : Refinement P F.parents) (H : HiddenBasis (P.Q F.q) r)
    (hnc : ¬F.ParentIdentified) (hs : F.StrongReportRestrictions H.N) :
    F.GroupQuantitiesIdentified P := by
  have hm := F.strong_restrictions_moments hn P R H hnc hs
  intro C E he
  obtain ⟨hmom,hK⟩ := hm C E he
  obtain ⟨Z,hZ⟩ := (H.fiber_exists_iff E.val C.val).mp he
  have hd := F.groupQuantityResponse_variation P C E H.N Z hZ
    (F.responseY_eq_of_moments C E hmom hK)
  rw [F.valueAggregation_hidden_zero P H hs.1,Matrix.zero_mul,Matrix.zero_mulVec] at hd
  exact sub_eq_zero.mp hd

theorem strong_restrictions_identify_both (hn : 0<n) (P : Partition n g)
    (R : Refinement P F.parents) (H : HiddenBasis (P.Q F.q) r)
    (hnc : ¬F.ParentIdentified) (hs : F.StrongReportRestrictions H.N) :
    F.ReportIdentified P ∧ F.GroupQuantitiesIdentified P :=
  ⟨F.report_moments_identifies P (F.strong_restrictions_moments hn P R H hnc hs),
    F.strong_restrictions_identify_quantities hn P R H hnc hs⟩

theorem policy_demand_form_identifies_both (hn : 0<n) (P : Partition n g)
    (R : Refinement P F.parents) (H : HiddenBasis (P.Q F.q) r)
    (hnc : ¬F.ParentIdentified) (hs : F.PolicyDemandForm P) :
    F.ReportIdentified P ∧ F.GroupQuantitiesIdentified P :=
  F.strong_restrictions_identify_both hn P R H hnc
    ((F.strong_report_restrictions_iff_policy_demand P H).mpr hs)

end CommodityClassification.Equilibrium.BenchmarkFamily
