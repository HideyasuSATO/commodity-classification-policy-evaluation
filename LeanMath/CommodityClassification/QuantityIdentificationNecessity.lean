module

public import LeanMath.CommodityClassification.SmallResponseVariations

/-! Necessity uses one nonzero answer and only positive feasible perturbations. -/
@[expose] public section
noncomputable section
namespace CommodityClassification.Equilibrium.BenchmarkFamily
open Matrix InputCoordinates Filter
open scoped Topology
variable {n k h g r : ℕ} (F : BenchmarkFamily n k h)

theorem exists_nonzero_response_of_parent_failure (hnc : ¬F.ParentIdentified) :
    ∃C : F.Candidate,F.responseY C≠0 := by
  by_contra hn
  push Not at hn
  have hc (C : F.Candidate) : F.coefficient C.val=dotProduct F.b (F.D *ᵥ F.b) := by
    rw [←F.candidate_lossCoefficient C]
    change dotProduct F.b (F.D *ᵥ F.b)-dotProduct (F.model C).m (F.responseY C)=_
    rw [hn C,dotProduct_zero,sub_zero]
  apply hnc
  intro C
  exact (hc C).trans (hc F.referenceCandidate).symm

theorem group_identification_small_variations (P : Partition n g) (R : Refinement P F.parents)
    (H : HiddenBasis (P.Q F.q) r) (hm : F.ReportMomentsPreserved P)
    (hg : F.GroupQuantitiesIdentified P) (C0 : F.Candidate) :
    ∀ᶠZ : Mat r k in 𝓝 0,
      (P.valueAggregation F.p*F.D*H.N) *ᵥ (Z *ᵥ F.responseY C0)=0 := by
  have hp := F.frame.small_perturbations F.p F.q R F.report C0.val C0.property H
  filter_upwards [hp] with Z hZ
  let C : F.Candidate := ⟨C0.val+H.N*Z,hZ.1⟩
  have hr : P.report F.q C.val=P.report F.q C0.val := hZ.2
  obtain ⟨hmom,hK⟩ := hm C C0 hr
  have hy := F.responseY_eq_of_moments C C0 hmom hK
  have hd := F.groupQuantityResponse_variation P C C0 H.N Z rfl hy
  rw [hg C C0 hr,sub_self] at hd
  rw [Matrix.mulVec_mulVec]
  exact hd.symm

theorem group_identification_hidden_zero (P : Partition n g) (R : Refinement P F.parents)
    (H : HiddenBasis (P.Q F.q) r) (hm : F.ReportMomentsPreserved P)
    (hg : F.GroupQuantitiesIdentified P) (hnc : ¬F.ParentIdentified) :
    P.valueAggregation F.p*F.D*H.N=0 := by
  obtain ⟨C0,hy⟩ := F.exists_nonzero_response_of_parent_failure hnc
  exact matrix_zero_of_small_response_variations _ (F.responseY C0) hy
    (F.group_identification_small_variations P R H hm hg C0)

theorem both_identifications_require_strong (hn : 0<n) (P : Partition n g)
    (R : Refinement P F.parents) (H : HiddenBasis (P.Q F.q) r)
    (hnc : ¬F.ParentIdentified) (hw : F.ReportIdentified P)
    (hg : F.GroupQuantitiesIdentified P) : F.StrongReportRestrictions H.N := by
  have hl := (F.report_identified_iff_linear_restrictions_of_goods hn P R H hnc).mp hw
  have hm := (F.report_moments_iff_linear_restrictions (F.total_positive_of_goods hn)
    (F.positive_relative_dimension_of_parent_failure hnc) P R H).mpr hl
  have hd := F.group_identification_hidden_zero P R H hm hg hnc
  obtain ⟨hload,Γ,hLN,hΓ⟩ := hl
  have hzero : P.valueAggregation F.p*F.parents.Q F.q*Γ=0 := by
    rw [Matrix.mul_assoc,←hLN,←Matrix.mul_assoc,←F.valueAggregation_adjusted_hidden P H]
    exact hd
  have hΓzero := R.valueAggregation_parent_cancel F.p F.q F.hp F.hq Γ hzero
  refine ⟨?_,hload⟩
  rw [hLN,hΓzero,Matrix.mul_zero]

end CommodityClassification.Equilibrium.BenchmarkFamily
