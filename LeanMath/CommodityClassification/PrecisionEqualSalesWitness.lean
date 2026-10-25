module

public import LeanMath.CommodityClassification.PrecisionEqualSalesDesign

/-! The printed positive-share witness for every four-group classification. -/
@[expose] public section
noncomputable section
set_option maxHeartbeats 1600000
namespace CommodityClassification.Precision.Illustration
open InputCoordinates

theorem equalSales_path_secondMoment (e : Vec 32)
    (hθ : equalSales.theta e=equalSales.theta equalSales.criticalInputs)
    (hQ : 27/32≤equalSales.secondMoment e) :
    6323/8192≤equalSales.secondMoment (equalSales.fixedLoadPath e (15/16)) := by
  rw [equalSales.fixedLoadPath_secondMoment e hθ,
    (equalSales.illustration_constants equalSales_parameters).2.2.2.2.1]
  nlinarith

theorem equalSales_positive_witness (P : Partition 32 4) :
    ∃e c : Vec 32,e∈equalSales.closedFiber P (equalSales.groupTotal P equalSales.criticalInputs) ∧
      equalSales.theta e=equalSales.theta equalSales.criticalInputs ∧ 27/32≤equalSales.secondMoment e ∧
      c=(fun i => (15*e i+equalSales.criticalInputs i)/16) ∧
      equalSales.Admissible c ∧ equalSales.groupTotal P c=equalSales.groupTotal P equalSales.criticalInputs ∧
      equalSales.theta c=equalSales.theta equalSales.criticalInputs ∧
      6323/8192≤equalSales.secondMoment c ∧
      (∀i j,(1/64:ℝ)≤equalSales.inputs equalSales.criticalInputs i j ∧ (1/64:ℝ)≤equalSales.inputs c i j) ∧
      (1/20:ℝ) < |equalSales.normalizedWelfare equalSales.criticalInputs-equalSales.normalizedWelfare c| := by
  obtain ⟨e,he,_,hθ,hj,hQ⟩ := equalSales.classification_vertex_concentration P equalSales.criticalInputs
    (fun i => (equalSales.criticalInputs_admissible.1 i).le)
  have hclosed : e∈equalSales.closedFiber P (equalSales.groupTotal P equalSales.criticalInputs) := ⟨he.1.1,hj⟩
  have hQe : 27/32≤equalSales.secondMoment e := by
    rw [equalSales_coarseSales] at hQ
    linarith
  let c := equalSales.fixedLoadPath e (15/16)
  have hc : equalSales.Admissible c := equalSales.fixedLoadPath_admissible P e hclosed _ (by norm_num) (by norm_num)
  have hctheta : equalSales.theta c=equalSales.theta equalSales.criticalInputs :=
    equalSales.fixedLoadPath_theta e hθ _
  have hQc : 6323/8192≤equalSales.secondMoment c := equalSales_path_secondMoment e hθ hQe
  refine ⟨e,c,hclosed,hθ,hQe,equalSales.illustration_fixedLoadPath e,hc,
    equalSales.fixedLoadPath_report P e hj _,hctheta,hQc,?_,?_⟩
  · have hbase := equalSales.criticalInputs_share_lower (15/16) (by norm_num)
    have hpath := equalSales.fixedLoadPath_share_lower e he.1.1 (15/16) (by norm_num) (by norm_num)
    rw [equalSales.illustration_shareFloor equalSales_parameters] at hbase hpath
    exact fun i j => ⟨hbase i j,hpath i j⟩
  · rw [Data.normalizedWelfare_momentValue,Data.normalizedWelfare_momentValue,hctheta,
      equalSales.criticalInputs_theta_sq,equalSales.criticalInputs_secondMoment,
      ←equalSales.momentWidth_eq_abs _ _ _ equalSales.criticalExposure_mem.1.le,
      (equalSales.illustration_constants equalSales_parameters).2.2.2.2.1]
    exact (equalSales.illustration_width_threshold equalSales_parameters _ (by linarith)).mpr (by linarith)

theorem equalSales_actual_positive_witness (P : Partition 32 4) :
    ∃c,∃hc : equalSales.Admissible c,
      equalSales.groupTotal P c=equalSales.groupTotal P equalSales.criticalInputs ∧
      equalSales.theta c=equalSales.theta equalSales.criticalInputs ∧
      (∀i j,(1/64:ℝ)≤equalSales.inputs equalSales.criticalInputs i j ∧ (1/64:ℝ)≤equalSales.inputs c i j) ∧
      (1/20:ℝ) < |(equalSales.family.model
          (equalSales.candidate equalSales.criticalInputs equalSales.criticalInputs_admissible)).lossCoefficient/equalSales.nu-
        (equalSales.family.model (equalSales.candidate c hc)).lossCoefficient/equalSales.nu| := by
  obtain ⟨_,c,_,_,_,_,hc,hj,hθ,_,hshares,hgap⟩ := equalSales_positive_witness P
  refine ⟨c,hc,hj,hθ,hshares,?_⟩
  rwa [equalSales.actual_normalized_coefficient,equalSales.actual_normalized_coefficient]

end CommodityClassification.Precision.Illustration
