module

public import LeanMath.CommodityClassification.UntaxedNestMoments

/-! Covariance that remains invisible in the untaxed nest. -/
@[expose] public section
noncomputable section
set_option maxHeartbeats 2000000
namespace CommodityClassification.UntaxedNest
open Matrix InputCoordinates

theorem nest_covariance (t : ℝ) (a : Fin 2) :
    nestData.nestCovariance (coordinates t) a=if a=0 then 0 else ![![t^2/2]] := by
  rw [nestData.nestCovariance_manuscript]
  ext l m;fin_cases l;fin_cases m
  simp only [Matrix.sub_apply,Matrix.smul_apply,smul_eq_mul,Matrix.vecMulVec_apply]
  rw [nestData.nestSecondMoment_apply]
  change (∑i∈nests.cell a,(quantities i/prices i)*coordinates t i 0*coordinates t i 0)-
    (nests.sales prices quantities a)⁻¹*(nests.report quantities (coordinates t) a 0*
      nests.report quantities (coordinates t) a 0)=_
  rw [nest_sales,nest_report]
  simp only [Partition.cell,Finset.sum_filter]
  fin_cases a <;>
    norm_num [Partition.cell,nests,SeparableFour.fine,prices,quantities,coordinates,Fin.sum_univ_succ]
  ring

theorem printed_covariance_change :
    nestData.nestCovariance (coordinates (1/4)) 0=nestData.nestCovariance (coordinates 0) 0 ∧
    nestData.nestCovariance (coordinates (1/4)) 1-nestData.nestCovariance (coordinates 0) 1=![![1/32]] := by
  simp only [nest_covariance]
  constructor
  · rfl
  · simp only [show (1 : Fin 2)≠0 by decide,ite_false]
    ext i j
    fin_cases i;fin_cases j
    change ((1/4 : ℝ)^2/2-0^2/2)=1/32
    norm_num

theorem covariance_correction_untaxed (C : Mat 4 1) :
    nestData.covarianceCorrection C 1=nestData.nestCovariance C 1 := by
  unfold DemandNests.Data.covarianceCorrection
  rw [Fin.sum_univ_two]
  change (eta 0-1) • nestData.nestCovariance C 0+(eta 1-1) • nestData.nestCovariance C 1=_
  norm_num [eta]

theorem nest_reports_and_untaxed_covariance_suffice (C E : family.Candidate)
    (hJ : nests.report quantities C.val=nests.report quantities E.val)
    (hV : nestData.nestCovariance C.val 1=nestData.nestCovariance E.val 1) :
    (family.model C).m=(family.model E).m ∧ (family.model C).K=(family.model E).K ∧
      (family.model C).lossCoefficient=(family.model E).lossCoefficient := by
  apply family.nested_information_sufficient nests eta eta_pos outerD beta demand_eq_nested policy_eq_nested C E hJ
  change nestData.covarianceCorrection C.val 1=nestData.covarianceCorrection E.val 1
  rw [covariance_correction_untaxed,covariance_correction_untaxed,hV]

end CommodityClassification.UntaxedNest
