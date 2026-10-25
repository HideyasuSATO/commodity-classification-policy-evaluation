module

public import LeanMath.CommodityClassification.PrecisionDemandMoments

/-! The structured formula is the coefficient of actual competitive equilibrium welfare. -/
@[expose] public section
noncomputable section
set_option maxHeartbeats 1400000
namespace CommodityClassification.Precision.Data
open Matrix InputCoordinates Filter Asymptotics
open scoped BigOperators Topology
variable {n : ℕ} (d : Precision.Data n)

def normalizedWelfare (c : Vec n) : ℝ :=
  1-d.lossScale*(d.theta c)^2/d.denominator d.sigma (d.secondMoment c) ((d.theta c)^2)

theorem coefficient_formula (c : Vec n) (hc : ∑i,d.w i*c i=0) :
    d.family.coefficient (d.coordinates c)=
      d.nu-(d.totalElasticity*d.beta*d.theta c)^2/
        d.denominator d.sigma (d.secondMoment c) ((d.theta c)^2) := by
  change dotProduct d.policy (d.demand *ᵥ d.policy)-
    dotProduct ((d.coordinates c).transpose *ᵥ (d.demand *ᵥ d.policy))
      ((Regularity.K d.prices d.w d.demand d.family.fixedR d.sigma (d.coordinates c))⁻¹ *ᵥ
        ((d.coordinates c).transpose *ᵥ (d.demand *ᵥ d.policy)))=_
  rw [d.policy_energy,d.moment_m c hc,d.moment_K,ResourceCancellation.scalar_inverse]
  simp only [dotProduct,Matrix.mulVec,Fin.sum_univ_succ,Finset.univ_eq_empty,Finset.sum_empty,
    Matrix.cons_val_fin_one,add_zero]
  ring

theorem normalized_coefficient (c : Vec n) (hc : ∑i,d.w i*c i=0) :
    d.family.coefficient (d.coordinates c)/d.nu=d.normalizedWelfare c := by
  rw [d.coefficient_formula c hc,sub_div,div_self d.nu_pos.ne']
  unfold normalizedWelfare lossScale policyShare
  ring

theorem coefficient_scaled_normalized (c : Vec n) (hc : ∑i,d.w i*c i=0) :
    d.family.coefficient (d.coordinates c)=d.nu*d.normalizedWelfare c := by
  have hh := d.normalized_coefficient c hc
  exact (div_eq_iff d.nu_pos.ne').mp hh |>.trans (mul_comm _ _)

theorem actual_moments (c : Vec n) (hc : d.Admissible c) :
    (d.family.model (d.candidate c hc)).m=![d.totalElasticity*d.beta*d.theta c] ∧
    (d.family.model (d.candidate c hc)).K=
      ![![d.denominator d.sigma (d.secondMoment c) ((d.theta c)^2)]] := by
  constructor
  · exact d.moment_m c hc.2
  · change Regularity.K d.prices d.w d.demand (d.family.model (d.candidate c hc)).R
      d.sigma (d.coordinates c)=_
    rw [d.family.candidate_R_fixed]
    exact d.moment_K c

theorem actual_normalized_coefficient (c : Vec n) (hc : d.Admissible c) :
    (d.family.model (d.candidate c hc)).lossCoefficient/d.nu=d.normalizedWelfare c := by
  rw [d.family.candidate_lossCoefficient]
  exact d.normalized_coefficient c hc.2

theorem all_candidates_normalized_coefficient (C : d.family.Candidate) :
    (d.family.model C).lossCoefficient/d.nu=d.normalizedWelfare (fun i => C.val i 0) := by
  rw [d.family.candidate_lossCoefficient,←d.candidate_coordinates C]
  exact d.normalized_coefficient _ (d.candidate_admissible C).2

theorem actual_competitive_welfare (c : Vec n) (hc : d.Admissible c)
    (s0 a : ℝ) (hs : 0<s0) :
    let E := d.family.model (d.candidate c hc)
    ∃u : ℝ → Vec 1,∃s : ℝ → ℝ,E.PositiveLocalPath s0 u s ∧
      (∃I : Set ℝ,IsOpen I ∧ 0∈I ∧ ∀t∈I,E.CompetitiveState
        (d.family.commonUtility a) Set.univ (d.family.commonEndowment s0) (t,u t) (s t)) ∧
      (fun t => E.welfare (d.family.commonUtility a) u s 0-
        E.welfare (d.family.commonUtility a) u s t-(1/2 : ℝ)*t^2*(d.nu*d.normalizedWelfare c))
        =o[𝓝 (0 : ℝ)] (fun t : ℝ => t^2) := by
  obtain ⟨u,s,hp,hcomp,_,_,_,hw⟩ := d.family.candidate_competitive_implementation
    (d.family.total_positive_of_goods d.goods_nonempty) s0 a hs (d.candidate c hc)
  refine ⟨u,s,hp,hcomp,?_⟩
  change (fun t => (d.family.model (d.candidate c hc)).welfare (d.family.commonUtility a) u s 0-
    (d.family.model (d.candidate c hc)).welfare (d.family.commonUtility a) u s t-
      (1/2 : ℝ)*t^2*d.family.coefficient (d.coordinates c))=o[𝓝 (0 : ℝ)] (fun t : ℝ => t^2) at hw
  rwa [d.coefficient_scaled_normalized c hc.2] at hw

end CommodityClassification.Precision.Data
