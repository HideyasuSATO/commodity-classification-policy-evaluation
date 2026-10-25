module

public import LeanMath.CommodityClassification.PrecisionMomentValue

/-! Conditional necessity, sufficiency and the exact degenerate cases. -/
@[expose] public section
noncomputable section
set_option maxHeartbeats 1200000
namespace CommodityClassification.Precision.Data
open Matrix InputCoordinates
open scoped BigOperators
variable {n : ℕ} (d : Precision.Data n)

def momentReport (c : Vec n) : ℝ × ℝ := (d.theta c,d.secondMoment c)

def FixedThetaIdentified {A : Type*} (θ : ℝ) (O : Vec n → A) (f : Vec n → ℝ) : Prop :=
  ∀c e,d.Admissible c → d.Admissible e → d.theta c=θ → d.theta e=θ → O c=O e → f c=f e

theorem momentReport_sufficient (c e : Vec n) (hO : d.momentReport c=d.momentReport e) :
    d.normalizedWelfare c=d.normalizedWelfare e := by
  have ht := congrArg Prod.fst hO
  have hq := congrArg Prod.snd hO
  change d.theta c=d.theta e at ht
  change d.secondMoment c=d.secondMoment e at hq
  simp only [normalizedWelfare,ht,hq]

theorem fixed_theta_pair_iff (c e : Vec n) (hc : d.Admissible c) (he : d.Admissible e)
    (ht : d.theta c=d.theta e) (hθ : d.theta c≠0) (hm : d.eta≠d.sigma) :
    d.normalizedWelfare c=d.normalizedWelfare e ↔ d.secondMoment c=d.secondMoment e := by
  rw [d.normalizedWelfare_momentValue,d.normalizedWelfare_momentValue,←ht]
  apply d.momentValue_eq_iff _ _ _ (pow_ne_zero _ hθ) hm
    (d.denominator_positive c hc).ne'
  rw [ht]
  exact (d.denominator_positive e he).ne'

theorem fixed_theta_information_iff {A : Type*} (θ : ℝ) (hθ : θ≠0) (hm : d.eta≠d.sigma)
    (O : Vec n → A) :
    d.FixedThetaIdentified θ O d.normalizedWelfare ↔ d.FixedThetaIdentified θ O d.secondMoment := by
  constructor
  · intro hi c e hc he hct het hO
    exact (d.fixed_theta_pair_iff c e hc he (hct.trans het.symm)
      (by rwa [hct]) hm).mp (hi c e hc he hct het hO)
  · intro hi c e hc he hct het hO
    exact (d.fixed_theta_pair_iff c e hc he (hct.trans het.symm)
      (by rwa [hct]) hm).mpr (hi c e hc he hct het hO)

theorem zero_theta_welfare (c : Vec n) (ht : d.theta c=0) : d.normalizedWelfare c=1 := by
  simp only [normalizedWelfare,ht,zero_pow (by norm_num : (2:ℕ)≠0),mul_zero,zero_div,sub_zero]

theorem matching_elasticity_welfare (hm : d.eta=d.sigma) (c : Vec n) :
    d.normalizedWelfare c=1-d.lossScale*(d.theta c)^2/(d.sigma+d.alpha*(d.theta c)^2) := by
  simp only [normalizedWelfare,denominator,hm,sub_self,zero_mul,add_zero]

theorem zero_theta_information {A : Type*} (O : Vec n → A) :
    d.FixedThetaIdentified 0 O d.normalizedWelfare := by
  intro c e _ _ hc he _
  rw [d.zero_theta_welfare c hc,d.zero_theta_welfare e he]

theorem matching_elasticity_information {A : Type*} (hm : d.eta=d.sigma) (θ : ℝ)
    (O : Vec n → A) : d.FixedThetaIdentified θ O d.normalizedWelfare := by
  intro c e _ _ hc he _
  rw [d.matching_elasticity_welfare hm,d.matching_elasticity_welfare hm,hc,he]

def typeInputTotal (c : Vec n) (a : ℝ) : ℝ :=
  ∑i∈Finset.univ.filter (fun i => d.v i=a),d.w i*c i

theorem type_totals_recover_theta (c : Vec n) :
    d.theta c=d.typeInputTotal c 1-d.typeInputTotal c (-1) := by
  simp only [theta,typeInputTotal,Finset.sum_filter,←Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _
  rcases d.type_sign i with hi|hi <;> rw [hi] <;> norm_num

theorem same_type_totals_same_theta (c e : Vec n)
    (hplus : d.typeInputTotal c 1=d.typeInputTotal e 1)
    (hminus : d.typeInputTotal c (-1)=d.typeInputTotal e (-1)) : d.theta c=d.theta e := by
  rw [d.type_totals_recover_theta c,d.type_totals_recover_theta e,hplus,hminus]

theorem coefficient_eq_iff_normalized (c e : Vec n) (hc : d.Admissible c) (he : d.Admissible e) :
    d.family.coefficient (d.coordinates c)=d.family.coefficient (d.coordinates e) ↔
      d.normalizedWelfare c=d.normalizedWelfare e := by
  rw [d.coefficient_scaled_normalized c hc.2,d.coefficient_scaled_normalized e he.2]
  exact ⟨mul_left_cancel₀ d.nu_pos.ne',congrArg (fun x => d.nu*x)⟩

theorem actual_momentReport_sufficient (c e : Vec n) (hc : d.Admissible c) (he : d.Admissible e)
    (hO : d.momentReport c=d.momentReport e) :
    (d.family.model (d.candidate c hc)).lossCoefficient=
      (d.family.model (d.candidate e he)).lossCoefficient := by
  rw [d.family.candidate_lossCoefficient,d.family.candidate_lossCoefficient]
  exact (d.coefficient_eq_iff_normalized c e hc he).mpr (d.momentReport_sufficient c e hO)

theorem fixed_theta_actual_coefficient_iff (c e : Vec n) (hc : d.Admissible c) (he : d.Admissible e)
    (ht : d.theta c=d.theta e) (hθ : d.theta c≠0) (hm : d.eta≠d.sigma) :
    (d.family.model (d.candidate c hc)).lossCoefficient=
      (d.family.model (d.candidate e he)).lossCoefficient ↔ d.secondMoment c=d.secondMoment e := by
  rw [d.family.candidate_lossCoefficient,d.family.candidate_lossCoefficient]
  exact (d.coefficient_eq_iff_normalized c e hc he).trans (d.fixed_theta_pair_iff c e hc he ht hθ hm)

def typePhysicalUse (c : Vec n) (a : ℝ) (j : Fin 2) : ℝ :=
  ∑i∈Finset.univ.filter (fun i => d.v i=a),d.w i*d.inputs c i j

theorem typeInputTotal_physical (c : Vec n) (a : ℝ) :
    d.typeInputTotal c a=d.typePhysicalUse c a 0-d.typePhysicalUse c a 1 := by
  simp only [typeInputTotal,typePhysicalUse,←Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _
  norm_num [inputs]
  ring

end CommodityClassification.Precision.Data
