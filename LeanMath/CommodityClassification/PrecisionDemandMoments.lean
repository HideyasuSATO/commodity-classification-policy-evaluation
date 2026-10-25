module

public import LeanMath.CommodityClassification.PrecisionSupplyFamily

/-! Exact demand and policy moments for the structured precision class. -/
@[expose] public section
noncomputable section
set_option maxHeartbeats 1200000
namespace CommodityClassification.Precision.Data
open Matrix InputCoordinates
open scoped BigOperators
variable {n : ℕ} (d : Precision.Data n)

theorem theta_policy : d.theta d.policy=d.beta := by
  calc
    _=(∑i,d.w i*d.v i)+d.beta*(∑i,d.w i*(d.v i)^2) := by
      rw [Finset.mul_sum,←Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro i _
      dsimp only [policy]
      ring
    _=_ := by rw [d.type_balance,d.type_norm];ring

theorem demand_action (c : Vec n) (i : Fin n) :
    (d.demand *ᵥ c) i=d.eta*d.w i*c i+d.alpha*d.w i*d.v i*d.theta c := by
  simp only [demand,Matrix.add_mulVec,Matrix.smul_mulVec,Matrix.mulVec_diagonal,
    Matrix.vecMulVec_mulVec,Pi.add_apply,Pi.smul_apply,smul_eq_mul]
  change d.eta*(d.w i*c i)+d.alpha*(d.weightedType i*dotProduct d.weightedType c)=_
  change d.eta*(d.w i*c i)+d.alpha*((d.w i*d.v i)*d.theta c)=_
  ring

theorem demand_policy (i : Fin n) :
    (d.demand *ᵥ d.policy) i=d.eta*d.w i+d.totalElasticity*d.beta*d.w i*d.v i := by
  rw [d.demand_action,d.theta_policy]
  dsimp only [policy,totalElasticity]
  ring

theorem demand_quadratic (c : Vec n) :
    dotProduct c (d.demand *ᵥ c)=d.eta*d.secondMoment c+d.alpha*(d.theta c)^2 := by
  simp only [dotProduct,d.demand_action]
  calc
    _=d.eta*(∑i,d.w i*(c i)^2)+(d.alpha*d.theta c)*(∑i,d.w i*d.v i*c i) := by
      rw [Finset.mul_sum,Finset.mul_sum,←Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro i _;ring
    _=_ := by change d.eta*d.secondMoment c+(d.alpha*d.theta c)*d.theta c=_;ring

theorem policy_energy : dotProduct d.policy (d.demand *ᵥ d.policy)=d.nu := by
  simp only [dotProduct,d.demand_policy]
  calc
    _=d.eta*(∑i,d.w i)+(d.beta*(d.eta+d.totalElasticity))*(∑i,d.w i*d.v i)+
        (d.totalElasticity*d.beta^2)*(∑i,d.w i*(d.v i)^2) := by
      simp only [Finset.mul_sum,←Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro i _;dsimp only [policy];ring
    _=_ := by rw [d.sum_w,d.type_balance,d.type_norm];simp only [nu];ring

theorem moment_m (c : Vec n) (hc : ∑i,d.w i*c i=0) :
    (d.coordinates c).transpose *ᵥ (d.demand *ᵥ d.policy)=![d.totalElasticity*d.beta*d.theta c] := by
  ext j;fin_cases j
  change (∑i,c i*(d.demand *ᵥ d.policy) i)=_
  simp only [d.demand_policy]
  calc
    _=d.eta*(∑i,d.w i*c i)+(d.totalElasticity*d.beta)*(∑i,d.w i*d.v i*c i) := by
      rw [Finset.mul_sum,Finset.mul_sum,←Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro i _;ring
    _=_ := by rw [hc];simp only [mul_zero,zero_add];rfl

theorem xi_quadratic (c : Vec n) :
    dotProduct c (Supply.xi d.prices d.w *ᵥ c)=d.secondMoment c := by
  simp only [Supply.xi,prices,div_one,Matrix.mulVec_diagonal,dotProduct,secondMoment]
  apply Finset.sum_congr rfl
  intro i _;ring

theorem moment_K (c : Vec n) :
    Regularity.K d.prices d.w d.demand d.family.fixedR d.sigma (d.coordinates c)=
      ![![d.denominator d.sigma (d.secondMoment c) ((d.theta c)^2)]] := by
  rw [Regularity.K,d.fixed_R,Matrix.mul_assoc]
  ext i j;fin_cases i;fin_cases j
  change d.sigma*1+dotProduct c ((d.demand-d.sigma • Supply.xi d.prices d.w) *ᵥ c)=
    d.denominator d.sigma (d.secondMoment c) ((d.theta c)^2)
  rw [Matrix.sub_mulVec,Matrix.smul_mulVec,dotProduct_sub,dotProduct_smul,
    d.demand_quadratic,d.xi_quadratic]
  simp only [smul_eq_mul,denominator]
  ring

end CommodityClassification.Precision.Data
