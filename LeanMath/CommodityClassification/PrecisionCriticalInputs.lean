module

public import LeanMath.CommodityClassification.PrecisionSalesConcentration

/-! The strictly positive starting technology at the critical exposure. -/
@[expose] public section
noncomputable section
set_option maxHeartbeats 1400000
namespace CommodityClassification.Precision.Data
open Matrix InputCoordinates
open scoped BigOperators
variable {n : ℕ} (d : Precision.Data n)

def typeRay (a : ℝ) : Vec n := a • d.v
def criticalInputs : Vec n := d.typeRay (Real.sqrt d.criticalExposure)

theorem typeRay_balance (a : ℝ) : (∑i,d.w i*d.typeRay a i)=0 := by
  calc
    _=a*(∑i,d.w i*d.v i) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      change d.w i*(a*d.v i)=a*(d.w i*d.v i)
      ring
    _=0 := by rw [d.type_balance,mul_zero]

theorem typeRay_theta (a : ℝ) : d.theta (d.typeRay a)=a := by
  calc
    _=a*(∑i,d.w i*(d.v i)^2) := by
      rw [Finset.mul_sum]
      unfold theta
      apply Finset.sum_congr rfl
      intro i _
      change d.w i*d.v i*(a*d.v i)=a*(d.w i*(d.v i)^2)
      ring
    _=a := by rw [d.type_norm,mul_one]

theorem typeRay_secondMoment (a : ℝ) : d.secondMoment (d.typeRay a)=a^2 := by
  calc
    _=a^2*(∑i,d.w i*(d.v i)^2) := by
      rw [Finset.mul_sum]
      unfold secondMoment
      apply Finset.sum_congr rfl
      intro i _
      change d.w i*(a*d.v i)^2=a^2*(d.w i*(d.v i)^2)
      ring
    _=a^2 := by rw [d.type_norm,mul_one]

theorem typeRay_abs (a : ℝ) (i : Fin n) : |d.typeRay a i|=|a| := by
  change |a*d.v i|=|a|
  rcases d.type_sign i with hi|hi <;> rw [hi] <;> simp

theorem typeRay_admissible (a : ℝ) (ha : |a|<1) : d.Admissible (d.typeRay a) := by
  exact ⟨fun i => (d.typeRay_abs a i).trans_lt ha,d.typeRay_balance a⟩

theorem criticalInputs_admissible : d.Admissible d.criticalInputs := by
  apply d.typeRay_admissible
  rw [abs_of_nonneg (Real.sqrt_nonneg _)]
  nlinarith [Real.sq_sqrt d.criticalExposure_mem.1.le,
    Real.sqrt_nonneg d.criticalExposure,d.criticalExposure_mem.2]

theorem criticalInputs_theta : d.theta d.criticalInputs=Real.sqrt d.criticalExposure :=
  d.typeRay_theta _

theorem criticalInputs_theta_sq : (d.theta d.criticalInputs)^2=d.criticalExposure := by
  rw [d.criticalInputs_theta,Real.sq_sqrt d.criticalExposure_mem.1.le]

theorem criticalInputs_secondMoment : d.secondMoment d.criticalInputs=d.criticalExposure := by
  rw [criticalInputs,d.typeRay_secondMoment,Real.sq_sqrt d.criticalExposure_mem.1.le]

theorem criticalInputs_abs (i : Fin n) : |d.criticalInputs i|=Real.sqrt d.criticalExposure := by
  rw [criticalInputs,d.typeRay_abs,abs_of_nonneg (Real.sqrt_nonneg _)]

theorem secondMoment_sub_typeRay (e : Vec n) (a : ℝ) :
    d.secondMoment (e-d.typeRay a)=d.secondMoment e-2*a*d.theta e+a^2 := by
  calc
    _=d.secondMoment e-2*a*d.theta e+a^2*(∑i,d.w i*(d.v i)^2) := by
      simp only [secondMoment,theta,Finset.mul_sum,←Finset.sum_sub_distrib,←Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro i _
      change d.w i*(e i-a*d.v i)^2=
        d.w i*(e i)^2-2*a*(d.w i*d.v i*e i)+a^2*(d.w i*(d.v i)^2)
      ring
    _=_ := by rw [d.type_norm,mul_one]

end CommodityClassification.Precision.Data
