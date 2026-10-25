module

public import LeanMath.CommodityClassification.PrecisionVertexCoordinates

/-! Positive paths from the reported mean to any closed-fiber point. -/
@[expose] public section
noncomputable section
set_option maxHeartbeats 1200000
namespace CommodityClassification.Precision.Data
open Matrix InputCoordinates
open scoped BigOperators
variable {n g : ℕ} (d : Precision.Data n)

def endpointPath (P : Partition n g) (c e : Vec n) (t : ℝ) : Vec n :=
  (1-t) • d.meanVector P c+t • e

theorem endpointPath_manuscript (P : Partition n g) (c e : Vec n) (t : ℝ) :
    d.endpointPath P c e t=d.meanVector P c+t • (e-d.meanVector P c) := by
  ext i
  simp only [endpointPath,Pi.add_apply,Pi.sub_apply,Pi.smul_apply,smul_eq_mul]
  ring

theorem endpointPath_zero (P : Partition n g) (c e : Vec n) :
    d.endpointPath P c e 0=d.meanVector P c := by simp [endpointPath]

theorem endpointPath_one (P : Partition n g) (c e : Vec n) :
    d.endpointPath P c e 1=e := by simp [endpointPath]

theorem endpointPath_continuous (P : Partition n g) (c e : Vec n) :
    Continuous (d.endpointPath P c e) := by unfold endpointPath;fun_prop

theorem endpointPath_report (P : Partition n g) (c e : Vec n)
    (he : d.groupTotal P e=d.groupTotal P c) (t : ℝ) :
    d.groupTotal P (d.endpointPath P c e t)=d.groupTotal P c := by
  rw [endpointPath,d.groupTotal_add,d.groupTotal_smul,d.groupTotal_smul,
    d.meanVector_report,he,←add_smul]
  simp

theorem same_report_balance (P : Partition n g) (c e : Vec n)
    (he : d.groupTotal P e=d.groupTotal P c) : (∑i,d.w i*e i)=∑i,d.w i*c i := by
  rw [←sum_by_partition P (fun i => d.w i*e i),←sum_by_partition P (fun i => d.w i*c i)]
  change (∑a,d.groupTotal P e a)=∑a,d.groupTotal P c a
  rw [he]

theorem endpointPath_admissible (P : Partition n g) (c e : Vec n)
    (hc : d.Admissible c) (he : e∈d.closedFiber P (d.groupTotal P c))
    (t : ℝ) (ht : 0≤t) (ht1 : t<1) : d.Admissible (d.endpointPath P c e t) := by
  have hm := d.meanVector_admissible P c hc
  refine ⟨?_,?_⟩
  · intro i
    change |(1-t)*d.meanVector P c i+t*e i|<1
    calc
      _≤|(1-t)*d.meanVector P c i|+|t*e i| := abs_add_le _ _
      _=(1-t)*|d.meanVector P c i|+t*|e i| := by
        rw [abs_mul,abs_mul,abs_of_nonneg (by linarith : 0≤1-t),abs_of_nonneg ht]
      _<(1-t)*1+t*1 := add_lt_add_of_lt_of_le
        (mul_lt_mul_of_pos_left (hm.1 i) (by linarith))
        (mul_le_mul_of_nonneg_left (he.1 i) ht)
      _=1 := by ring
  · rw [d.same_report_balance P c _ (d.endpointPath_report P c e he.2 t)]
    exact hc.2

theorem endpointPath_mean (P : Partition n g) (c e : Vec n)
    (he : d.groupTotal P e=d.groupTotal P c) (t : ℝ) :
    d.meanVector P (d.endpointPath P c e t)=d.meanVector P c :=
  d.meanVector_same_report P _ _ (d.endpointPath_report P c e he t)

theorem endpointPath_variance (P : Partition n g) (c e : Vec n)
    (he : d.groupTotal P e=d.groupTotal P c) (t : ℝ) :
    d.residualVariance P (d.endpointPath P c e t)=t^2*d.residualVariance P e := by
  unfold residualVariance
  rw [d.endpointPath_mean P c e he t,d.meanVector_same_report P e c he,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  change d.w i*((1-t)*d.meanVector P c i+t*e i-d.meanVector P c i)^2=
    t^2*(d.w i*(e i-d.meanVector P c i)^2)
  ring

theorem endpointPath_secondMoment (P : Partition n g) (c e : Vec n)
    (he : d.groupTotal P e=d.groupTotal P c) (t : ℝ) :
    d.secondMoment (d.endpointPath P c e t)=d.lowerMoment P (d.groupTotal P c)+
      t^2*(d.secondMoment e-d.lowerMoment P (d.groupTotal P c)) := by
  have hh := d.endpointPath_variance P c e he t
  rw [d.residualVariance_identity,d.residualVariance_identity,
    d.endpointPath_report P c e he t,he] at hh
  linarith

theorem endpointPath_theta (P : Partition n g) (hP : d.TypeRespecting P) (c e : Vec n)
    (he : d.groupTotal P e=d.groupTotal P c) (t : ℝ) :
    d.theta (d.endpointPath P c e t)=d.theta c :=
  d.same_report_theta P hP _ _ (d.endpointPath_report P c e he t)

end CommodityClassification.Precision.Data
