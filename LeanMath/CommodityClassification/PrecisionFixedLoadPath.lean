module

public import LeanMath.CommodityClassification.PrecisionCriticalInputs

/-! Positive paths retain the same group reports and policy load. -/
@[expose] public section
noncomputable section
set_option maxHeartbeats 1400000
namespace CommodityClassification.Precision.Data
open Matrix InputCoordinates Filter
open scoped BigOperators Topology
variable {n g : ℕ} (d : Precision.Data n)

def fixedLoadPath (e : Vec n) (t : ℝ) : Vec n := (1-t) • d.criticalInputs+t • e

theorem fixedLoadPath_manuscript (e : Vec n) (t : ℝ) :
    d.fixedLoadPath e t=d.criticalInputs+t • (e-d.criticalInputs) := by
  ext i
  simp only [fixedLoadPath,Pi.add_apply,Pi.sub_apply,Pi.smul_apply,smul_eq_mul]
  ring

theorem fixedLoadPath_zero (e : Vec n) : d.fixedLoadPath e 0=d.criticalInputs := by
  simp [fixedLoadPath]

theorem fixedLoadPath_one (e : Vec n) : d.fixedLoadPath e 1=e := by simp [fixedLoadPath]

theorem fixedLoadPath_report (P : Partition n g) (e : Vec n)
    (he : d.groupTotal P e=d.groupTotal P d.criticalInputs) (t : ℝ) :
    d.groupTotal P (d.fixedLoadPath e t)=d.groupTotal P d.criticalInputs := by
  rw [fixedLoadPath,d.groupTotal_add,d.groupTotal_smul,d.groupTotal_smul,he,←add_smul]
  simp

theorem fixedLoadPath_theta (e : Vec n) (he : d.theta e=d.theta d.criticalInputs) (t : ℝ) :
    d.theta (d.fixedLoadPath e t)=d.theta d.criticalInputs := by
  rw [fixedLoadPath,d.theta_add,d.theta_smul,d.theta_smul,he]
  ring

theorem fixedLoadPath_admissible (P : Partition n g) (e : Vec n)
    (he : e∈d.closedFiber P (d.groupTotal P d.criticalInputs))
    (t : ℝ) (ht : 0≤t) (ht1 : t<1) : d.Admissible (d.fixedLoadPath e t) := by
  refine ⟨?_,?_⟩
  · intro i
    change |(1-t)*d.criticalInputs i+t*e i|<1
    calc
      _≤|(1-t)*d.criticalInputs i|+|t*e i| := abs_add_le _ _
      _=(1-t)*|d.criticalInputs i|+t*|e i| := by
        rw [abs_mul,abs_mul,abs_of_nonneg (by linarith : 0≤1-t),abs_of_nonneg ht]
      _<(1-t)*1+t*1 := add_lt_add_of_lt_of_le
        (mul_lt_mul_of_pos_left (d.criticalInputs_admissible.1 i) (by linarith))
        (mul_le_mul_of_nonneg_left (he.1 i) ht)
      _=1 := by ring
  · rw [d.same_report_balance P d.criticalInputs _ (d.fixedLoadPath_report P e he.2 t)]
    exact d.criticalInputs_admissible.2

theorem fixedLoadPath_secondMoment (e : Vec n) (he : d.theta e=d.theta d.criticalInputs) (t : ℝ) :
    d.secondMoment (d.fixedLoadPath e t)=d.criticalExposure+t^2*(d.secondMoment e-d.criticalExposure) := by
  have hs : d.secondMoment (e-d.criticalInputs)=d.secondMoment e-d.criticalExposure := by
    rw [criticalInputs,d.secondMoment_sub_typeRay,he,d.criticalInputs_theta]
    nlinarith [Real.sq_sqrt d.criticalExposure_mem.1.le]
  have hn : d.secondMoment (d.criticalInputs-e)=d.secondMoment (e-d.criticalInputs) := by
    unfold secondMoment
    apply Finset.sum_congr rfl
    intro i _
    change d.w i*(d.criticalInputs i-e i)^2=d.w i*(e i-d.criticalInputs i)^2
    ring
  rw [fixedLoadPath,d.secondMoment_convex_identity _ _ _ _ (by ring),
    d.criticalInputs_secondMoment,hn,hs]
  ring

theorem fixedLoadPath_tendsto (e : Vec n) :
    Tendsto (d.fixedLoadPath e) (𝓝[<] (1:ℝ)) (𝓝 e) := by
  have hC : Continuous (d.fixedLoadPath e) := by unfold fixedLoadPath;fun_prop
  have hh := hC.continuousAt.tendsto.mono_left
    (nhdsWithin_le_nhds (a := (1:ℝ)) (s := Set.Iio 1))
  simpa only [d.fixedLoadPath_one] using hh

theorem fixedLoadPath_welfare_limit (P : Partition n g) (e : Vec n)
    (he : e∈d.closedFiber P (d.groupTotal P d.criticalInputs)) :
    Tendsto (fun t => d.normalizedWelfare (d.fixedLoadPath e t))
      (𝓝[<] (1:ℝ)) (𝓝 (d.normalizedWelfare e)) :=
  (d.normalizedWelfare_continuousAt e (d.closedFiber_denominator_positive P _ e he).ne').tendsto.comp
    (d.fixedLoadPath_tendsto e)

theorem fixedLoadPath_pair_lower (P : Partition n g) (e : Vec n)
    (he : e∈d.closedFiber P (d.groupTotal P d.criticalInputs)) :
    |d.normalizedWelfare d.criticalInputs-d.normalizedWelfare e|≤d.exAnteWidth P := by
  apply le_of_tendsto ((tendsto_const_nhds.sub (d.fixedLoadPath_welfare_limit P e he)).abs)
  have h0 : ∀ᶠt : ℝ in 𝓝[<] (1:ℝ),0≤t :=
    (eventually_ge_nhds (by norm_num : (0:ℝ)<1)).filter_mono nhdsWithin_le_nhds
  filter_upwards [h0,self_mem_nhdsWithin] with t ht ht1
  exact d.arbitrary_partition_pair_lower P d.criticalInputs (d.fixedLoadPath e t)
    d.criticalInputs_admissible (d.fixedLoadPath_admissible P e he t ht ht1)
    (d.fixedLoadPath_report P e he.2 t)

end CommodityClassification.Precision.Data
