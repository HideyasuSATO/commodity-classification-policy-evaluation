module

public import LeanMath.CommodityClassification.PrecisionBestClassification

/-! A common positive factor-share bound along the fixed-load paths. -/
@[expose] public section
noncomputable section
set_option maxHeartbeats 1400000
namespace CommodityClassification.Precision.Data
open InputCoordinates
variable {n : ℕ} (d : Precision.Data n)

def shareFloor (t : ℝ) : ℝ := (1-t)*(1-Real.sqrt d.criticalExposure)/2

theorem criticalRoot_lt_one : Real.sqrt d.criticalExposure<1 := by
  nlinarith [Real.sq_sqrt d.criticalExposure_mem.1.le,
    Real.sqrt_nonneg d.criticalExposure,d.criticalExposure_mem.2]

theorem shareFloor_pos (t : ℝ) (ht : t<1) : 0<d.shareFloor t :=
  div_pos (mul_pos (sub_pos.mpr ht) (sub_pos.mpr d.criticalRoot_lt_one)) (by norm_num)

theorem fixedLoadPath_abs_bound (e : Vec n) (he : ∀i,|e i|≤1)
    (t : ℝ) (ht : 0≤t) (ht1 : t≤1) (i : Fin n) :
    |d.fixedLoadPath e t i|≤t+(1-t)*Real.sqrt d.criticalExposure := by
  change |(1-t)*d.criticalInputs i+t*e i|≤_
  calc
    _≤|(1-t)*d.criticalInputs i|+|t*e i| := abs_add_le _ _
    _=(1-t)*Real.sqrt d.criticalExposure+t*|e i| := by
      rw [abs_mul,abs_mul,abs_of_nonneg (sub_nonneg.mpr ht1),abs_of_nonneg ht,d.criticalInputs_abs]
    _≤t+(1-t)*Real.sqrt d.criticalExposure := by
      have hh := mul_le_mul_of_nonneg_left (he i) ht
      linarith

theorem inputs_lower_from_abs (c : Vec n) (a : ℝ) (hc : ∀i,|c i|≤a) :
    ∀i j,(1-a)/2≤d.inputs c i j := by
  intro i j
  obtain ⟨hl,hu⟩ := abs_le.mp (hc i)
  fin_cases j <;> norm_num [inputs] <;> linarith

theorem fixedLoadPath_share_lower (e : Vec n) (he : ∀i,|e i|≤1)
    (t : ℝ) (ht : 0≤t) (ht1 : t≤1) :
    ∀i j,d.shareFloor t≤d.inputs (d.fixedLoadPath e t) i j := by
  have hh := d.inputs_lower_from_abs (d.fixedLoadPath e t)
    (t+(1-t)*Real.sqrt d.criticalExposure) (d.fixedLoadPath_abs_bound e he t ht ht1)
  intro i j
  have hi := hh i j
  unfold shareFloor
  nlinarith

theorem criticalInputs_share_lower (t : ℝ) (ht : 0≤t) :
    ∀i j,d.shareFloor t≤d.inputs d.criticalInputs i j := by
  have hh := d.inputs_lower_from_abs d.criticalInputs (Real.sqrt d.criticalExposure)
    (fun i => (d.criticalInputs_abs i).le)
  have hfactor : 0≤t*(1-Real.sqrt d.criticalExposure) :=
    mul_nonneg ht (sub_nonneg.mpr d.criticalRoot_lt_one.le)
  intro i j
  have hi := hh i j
  unfold shareFloor
  nlinarith

theorem criticalExposure_parameters_eq {n' : ℕ} (e : Precision.Data n')
    (hη : d.eta=e.eta) (hα : d.alpha=e.alpha) (hσ : d.sigma=e.sigma) :
    d.criticalExposure=e.criticalExposure := by
  simp only [criticalExposure,minElasticity,maxElasticity,totalElasticity]
  rw [hη,hα,hσ]

theorem shareFloor_parameters_eq {n' : ℕ} (e : Precision.Data n')
    (hη : d.eta=e.eta) (hα : d.alpha=e.alpha) (hσ : d.sigma=e.sigma) (t : ℝ) :
    d.shareFloor t=e.shareFloor t := by
  rw [shareFloor,shareFloor,d.criticalExposure_parameters_eq e hη hα hσ]

end CommodityClassification.Precision.Data
