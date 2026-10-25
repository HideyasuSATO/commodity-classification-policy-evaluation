module

public import LeanMath.CommodityClassification.PrecisionScalarEnvelope

/-! The manuscript's a, d*, x* and G*, and their exact scalar-welfare meaning. -/
@[expose] public section
noncomputable section
set_option maxHeartbeats 1800000
namespace CommodityClassification.Precision.Data
open Matrix InputCoordinates
variable {n : ℕ} (d : Precision.Data n)

def minElasticity : ℝ := min d.eta d.sigma
def maxElasticity : ℝ := max d.eta d.sigma
def criticalExposure : ℝ := Envelope.optimizer d.minElasticity d.maxElasticity d.totalElasticity
def precisionFloor : ℝ := d.policyShare*(Real.sqrt d.maxElasticity-Real.sqrt d.minElasticity)/
  (Real.sqrt d.maxElasticity+Real.sqrt d.minElasticity)

theorem minElasticity_pos : 0<d.minElasticity := lt_min d.heta d.hsigma
theorem maxElasticity_pos : 0<d.maxElasticity := d.heta.trans_le (le_max_left _ _)
theorem minElasticity_le_max : d.minElasticity≤d.maxElasticity := (min_le_left _ _).trans (le_max_left _ _)

theorem policyShare_pos : 0<d.policyShare :=
  div_pos (mul_pos d.totalElasticity_pos (sq_pos_of_pos d.hbeta.1)) d.nu_pos

theorem criticalExposure_mem : d.criticalExposure∈Set.Ioo (0:ℝ) 1 :=
  Envelope.optimizer_mem _ _ _ d.minElasticity_pos d.maxElasticity_pos d.totalElasticity_pos

theorem envelope_bound_formula :
    Envelope.bound d.minElasticity d.maxElasticity d.totalElasticity d.lossScale=d.precisionFloor := by
  rw [lossScale,Envelope.bound_scaled _ _ _ _ d.minElasticity_pos d.maxElasticity_pos d.totalElasticity_pos]
  rfl

theorem precisionFloor_nonneg : 0≤d.precisionFloor := by
  exact div_nonneg (mul_nonneg d.policyShare_pos.le
    (sub_nonneg.mpr (Real.sqrt_le_sqrt d.minElasticity_le_max)))
    (add_pos (Real.sqrt_pos.mpr d.maxElasticity_pos) (Real.sqrt_pos.mpr d.minElasticity_pos)).le

theorem precisionFloor_matching (hs : d.eta=d.sigma) : d.precisionFloor=0 := by
  simp [precisionFloor,minElasticity,maxElasticity,hs]

theorem momentWidth_full_equals_envelope (x : ℝ) (hx : x∈Set.Icc (0:ℝ) 1) :
    d.momentWidth x x 1=Envelope.value d.minElasticity d.maxElasticity d.totalElasticity d.lossScale x := by
  rw [d.momentWidth_fraction x x 1 hx.2
    (d.denominator_positive_unit x x hx.1 hx.2 hx.1)
    (d.denominator_positive_unit 1 x (by norm_num) le_rfl hx.1)]
  unfold Envelope.value Envelope.factor minElasticity maxElasticity denominator totalElasticity
  rcases le_total d.eta d.sigma with hle|hle
  · rw [min_eq_left hle,max_eq_right hle,abs_of_nonpos (sub_nonpos.mpr hle)]
    ring
  · rw [min_eq_right hle,max_eq_left hle,abs_of_nonneg (sub_nonneg.mpr hle)]
    ring

theorem scalar_envelope_upper (x : ℝ) (hx : x∈Set.Icc (0:ℝ) 1) :
    d.momentWidth x x 1≤d.precisionFloor := by
  rw [d.momentWidth_full_equals_envelope x hx,←d.envelope_bound_formula]
  exact Envelope.value_le_bound _ _ _ _ _ d.minElasticity_pos d.maxElasticity_pos
    d.minElasticity_le_max d.totalElasticity_pos d.lossScale_pos.le hx

theorem scalar_envelope_attains :
    d.momentWidth d.criticalExposure d.criticalExposure 1=d.precisionFloor := by
  have hx := d.criticalExposure_mem
  rw [d.momentWidth_full_equals_envelope _ ⟨hx.1.le,hx.2.le⟩,←d.envelope_bound_formula]
  exact Envelope.value_at_optimizer _ _ _ _ d.minElasticity_pos d.maxElasticity_pos d.totalElasticity_pos

theorem scalar_envelope_isGreatest :
    IsGreatest ((fun x : ℝ => d.momentWidth x x 1) '' Set.Icc (0:ℝ) 1) d.precisionFloor := by
  have hx := d.criticalExposure_mem
  refine ⟨⟨d.criticalExposure,⟨hx.1.le,hx.2.le⟩,d.scalar_envelope_attains⟩,?_⟩
  rintro z ⟨x,hx,rfl⟩
  exact d.scalar_envelope_upper x hx

end CommodityClassification.Precision.Data
