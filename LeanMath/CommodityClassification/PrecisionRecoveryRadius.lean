module

public import LeanMath.CommodityClassification.ObservationRecoveryRadius

/-! The precision tolerance in the manuscript is a range width, twice unrestricted recovery error. -/
@[expose] public section
noncomputable section
namespace CommodityClassification.Precision.Data
open InputCoordinates Information
variable {n : ℕ} (d : Precision.Data n) {A : Type*}

theorem observation_recovery_radius (O : Vec n→A) :
    recoveryRadius {c | d.Admissible c} O d.normalizedWelfare=d.observationExAnteWidth O/2 := by
  rw [recoveryRadius_eq_half_width _ ⟨0,d.zero_admissible⟩ _ _ d.general_observation_bounded,
    d.general_observation_width]

theorem width_tolerance_iff_prediction (O : Vec n→A) (eps : ℝ) :
    d.observationExAnteWidth O≤eps ↔ ∃a : A→ℝ,
      ∀c,d.Admissible c→|a (O c)-d.normalizedWelfare c|≤eps/2 := by
  change d.observationExAnteWidth O≤eps ↔ ∃a : A→ℝ,
    UniformErrorBound {c | d.Admissible c} O d.normalizedWelfare a (eps/2)
  rw [uniform_error_achievable_iff _ ⟨0,d.zero_admissible⟩ _ _ d.general_observation_bounded,
    d.general_observation_width]
  ring_nf

theorem partition_recovery_radius {g : ℕ} (P : Partition n g) :
    recoveryRadius {c | d.Admissible c} (d.groupTotal P) d.normalizedWelfare=d.exAnteWidth P/2 := by
  rw [d.observation_recovery_radius,d.observation_partition_exAnte]

end CommodityClassification.Precision.Data
