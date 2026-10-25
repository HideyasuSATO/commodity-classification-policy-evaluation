module

public import LeanMath.CommodityClassification.UnknownSigmaEnvelope

/-! Attainment of the unknown-substitution bound by strictly positive inputs. -/
@[expose] public section
noncomputable section
set_option maxHeartbeats 1800000
namespace CommodityClassification.Precision.Data
open InputCoordinates
variable {n : ℕ} (d : Precision.Data n)

def sigmaCriticalInputs (l u : ℝ) : Vec n :=
  d.typeRay (Real.sqrt (Envelope.optimizer l u d.totalElasticity))

theorem sigmaCriticalInputs_admissible (l u : ℝ) (hl : 0<l) (hu : 0<u) :
    d.Admissible (d.sigmaCriticalInputs l u) := by
  have hx := Envelope.optimizer_mem l u d.totalElasticity hl hu d.totalElasticity_pos
  apply d.typeRay_admissible
  rw [abs_of_nonneg (Real.sqrt_nonneg _)]
  nlinarith [Real.sq_sqrt hx.1.le,Real.sqrt_nonneg (Envelope.optimizer l u d.totalElasticity),hx.2]

theorem sigmaCriticalInputs_moments (l u : ℝ) (hl : 0<l) (hu : 0<u) :
    (d.theta (d.sigmaCriticalInputs l u))^2=Envelope.optimizer l u d.totalElasticity ∧
      d.secondMoment (d.sigmaCriticalInputs l u)=Envelope.optimizer l u d.totalElasticity := by
  have hx := Envelope.optimizer_mem l u d.totalElasticity hl hu d.totalElasticity_pos
  unfold sigmaCriticalInputs
  rw [d.typeRay_theta,d.typeRay_secondMoment,Real.sq_sqrt hx.1.le]
  exact ⟨rfl,rfl⟩

theorem sigmaConditionalWidth_equal_moments (l u : ℝ) (hl : 0<l) (hlu : l≤u)
    (c : Vec n) (hc : d.Admissible c) (x : ℝ)
    (ht : (d.theta c)^2=x) (hQ : d.secondMoment c=x) :
    d.sigmaConditionalWidth l u c=Envelope.value l u d.totalElasticity d.lossScale x := by
  rw [d.sigmaConditionalWidth_formula l u hl hlu c hc,ht,hQ]
  have hf : ∀s,d.denominator s x x=Envelope.factor s d.totalElasticity x := by
    intro s
    unfold denominator Envelope.factor totalElasticity
    ring
  rw [hf,hf]
  unfold Envelope.value
  ring

theorem sigmaCriticalInputs_attain (l u : ℝ) (hl : 0<l) (hlu : l≤u) :
    d.sigmaConditionalWidth l u (d.sigmaCriticalInputs l u)=d.sigmaFloor l u := by
  have hu := hl.trans_le hlu
  have hm := d.sigmaCriticalInputs_moments l u hl hu
  rw [d.sigmaConditionalWidth_equal_moments l u hl hlu _
    (d.sigmaCriticalInputs_admissible l u hl hu) _ hm.1 hm.2,
    Envelope.value_at_optimizer l u _ _ hl hu d.totalElasticity_pos,
    d.sigmaEnvelope_bound_formula l u hl hu]

theorem sigmaFloor_known (l : ℝ) : d.sigmaFloor l l=0 := by simp [sigmaFloor]

theorem sigmaFloor_positive (l u : ℝ) (hl : 0<l) (hlu : l<u) : 0<d.sigmaFloor l u := by
  apply div_pos
  · exact mul_pos d.policyShare_pos (sub_pos.mpr (Real.sqrt_lt_sqrt hl.le hlu))
  · exact add_pos (Real.sqrt_pos.mpr (hl.trans hlu)) (Real.sqrt_pos.mpr hl)

theorem sigmaCriticalInputs_actual_gap (l u : ℝ) (hl : 0<l) (hlu : l≤u) :
    let c := d.sigmaCriticalInputs l u
    let hc := d.sigmaCriticalInputs_admissible l u hl (hl.trans_le hlu)
    ((d.withSigma u (hl.trans_le hlu)).family.model
      ((d.withSigma u (hl.trans_le hlu)).candidate c hc)).lossCoefficient/d.nu-
      ((d.withSigma l hl).family.model ((d.withSigma l hl).candidate c hc)).lossCoefficient/d.nu=
        d.sigmaFloor l u := by
  dsimp only
  rw [d.withSigma_actual_coefficient,d.withSigma_actual_coefficient,
    ←d.sigmaConditionalWidth_endpoints l u hl hlu _
      (d.sigmaCriticalInputs_admissible l u hl (hl.trans_le hlu)),d.sigmaCriticalInputs_attain l u hl hlu]

end CommodityClassification.Precision.Data
