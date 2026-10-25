module

public import LeanMath.CommodityClassification.PrecisionTailCapacity

/-! Exact scalar constants shared by the two finite-sales illustrations. -/
@[expose] public section
noncomputable section
set_option maxHeartbeats 1600000
namespace CommodityClassification.Precision.Illustration

theorem sqrt_four : Real.sqrt (4:ℝ)=2 :=
  (Real.sqrt_eq_iff_eq_sq (by norm_num) (by norm_num)).mpr (by norm_num)

theorem sqrt_nine : Real.sqrt (9:ℝ)=3 :=
  (Real.sqrt_eq_iff_eq_sq (by norm_num) (by norm_num)).mpr (by norm_num)

end CommodityClassification.Precision.Illustration

namespace CommodityClassification.Precision.Data
open InputCoordinates
variable {n : ℕ} (d : Precision.Data n)

def HasIllustrationParameters : Prop :=
  d.eta=9/4 ∧ d.alpha=9/4 ∧ d.beta=1/2 ∧ d.sigma=1

theorem illustration_constants (h : d.HasIllustrationParameters) :
    d.totalElasticity=9/2 ∧ d.nu=27/8 ∧ d.policyShare=1/3 ∧ d.lossScale=3/2 ∧
      d.criticalExposure=1/4 ∧ d.precisionFloor=1/15 ∧ d.capacityMultiplier=15/112 := by
  rcases h with ⟨hη,hα,hβ,hσ⟩
  norm_num [totalElasticity,nu,policyShare,lossScale,criticalExposure,precisionFloor,
    capacityMultiplier,minElasticity,maxElasticity,Envelope.optimizer,Capacity.chi,
    hη,hα,hβ,hσ,Real.sqrt_div,Illustration.sqrt_four,Illustration.sqrt_nine]

theorem illustration_shareFloor (h : d.HasIllustrationParameters) : d.shareFloor (15/16)=1/64 := by
  rw [shareFloor,(d.illustration_constants h).2.2.2.2.1]
  norm_num [Real.sqrt_div,Illustration.sqrt_four]

theorem illustration_criticalInputs (h : d.HasIllustrationParameters) :
    d.criticalInputs=fun i => d.v i/2 := by
  rw [criticalInputs,(d.illustration_constants h).2.2.2.2.1]
  ext i
  change Real.sqrt (1/4:ℝ)*d.v i=d.v i/2
  norm_num [Real.sqrt_div,Illustration.sqrt_four]
  ring

theorem illustration_fixedLoadPath (e : Vec n) :
    d.fixedLoadPath e (15/16)=fun i => (15*e i+d.criticalInputs i)/16 := by
  ext i
  change (1-(15/16:ℝ))*d.criticalInputs i+(15/16:ℝ)*e i=_
  ring

theorem illustration_width_formula (h : d.HasIllustrationParameters) (Q : ℝ) :
    d.momentWidth (1/4) (1/4) Q= (3/8)*|8/15-1/(25/16+5*Q/4)| := by
  rcases h with ⟨hη,hα,hβ,hσ⟩
  norm_num [momentWidth,lossScale,policyShare,nu,totalElasticity,denominator,hη,hα,hβ,hσ]
  congr 2
  ring

theorem illustration_width_threshold (h : d.HasIllustrationParameters) (Q : ℝ)
    (hQ : 1/4≤Q) : (1/20 : ℝ)<d.momentWidth (1/4) (1/4) Q ↔ 3/4<Q := by
  rw [d.illustration_width_formula h Q]
  have hk : 0<25/16+5*Q/4 := by linarith
  have hrec : 1/(25/16+5*Q/4)≤8/15 := by
    rw [div_le_iff₀ hk]
    linarith
  rw [abs_of_nonneg (sub_nonneg.mpr hrec)]
  have he : (1/20:ℝ)<(3/8)*(8/15-1/(25/16+5*Q/4)) ↔
      1/(25/16+5*Q/4)<2/5 := by constructor <;> intro hh <;> linarith
  rw [he,div_lt_iff₀ hk]
  constructor <;> intro hh <;> linarith

end CommodityClassification.Precision.Data
