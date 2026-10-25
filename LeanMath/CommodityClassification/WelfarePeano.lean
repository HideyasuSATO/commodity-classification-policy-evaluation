module
public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.Analysis.Asymptotics.Ring
public import Mathlib.Analysis.Asymptotics.Lemmas
public import Mathlib.Analysis.Calculus.Deriv.Pow
public import Mathlib.Tactic.Ring
@[expose] public section
set_option maxHeartbeats 1800000
namespace CommodityClassification.WelfareAnalysis
open Filter Asymptotics
open scoped Topology

/-- A two-sided Peano remainder from a locally known first derivative.
No second derivative of W or derivative of h is assumed. -/
theorem peano_of_derivative (W h : ℝ → ℝ) (hc : ContinuousAt h 0)
    (hd : ∀ᶠ t in 𝓝 (0 : ℝ), HasDerivAt W (t*h t) t) :
    (fun t => W t-W 0-(1/2 : ℝ)*t^2*h 0) =o[𝓝 (0 : ℝ)] (fun t : ℝ => t^2) := by
  let r := fun t => W t-W 0-(1/2 : ℝ)*t^2*h 0
  have hlo : (fun t => h t-h 0) =o[𝓝 (0 : ℝ)] (fun _ : ℝ => (1 : ℝ)) := by
    apply (isLittleO_one_iff ℝ).mpr
    simpa only [sub_self] using hc.tendsto.sub (tendsto_const_nhds (x := h 0))
  have hsmall : (fun t => t*(h t-h 0)) =o[𝓝 (0 : ℝ)] (fun t : ℝ => t) := by
    simpa only [mul_one] using (isBigO_refl (fun t : ℝ => t) (𝓝 0)).mul_isLittleO hlo
  obtain ⟨δ,hδ,hball⟩ := Metric.mem_nhds_iff.mp hd
  have hr (t : ℝ) (ht : t ∈ Metric.ball (0 : ℝ) δ) : HasDerivAt r (t*(h t-h 0)) t := by
    have hp := (((hasDerivAt_id t).pow 2).const_mul (1/2 : ℝ)).mul_const (h 0)
    convert ((hball ht).sub_const (W 0)).sub hp using 1
    · funext x
      rfl
    · dsimp
      ring
  have hout := (convex_ball (0 : ℝ) δ).isLittleO_pow_succ_real
    (x₀ := (0 : ℝ)) (n := 1) (Metric.mem_ball_self hδ)
    (fun t ht => (hr t ht).hasDerivWithinAt)
    (by
      rw [nhdsWithin_eq_nhds.mpr (Metric.ball_mem_nhds (0 : ℝ) hδ)]
      simpa only [sub_zero,pow_one] using hsmall)
  rw [nhdsWithin_eq_nhds.mpr (Metric.ball_mem_nhds (0 : ℝ) hδ)] at hout
  simpa only [r,sub_zero,zero_pow (by decide : (2 : ℕ) ≠ 0),mul_zero,zero_mul,sub_self] using hout

theorem loss_peano_of_derivative (W h : ℝ → ℝ) (hc : ContinuousAt h 0)
    (hd : ∀ᶠ t in 𝓝 (0 : ℝ), HasDerivAt W (t*h t) t) :
    (fun t => W 0-W t-(1/2 : ℝ)*t^2*(-h 0)) =o[𝓝 (0 : ℝ)] (fun t : ℝ => t^2) := by
  have hh := (peano_of_derivative W h hc hd).neg_left
  convert hh using 1
  funext t
  ring

/-- The scalar argument never divides by its leading coefficient. -/
theorem zero_coefficient (W h : ℝ → ℝ) (hc : ContinuousAt h 0) (h0 : h 0=0)
    (hd : ∀ᶠ t in 𝓝 (0 : ℝ), HasDerivAt W (t*h t) t) :
    (fun t => W 0-W t) =o[𝓝 (0 : ℝ)] (fun t : ℝ => t^2) := by
  simpa only [h0,neg_zero,mul_zero,sub_zero] using loss_peano_of_derivative W h hc hd

end CommodityClassification.WelfareAnalysis
