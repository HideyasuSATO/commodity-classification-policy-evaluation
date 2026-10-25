module

public import LeanMath.CommodityClassification.PrecisionManuscriptWidth

/-! Exact rational inequalities for the two variance-allowance branches. -/
@[expose] public section
noncomputable section
set_option maxHeartbeats 1200000
namespace CommodityClassification.Precision.Variance

def growing (A h k V : ℝ) : ℝ := A*h*V/(k*(k+h*V))
def shrinking (A h k V : ℝ) : ℝ := A*h*V/(k*(k-h*V))

theorem growing_iff (A h k V eps : ℝ) (hh : 0<h) (hk : 0<k) (hV : 0≤V)
    (hA : eps*k<A) : growing A h k V≤eps ↔ V≤eps*k^2/(h*(A-eps*k)) := by
  have hden : 0<k*(k+h*V) := mul_pos hk (by nlinarith [mul_nonneg hh.le hV])
  have hr : 0<h*(A-eps*k) := mul_pos hh (sub_pos.mpr hA)
  rw [growing,div_le_iff₀ hden,le_div_iff₀ hr]
  constructor <;> intro he <;> nlinarith [he]

theorem growing_all_pass (A h k V eps : ℝ) (hh : 0≤h) (hk : 0<k) (hV : 0≤V)
    (heps : 0≤eps) (hA : A≤eps*k) : growing A h k V≤eps := by
  have hden : 0<k*(k+h*V) := mul_pos hk (by nlinarith [mul_nonneg hh hV])
  rw [growing,div_le_iff₀ hden]
  have ht := mul_le_mul_of_nonneg_right hA (mul_nonneg hh hV)
  have hp := mul_nonneg heps (sq_nonneg k)
  nlinarith

theorem shrinking_iff (A h k V eps : ℝ) (hA : 0<A) (hh : 0<h) (hk : 0<k)
    (heps : 0≤eps) (hK : 0<k-h*V) :
    shrinking A h k V≤eps ↔ V≤eps*k^2/(h*(A+eps*k)) := by
  have hr : 0<h*(A+eps*k) := mul_pos hh (by nlinarith [mul_nonneg heps hk.le])
  rw [shrinking,div_le_iff₀ (mul_pos hk hK),le_div_iff₀ hr]
  constructor <;> intro he <;> nlinarith [he]

theorem growing_zero_variance (A h k : ℝ) : growing A h k 0=0 := by simp [growing]
theorem shrinking_zero_variance (A h k : ℝ) : shrinking A h k 0=0 := by simp [shrinking]

end CommodityClassification.Precision.Variance
