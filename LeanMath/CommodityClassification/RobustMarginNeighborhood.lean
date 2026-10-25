module

public import LeanMath.CommodityClassification.RobustStructuredWidth

/-! A common strict precision margin provides a neighborhood independent of the number of goods. -/
@[expose] public section
noncomputable section
namespace CommodityClassification.Robust
open Filter
open scoped Topology

theorem strict_margin_neighborhood (L eps : ℝ) (hε : 0<eps) (hL : eps<L) :
    ∀ᶠ x : ℝ×ℝ in 𝓝 (0,0),
      2*errorConstant x.1 x.2/normalizationLower x.1 x.2<eps ∧
        eps<(L-2*errorConstant x.1 x.2)/normalizationUpper x.1 x.2 := by
  have hlow : ContinuousAt (fun x : ℝ×ℝ =>
      2*errorConstant x.1 x.2/normalizationLower x.1 x.2) (0,0) := by
    unfold errorConstant normalizationLower
    fun_prop (disch := norm_num)
  have hupp : ContinuousAt (fun x : ℝ×ℝ =>
      (L-2*errorConstant x.1 x.2)/normalizationUpper x.1 x.2) (0,0) := by
    unfold errorConstant normalizationUpper
    fun_prop (disch := norm_num)
  have hl := hlow.eventually (gt_mem_nhds (by simpa [errorConstant,normalizationLower] using hε))
  have hu := hupp.eventually (lt_mem_nhds (by simpa [errorConstant,normalizationUpper] using hL))
  exact hl.and hu

end CommodityClassification.Robust
