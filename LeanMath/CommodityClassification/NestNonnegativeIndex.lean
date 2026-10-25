module

public import LeanMath.CommodityClassification.NestConditionalDemand
public import Mathlib.Analysis.SpecialFunctions.Pow.Continuity

/-! A distinct CES extension to nonnegative quantities. -/
@[expose] public section
noncomputable section
set_option maxHeartbeats 200000
namespace CommodityClassification.DemandNest.Data
open Matrix Filter
open scoped Topology BigOperators
variable {n : ℕ} (d : DemandNest.Data n)

def quantityOnNonnegative (x : Vec n) : ℝ :=
  if 1<d.eta then d.quantityIndex x
  else if ∀i,0<x i then d.quantityIndex x else 0

theorem quantityOnNonnegative_of_positive {x : Vec n} (hx : ∀i,0<x i) :
    d.quantityOnNonnegative x=d.quantityIndex x := by
  unfold quantityOnNonnegative
  rw [if_pos hx,ite_self]

theorem quantityOnNonnegative_of_large (hη : 1<d.eta) (x : Vec n) :
    d.quantityOnNonnegative x=d.quantityIndex x := by
  simp only [quantityOnNonnegative,hη,ite_true]

theorem quantityOnNonnegative_boundary (hη : d.eta≤1) {x : Vec n}
    (hx : ¬∀i,0<x i) : d.quantityOnNonnegative x=0 := by
  simp only [quantityOnNonnegative,not_lt.mpr hη,hx,ite_false]

theorem quantity_continuous_large (hη : 1<d.eta) : Continuous d.quantityIndex := by
  have hi : 0≤(d.eta-1)/d.eta := (div_pos (sub_pos.mpr hη) d.heta).le
  have ho : 0≤d.eta/(d.eta-1) := (div_pos d.heta (sub_pos.mpr hη)).le
  have he : d.quantityIndex=(fun x : Vec n => d.sales*
      (∑i,d.share i*(x i/d.q i)^((d.eta-1)/d.eta))^(d.eta/(d.eta-1))) :=
    funext (d.quantity_ces_normalized (ne_of_gt hη))
  rw [he]
  apply continuous_const.mul
  apply Continuous.rpow_const _ (fun _ => Or.inr ho)
  apply continuous_finsetSum
  intro i _
  have hc : Continuous (fun x : Vec n => x i/d.q i) := (continuous_apply i).div_const _
  exact continuous_const.mul (hc.rpow_const (fun _ => Or.inr hi))

theorem quantityOnNonnegative_nonneg {x : Vec n} (hx : ∀i,0≤x i) :
    0≤d.quantityOnNonnegative x := by
  by_cases hη : 1<d.eta
  · rw [d.quantityOnNonnegative_of_large hη,d.quantity_ces_normalized (ne_of_gt hη)]
    exact mul_nonneg d.sales_pos.le (Real.rpow_nonneg (Finset.sum_nonneg
      (fun i _ => mul_nonneg (d.share_pos i).le
        (Real.rpow_nonneg (div_nonneg (hx i) (d.hq i).le) _))) _)
  · by_cases hp : ∀i,0<x i
    · rw [d.quantityOnNonnegative_of_positive hp]
      exact (d.quantity_positive hp).le
    · rw [d.quantityOnNonnegative_boundary (le_of_not_gt hη) hp]

theorem positive_approximation {x : Vec n} (hx : ∀i,0≤x i) {ε : ℝ} (hε : 0<ε) :
    ∀i,0<(x+ε • d.q) i := by
  intro i
  exact add_pos_of_nonneg_of_pos (hx i) (mul_pos hε (d.hq i))

theorem nonnegative_dual_inequality_large (hη : 1<d.eta) {r x : Vec n}
    (hr : ∀i,0<r i) (hx : ∀i,0≤x i) :
    d.expenditureIndex r*d.quantityIndex x≤dotProduct r x := by
  have ha : Continuous (fun ε : ℝ => x+ε • d.q) :=
    continuous_const.add (continuous_id.smul continuous_const)
  have hF : Tendsto (fun ε : ℝ => d.quantityIndex (x+ε • d.q)) (𝓝[>]0)
      (𝓝 (d.quantityIndex x)) := by
    have h0 : Tendsto (fun ε : ℝ => d.quantityIndex (x+ε • d.q)) (𝓝 (0:ℝ))
        (𝓝 (d.quantityIndex (x+(0:ℝ) • d.q))) :=
      ((d.quantity_continuous_large hη).comp ha).continuousAt.tendsto
    simpa only [zero_smul,add_zero] using h0.mono_left nhdsWithin_le_nhds
  have hE : Tendsto (fun ε : ℝ => dotProduct r (x+ε • d.q)) (𝓝[>]0)
      (𝓝 (dotProduct r x)) := by
    have h0 : Tendsto (fun ε : ℝ => (CESCost.weightedLinear r) (x+ε • d.q)) (𝓝 (0:ℝ))
        (𝓝 ((CESCost.weightedLinear r) (x+(0:ℝ) • d.q))) :=
      ((CESCost.weightedLinear r).continuous.comp ha).continuousAt.tendsto
    simpa only [CESCost.weightedLinear_apply,zero_smul,add_zero] using h0.mono_left
      nhdsWithin_le_nhds
  apply le_of_tendsto_of_tendsto (tendsto_const_nhds.mul hF) hE
  filter_upwards [self_mem_nhdsWithin] with ε hε
  exact d.positive_dual_inequality hr (d.positive_approximation hx hε)

theorem nonnegative_dual_inequality {r x : Vec n} (hr : ∀i,0<r i) (hx : ∀i,0≤x i) :
    d.expenditureIndex r*d.quantityOnNonnegative x≤dotProduct r x := by
  by_cases hη : 1<d.eta
  · rw [d.quantityOnNonnegative_of_large hη]
    exact d.nonnegative_dual_inequality_large hη hr hx
  · by_cases hp : ∀i,0<x i
    · rw [d.quantityOnNonnegative_of_positive hp]
      exact d.positive_dual_inequality hr hp
    · rw [d.quantityOnNonnegative_boundary (le_of_not_gt hη) hp,mul_zero]
      exact Finset.sum_nonneg (fun i _ => mul_nonneg (hr i).le (hx i))

end CommodityClassification.DemandNest.Data
