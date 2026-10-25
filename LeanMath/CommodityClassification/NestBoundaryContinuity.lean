module

public import LeanMath.CommodityClassification.NestBoundaryBounds

/-! The nonnegative extension is continuous and is the positive-domain limit. -/
@[expose] public section
noncomputable section
set_option maxHeartbeats 400000
namespace CommodityClassification.DemandNest.Data
open Matrix Filter
open scoped Topology BigOperators
variable {n : ℕ} (d : DemandNest.Data n)

theorem quantityOnNonnegative_continuousAt_positive {x : Vec n} (hx : ∀i,0<x i) :
    ContinuousAt d.quantityOnNonnegative x := by
  apply (d.quantity_smooth hx).continuousAt.congr_of_eventuallyEq
  filter_upwards [CESCost.positivePrices_open.mem_nhds hx] with y hy
  exact d.quantityOnNonnegative_of_positive hy

theorem quantityOnNonnegative_continuousWithinAt_small_boundary (hη : d.eta<1)
    {x : Vec n} (hx : ∀i,0≤x i) (hp : ¬∀i,0<x i) :
    ContinuousWithinAt d.quantityOnNonnegative {y | ∀i,0≤y i} x := by
  obtain ⟨j,hj⟩ := nonnegative_zero_component hx hp
  have hc : Continuous (fun y : Vec n => d.sales*(d.share j)^(d.eta/(d.eta-1))*(y j/d.q j)) :=
    continuous_const.mul ((continuous_apply j).div_const _)
  have ht : Tendsto (fun y : Vec n => d.sales*(d.share j)^(d.eta/(d.eta-1))*(y j/d.q j))
      (𝓝[{y | ∀i,0≤y i}]x) (𝓝 0) := by
    have h0 : Tendsto (fun y : Vec n => d.sales*(d.share j)^(d.eta/(d.eta-1))*(y j/d.q j))
        (𝓝 x) (𝓝 (d.sales*(d.share j)^(d.eta/(d.eta-1))*(x j/d.q j))) :=
      hc.continuousAt.tendsto
    simpa only [hj,zero_div,mul_zero] using h0.mono_left nhdsWithin_le_nhds
  change Tendsto _ _ (𝓝 (d.quantityOnNonnegative x))
  rw [d.quantityOnNonnegative_boundary hη.le hp]
  apply squeeze_zero' _ _ ht
  · filter_upwards [self_mem_nhdsWithin] with y hy
    exact d.quantityOnNonnegative_nonneg hy
  · filter_upwards [self_mem_nhdsWithin] with y hy
    exact d.nonnegative_component_bound hη hy j

theorem quantityOnNonnegative_continuousOn :
    ContinuousOn d.quantityOnNonnegative {x : Vec n | ∀i,0≤x i} := by
  rcases lt_trichotomy d.eta 1 with hη | hη | hη
  · intro x hx
    by_cases hp : ∀i,0<x i
    · exact (d.quantityOnNonnegative_continuousAt_positive hp).continuousWithinAt
    · exact d.quantityOnNonnegative_continuousWithinAt_small_boundary hη hx hp
  · exact d.cobb_product_continuous.continuousOn.congr (fun x hx => d.cobb_boundary_product hη hx)
  · have he : d.quantityOnNonnegative=d.quantityIndex := funext (d.quantityOnNonnegative_of_large hη)
    rw [he]
    exact (d.quantity_continuous_large hη).continuousOn

theorem positive_approximation_tendsto {x : Vec n} (hx : ∀i,0≤x i) :
    Tendsto (fun ε : ℝ => x+ε • d.q) (𝓝[>]0) (𝓝[{y | ∀i,0≤y i}]x) := by
  apply tendsto_nhdsWithin_iff.mpr
  constructor
  · have hc : Continuous (fun ε : ℝ => x+ε • d.q) :=
      continuous_const.add (continuous_id.smul continuous_const)
    have ht : Tendsto (fun ε : ℝ => x+ε • d.q) (𝓝 (0:ℝ)) (𝓝 (x+(0:ℝ) • d.q)) :=
      hc.continuousAt.tendsto
    simpa only [zero_smul,add_zero] using ht.mono_left nhdsWithin_le_nhds
  · filter_upwards [self_mem_nhdsWithin] with ε hε
    exact fun i => (d.positive_approximation hx hε i).le

theorem quantity_boundary_limit {x : Vec n} (hx : ∀i,0≤x i) :
    Tendsto (fun ε : ℝ => d.quantityIndex (x+ε • d.q)) (𝓝[>]0)
      (𝓝 (d.quantityOnNonnegative x)) := by
  have ht := (d.quantityOnNonnegative_continuousOn x hx).tendsto.comp
    (d.positive_approximation_tendsto hx)
  apply ht.congr'
  filter_upwards [self_mem_nhdsWithin] with ε hε
  exact d.quantityOnNonnegative_of_positive (d.positive_approximation hx hε)

theorem continuous_extension_unique {f : Vec n → ℝ}
    (hf : ContinuousOn f {x | ∀i,0≤x i})
    (hagree : ∀x,(∀i,0<x i) → f x=d.quantityIndex x) {x : Vec n} (hx : ∀i,0≤x i) :
    f x=d.quantityOnNonnegative x := by
  have ht := (hf x hx).tendsto.comp (d.positive_approximation_tendsto hx)
  have hp : Tendsto (fun ε : ℝ => d.quantityIndex (x+ε • d.q)) (𝓝[>]0) (𝓝 (f x)) := by
    apply ht.congr'
    filter_upwards [self_mem_nhdsWithin] with ε hε
    exact hagree _ (d.positive_approximation hx hε)
  exact tendsto_nhds_unique hp (d.quantity_boundary_limit hx)

theorem ces_primal_dual_complete :
    ContinuousOn d.quantityOnNonnegative {x : Vec n | ∀i,0≤x i} ∧
    (∀x,(∀i,0<x i) → d.quantityOnNonnegative x=d.quantityIndex x) ∧
    ∀r,(∀i,0<r i) →
      IsLeast {v : ℝ | ∃x : Vec n,(∀i,0≤x i) ∧ 1≤d.quantityOnNonnegative x ∧ v=dotProduct r x}
        (d.expenditureIndex r) ∧
      ∃!x : Vec n,(∀i,0≤x i) ∧ 1≤d.quantityOnNonnegative x ∧ dotProduct r x=d.expenditureIndex r := by
  refine ⟨d.quantityOnNonnegative_continuousOn,fun x hx => d.quantityOnNonnegative_of_positive hx,?_⟩
  intro r hr
  refine ⟨d.nonnegative_unit_expenditure_isLeast hr, d.unitBundle r, ?_, ?_⟩
  · exact ⟨fun i => (d.unitBundle_positive hr i).le,(d.unitBundle_extended_quantity hr).ge,
      d.unitBundle_expenditure hr⟩
  · intro x hx
    exact d.nonnegative_optimum_unique hr hx.1 hx.2.1 hx.2.2

end CommodityClassification.DemandNest.Data
