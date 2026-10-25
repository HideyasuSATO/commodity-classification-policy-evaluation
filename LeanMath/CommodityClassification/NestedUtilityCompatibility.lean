module

public import LeanMath.CommodityClassification.NestedDemandSmoothness
public import Mathlib.Analysis.Calculus.LocalExtr.Basic

/-! Derive marginal utility from the actual interior optimum of nested preferences. -/
@[expose] public section
noncomputable section
set_option maxHeartbeats 1000000
namespace CommodityClassification.Equilibrium
open Matrix Filter
open scoped Topology
variable {n : ℕ}

theorem interior_surplus_marginals (utility : Vec n → ℝ) (r x : Vec n)
    (hx : ∀i,0<x i) (hd : DifferentiableAt ℝ utility x)
    (hmax : IsMaxOn (fun y => utility y-dotProduct r y) {y | ∀i,0≤y i} x) :
    HasFDerivAt utility (CESCost.weightedLinear r) x := by
  have hm : IsLocalMax (fun y => utility y-dotProduct r y) x := by
    filter_upwards [CESCost.positivePrices_open.mem_nhds hx] with y hy
    exact hmax (fun i => (hy i).le)
  have hf : HasFDerivAt (fun y => utility y-dotProduct r y)
      (fderiv ℝ utility x-CESCost.weightedLinear r) x := by
    convert hd.hasFDerivAt.sub (CESCost.weightedLinear r).hasFDerivAt using 1
    ext y
    simp only [Pi.sub_apply,CESCost.weightedLinear_apply]
  have he := sub_eq_zero.mp (hm.hasFDerivAt_eq_zero hf)
  exact he ▸ hd.hasFDerivAt

end CommodityClassification.Equilibrium

namespace CommodityClassification.DemandNests.Data
open Matrix Equilibrium Filter
open scoped Topology
variable {n g : ℕ} (d : DemandNests.Data n g)

def nestedUtility (DG : Mat g g) (c : ℝ) (x : Vec n) : ℝ := d.outerUtility DG c (d.quantityMap x)

theorem nestedUtility_differentiable (DG : Mat g g) (hDG : DG.PosDef) (c : ℝ)
    {x : Vec n} (hx : ∀i,0<x i) : DifferentiableAt ℝ (d.nestedUtility DG c) x := by
  exact (benchmarkUtility_derivative (fun _ => 1) (d.partition.sales d.p d.q) DG hDG c
    (d.quantityMap x)).differentiableAt.comp x ((d.quantityMap_smooth hx).differentiableAt (by simp))

theorem quadratic_nested_utility_compatible (DG : Mat g g) (hDG : DG.PosDef) (c : ℝ) :
    ∀ᶠr in 𝓝 d.p,HasFDerivAt (d.nestedUtility DG c) (CESCost.weightedLinear r)
      (d.demand (d.quadraticOuter DG) r) := by
  filter_upwards [d.quadratic_nested_optimal_near DG hDG c] with r hr
  exact interior_surplus_marginals _ r _ hr.2.1
    (d.nestedUtility_differentiable DG hDG c hr.2.1) hr.2.2

end CommodityClassification.DemandNests.Data
