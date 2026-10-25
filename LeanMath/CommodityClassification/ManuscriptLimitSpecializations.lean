module

public import LeanMath.CommodityClassification.PrecisionDecisionTable

/-! Explicit use of the proved CES parameter limit for the manuscript's demand index. -/
@[expose] public section
noncomputable section
namespace CommodityClassification.DemandNest.Data
open Filter
open scoped Topology BigOperators
variable {n : ℕ} (d : DemandNest.Data n)

theorem expenditure_parameter_continuity {r : Vec n} (hr : CESCost.PositivePrices n r) :
    ContinuousAt (fun eta => d.expenditureData.cost eta r) 1 :=
  d.expenditureData.cost_parameter_continuousAt_one hr

theorem expenditure_geometric_parameter_limit {r : Vec n} (hr : CESCost.PositivePrices n r) :
    Tendsto (fun eta => d.expenditureData.ces eta r) (𝓝[≠] (1:ℝ))
      (𝓝 (∏i,(r i/d.p i)^(d.share i))) := by
  have h := d.expenditureData.ces_tendsto_cobb hr
  rw [d.expenditureData.cobb_eq_product hr] at h
  simp only [d.expenditure_share] at h
  simpa only [expenditureData,CESCost.Data.ratio,one_mul] using h

end CommodityClassification.DemandNest.Data
