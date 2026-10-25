module

public import LeanMath.CommodityClassification.CompositeMeanShares

/-! Exact CES and Cobb-Douglas composition on the full positive price domain. -/
@[expose] public section
noncomputable section
set_option maxHeartbeats 1000000
namespace CommodityClassification.CESCost.Data
open Matrix
open scoped BigOperators
variable {f : ℕ} (d : CESCost.Data f)

theorem cost_eq_of_primitives (d' : CESCost.Data f) (hp : d.p=d'.p)
    (hw : d.w0=d'.w0) (ha : d.a=d'.a) (s : ℝ) (w : Vec f) :
    d.cost s w=d'.cost s w := by
  simp only [CESCost.Data.cost,CESCost.Data.cobb,CESCost.Data.ces,CESCost.Data.powerSum,
    CESCost.Data.logSum,CESCost.Data.share,CESCost.Data.ratio,hp,hw,ha]

theorem cost_normalized_power {s : ℝ} (hs : s≠1) {w : Vec f} (hw : ∀j,0<w j) :
    (d.cost s w/d.p)^(1-s)=d.powerSum s w := by
  rw [d.cost_eq_ces hs,CESCost.Data.ces]
  have he : d.p*d.powerSum s w^(1/(1-s))/d.p=d.powerSum s w^(1/(1-s)) := by
    field_simp [d.p_pos.ne']
  rw [he,←Real.rpow_mul (d.powerSum_pos s hw).le]
  have ht : 1-s≠0 := sub_ne_zero.mpr hs.symm
  rw [show (1/(1-s))*(1-s)=1 by field_simp,Real.rpow_one]

theorem cost_normalized_log {s : ℝ} (hs : s=1) (w : Vec f) :
    Real.log (d.cost s w/d.p)=d.logSum w := by
  rw [d.cost_eq_cobb hs,CESCost.Data.cobb]
  have he : d.p*Real.exp (d.logSum w)/d.p=Real.exp (d.logSum w) := by
    field_simp [d.p_pos.ne']
  rw [he,Real.log_exp]

end CommodityClassification.CESCost.Data

namespace CommodityClassification.Composite.Data
open Matrix InputCoordinates
open scoped BigOperators
variable {n f : ℕ} (e : Composite.Data n f)

theorem compositeCost_matched_ces (hmatch : e.nest.eta=e.sigma) (hs : e.sigma≠1)
    {w : Vec f} (hw : ∀j,0<w j) :
    e.compositeCost w=e.meanCostData.ces e.sigma w := by
  have hη : e.nest.eta≠1 := hmatch ▸ hs
  rw [compositeCost,e.nest.expenditure_ces hη,hmatch]
  have hi (i : Fin n) : (e.costs w i/e.nest.p i)^(1-e.sigma)=(e.costData i).powerSum e.sigma w :=
    (e.costData i).cost_normalized_power hs hw
  simp_rw [hi]
  rw [←e.meanCostData_powerSum]
  change _=1*_
  rw [one_mul]

theorem compositeCost_matched_cobb (hmatch : e.nest.eta=e.sigma) (hs : e.sigma=1)
    (w : Vec f) : e.compositeCost w=e.meanCostData.cobb w := by
  have hη : e.nest.eta=1 := hmatch.trans hs
  rw [compositeCost,DemandNest.Data.expenditureIndex,e.nest.expenditureData.cost_eq_cobb hη]
  change 1*Real.exp (∑i,e.nest.expenditureData.share i*
    Real.log (e.costs w i/e.nest.p i))=1*Real.exp (e.meanCostData.logSum w)
  simp only [e.nest.expenditure_share]
  have hi (i : Fin n) : Real.log (e.costs w i/e.nest.p i)=(e.costData i).logSum w :=
    (e.costData i).cost_normalized_log hs w
  simp_rw [hi]
  rw [e.meanCostData_logSum]

theorem compositeCost_matched (hmatch : e.nest.eta=e.sigma)
    {w : Vec f} (hw : ∀j,0<w j) :
    e.compositeCost w=e.meanCostData.cost e.sigma w := by
  by_cases hs : e.sigma=1
  · rw [e.meanCostData.cost_eq_cobb hs]
    exact e.compositeCost_matched_cobb hmatch hs w
  · rw [e.meanCostData.cost_eq_ces hs]
    exact e.compositeCost_matched_ces hmatch hs hw

end CommodityClassification.Composite.Data
