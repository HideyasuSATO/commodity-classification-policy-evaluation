module

public import LeanMath.CommodityClassification.CompositeMatchedCost

/-! Exact matched composite costs are determined by physical group input reports. -/
@[expose] public section
noncomputable section
set_option maxHeartbeats 1000000
namespace CommodityClassification.Equilibrium.BenchmarkFamily
open Matrix InputCoordinates
open scoped BigOperators
variable {n k h g : ℕ} (F : BenchmarkFamily n k h)

theorem nestProduction_meanShare (G : Partition n g) (η : Vec g) (hη : ∀a,0<η a)
    (C : F.Candidate) (a : Fin g) (j : Fin (k+1)) :
    (F.nestProduction G η hη C a).meanCostData.share j=
      F.frame.w j*G.report F.q (F.model C).A a j/G.sales F.p F.q a := by
  rw [(F.nestProduction G η hη C a).meanCostData_share_total,F.nestProduction_totalInputs]
  have hs : (F.nestProduction G η hη C a).nest.sales=G.sales F.p F.q a :=
    (F.nestData G η hη).nest_sales a
  rw [hs]
  rfl

theorem nested_matched_composite_cost (G : Partition n g) (η : Vec g) (hη : ∀a,0<η a)
    (C : F.Candidate) (a : Fin g) (hmatch : η a=F.sigma)
    {w : Vec (k+1)} (hw : ∀j,0<w j) :
    (F.nestProduction G η hη C a).compositeCost w=
      (F.nestProduction G η hη C a).meanCostData.cost F.sigma w :=
  (F.nestProduction G η hη C a).compositeCost_matched hmatch hw

theorem nested_matched_ces_formula (G : Partition n g) (η : Vec g) (hη : ∀a,0<η a)
    (C : F.Candidate) (a : Fin g) (hmatch : η a=F.sigma) (hs : F.sigma≠1)
    {w : Vec (k+1)} (hw : ∀j,0<w j) :
    (F.nestProduction G η hη C a).compositeCost w=
      (∑j,(F.frame.w j*G.report F.q (F.model C).A a j/G.sales F.p F.q a)*
        (w j/F.frame.w j)^(1-F.sigma))^(1/(1-F.sigma)) := by
  rw [F.nested_matched_composite_cost G η hη C a hmatch hw,
    (F.nestProduction G η hη C a).meanCostData.cost_eq_ces hs,CESCost.Data.ces,
    CESCost.Data.powerSum]
  simp_rw [F.nestProduction_meanShare]
  change 1*_= _
  rw [one_mul]
  rfl

theorem nested_matched_cobb_formula (G : Partition n g) (η : Vec g) (hη : ∀a,0<η a)
    (C : F.Candidate) (a : Fin g) (hmatch : η a=F.sigma) (hs : F.sigma=1)
    {w : Vec (k+1)} (hw : ∀j,0<w j) :
    (F.nestProduction G η hη C a).compositeCost w=
      Real.exp (∑j,(F.frame.w j*G.report F.q (F.model C).A a j/G.sales F.p F.q a)*
        Real.log (w j/F.frame.w j)) := by
  rw [F.nested_matched_composite_cost G η hη C a hmatch hw,
    (F.nestProduction G η hη C a).meanCostData.cost_eq_cobb hs,CESCost.Data.cobb,
    CESCost.Data.logSum]
  simp_rw [F.nestProduction_meanShare]
  change 1*_= _
  rw [one_mul]
  rfl

theorem nested_matched_report_cost (G : Partition n g) (η : Vec g) (hη : ∀a,0<η a)
    (C E : F.Candidate) (a : Fin g) (hmatch : η a=F.sigma)
    (hreport : G.report F.q (F.model C).A a=G.report F.q (F.model E).A a)
    {w : Vec (k+1)} (hw : ∀j,0<w j) :
    (F.nestProduction G η hη C a).compositeCost w=
      (F.nestProduction G η hη E a).compositeCost w := by
  rw [F.nested_matched_composite_cost G η hη C a hmatch hw,
    F.nested_matched_composite_cost G η hη E a hmatch hw]
  refine (F.nestProduction G η hη C a).meanCostData.cost_eq_of_primitives
    (F.nestProduction G η hη E a).meanCostData rfl rfl ?_ F.sigma w
  change (F.nestProduction G η hη C a).meanInputs=(F.nestProduction G η hη E a).meanInputs
  rw [F.nestProduction_meanInputs,F.nestProduction_meanInputs,hreport]

end CommodityClassification.Equilibrium.BenchmarkFamily
