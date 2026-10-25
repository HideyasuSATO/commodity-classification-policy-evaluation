module

public import LeanMath.CommodityClassification.NestData

/-! Genuine derivatives of the calibrated nest functions, including elasticity one. -/
@[expose] public section
noncomputable section
set_option maxHeartbeats 2400000
namespace CommodityClassification.DemandNest.Data
open Matrix
variable {n : ℕ} (d : DemandNest.Data n)

theorem quantity_benchmark : d.quantityIndex d.q=d.sales :=
  d.quantityData.cost_benchmark (1/d.eta)

theorem expenditure_benchmark : d.expenditureIndex d.p=1 :=
  d.expenditureData.cost_benchmark d.eta

theorem quantity_smooth {x : Vec n} (hx : ∀i,0<x i) :
    ContDiffAt ℝ ⊤ d.quantityIndex x := d.quantityData.cost_contDiffAt (1/d.eta) hx

theorem expenditure_smooth {r : Vec n} (hr : ∀i,0<r i) :
    ContDiffAt ℝ ⊤ d.expenditureIndex r := d.expenditureData.cost_contDiffAt d.eta hr

theorem quantity_derivative : HasFDerivAt d.quantityIndex (CESCost.weightedLinear d.p) d.q :=
  d.quantityData.hasFDerivAt_cost_benchmark (1/d.eta)

theorem expenditure_derivative :
    HasFDerivAt d.expenditureIndex (CESCost.weightedLinear (fun i => d.q i/d.sales)) d.p :=
  d.expenditureData.hasFDerivAt_cost_benchmark d.eta

theorem quantity_gradient (i : Fin n) : CESCost.pricePartial d.quantityIndex i d.q=d.p i :=
  d.quantityData.cost_gradient (1/d.eta) i

theorem expenditure_gradient (i : Fin n) :
    CESCost.pricePartial d.expenditureIndex i d.p=d.q i/d.sales :=
  d.expenditureData.cost_gradient d.eta i

theorem expenditure_hessian_formula :
    d.expenditureData.hessian d.eta=(-d.eta/d.sales) •
      (Supply.xi d.p d.q-(1/d.sales) • vecMulVec d.q d.q) := by
  ext i j
  by_cases hij : i=j
  · subst j
    simp [CESCost.Data.hessian,expenditureData,Supply.xi,Matrix.diagonal,vecMulVec,
      Matrix.smul_apply]
    field_simp [ne_of_gt d.sales_pos,ne_of_gt (d.hp i)]
    ring
  · simp [CESCost.Data.hessian,expenditureData,Supply.xi,Matrix.diagonal,vecMulVec,
      Matrix.smul_apply,hij]
    ring

theorem expenditure_actual_hessian :
    (fun i j => CESCost.pricePartial (CESCost.pricePartial d.expenditureIndex i) j d.p)=
      (-d.eta/d.sales) • (Supply.xi d.p d.q-(1/d.sales) • vecMulVec d.q d.q) := by
  rw [←d.expenditure_hessian_formula]
  ext i j
  exact d.expenditureData.cost_mixed_derivative d.eta i j

theorem expenditure_directional_hessian (u v : Vec n) :
    fderiv ℝ (fun r => fderiv ℝ d.expenditureIndex r v) d.p u=
      d.eta*((dotProduct (fun i => d.q i/d.sales) u)*
        (dotProduct (fun i => d.q i/d.sales) v)-
          ∑i,(d.q i/d.sales/d.p i)*u i*v i) := by
  simpa only [expenditureIndex,expenditureData,div_one] using
    d.expenditureData.cost_second_derivative d.eta u v

end CommodityClassification.DemandNest.Data
