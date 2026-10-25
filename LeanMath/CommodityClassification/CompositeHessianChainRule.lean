module

public import LeanMath.CommodityClassification.CompositeCurrentDerivative

/-! The actual second derivative, obtained by differentiating the current gradient. -/
@[expose] public section
noncomputable section
set_option maxHeartbeats 800000
namespace CommodityClassification.Composite.Data
open Matrix InputCoordinates Filter
open scoped BigOperators Topology
variable {n f : ℕ} (e : Composite.Data n f)

def compositeHessianRow (j : Fin f) : Vec f →L[ℝ] ℝ :=
  ∑i,((e.nest.q i/e.nest.sales) • (e.costData i).hessianRow e.sigma j+
    (e.A i j) • ((e.nest.expenditureData.hessianRow e.nest.eta i).comp e.costDerivative))

def compositeHessian : Mat f f :=
  e.A.transpose*e.nest.expenditureData.hessian e.nest.eta*e.A+
    ∑i,(e.nest.q i/e.nest.sales) • (e.costData i).hessian e.sigma

theorem composite_partial_derivative (j : Fin f) :
    HasFDerivAt (CESCost.pricePartial e.compositeCost j) (e.compositeHessianRow j) e.w0 := by
  have ha (i : Fin n) : HasFDerivAt (CESCost.pricePartial e.nest.expenditureIndex i)
      (e.nest.expenditureData.hessianRow e.nest.eta i) (e.costs e.w0) := by
    rw [e.costs_benchmark]
    exact e.nest.expenditureData.hasFDerivAt_cost_partial_benchmark e.nest.eta i
  have hi (i : Fin n) := ((ha i).comp e.w0 e.costs_derivative).mul
    ((e.costData i).hasFDerivAt_cost_partial_benchmark e.sigma j)
  have hh := HasFDerivAt.fun_sum (u := Finset.univ) (fun i _ => hi i)
  have hg (i : Fin n) : CESCost.pricePartial ((e.costData i).cost e.sigma) j e.w0=e.A i j :=
    (e.costData i).cost_gradient e.sigma j
  simp only [Function.comp_def,Pi.mul_apply,e.costs_benchmark,e.nest.expenditure_gradient,
    hg] at hh
  have hs : HasFDerivAt (fun w => ∑i,CESCost.pricePartial e.nest.expenditureIndex i (e.costs w)*
      CESCost.pricePartial ((e.costData i).cost e.sigma) j w) (e.compositeHessianRow j) e.w0 := hh
  apply hs.congr_of_eventuallyEq
  filter_upwards [CESCost.positivePrices_open.mem_nhds e.hw] with w hw
  exact e.compositeCost_current_partial hw j

theorem compositeHessianRow_apply (j : Fin f) (v : Vec f) :
    e.compositeHessianRow j v=(e.compositeHessian *ᵥ v) j := by
  simp only [compositeHessianRow,compositeHessian,_root_.sum_apply,_root_.add_apply,
    _root_.smul_apply,ContinuousLinearMap.comp_apply,Equilibrium.hessianRow_apply,
    e.costDerivative_apply,smul_eq_mul,Matrix.add_mulVec,Matrix.sum_mulVec,
    Matrix.smul_mulVec,Pi.add_apply,Finset.sum_apply,Pi.smul_apply]
  rw [Finset.sum_add_distrib,←Matrix.mulVec_mulVec,←Matrix.mulVec_mulVec]
  change (∑i,_) + (∑i,e.A i j*(e.nest.expenditureData.hessian e.nest.eta *ᵥ (e.A *ᵥ v)) i)=
    (∑i,e.A i j*(e.nest.expenditureData.hessian e.nest.eta *ᵥ (e.A *ᵥ v)) i)+(∑i,_)
  exact add_comm _ _

theorem compositeCost_actual_hessian :
    (fun j l => CESCost.pricePartial (CESCost.pricePartial e.compositeCost j) l e.w0)=
      e.compositeHessian := by
  ext j l
  rw [CESCost.pricePartial,(e.composite_partial_derivative j).fderiv,e.compositeHessianRow_apply]
  simp only [Matrix.mulVec_single_one]
  rfl

end CommodityClassification.Composite.Data
