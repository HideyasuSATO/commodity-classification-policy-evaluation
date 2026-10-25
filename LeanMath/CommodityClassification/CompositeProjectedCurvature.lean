module

public import LeanMath.CommodityClassification.CompositeHessianChainRule

/-! Actual projected composite curvature, retaining both sources of substitution. -/
@[expose] public section
noncomputable section
set_option maxHeartbeats 1200000
namespace CommodityClassification.Composite.Data
open Matrix InputCoordinates
open scoped BigOperators
variable {n f k : ℕ} (e : Composite.Data n f)

def relativeMoment (V : Mat f k) : Vec k := (e.A*V).transpose *ᵥ e.nest.q

def relativeCovariance (V : Mat f k) : Mat k k :=
  (e.A*V).transpose * Supply.curvature e.nest.q e.nest.p e.nest.sales * (e.A*V)

def relativeR (V : Mat f k) : Mat k k :=
  Supply.knownR e.w0 V (Supply.totalInputs e.nest.q e.A)

theorem relativeCovariance_moments (V : Mat f k) :
    e.relativeCovariance V=(e.A*V).transpose * Supply.xi e.nest.p e.nest.q * (e.A*V)-
      e.nest.sales⁻¹ • vecMulVec (e.relativeMoment V) (e.relativeMoment V) := by
  have hv : e.nest.q ᵥ* (e.A*V)=(e.A*V).transpose *ᵥ e.nest.q := by
    funext l
    simp only [Matrix.vecMul,Matrix.mulVec,Matrix.transpose_apply,dotProduct,mul_comm]
  rw [relativeCovariance,Supply.curvature,Matrix.mul_sub,Matrix.sub_mul,
    Matrix.mul_smul,Matrix.smul_mul,Matrix.mul_vecMulVec,Matrix.vecMulVec_mul,hv]
  rfl

theorem compositeHessian_projected_split (V : Mat f k) :
    (-e.nest.sales) • (V.transpose*e.compositeHessian*V)=
      e.sigma • (e.relativeR V-(e.A*V).transpose*Supply.xi e.nest.p e.nest.q*(e.A*V))+
      e.nest.eta • e.relativeCovariance V := by
  have hP : e.nest.expenditureData.hessian e.nest.eta=
      (-e.nest.eta/e.nest.sales) • Supply.curvature e.nest.q e.nest.p e.nest.sales := by
    simpa only [Supply.curvature,Supply.xi,one_div] using e.nest.expenditure_hessian_formula
  have hs : (-e.nest.sales)*(-e.nest.eta/e.nest.sales)=e.nest.eta := by
    field_simp [e.nest.sales_pos.ne']
  have hp : (-e.nest.sales) • (V.transpose*(e.A.transpose*e.nest.expenditureData.hessian e.nest.eta*e.A)*V)=
      e.nest.eta • e.relativeCovariance V := by
    rw [hP]
    simp only [Matrix.mul_smul,Matrix.smul_mul,smul_smul,hs,relativeCovariance,
      Matrix.transpose_mul,Matrix.mul_assoc]
  have hh : (-e.nest.sales) •
      (V.transpose*(∑i,(e.nest.q i/e.nest.sales) • (e.costData i).hessian e.sigma)*V)=
      -(∑i,e.nest.q i • (V.transpose*(e.costData i).hessian e.sigma*V)) := by
    simp only [Matrix.mul_sum,Matrix.sum_mul,Matrix.mul_smul,Matrix.smul_mul,
      Finset.smul_sum,←Finset.sum_neg_distrib,smul_smul,←neg_smul]
    apply Finset.sum_congr rfl
    intro i _
    congr 1
    field_simp [e.nest.sales_pos.ne']
  have ha := Supply.aggregate_negative_hessian e.A e.nest.p e.nest.q e.w0 V
    e.hA e.nest.hp e.hw e.hcost e.sigma
  change -(∑i,e.nest.q i • (V.transpose*(e.costData i).hessian e.sigma*V))=
    e.sigma • (e.relativeR V-(e.A*V).transpose*Supply.xi e.nest.p e.nest.q*(e.A*V)) at ha
  rw [compositeHessian,Matrix.mul_add,Matrix.add_mul,smul_add,hp,hh,ha]
  exact add_comm _ _

theorem compositeHessian_projected_covariance (V : Mat f k) :
    (-e.nest.sales) • (V.transpose*e.compositeHessian*V)=
      e.sigma • (e.relativeR V-e.nest.sales⁻¹ • vecMulVec (e.relativeMoment V) (e.relativeMoment V))+
      (e.nest.eta-e.sigma) • e.relativeCovariance V := by
  rw [e.compositeHessian_projected_split,e.relativeCovariance_moments]
  ext l m
  simp only [Matrix.add_apply,Matrix.sub_apply,Matrix.smul_apply,smul_eq_mul]
  ring

theorem compositeCost_actual_projected_curvature (V : Mat f k) :
    (-e.nest.sales) • (V.transpose*
      Matrix.of (fun j l => CESCost.pricePartial (CESCost.pricePartial e.compositeCost j) l e.w0)*V)=
      e.sigma • (e.relativeR V-e.nest.sales⁻¹ • vecMulVec (e.relativeMoment V) (e.relativeMoment V))+
      (e.nest.eta-e.sigma) • e.relativeCovariance V := by
  have hh : Matrix.of (fun j l => CESCost.pricePartial
      (CESCost.pricePartial e.compositeCost j) l e.w0)=e.compositeHessian := e.compositeCost_actual_hessian
  rw [hh]
  exact e.compositeHessian_projected_covariance V

end CommodityClassification.Composite.Data
