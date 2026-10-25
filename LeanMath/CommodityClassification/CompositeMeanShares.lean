module

public import LeanMath.CommodityClassification.CompositeEconomicCurvature

/-! The averaged factor shares of the actual composite technology. -/
@[expose] public section
noncomputable section
set_option maxHeartbeats 800000
namespace CommodityClassification.Composite.Data
open Matrix InputCoordinates
open scoped BigOperators
variable {n f : ℕ} (e : Composite.Data n f)

theorem meanCostData_share_total (j : Fin f) :
    e.meanCostData.share j=e.w0 j*Supply.totalInputs e.nest.q e.A j/e.nest.sales := by
  change e.w0 j*e.meanInputs j/1=_
  rw [e.meanInputs_total]
  simp only [div_one,Pi.smul_apply,smul_eq_mul,Matrix.mulVec,Matrix.transpose_apply,dotProduct,
    Supply.totalInputs]
  simp_rw [mul_comm (e.A _ j)]
  ring

theorem meanCostData_share_average (j : Fin f) :
    e.meanCostData.share j=∑i,e.nest.share i*(e.costData i).share j := by
  rw [e.meanCostData_share_total]
  change e.w0 j*(∑i,e.nest.q i*e.A i j)/e.nest.sales=
    ∑i,(e.nest.p i*e.nest.q i/e.nest.sales)*(e.w0 j*e.A i j/e.nest.p i)
  rw [Finset.mul_sum,Finset.sum_div]
  apply Finset.sum_congr rfl
  intro i _
  field_simp [(e.nest.hp i).ne',e.nest.sales_pos.ne']

theorem meanCostData_powerSum (s : ℝ) (w : Vec f) :
    e.meanCostData.powerSum s w=∑i,e.nest.share i*(e.costData i).powerSum s w := by
  simp only [CESCost.Data.powerSum,e.meanCostData_share_average,Finset.sum_mul,Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  change (e.nest.share i*(e.costData i).share j)*(w j/e.w0 j)^(1-s)=
    e.nest.share i*((e.costData i).share j*(w j/e.w0 j)^(1-s))
  ring

theorem meanCostData_logSum (w : Vec f) :
    e.meanCostData.logSum w=∑i,e.nest.share i*(e.costData i).logSum w := by
  simp only [CESCost.Data.logSum,e.meanCostData_share_average,Finset.sum_mul,Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  change (e.nest.share i*(e.costData i).share j)*Real.log (w j/e.w0 j)=
    e.nest.share i*((e.costData i).share j*Real.log (w j/e.w0 j))
  ring

end CommodityClassification.Composite.Data
