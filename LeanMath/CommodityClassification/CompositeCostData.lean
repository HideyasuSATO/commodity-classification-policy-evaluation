module

public import LeanMath.CommodityClassification.NestedEquilibriumInformation

/-! Actual CES product costs inside a fixed demand composite. -/
@[expose] public section
noncomputable section
set_option maxHeartbeats 600000
namespace CommodityClassification.Composite
open Matrix InputCoordinates
open scoped BigOperators

structure Data (n f : ℕ) where
  nest : DemandNest.Data n
  A : Mat n f
  w0 : Vec f
  sigma : ℝ
  hA : Positive A
  hw : ∀j,0<w0 j
  hcost : A *ᵥ w0=nest.p
  hsigma : 0<sigma

namespace Data
variable {n f : ℕ} (e : Data n f)

def costData (i : Fin n) : CESCost.Data f :=
  CESCost.ofInputs e.A e.nest.p e.w0 e.hA e.nest.hp e.hw e.hcost i

def costs (w : Vec f) : Vec n := fun i => (e.costData i).cost e.sigma w
def compositeCost (w : Vec f) : ℝ := e.nest.expenditureIndex (e.costs w)
def compositeMix (w : Vec f) : Vec n := e.nest.unitBundle (e.costs w)
def costDerivative : Vec f →L[ℝ] Vec n :=
  ContinuousLinearMap.pi (fun i => CESCost.weightedLinear (e.A i))
def meanInputs : Vec f := e.A.transpose *ᵥ (fun i => e.nest.q i/e.nest.sales)

theorem costs_positive {w : Vec f} (hw : ∀j,0<w j) : ∀i,0<e.costs w i :=
  fun i => (e.costData i).cost_pos e.sigma hw

theorem costs_benchmark : e.costs e.w0=e.nest.p := by
  funext i
  exact (e.costData i).cost_benchmark e.sigma

theorem costs_smooth {w : Vec f} (hw : ∀j,0<w j) : ContDiffAt ℝ ⊤ e.costs w :=
  contDiffAt_pi.mpr (fun i => (e.costData i).cost_contDiffAt e.sigma hw)

theorem costDerivative_apply (v : Vec f) : e.costDerivative v=e.A *ᵥ v := by
  funext i
  exact CESCost.weightedLinear_apply (e.A i) v

theorem costs_derivative : HasFDerivAt e.costs e.costDerivative e.w0 :=
  hasFDerivAt_pi.mpr (fun i => (e.costData i).hasFDerivAt_cost_benchmark e.sigma)

theorem meanInputs_positive (j : Fin f) : 0<e.meanInputs j := by
  change 0<∑i,e.A i j*(e.nest.q i/e.nest.sales)
  apply Finset.sum_pos
  · intro i _
    exact mul_pos (e.hA i j) (div_pos (e.nest.hq i) e.nest.sales_pos)
  · exact ⟨⟨0,e.nest.nonempty⟩,Finset.mem_univ _⟩

theorem meanInputs_apply (v : Vec f) :
    dotProduct e.meanInputs v=dotProduct (fun i => e.nest.q i/e.nest.sales) (e.A *ᵥ v) := by
  unfold meanInputs
  rw [dotProduct_comm,Matrix.dotProduct_transpose_mulVec]

theorem meanInputs_calibrated : dotProduct e.meanInputs e.w0=1 := by
  rw [e.meanInputs_apply,e.hcost]
  exact e.nest.expenditureData.cost_identity

theorem meanInputs_total : e.meanInputs=e.nest.sales⁻¹ • (e.A.transpose *ᵥ e.nest.q) := by
  unfold meanInputs
  rw [←Matrix.mulVec_smul]
  congr 1
  funext i
  simp only [Pi.smul_apply,smul_eq_mul,div_eq_mul_inv,mul_comm]

def meanCostData : CESCost.Data f where
  p := 1
  w0 := e.w0
  a := e.meanInputs
  p_pos := zero_lt_one
  w0_pos := e.hw
  a_pos := e.meanInputs_positive
  cost_identity := e.meanInputs_calibrated

end Data
end CommodityClassification.Composite
