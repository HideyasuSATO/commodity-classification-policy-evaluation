module
public import LeanMath.CommodityClassification.EquilibriumDefinitions
@[expose] public section
set_option maxHeartbeats 2000000
namespace CommodityClassification.Equilibrium
open Matrix Filter
open scoped BigOperators Topology
variable {n k : ℕ}

theorem hessianRow_apply {f : ℕ} (d : CESCost.Data f) (σ : ℝ) (j : Fin f) (v : Vec f) :
    d.hessianRow σ j v = (d.hessian σ *ᵥ v) j := by
  have hh := CESCost.clm_apply_eq_sum (d.hessianRow σ j) v
  rw [hh]
  apply Finset.sum_congr rfl
  intro l hl
  have hs : d.hessianRow σ j (Pi.single l 1) = d.hessian σ j l := by
    simpa only [CESCost.pricePartial, (d.hasFDerivAt_cost_partial_benchmark σ j).fderiv] using
      d.cost_mixed_derivative σ j l
  rw [hs, mul_comm]

namespace Model
variable (E : Model n k)
theorem currentPrice_hasFDerivAt (u : Vec k) :
    HasFDerivAt E.currentPrice (matCLM E.frame.V) u := by
  change HasFDerivAt (fun u => E.frame.w + E.frame.V *ᵥ u) _ _
  simpa only [matCLM_apply] using (matCLM E.frame.V).hasFDerivAt.const_add E.frame.w

theorem costs_hasFDerivAt : HasFDerivAt E.costs (matCLM E.A) E.frame.w := by
  apply hasFDerivAt_pi.mpr
  intro i
  exact (E.costData i).hasFDerivAt_cost_benchmark E.sigma

theorem currentInputs_hasFDerivAt (i : Fin n) (j : Fin (k+1)) :
    HasFDerivAt (fun w => E.currentInputs w i j) ((E.costData i).hessianRow E.sigma j) E.frame.w :=
  (E.costData i).hasFDerivAt_cost_partial_benchmark E.sigma j

theorem prices_hasFDerivAt : HasFDerivAt E.prices E.priceChange 0 := by
  have hw := (E.currentPrice_hasFDerivAt 0).comp (0 : PolicyPrice k) (coordCLM k).hasFDerivAt
  have hg : HasFDerivAt E.costs (matCLM E.A) (E.currentPrice ((coordCLM k) 0)) := by
    simp only [map_zero, E.currentPrice_zero]
    exact E.costs_hasFDerivAt
  have hg' := hg.comp (0 : PolicyPrice k) hw
  have hb : HasFDerivAt (fun y : PolicyPrice k => y.1 • E.b)
      (ContinuousLinearMap.pi (fun i => E.b i • taxCLM k)) 0 := by
    apply hasFDerivAt_pi.mpr
    intro i
    simpa [smul_eq_mul, mul_comm] using (taxCLM k).hasFDerivAt.const_mul (E.b i)
  apply (hg'.add hb).congr_fderiv
  apply ContinuousLinearMap.ext
  intro y
  simp only [_root_.add_apply, ContinuousLinearMap.comp_apply, matCLM_apply, coordCLM_apply, priceChange]
  rw [Matrix.mulVec_mulVec, A, E.frame.reconstruct_exposure]

theorem quantities_hasFDerivAt : HasFDerivAt E.quantities E.quantityChange 0 := by
  have hd : HasFDerivAt E.demand (-matCLM E.D) (E.prices 0) := by
    rw [E.prices_zero]
    exact E.demand_deriv
  exact hd.comp (0 : PolicyPrice k) E.prices_hasFDerivAt

theorem factorDemand_hasFDerivAt : HasFDerivAt E.factorDemand E.factorChange 0 := by
  apply hasFDerivAt_pi'.mpr
  intro j
  have hw := (E.currentPrice_hasFDerivAt 0).comp (0 : PolicyPrice k) (coordCLM k).hasFDerivAt
  have hin (i : Fin n) : HasFDerivAt (fun y : PolicyPrice k => E.currentInputs (E.currentPrice y.2) i j)
      (((E.costData i).hessianRow E.sigma j).comp ((matCLM E.frame.V).comp (coordCLM k))) 0 := by
    have hi : HasFDerivAt (fun w => E.currentInputs w i j) ((E.costData i).hessianRow E.sigma j)
        (E.currentPrice ((coordCLM k) 0)) := by
      simp only [map_zero, E.currentPrice_zero]
      exact E.currentInputs_hasFDerivAt i j
    exact hi.comp (0 : PolicyPrice k) hw
  have hq (i : Fin n) := hasFDerivAt_pi'.mp E.quantities_hasFDerivAt i
  have hh := HasFDerivAt.fun_sum (u := Finset.univ) (fun i _ => (hin i).mul (hq i))
  apply hh.congr_fderiv
  apply ContinuousLinearMap.ext
  intro y
  change _ = (E.factorChange y) j
  symm
  simp only [E.factorChange_apply, Pi.add_apply, Matrix.mulVec, dotProduct, Matrix.transpose_apply,
      _root_.sum_apply, _root_.add_apply, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.proj_apply, _root_.smul_apply, smul_eq_mul,
      Prod.snd_zero, E.currentPrice_zero, E.inputs_base, E.quantities_zero, matCLM_apply, coordCLM_apply,
      hessianRow_apply]
  simp only [aggregateHessian, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul]
  change (∑ i, E.A i j * E.quantityChange y i) +
      (∑ l, (∑ i, E.q i * E.hessian i j l) * (E.frame.V *ᵥ y.2) l) = _
  simp only [Finset.sum_mul, Finset.sum_add_distrib]
  rw [Finset.sum_comm]
  simp only [mul_assoc, ← Finset.mul_sum]
  rfl

theorem excess_hasFDerivAt (abar : Vec (k+1)) (s0 : ℝ) :
    HasFDerivAt (E.excess abar) E.excessChange (0,s0) := by
  have hf := E.factorDemand_hasFDerivAt.comp (0,s0)
    (ContinuousLinearMap.fst ℝ (PolicyPrice k) ℝ).hasFDerivAt
  have hs : HasFDerivAt (fun ys : PolicyPrice k × ℝ => ys.2 • E.frame.a0)
      (ContinuousLinearMap.pi (fun j => E.frame.a0 j • ContinuousLinearMap.snd ℝ (PolicyPrice k) ℝ)) (0,s0) := by
    apply hasFDerivAt_pi.mpr
    intro j
    simpa [smul_eq_mul, mul_comm] using
      (ContinuousLinearMap.snd ℝ (PolicyPrice k) ℝ).hasFDerivAt.const_mul (E.frame.a0 j)
  exact (hf.add hs).sub_const abar

theorem reduced_hasFDerivAt (abar : Vec (k+1)) :
    HasFDerivAt (E.reduced abar) ((matCLM E.frame.V.transpose).comp E.factorChange) 0 := by
  change HasFDerivAt (fun y => E.frame.V.transpose *ᵥ (E.factorDemand y - abar)) _ _
  simpa only [Function.comp_def, matCLM_apply] using
    (matCLM E.frame.V.transpose).hasFDerivAt.comp 0 (E.factorDemand_hasFDerivAt.sub_const abar)
end Model
end CommodityClassification.Equilibrium
