module
public import LeanMath.CommodityClassification.EquilibriumConsistency
public import Mathlib.Analysis.Calculus.ImplicitContDiff
@[expose] public section
set_option maxHeartbeats 2000000
namespace CommodityClassification.Equilibrium
open Matrix Filter
open scoped BigOperators Topology ContDiff
variable {n k : ℕ}
namespace Model
variable (E : Model n k)

/-- Additional local C1 regularity, separate from the point derivative in Model. -/
def DemandC1 : Prop := ContDiffAt ℝ 1 E.demand E.p

theorem demandC1_of_open {U : Set (Vec n)} (hU : IsOpen U) (hpU : E.p ∈ U)
    (h : ContDiffOn ℝ 1 E.demand U) : E.DemandC1 :=
  (h E.p hpU).contDiffAt (hU.mem_nhds hpU)

theorem currentPrice_contDiff : ContDiff ℝ ⊤ E.currentPrice := by
  change ContDiff ℝ ⊤ (fun u => E.frame.w + E.frame.V *ᵥ u)
  simpa only [matCLM_apply] using
    (contDiff_const (c := E.frame.w)).add (matCLM E.frame.V).contDiff

theorem costs_contDiffAt {w : Vec (k+1)} (hw : w ∈ CESCost.PositivePrices (k+1)) :
    ContDiffAt ℝ ⊤ E.costs w := by
  apply contDiffAt_pi.mpr
  intro i
  exact (E.costData i).cost_contDiffAt E.sigma hw

theorem currentInputs_contDiffAt {w : Vec (k+1)} (hw : w ∈ CESCost.PositivePrices (k+1))
    (i : Fin n) (j : Fin (k+1)) :
    ContDiffAt ℝ 1 (fun w => E.currentInputs w i j) w := by
  exact ((E.costData i).cost_contDiffAt E.sigma hw).fderiv_right (by simp) |>.clm_apply contDiffAt_const

theorem prices_contDiffAt : ContDiffAt ℝ 1 E.prices 0 := by
  have hc : ContDiffAt ℝ 1 E.costs (E.currentPrice 0) := by
    rw [E.currentPrice_zero]
    exact (E.costs_contDiffAt E.hw).of_le (by simp)
  have hw : ContDiffAt ℝ 1 (fun y : PolicyPrice k => E.currentPrice y.2) 0 :=
    ((E.currentPrice_contDiff.of_le (by simp : (1 : ℕ∞ω) ≤ ⊤)).contDiffAt.comp 0 contDiffAt_snd)
  exact (hc.comp (f := fun y : PolicyPrice k => E.currentPrice y.2) (0 : PolicyPrice k) hw).add
    (contDiffAt_fst.smul contDiffAt_const)

theorem quantities_contDiffAt (h : E.DemandC1) : ContDiffAt ℝ 1 E.quantities 0 := by
  have hd : ContDiffAt ℝ 1 E.demand (E.prices 0) := by rw [E.prices_zero]; exact h
  exact hd.comp 0 E.prices_contDiffAt

theorem factorDemand_contDiffAt (h : E.DemandC1) : ContDiffAt ℝ 1 E.factorDemand 0 := by
  have ha (i : Fin n) (j : Fin (k+1)) :
      ContDiffAt ℝ 1 (fun y : PolicyPrice k => E.currentInputs (E.currentPrice y.2) i j) 0 := by
    have hh : ContDiffAt ℝ 1 (fun w => E.currentInputs w i j) (E.currentPrice 0) := by
      rw [E.currentPrice_zero]
      exact E.currentInputs_contDiffAt E.hw i j
    exact hh.comp (f := fun y : PolicyPrice k => E.currentPrice y.2) (0 : PolicyPrice k)
      ((E.currentPrice_contDiff.of_le (by simp : (1 : ℕ∞ω) ≤ ⊤)).contDiffAt.comp (0 : PolicyPrice k) contDiffAt_snd)
  apply contDiffAt_pi.mpr
  intro j
  change ContDiffAt ℝ 1 (fun y => ∑ i, E.currentInputs (E.currentPrice y.2) i j * E.quantities y i) 0
  apply ContDiffAt.sum
  intro i _
  exact (ha i j).mul (contDiffAt_pi.mp (E.quantities_contDiffAt h) i)

theorem reduced_contDiffAt (h : E.DemandC1) (abar : Vec (k+1)) :
    ContDiffAt ℝ 1 (E.reduced abar) 0 := by
  change ContDiffAt ℝ 1 (fun y => E.frame.V.transpose *ᵥ (E.factorDemand y - abar)) 0
  simpa only [Function.comp_def, matCLM_apply] using
    (matCLM E.frame.V.transpose).contDiff.contDiffAt.comp 0
      ((E.factorDemand_contDiffAt h).sub (contDiffAt_const (c := abar)))

theorem price_partial_eq (abar : Vec (k+1)) :
    fderiv ℝ (E.reduced abar) 0 ∘L ContinuousLinearMap.inr ℝ ℝ (Vec k) = -matCLM E.K := by
  apply ContinuousLinearMap.ext
  intro u
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.inr_apply,
    E.reduced_derivative_apply, neg_zero, zero_smul, zero_sub, _root_.neg_apply, matCLM_apply]

theorem price_partial_invertible (abar : Vec (k+1)) (hK : E.K.PosDef) :
    (fderiv ℝ (E.reduced abar) 0 ∘L ContinuousLinearMap.inr ℝ ℝ (Vec k)).IsInvertible := by
  rw [E.price_partial_eq]
  apply ContinuousLinearMap.IsInvertible.of_inverse (g := -matCLM E.K⁻¹)
  · apply ContinuousLinearMap.ext
    intro u
    simp only [ContinuousLinearMap.comp_apply, _root_.neg_apply, matCLM_apply,
      Matrix.mulVec_neg, neg_neg, ContinuousLinearMap.id_apply, Matrix.mulVec_mulVec]
    rw [(Regularity.inverse_identities E.K hK).2.1, Matrix.one_mulVec]
  · apply ContinuousLinearMap.ext
    intro u
    simp only [ContinuousLinearMap.comp_apply, _root_.neg_apply, matCLM_apply,
      Matrix.mulVec_neg, neg_neg, ContinuousLinearMap.id_apply, Matrix.mulVec_mulVec]
    rw [(Regularity.inverse_identities E.K hK).2.2, Matrix.one_mulVec]
end Model
end CommodityClassification.Equilibrium
