module
public import LeanMath.CommodityClassification.EquilibriumPathDerivative
public import LeanMath.CommodityClassification.SupplyBoundaryExample
@[expose] public section
set_option maxHeartbeats 2000000
namespace CommodityClassification.Equilibrium
open Matrix
open scoped BigOperators
variable {n k : ℕ}

noncomputable def affineDemand (p q : Vec n) (D : Mat n n) (v : Vec n) : Vec n := q - D *ᵥ (v-p)
theorem affineDemand_base (p q : Vec n) (D : Mat n n) : affineDemand p q D p = q := by
  simp [affineDemand]
theorem affineDemand_derivative (p q : Vec n) (D : Mat n n) :
    HasFDerivAt (affineDemand p q D) (-matCLM D) p := by
  have hh := (matCLM D).hasFDerivAt.comp p ((hasFDerivAt_id p).sub_const p)
  have hc := hh.const_sub q
  convert hc using 1
  · funext v
    simp [affineDemand]
  · simp

noncomputable def Model.ofAffine (e : InputCoordinates.Frame k) (p q : Vec n) (C : Mat n k)
    (D : Mat n n) (b : Vec n) (σ : ℝ) (hp : ∀ i, 0 < p i) (hw : ∀ j, 0 < e.w j)
    (hC : C ∈ e.PositiveDomain p) : Model n k where
  frame := e
  p := p
  q := q
  C := C
  D := D
  b := b
  sigma := σ
  hp := hp
  hw := hw
  hC := hC
  demand := affineDemand p q D
  demand_base := affineDemand_base p q D
  demand_deriv := affineDemand_derivative p q D

namespace Example
open Supply.Example
theorem ones_pos : ∀ i, 0 < ones i := by intro i; fin_cases i <;> norm_num [ones]
theorem frame_price_pos : ∀ j, 0 < frame.w j := by intro j; fin_cases j <;> norm_num [frame]
noncomputable def model : Model 2 1 := Model.ofAffine frame ones ones (path (1/2))
  1 ![1,0] 1 ones_pos frame_price_pos (path_mem (by norm_num) (by norm_num)).1
theorem model_report : parent.report model.q model.C = 0 := path_report (1/2)
theorem model_total_pos : ∀ j, 0 < Supply.totalInputs model.q model.A j := by
  change ∀ j, 0 < Supply.totalInputs ones (frame.reconstruct ones (path (1/2))) j
  rw [path_reconstruct, path_total]
  exact ones_pos
theorem model_K_posDef : model.K.PosDef :=
  model.K_posDef parent 0 model_report ones_pos model_total_pos Matrix.PosDef.one (by norm_num [model,Model.ofAffine])

/-- An interior two-good, two-factor example at sigma=1. Both factor-input shares
are positive; the numeraire change is not constrained to have the sign of qdot. -/
theorem concrete_linearized : model.Linearized ![-7/8,-1/8] ![-1/4] 1 := by
  have hz : path (1/2) *ᵥ ![-1/4] = ![-1/8,1/8] := by
    rw [path_exposure]
    ext i
    fin_cases i <;> norm_num [Matrix.mulVec, dotProduct, Fin.sum_univ_succ]
  have ha : model.A = inputs (1/2) := path_reconstruct (1/2)
  have hH : model.aggregateHessian = ![![-3/8,3/8],![3/8,-3/8]] := by
    ext j l
    simp only [Model.aggregateHessian, Matrix.sum_apply, Matrix.smul_apply, Model.hessian_apply, ha]
    fin_cases j <;> fin_cases l <;>
      norm_num [model, Model.ofAffine, inputs, frame, ones, Fin.sum_univ_succ]
  constructor
  · change ![-(7:ℝ)/8,-1/8] = -((1 : Mat 2 2) *ᵥ (path (1/2) *ᵥ ![-1/4] + ![1,0]))
    rw [hz, Matrix.one_mulVec]
    ext i
    fin_cases i <;> norm_num
  · rw [ha, hH]
    change (inputs (1/2)).transpose *ᵥ ![-7/8,-1/8] +
      (![![-3/8,3/8],![3/8,-3/8]] : Mat 2 2) *ᵥ (frame.V *ᵥ ![-1/4]) + (1:ℝ) • frame.a0 = 0
    ext j
    fin_cases j <;>
      norm_num [inputs, frame, Matrix.mulVec, dotProduct, Matrix.transpose, Fin.sum_univ_succ]
theorem concrete_solution : model.qSolution = ![-7/8,-1/8] ∧ model.zSolution = ![-1/4] ∧ model.sSolution = 1 := by
  have hh := model.linearized_unique model_K_posDef _ _ _ concrete_linearized
  exact ⟨hh.1.symm, hh.2.1.symm, hh.2.2.symm⟩
end Example
end CommodityClassification.Equilibrium
