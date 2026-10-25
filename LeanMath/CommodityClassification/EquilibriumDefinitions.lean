module
public import LeanMath.CommodityClassification.CandidateRegularity
public import LeanMath.CommodityClassification.CostInputConnection
@[expose] public section
set_option maxHeartbeats 1600000
namespace CommodityClassification.Equilibrium
open Matrix Filter
open scoped BigOperators Topology
abbrev Vec (n : ℕ) := Fin n → ℝ
abbrev Mat (n m : ℕ) := Matrix (Fin n) (Fin m) ℝ
abbrev PolicyPrice (k : ℕ) := ℝ × Vec k
variable {n k f : ℕ}

noncomputable def matCLM (M : Mat n f) : Vec f →L[ℝ] Vec n :=
  ContinuousLinearMap.pi (fun i => CESCost.weightedLinear (M i))
@[simp] theorem matCLM_apply (M : Mat n f) (v : Vec f) : matCLM M v = M *ᵥ v := by
  ext i
  simp [matCLM, Matrix.mulVec]

noncomputable def taxCLM (k : ℕ) : PolicyPrice k →L[ℝ] ℝ := ContinuousLinearMap.fst ℝ ℝ (Vec k)
noncomputable def coordCLM (k : ℕ) : PolicyPrice k →L[ℝ] Vec k := ContinuousLinearMap.snd ℝ ℝ (Vec k)
@[simp] theorem taxCLM_apply (y : PolicyPrice k) : taxCLM k y = y.1 := rfl
@[simp] theorem coordCLM_apply (y : PolicyPrice k) : coordCLM k y = y.2 := rfl

/-- Data for differentiation at the positive benchmark. The solution theorem
assumes positive quantities, SPD demand, and positive substitution. -/
structure Model (n k : ℕ) where
  frame : InputCoordinates.Frame k
  p : Vec n
  q : Vec n
  C : Mat n k
  D : Mat n n
  b : Vec n
  sigma : ℝ
  hp : ∀ i, 0 < p i
  hw : ∀ j, 0 < frame.w j
  hC : C ∈ frame.PositiveDomain p
  demand : Vec n → Vec n
  demand_base : demand p = q
  demand_deriv : HasFDerivAt demand (-matCLM D) p

namespace Model
variable (E : Model n k)
noncomputable def A : Mat n (k+1) := E.frame.reconstruct E.p E.C
noncomputable def costData (i : Fin n) := CESCost.ofCoordinates E.frame E.p E.C E.hp E.hw E.hC i
noncomputable def currentPrice (u : Vec k) : Vec (k+1) := E.frame.w + E.frame.V *ᵥ u
noncomputable def costs (w : Vec (k+1)) : Vec n := fun i => (E.costData i).cost E.sigma w
noncomputable def currentInputs (w : Vec (k+1)) : Mat n (k+1) :=
  fun i j => CESCost.pricePartial ((E.costData i).cost E.sigma) j w
noncomputable def prices (y : PolicyPrice k) : Vec n := E.costs (E.currentPrice y.2) + y.1 • E.b
noncomputable def quantities (y : PolicyPrice k) : Vec n := E.demand (E.prices y)
noncomputable def factorDemand (y : PolicyPrice k) : Vec (k+1) :=
  (E.currentInputs (E.currentPrice y.2)).transpose *ᵥ E.quantities y
noncomputable def excess (abar : Vec (k+1)) (ys : PolicyPrice k × ℝ) : Vec (k+1) :=
  E.factorDemand ys.1 + ys.2 • E.frame.a0 - abar
noncomputable def reduced (abar : Vec (k+1)) (y : PolicyPrice k) : Vec k :=
  E.frame.V.transpose *ᵥ (E.factorDemand y - abar)
noncomputable def hessian (i : Fin n) : Mat (k+1) (k+1) := (E.costData i).hessian E.sigma
noncomputable def aggregateHessian : Mat (k+1) (k+1) := ∑ i, E.q i • E.hessian i
theorem hessian_apply (i : Fin n) (j l : Fin (k+1)) :
    E.hessian i j l = E.sigma * (E.A i j * E.A i l / E.p i -
      if j=l then E.A i j / E.frame.w j else 0) := rfl
noncomputable def R : Mat k k := Supply.candidateR E.frame E.p E.q E.C
noncomputable def K : Mat k k := Regularity.K E.p E.q E.D E.R E.sigma E.C
noncomputable def m : Vec k := E.C.transpose *ᵥ (E.D *ᵥ E.b)
noncomputable def priceChange : PolicyPrice k →L[ℝ] Vec n :=
  (matCLM E.C).comp (coordCLM k) + ContinuousLinearMap.pi (fun i => E.b i • taxCLM k)
noncomputable def quantityChange : PolicyPrice k →L[ℝ] Vec n :=
  (-matCLM E.D).comp E.priceChange
noncomputable def factorChange : PolicyPrice k →L[ℝ] Vec (k+1) :=
  (matCLM E.A.transpose).comp E.quantityChange +
  (matCLM E.aggregateHessian).comp ((matCLM E.frame.V).comp (coordCLM k))
noncomputable def excessChange : (PolicyPrice k × ℝ) →L[ℝ] Vec (k+1) :=
  E.factorChange.comp (ContinuousLinearMap.fst ℝ (PolicyPrice k) ℝ) +
  ContinuousLinearMap.pi (fun j => E.frame.a0 j • ContinuousLinearMap.snd ℝ (PolicyPrice k) ℝ)

@[simp] theorem currentPrice_zero : E.currentPrice 0 = E.frame.w := by simp [currentPrice]
@[simp] theorem costs_base : E.costs E.frame.w = E.p := by
  ext i
  exact (E.costData i).cost_benchmark E.sigma
@[simp] theorem inputs_base : E.currentInputs E.frame.w = E.A := by
  ext i j
  exact (E.costData i).cost_gradient E.sigma j
@[simp] theorem prices_zero : E.prices 0 = E.p := by simp [prices]
@[simp] theorem quantities_zero : E.quantities 0 = E.q := by simp [quantities, E.demand_base]
@[simp] theorem factorDemand_zero : E.factorDemand 0 = E.A.transpose *ᵥ E.q := by simp [factorDemand]
theorem excess_base (s0 : ℝ) : E.excess (E.A.transpose *ᵥ E.q + s0 • E.frame.a0) (0,s0) = 0 := by
  simp [excess]
theorem priceChange_apply (y : PolicyPrice k) : E.priceChange y = E.C *ᵥ y.2 + y.1 • E.b := by
  ext i
  simp [priceChange, mul_comm]
theorem quantityChange_apply (y : PolicyPrice k) : E.quantityChange y = -(E.D *ᵥ (E.C *ᵥ y.2 + y.1 • E.b)) := by
  simp [quantityChange, E.priceChange_apply]
theorem factorChange_apply (y : PolicyPrice k) :
    E.factorChange y = E.A.transpose *ᵥ E.quantityChange y + E.aggregateHessian *ᵥ (E.frame.V *ᵥ y.2) := by
  simp [factorChange]
theorem excessChange_apply (ys : PolicyPrice k × ℝ) :
    E.excessChange ys = E.factorChange ys.1 + ys.2 • E.frame.a0 := by
  ext j
  simp [excessChange, mul_comm]
theorem currentPrice_normalized (u : Vec k) : dotProduct E.frame.a0 (E.currentPrice u) = 1 := by
  simp [currentPrice, dotProduct_add, E.frame.normalized, E.frame.a0_dot_V]
theorem currentPrice_continuous : Continuous E.currentPrice := by
  unfold currentPrice
  fun_prop
theorem positivePrice_neighborhood : {u | E.currentPrice u ∈ CESCost.PositivePrices (k+1)} ∈ 𝓝 0 :=
  E.currentPrice_continuous.continuousAt.preimage_mem_nhds
    (CESCost.positivePrices_open.mem_nhds (by simpa [CESCost.PositivePrices] using E.hw))
theorem positivePrice_domain_open : IsOpen {u | E.currentPrice u ∈ CESCost.PositivePrices (k+1)} :=
  CESCost.positivePrices_open.preimage E.currentPrice_continuous
theorem reduced_eq_project_excess (abar : Vec (k+1)) (y : PolicyPrice k) (s : ℝ) :
    E.reduced abar y = E.frame.V.transpose *ᵥ E.excess abar (y,s) := by
  simp [reduced, excess, Matrix.mulVec_sub, Matrix.mulVec_add, Matrix.mulVec_smul, E.frame.annihilates]
end Model
end CommodityClassification.Equilibrium
