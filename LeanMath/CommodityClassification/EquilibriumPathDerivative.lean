module
public import LeanMath.CommodityClassification.EquilibriumLinearSolution
public import Mathlib.Analysis.Calculus.Deriv.Prod
@[expose] public section
set_option maxHeartbeats 2000000
namespace CommodityClassification.Equilibrium
open Matrix Filter
open scoped BigOperators Topology
variable {n k g : ℕ}
namespace Model
variable (E : Model n k)

theorem quantity_path_derivative (u : ℝ → Vec k) (z : Vec k)
    (hu0 : u 0 = 0) (hu : HasDerivAt u z 0) :
    HasDerivAt (fun t => E.quantities (t,u t)) (E.quantityChange (1,z)) 0 := by
  have hp : HasDerivAt (fun t : ℝ => (t,u t)) (1,z) 0 :=
    HasDerivAt.prodMk (hasDerivAt_id (0 : ℝ)) hu
  have hq : HasFDerivAt E.quantities E.quantityChange ((0 : ℝ),u 0) := by
    rw [hu0]
    exact E.quantities_hasFDerivAt
  exact hq.comp_hasDerivAt (0 : ℝ) hp

theorem path_positive_prices (u : ℝ → Vec k) (z : Vec k)
    (hu0 : u 0 = 0) (hu : HasDerivAt u z 0) :
    ∀ᶠ t in 𝓝 (0 : ℝ), E.currentPrice (u t) ∈ CESCost.PositivePrices (k+1) := by
  have hh := hu.continuousAt
  rw [ContinuousAt, hu0] at hh
  exact hh E.positivePrice_neighborhood

/-- Linearization of a differentiable path that clears markets
throughout a neighborhood of the benchmark. -/
theorem clearing_path_linearized (abar : Vec (k+1)) (s0 : ℝ)
    (u : ℝ → Vec k) (s : ℝ → ℝ) (z : Vec k) (ds : ℝ)
    (hu0 : u 0 = 0) (hs0 : s 0 = s0)
    (hu : HasDerivAt u z 0) (hs : HasDerivAt s ds 0)
    (hclear : ∀ᶠ t in 𝓝 (0 : ℝ), E.excess abar ((t,u t),s t) = 0) :
    E.Linearized (E.quantityChange (1,z)) z ds := by
  have hp1 : HasDerivAt (fun t : ℝ => (t,u t)) (1,z) 0 :=
    HasDerivAt.prodMk (hasDerivAt_id (0 : ℝ)) hu
  have hp : HasDerivAt (fun t : ℝ => ((t,u t),s t)) ((1,z),ds) 0 :=
    HasDerivAt.prodMk hp1 hs
  have he : HasFDerivAt (E.excess abar) E.excessChange (((0 : ℝ),u 0),s 0) := by
    rw [hu0, hs0]
    exact E.excess_hasFDerivAt abar s0
  have hd := he.comp_hasDerivAt (0 : ℝ) hp
  have hz : HasDerivAt (fun t : ℝ => E.excess abar ((t,u t),s t)) 0 0 :=
    (hasDerivAt_const (0 : ℝ) (0 : Vec (k+1))).congr_of_eventuallyEq hclear
  have hzero := hd.unique hz
  apply (E.linearized_iff_change _ _ _).mpr
  exact ⟨rfl, by simpa only [E.excessChange_apply] using hzero⟩

theorem economic_path_derivatives (P : InputCoordinates.Partition n g) (J : Mat g k)
    (hreport : P.report E.q E.C = J) (hq : ∀ i, 0 < E.q i)
    (hI : ∀ j, 0 < Supply.totalInputs E.q E.A j) (hD : E.D.PosDef) (hσ : 0 < E.sigma)
    (abar : Vec (k+1)) (s0 : ℝ) (u : ℝ → Vec k) (s : ℝ → ℝ)
    (z : Vec k) (ds : ℝ) (hu0 : u 0 = 0) (hs0 : s 0 = s0)
    (hu : HasDerivAt u z 0) (hs : HasDerivAt s ds 0)
    (hclear : ∀ᶠ t in 𝓝 (0 : ℝ), E.excess abar ((t,u t),s t) = 0) :
    z = E.zSolution ∧ ds = E.sSolution ∧
    HasDerivAt (fun t => E.quantities (t,u t)) E.qSolution 0 ∧
    (∀ᶠ t in 𝓝 (0 : ℝ), E.currentPrice (u t) ∈ CESCost.PositivePrices (k+1)) := by
  have hlin := E.clearing_path_linearized abar s0 u s z ds hu0 hs0 hu hs hclear
  have huniq := (E.economic_linearized_solution P J hreport hq hI hD hσ).2 _ _ _ hlin
  exact ⟨huniq.2.1, huniq.2.2,
    (E.quantity_path_derivative u z hu0 hu).congr_deriv huniq.1,
    E.path_positive_prices u z hu0 hu⟩
end Model
end CommodityClassification.Equilibrium
