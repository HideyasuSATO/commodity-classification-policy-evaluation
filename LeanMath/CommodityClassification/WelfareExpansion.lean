module
public import LeanMath.CommodityClassification.WelfarePeano
public import LeanMath.CommodityClassification.WelfareCoefficient
@[expose] public section
set_option maxHeartbeats 2200000
namespace CommodityClassification.Equilibrium
open Matrix Filter Asymptotics
open scoped BigOperators Topology
variable {n k g : ℕ}
namespace Model
variable (E : Model n k)

/-- An asymptotic statement about the actual previously defined welfare. -/
def WelfareExpansion (utility : Vec n → ℝ) (u : ℝ → Vec k) (s : ℝ → ℝ) : Prop :=
  (fun t => E.welfare utility u s 0-E.welfare utility u s t-(1/2 : ℝ)*t^2*E.lossCoefficient)
    =o[𝓝 (0 : ℝ)] (fun t : ℝ => t^2)

theorem constructed_welfare_taylor (h : E.DemandC1) (hK : E.K.PosDef)
    (hq : ∀ i, 0 < E.q i) (s0 : ℝ) (hs0 : 0 < s0)
    (utility : Vec n → ℝ) (hutility : E.UtilityCompatible utility) :
    let u := E.localPricePath h hK s0
    let s := E.localNumerairePath h hK s0
    (fun t => E.welfare utility u s 0-E.welfare utility u s t-
      (1/2 : ℝ)*t^2*(-dotProduct E.b (deriv (fun x => E.quantities (x,u x)) 0)))
      =o[𝓝 (0 : ℝ)] (fun t : ℝ => t^2) := by
  dsimp only
  apply WelfareAnalysis.loss_peano_of_derivative
    (E.welfare utility (E.localPricePath h hK s0) (E.localNumerairePath h hK s0))
    (fun t => dotProduct E.b (deriv (fun x => E.quantities (x,E.localPricePath h hK s0 x)) t))
    (E.weighted_quantity_derivative_continuous h hK s0)
  obtain ⟨I,hIo,hI0,hI⟩ := E.constructed_welfare_neighborhood h hK hq s0 hs0 utility hutility
  filter_upwards [hIo.mem_nhds hI0] with t ht
  exact (hI t ht).2.2.2.2

theorem constructed_welfare_expansion (h : E.DemandC1)
    (P : InputCoordinates.Partition n g) (J : Mat g k)
    (hreport : P.report E.q E.C=J) (hq : ∀ i, 0 < E.q i)
    (hI : ∀ j, 0 < Supply.totalInputs E.q E.A j) (hD : E.D.PosDef) (hσ : 0 < E.sigma)
    (s0 : ℝ) (hs0 : 0 < s0) (utility : Vec n → ℝ) (hutility : E.UtilityCompatible utility) :
    let hK := E.K_posDef P J hreport hq hI hD hσ
    E.WelfareExpansion utility (E.localPricePath h hK s0) (E.localNumerairePath h hK s0) := by
  dsimp only
  unfold WelfareExpansion
  have ht := E.constructed_welfare_taylor h (E.K_posDef P J hreport hq hI hD hσ) hq s0 hs0 utility hutility
  dsimp only at ht
  rw [E.quantity_derivative_zero h P J hreport hq hI hD hσ s0,
    ←E.lossCoefficient_eq_negative_quantity hD] at ht
  exact ht

theorem economic_welfare_expansion (h : E.DemandC1)
    (P : InputCoordinates.Partition n g) (J : Mat g k)
    (hreport : P.report E.q E.C=J) (hq : ∀ i, 0 < E.q i)
    (hI : ∀ j, 0 < Supply.totalInputs E.q E.A j) (hD : E.D.PosDef) (hσ : 0 < E.sigma)
    (s0 : ℝ) (hs0 : 0 < s0) (utility : Vec n → ℝ) (hutility : E.UtilityCompatible utility) :
    ∃ u : ℝ → Vec k, ∃ s : ℝ → ℝ, E.PositiveLocalPath s0 u s ∧
      E.WelfareNeighborhood s0 utility u s ∧
      HasDerivAt (fun t => E.quantities (t,u t)) E.qSolution 0 ∧
      E.WelfareExpansion utility u s := by
  let hK := E.K_posDef P J hreport hq hI hD hσ
  exact ⟨E.localPricePath h hK s0,E.localNumerairePath h hK s0,
    E.constructed_positive_path h hK hq s0 hs0,
    E.constructed_welfare_neighborhood h hK hq s0 hs0 utility hutility,
    (E.constructed_path_derivatives h P J hreport hq hI hD hσ s0).2.2,
    E.constructed_welfare_expansion h P J hreport hq hI hD hσ s0 hs0 utility hutility⟩

end Model
end CommodityClassification.Equilibrium
