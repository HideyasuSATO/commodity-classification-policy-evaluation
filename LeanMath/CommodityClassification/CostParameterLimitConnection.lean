module
public import LeanMath.CommodityClassification.CESParameterLimit
public import LeanMath.CommodityClassification.CostInputConnection
@[expose] public section
namespace CommodityClassification.CESCost
open Matrix Filter
open scoped BigOperators Topology
variable {n f k : ℕ}

theorem input_cost_parameter_limit (A : Mat n f) (p : Vec n) (w0 : Vec f)
    (hA : InputCoordinates.Positive A) (hp : ∀ i,0<p i) (hw0 : ∀ j,0<w0 j)
    (hc : A *ᵥ w0 = p) (i : Fin n) (w : Vec f) (hw : w ∈ PositivePrices f) :
    let d := ofInputs A p w0 hA hp hw0 hc i
    Tendsto (fun σ => d.ces σ w) (𝓝[≠] (1:ℝ)) (𝓝 (d.cobb w)) ∧
      ContinuousAt (fun σ => d.cost σ w) 1 :=
  ⟨(ofInputs A p w0 hA hp hw0 hc i).ces_tendsto_cobb hw,
    (ofInputs A p w0 hA hp hw0 hc i).cost_parameter_continuousAt_one hw⟩

theorem coordinate_cost_parameter_limit (e : InputCoordinates.Frame k) (p : Vec n)
    (C : Mat n k) (hp : ∀ i,0<p i) (hw0 : ∀ j,0<e.w j)
    (hC : C ∈ e.PositiveDomain p) (i : Fin n) (w : Vec (k+1))
    (hw : w ∈ PositivePrices (k+1)) :
    let d := ofCoordinates e p C hp hw0 hC i
    Tendsto (fun σ => d.ces σ w) (𝓝[≠] (1:ℝ)) (𝓝 (d.cobb w)) ∧
      ContinuousAt (fun σ => d.cost σ w) 1 :=
  ⟨(ofCoordinates e p C hp hw0 hC i).ces_tendsto_cobb hw,
    (ofCoordinates e p C hp hw0 hC i).cost_parameter_continuousAt_one hw⟩

end CommodityClassification.CESCost
