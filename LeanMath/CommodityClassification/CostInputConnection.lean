module
public import LeanMath.CommodityClassification.CostDerivativeIntegration
@[expose] public section
namespace CommodityClassification.CESCost
open Matrix
open scoped BigOperators
variable {n f k : ℕ}

noncomputable def ofInputs (A : Mat n f) (p : Vec n) (w0 : Vec f)
    (hA : InputCoordinates.Positive A) (hp : ∀ i, 0 < p i) (hw : ∀ j, 0 < w0 j)
    (hc : A *ᵥ w0 = p) (i : Fin n) : Data f where
  p := p i
  w0 := w0
  a := A i
  p_pos := hp i
  w0_pos := hw
  a_pos := hA i
  cost_identity := congrFun hc i

theorem input_cost_shares (A : Mat n f) (p : Vec n) (w0 : Vec f)
    (hA : InputCoordinates.Positive A) (hp : ∀ i, 0 < p i) (hw : ∀ j, 0 < w0 j)
    (hc : A *ᵥ w0 = p) (i : Fin n) :
    (∀ j, 0 < (ofInputs A p w0 hA hp hw hc i).share j) ∧
      (∑ j, (ofInputs A p w0 hA hp hw hc i).share j) = 1 :=
  ⟨(ofInputs A p w0 hA hp hw hc i).share_pos,
    (ofInputs A p w0 hA hp hw hc i).share_sum⟩

theorem input_cost_formulas (A : Mat n f) (p : Vec n) (w0 : Vec f)
    (hA : InputCoordinates.Positive A) (hp : ∀ i, 0 < p i) (hw : ∀ j, 0 < w0 j)
    (hc : A *ᵥ w0 = p) (σ : ℝ) (i : Fin n) :
    let d := ofInputs A p w0 hA hp hw hc i
    d.cost σ w0 = p i ∧
      (∀ w ∈ PositivePrices f, ContDiffAt ℝ ⊤ (d.cost σ) w) ∧
      (∀ u, fderiv ℝ (d.cost σ) w0 u = dotProduct (A i) u) ∧
      (∀ j l, pricePartial (pricePartial (d.cost σ) j) l w0 =
        σ * (A i j * A i l / p i - if j=l then A i j/w0 j else 0)) ∧
      (∀ u v, fderiv ℝ (fun w => fderiv ℝ (d.cost σ) w v) w0 u =
        σ * (dotProduct (A i) u * dotProduct (A i) v / p i -
          ∑ j, (A i j/w0 j)*u j*v j)) := by
  dsimp only
  let d := ofInputs A p w0 hA hp hw hc i
  exact ⟨d.cost_benchmark σ, fun _ hw' => d.cost_contDiffAt σ hw',
    d.cost_first_derivative σ, d.cost_mixed_derivative σ, d.cost_second_derivative σ⟩

noncomputable def ofCoordinates (e : InputCoordinates.Frame k) (p : Vec n)
    (C : Mat n k) (hp : ∀ i, 0 < p i) (hw : ∀ j, 0 < e.w j)
    (hC : C ∈ e.PositiveDomain p) (i : Fin n) : Data (k+1) :=
  ofInputs (e.reconstruct p C) p e.w hC hp hw (e.reconstruct_cost p C) i

theorem coordinate_cost_inputs (e : InputCoordinates.Frame k) (p : Vec n)
    (C : Mat n k) (hp : ∀ i, 0 < p i) (hw : ∀ j, 0 < e.w j)
    (hC : C ∈ e.PositiveDomain p) (i : Fin n) :
    (ofCoordinates e p C hp hw hC i).a = e.reconstruct p C i ∧
    (ofCoordinates e p C hp hw hC i).w0 = e.w ∧
    (ofCoordinates e p C hp hw hC i).p = p i := ⟨rfl,rfl,rfl⟩

theorem coordinate_cost_shares (e : InputCoordinates.Frame k) (p : Vec n)
    (C : Mat n k) (hp : ∀ i, 0 < p i) (hw : ∀ j, 0 < e.w j)
    (hC : C ∈ e.PositiveDomain p) (i : Fin n) :
    (∀ j, 0 < (ofCoordinates e p C hp hw hC i).share j) ∧
      (∑ j, (ofCoordinates e p C hp hw hC i).share j) = 1 :=
  ⟨(ofCoordinates e p C hp hw hC i).share_pos,
    (ofCoordinates e p C hp hw hC i).share_sum⟩

theorem coordinate_cost_formulas (e : InputCoordinates.Frame k) (p : Vec n)
    (C : Mat n k) (hp : ∀ i, 0 < p i) (hw : ∀ j, 0 < e.w j)
    (hC : C ∈ e.PositiveDomain p) (σ : ℝ) (i : Fin n) :
    let d := ofCoordinates e p C hp hw hC i
    d.cost σ e.w = p i ∧
      (∀ w ∈ PositivePrices (k+1), ContDiffAt ℝ ⊤ (d.cost σ) w) ∧
      (∀ u, fderiv ℝ (d.cost σ) e.w u = dotProduct (e.reconstruct p C i) u) ∧
      (∀ j l, pricePartial (pricePartial (d.cost σ) j) l e.w =
        σ * (e.reconstruct p C i j * e.reconstruct p C i l / p i -
          if j=l then e.reconstruct p C i j/e.w j else 0)) ∧
      (∀ u v, fderiv ℝ (fun w => fderiv ℝ (d.cost σ) w v) e.w u =
        σ * (dotProduct (e.reconstruct p C i) u * dotProduct (e.reconstruct p C i) v / p i -
          ∑ j, (e.reconstruct p C i j/e.w j)*u j*v j)) :=
  input_cost_formulas (e.reconstruct p C) p e.w hC hp hw (e.reconstruct_cost p C) σ i

end CommodityClassification.CESCost
