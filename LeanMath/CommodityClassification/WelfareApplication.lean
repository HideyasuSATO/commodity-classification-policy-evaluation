module
public import LeanMath.CommodityClassification.WelfareIdentity
@[expose] public section
set_option maxHeartbeats 2400000
namespace CommodityClassification.Equilibrium
open Matrix Filter
open scoped BigOperators Topology
variable {n k g : ℕ}
namespace Model
variable (E : Model n k)

def HouseholdState (s0 : ℝ) (utility : Vec n → ℝ) (U : Set (Vec n))
    (u : ℝ → Vec k) (s : ℝ → ℝ) (t : ℝ) : Prop :=
  E.quantities (t,u t) ∈ U ∧
  (∀ r ∈ U, ∀ z : ℝ,
    dotProduct (E.prices (t,u t)) r+z ≤ E.householdIncome (E.endowment s0) (t,u t) →
    utility r+z ≤ E.welfare utility u s t) ∧
  (∀ r ∈ U, ∀ z : ℝ, r ≠ E.quantities (t,u t) →
    dotProduct (E.prices (t,u t)) r+z ≤ E.householdIncome (E.endowment s0) (t,u t) →
    utility r+z < E.welfare utility u s t)

def QuadraticWelfareNeighborhood (s0 : ℝ) (utility : Vec n → ℝ) (U : Set (Vec n))
    (u : ℝ → Vec k) (s : ℝ → ℝ) : Prop :=
  ∃ I : Set ℝ, IsOpen I ∧ 0 ∈ I ∧ ∀ t ∈ I,
    E.WelfareState s0 utility u s t ∧ E.HouseholdState s0 utility U u s t

theorem constructed_quadratic_welfare (h : E.DemandC1) (hK : E.K.PosDef)
    (hq : ∀ i, 0 < E.q i) (s0 : ℝ) (hs0 : 0 < s0)
    (hD : E.D.PosDef) (haff : E.demand=affineDemand E.p E.q E.D)
    (utility : Vec n → ℝ) (c : ℝ) (U : Set (Vec n)) (hU : U ∈ 𝓝 E.q)
    (hmatch : ∀ r ∈ U, utility r=c+quadraticUtility E.p E.D (r-E.q)) :
    E.QuadraticWelfareNeighborhood s0 utility U
      (E.localPricePath h hK s0) (E.localNumerairePath h hK s0) := by
  have hcompat := E.quadratic_utility_compatible hD haff utility c U hU hmatch
  obtain ⟨J,hJo,hJ0,hJ⟩ := E.constructed_welfare_neighborhood h hK hq s0 hs0 utility hcompat
  have hopt := E.quadratic_path_local_optimum h hK s0 hD haff utility c U hU hmatch
  have hmemJ : ∀ᶠ t in 𝓝 (0 : ℝ), t ∈ J := hJo.mem_nhds hJ0
  have hall := hmemJ.and hopt
  obtain ⟨I,hI,hIo,hI0⟩ := mem_nhds_iff.mp hall
  refine ⟨I,hIo,hI0,?_⟩
  intro t ht
  have hw := hJ t (hI ht).1
  obtain ⟨hmem,hm,hs⟩ := (hI ht).2
  refine ⟨hw,hmem,?_,?_⟩
  · exact household_optimum_of_surplus utility _ _ _ _ U hw.2.2.1 hm
  · exact household_strict_of_surplus utility _ _ _ _ U hw.2.2.1 hs

theorem economic_quadratic_welfare (h : E.DemandC1)
    (P : InputCoordinates.Partition n g) (J : Mat g k)
    (hreport : P.report E.q E.C=J) (hq : ∀ i, 0 < E.q i)
    (hI : ∀ j, 0 < Supply.totalInputs E.q E.A j) (hD : E.D.PosDef) (hσ : 0 < E.sigma)
    (s0 : ℝ) (hs0 : 0 < s0) (haff : E.demand=affineDemand E.p E.q E.D)
    (utility : Vec n → ℝ) (c : ℝ) (U : Set (Vec n)) (hU : U ∈ 𝓝 E.q)
    (hmatch : ∀ r ∈ U, utility r=c+quadraticUtility E.p E.D (r-E.q)) :
    ∃ u : ℝ → Vec k, ∃ s : ℝ → ℝ, E.PositiveLocalPath s0 u s ∧
      E.QuadraticWelfareNeighborhood s0 utility U u s := by
  let hK := E.K_posDef P J hreport hq hI hD hσ
  exact ⟨E.localPricePath h hK s0,E.localNumerairePath h hK s0,
    E.constructed_positive_path h hK hq s0 hs0,
    E.constructed_quadratic_welfare h hK hq s0 hs0 hD haff utility c U hU hmatch⟩

theorem ofAffine_welfare (e : InputCoordinates.Frame k) (p q : Vec n) (C : Mat n k)
    (D : Mat n n) (b : Vec n) (σ : ℝ) (hp : ∀ i, 0 < p i) (hw : ∀ j, 0 < e.w j)
    (hC : C ∈ e.PositiveDomain p) (P : InputCoordinates.Partition n g) (J : Mat g k)
    (hreport : P.report q C=J) (hq : ∀ i, 0 < q i)
    (hI : ∀ j, 0 < Supply.totalInputs q (e.reconstruct p C) j) (hD : D.PosDef) (hσ : 0 < σ)
    (s0 : ℝ) (hs0 : 0 < s0) (utility : Vec n → ℝ) (c : ℝ) (U : Set (Vec n)) (hU : U ∈ 𝓝 q)
    (hmatch : ∀ r ∈ U, utility r=c+quadraticUtility p D (r-q)) :
    let E := Model.ofAffine e p q C D b σ hp hw hC
    ∃ u : ℝ → Vec k, ∃ s : ℝ → ℝ, E.PositiveLocalPath s0 u s ∧
      E.QuadraticWelfareNeighborhood s0 utility U u s := by
  exact (Model.ofAffine e p q C D b σ hp hw hC).economic_quadratic_welfare
    (ofAffine_demandC1 e p q C D b σ hp hw hC) P J hreport hq hI hD hσ s0 hs0 rfl utility c U hU hmatch

theorem WelfareNeighborhood.zero_derivative {E : Model n k} {s0 : ℝ} {utility : Vec n → ℝ}
    {u : ℝ → Vec k} {s : ℝ → ℝ} (h : E.WelfareNeighborhood s0 utility u s) :
    HasDerivAt (E.welfare utility u s) 0 0 := by
  obtain ⟨I,_,h0,hI⟩ := h
  simpa only [zero_mul] using (hI 0 h0).2.2.2.2

end Model

namespace Example
open Supply.Example
noncomputable def utility (r : Vec 2) : ℝ := quadraticUtility ones 1 (r-ones)

/-- Concrete positive two-good/two-factor application at sigma=1, without a
numeric approximation to the nonlinear local equilibrium path. -/
theorem concrete_welfare_identity :
    ∃ u : ℝ → Vec 1, ∃ s : ℝ → ℝ, model.PositiveLocalPath 1 u s ∧
      model.QuadraticWelfareNeighborhood 1 utility Set.univ u s := by
  apply model.economic_quadratic_welfare model_demandC1 parent 0 model_report ones_pos
    model_total_pos Matrix.PosDef.one (by norm_num [model,Model.ofAffine]) 1 (by norm_num) rfl utility 0 Set.univ
    (by simp)
  intro r _
  simp only [utility,zero_add]
  rfl
end Example
end CommodityClassification.Equilibrium
