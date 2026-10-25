module
public import LeanMath.CommodityClassification.EquilibriumQuadraticUtility
@[expose] public section
set_option maxHeartbeats 2200000
namespace CommodityClassification.Equilibrium
open Matrix Filter
open scoped BigOperators Topology ContDiff
variable {n k g : ℕ}
namespace Model
variable (E : Model n k)

/-- A local path satisfying the factor-market clearing equations. -/
structure PositiveLocalPath (s0 : ℝ) (u : ℝ → Vec k) (s : ℝ → ℝ) : Prop where
  price_base : u 0 = 0
  numeraire_base : s 0 = s0
  neighborhood : ∃ I : Set ℝ, IsOpen I ∧ 0 ∈ I ∧ ∀ t ∈ I,
    E.excess (E.endowment s0) ((t,u t),s t) = 0 ∧ E.PositiveState (t,u t) (s t) ∧
    ContDiffAt ℝ 1 u t ∧ ContDiffAt ℝ 1 s t
  local_unique : ∀ᶠ y in 𝓝 (0 : PolicyPrice k), ∀ r : ℝ,
    E.excess (E.endowment s0) (y,r) = 0 ↔ y.2 = u y.1 ∧ r = s y.1

theorem constructed_positive_path (h : E.DemandC1) (hK : E.K.PosDef)
    (hq : ∀ i, 0 < E.q i) (s0 : ℝ) (hs0 : 0 < s0) :
    E.PositiveLocalPath s0 (E.localPricePath h hK s0) (E.localNumerairePath h hK s0) :=
  ⟨E.localPricePath_base h hK s0,E.localNumerairePath_base h hK s0,
    E.local_common_neighborhood h hK hq s0 hs0,E.local_full_uniqueness h hK s0⟩

theorem constructed_path_derivatives (h : E.DemandC1)
    (P : InputCoordinates.Partition n g) (J : Mat g k)
    (hreport : P.report E.q E.C = J) (hq : ∀ i, 0 < E.q i)
    (hI : ∀ j, 0 < Supply.totalInputs E.q E.A j) (hD : E.D.PosDef) (hσ : 0 < E.sigma)
    (s0 : ℝ) :
    let hK := E.K_posDef P J hreport hq hI hD hσ
    HasDerivAt (E.localPricePath h hK s0) E.zSolution 0 ∧
    HasDerivAt (E.localNumerairePath h hK s0) E.sSolution 0 ∧
    HasDerivAt (fun t => E.quantities (t,E.localPricePath h hK s0 t)) E.qSolution 0 := by
  dsimp only
  let hK := E.K_posDef P J hreport hq hI hD hσ
  let u := E.localPricePath h hK s0
  let s := E.localNumerairePath h hK s0
  have hu : HasDerivAt u (deriv u 0) 0 :=
    ((E.localPricePath_contDiffAt h hK s0).differentiableAt (by norm_num)).hasDerivAt
  have hs : HasDerivAt s (deriv s 0) 0 :=
    ((E.localNumerairePath_contDiffAt h hK s0).differentiableAt (by norm_num)).hasDerivAt
  have hd := E.economic_path_derivatives P J hreport hq hI hD hσ (E.endowment s0) s0 u s
    (deriv u 0) (deriv s 0) (E.localPricePath_base h hK s0) (E.localNumerairePath_base h hK s0)
    hu hs (E.local_full_clearing h hK s0)
  exact ⟨hu.congr_deriv hd.1,hs.congr_deriv hd.2.1,hd.2.2.1⟩

/-- General C1 demand: economic hypotheses yield K invertibility internally. -/
theorem economic_local_existence (h : E.DemandC1)
    (P : InputCoordinates.Partition n g) (J : Mat g k)
    (hreport : P.report E.q E.C = J) (hq : ∀ i, 0 < E.q i)
    (hI : ∀ j, 0 < Supply.totalInputs E.q E.A j) (hD : E.D.PosDef) (hσ : 0 < E.sigma)
    (s0 : ℝ) (hs0 : 0 < s0) :
    ∃ u : ℝ → Vec k, ∃ s : ℝ → ℝ, E.PositiveLocalPath s0 u s ∧
      HasDerivAt u E.zSolution 0 ∧ HasDerivAt s E.sSolution 0 ∧
      HasDerivAt (fun t => E.quantities (t,u t)) E.qSolution 0 := by
  let hK := E.K_posDef P J hreport hq hI hD hσ
  exact ⟨E.localPricePath h hK s0,E.localNumerairePath h hK s0,
    E.constructed_positive_path h hK hq s0 hs0,
    E.constructed_path_derivatives h P J hreport hq hI hD hσ s0⟩

theorem ofAffine_demandC1 (e : InputCoordinates.Frame k) (p q : Vec n) (C : Mat n k)
    (D : Mat n n) (b : Vec n) (σ : ℝ) (hp : ∀ i, 0 < p i) (hw : ∀ j, 0 < e.w j)
    (hC : C ∈ e.PositiveDomain p) :
    (Model.ofAffine e p q C D b σ hp hw hC).DemandC1 :=
  ((affineDemand_contDiff p q D).of_le (by simp)).contDiffAt

/-- The manuscript's local quadratic implementation specializes the general theorem. -/
theorem quadratic_local_existence (e : InputCoordinates.Frame k) (p q : Vec n) (C : Mat n k)
    (D : Mat n n) (b : Vec n) (σ : ℝ) (hp : ∀ i, 0 < p i) (hw : ∀ j, 0 < e.w j)
    (hC : C ∈ e.PositiveDomain p) (P : InputCoordinates.Partition n g) (J : Mat g k)
    (hreport : P.report q C = J) (hq : ∀ i, 0 < q i)
    (hI : ∀ j, 0 < Supply.totalInputs q (e.reconstruct p C) j) (hD : D.PosDef) (hσ : 0 < σ)
    (s0 : ℝ) (hs0 : 0 < s0) :
    let E := Model.ofAffine e p q C D b σ hp hw hC
    ∃ u : ℝ → Vec k, ∃ s : ℝ → ℝ, E.PositiveLocalPath s0 u s ∧
      HasDerivAt u E.zSolution 0 ∧ HasDerivAt s E.sSolution 0 ∧
      HasDerivAt (fun t => E.quantities (t,u t)) E.qSolution 0 := by
  exact (Model.ofAffine e p q C D b σ hp hw hC).economic_local_existence
    (ofAffine_demandC1 e p q C D b σ hp hw hC) P J hreport hq hI hD hσ s0 hs0
end Model
end CommodityClassification.Equilibrium
