module
public import LeanMath.CommodityClassification.UniformRegularity
@[expose] public section
set_option maxHeartbeats 1800000
namespace CommodityClassification.Regularity
open Matrix
open scoped BigOperators Topology
variable {n k g r : ℕ}

theorem candidate_closure_lower_bound (e : InputCoordinates.Frame k)
    (P : InputCoordinates.Partition n g) (p q : Vec n) (J : Mat g k) (C0 C : Mat n k)
    (D : Mat n n) (σ : ℝ) (hp : ∀ i, 0 < p i) (hq : ∀ i, 0 < q i)
    (hw : ∀ j, 0 < e.w j) (hI : ∀ j, 0 < Supply.totalInputs q (e.reconstruct p C0) j)
    (h0 : C0 ∈ e.Candidates p q P J) (hC : C ∈ closure (e.Candidates p q P J))
    (hD : D.PosDef) (hn : 0 < n) :
    (K p q D (Supply.candidateR e p q C0) σ C -
      min (demandLambda p q D hp hq hD hn) σ • Supply.candidateR e p q C0).PosSemidef :=
  K_uniform_lower_bound p q D _ σ _ C (xi_posDef p q hp hq).posSemidef
    (demand_lower_bound p q D hp hq hD hn)
    (Supply.candidate_closure_residual_posSemidef e P p q J C0 C hp hq hw hI h0 hC)

/-- The quantifiers expose a single lambda and R before C ranges over the actual closure.
Positive observed total factor use implies that the goods set is nonempty. -/
theorem candidate_closure_certificate (e : InputCoordinates.Frame k)
    (P : InputCoordinates.Partition n g) (p q : Vec n) (J : Mat g k) (C0 : Mat n k)
    (D : Mat n n) (σ : ℝ) (hp : ∀ i, 0 < p i) (hq : ∀ i, 0 < q i)
    (hw : ∀ j, 0 < e.w j) (hI : ∀ j, 0 < Supply.totalInputs q (e.reconstruct p C0) j)
    (h0 : C0 ∈ e.Candidates p q P J) (hD : D.PosDef) (hσ : 0 < σ) :
    let hn := Supply.goods_nonempty_of_total_pos q (e.reconstruct p C0) hI
    let lam := demandLambda p q D hp hq hD hn
    let R := Supply.candidateR e p q C0
    0 < lam ∧ (min lam σ • R).PosDef ∧
      ∀ C ∈ closure (e.Candidates p q P J),
        (K p q D R σ C - min lam σ • R).PosSemidef ∧
        (K p q D R σ C).PosDef ∧
        (K p q D R σ C).det ≠ 0 ∧
        K p q D R σ C * (K p q D R σ C)⁻¹ = 1 ∧
        (K p q D R σ C)⁻¹ * K p q D R σ C = 1 := by
  dsimp only
  let hn := Supply.goods_nonempty_of_total_pos q (e.reconstruct p C0) hI
  have hlam := demandLambda_pos p q D hp hq hD hn
  have hR := Supply.candidate_R_posDef e p q C0 hw hI
  refine ⟨hlam, hR.smul (lt_min hlam hσ), ?_⟩
  intro C hC
  have hg := candidate_closure_lower_bound e P p q J C0 C D σ hp hq hw hI h0 hC hD hn
  have hk := posDef_of_positive_lower_bound _ _ _ hg hR (lt_min hlam hσ)
  exact ⟨hg, hk, inverse_identities _ hk⟩

theorem candidate_K_posDef (e : InputCoordinates.Frame k)
    (P : InputCoordinates.Partition n g) (p q : Vec n) (J : Mat g k) (C0 C : Mat n k)
    (D : Mat n n) (σ : ℝ) (hp : ∀ i, 0 < p i) (hq : ∀ i, 0 < q i)
    (hw : ∀ j, 0 < e.w j) (hI : ∀ j, 0 < Supply.totalInputs q (e.reconstruct p C0) j)
    (h0 : C0 ∈ e.Candidates p q P J) (hC : C ∈ e.Candidates p q P J)
    (hD : D.PosDef) (hσ : 0 < σ) :
    (K p q D (Supply.candidateR e p q C0) σ C).PosDef :=
  ((candidate_closure_certificate e P p q J C0 D σ hp hq hw hI h0 hD hσ).2.2
    C (subset_closure hC)).2.1

theorem candidate_certificate (e : InputCoordinates.Frame k)
    (P : InputCoordinates.Partition n g) (p q : Vec n) (J : Mat g k) (C0 : Mat n k)
    (D : Mat n n) (σ : ℝ) (hp : ∀ i, 0 < p i) (hq : ∀ i, 0 < q i)
    (hw : ∀ j, 0 < e.w j) (hI : ∀ j, 0 < Supply.totalInputs q (e.reconstruct p C0) j)
    (h0 : C0 ∈ e.Candidates p q P J) (hD : D.PosDef) (hσ : 0 < σ) :
    let hn := Supply.goods_nonempty_of_total_pos q (e.reconstruct p C0) hI
    let lam := demandLambda p q D hp hq hD hn
    let R := Supply.candidateR e p q C0
    0 < lam ∧ (min lam σ • R).PosDef ∧
      ∀ C ∈ e.Candidates p q P J,
        (K p q D R σ C - min lam σ • R).PosSemidef ∧
        (K p q D R σ C).PosDef ∧
        (K p q D R σ C).det ≠ 0 ∧
        K p q D R σ C * (K p q D R σ C)⁻¹ = 1 ∧
        (K p q D R σ C)⁻¹ * K p q D R σ C = 1 := by
  have hh := candidate_closure_certificate e P p q J C0 D σ hp hq hw hI h0 hD hσ
  exact ⟨hh.1, hh.2.1, fun C hC => hh.2.2 C (subset_closure hC)⟩

/-- The K_posDef condition of B.1 on an economic fiber. -/
theorem fixedAnswer_K_posDef_on (e : InputCoordinates.Frame k)
    (P : InputCoordinates.Partition n g) (p q : Vec n) (J : Mat g k) (Cref C0 : Mat n k)
    (D : Mat n n) (σ : ℝ) (b : Vec n) (N : Mat n r) (U : Set (Mat r k))
    (hp : ∀ i, 0 < p i) (hq : ∀ i, 0 < q i) (hw : ∀ j, 0 < e.w j)
    (hI : ∀ j, 0 < Supply.totalInputs q (e.reconstruct p Cref) j)
    (href : Cref ∈ e.Candidates p q P J) (hD : D.PosDef) (hσ : 0 < σ)
    (hU : ∀ Z ∈ U, C0 + N * Z ∈ e.Candidates p q P J) :
    let a := fixedAnswerData p q D (Supply.candidateR e p q Cref) σ b C0 N
    ∀ Z ∈ U, (a.K (a.point Z)).PosDef := by
  dsimp only
  intro Z hZ
  exact candidate_K_posDef e P p q J Cref (C0 + N * Z) D σ hp hq hw hI href
    (hU Z hZ) hD hσ

end CommodityClassification.Regularity
