module
public import LeanMath.CommodityClassification.SupplyCandidates
public import Mathlib.Analysis.Matrix.PosDef
public import Mathlib.Data.Finset.Lattice.Fold
public import Mathlib.Tactic.NoncommRing
@[expose] public section
set_option maxHeartbeats 1800000
namespace CommodityClassification.Regularity
open Matrix
open scoped BigOperators
abbrev Mat (n k : ℕ) := Matrix (Fin n) (Fin k) ℝ
abbrev Vec (n : ℕ) := Fin n → ℝ
variable {n : ℕ}

theorem fin_univ_nonempty (hn : 0 < n) : (Finset.univ : Finset (Fin n)).Nonempty :=
  ⟨⟨0, hn⟩, Finset.mem_univ _⟩

/-- The smallest real eigenvalue of the normalized demand matrix. -/
noncomputable def minEigen (B : Mat n n) (hB : B.IsHermitian) (hn : 0 < n) : ℝ :=
  Finset.univ.inf' (fin_univ_nonempty hn) hB.eigenvalues

theorem minEigen_le (B : Mat n n) (hB : B.IsHermitian) (hn : 0 < n) (i : Fin n) :
    minEigen B hB hn ≤ hB.eigenvalues i :=
  Finset.inf'_le _ (Finset.mem_univ i)

theorem minEigen_attained (B : Mat n n) (hB : B.IsHermitian) (hn : 0 < n) :
    ∃ i : Fin n, minEigen B hB hn = hB.eigenvalues i := by
  obtain ⟨i, _, hi⟩ := Finset.exists_mem_eq_inf' (fin_univ_nonempty hn) hB.eigenvalues
  exact ⟨i, hi⟩

theorem minEigen_mem_spectrum (B : Mat n n) (hB : B.IsHermitian) (hn : 0 < n) :
    minEigen B hB hn ∈ spectrum ℝ B := by
  obtain ⟨i, hi⟩ := minEigen_attained B hB hn
  rw [hi]
  exact hB.eigenvalues_mem_spectrum_real i

theorem minEigen_pos (B : Mat n n) (hB : B.PosDef) (hn : 0 < n) :
    0 < minEigen B hB.isHermitian hn := by
  obtain ⟨i, hi⟩ := minEigen_attained B hB.isHermitian hn
  rw [hi]
  exact hB.eigenvalues_pos i

theorem minEigen_isLeast_spectrum (B : Mat n n) (hB : B.IsHermitian) (hn : 0 < n) :
    IsLeast (spectrum ℝ B) (minEigen B hB hn) := by
  refine ⟨minEigen_mem_spectrum B hB hn, ?_⟩
  intro x hx
  rw [hB.spectrum_real_eq_range_eigenvalues] at hx
  obtain ⟨i, rfl⟩ := hx
  exact minEigen_le B hB hn i

theorem spectral_lower_bound (B : Mat n n) (hB : B.IsHermitian) (hn : 0 < n) :
    (B - minEigen B hB hn • (1 : Mat n n)).PosSemidef := by
  let a := minEigen B hB hn
  have hd : (diagonal (fun i => hB.eigenvalues i - a)).PosSemidef :=
    Matrix.PosSemidef.diagonal (fun i => sub_nonneg.mpr (minEigen_le B hB hn i))
  have hh := hd.mul_mul_conjTranspose_same (hB.eigenvectorUnitary : Mat n n)
  have he : diagonal (fun i => hB.eigenvalues i - a) =
      diagonal hB.eigenvalues - a • (1 : Mat n n) := by
    ext i j
    by_cases hij : i = j <;> simp [hij]
  rw [he] at hh
  have hs : B = (hB.eigenvectorUnitary : Mat n n) * diagonal hB.eigenvalues *
      star (hB.eigenvectorUnitary : Mat n n) := by
    simpa [Unitary.conjStarAlgAut_apply] using hB.spectral_theorem
  have hu : (hB.eigenvectorUnitary : Mat n n) * star (hB.eigenvectorUnitary : Mat n n) = 1 := by
    simpa only [Unitary.coe_star] using Unitary.coe_mul_star_self hB.eigenvectorUnitary
  simpa only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.smul_mul,
    Matrix.mul_one, ← Matrix.star_eq_conjTranspose, ← hs, hu] using hh

/-- Positive square root of Xi and its inverse. -/
noncomputable def rootXi (p q : Vec n) : Mat n n := diagonal (fun i => Real.sqrt (q i / p i))
noncomputable def invRootXi (p q : Vec n) : Mat n n :=
  diagonal (fun i => (Real.sqrt (q i / p i))⁻¹)
noncomputable def normalizedDemand (p q : Vec n) (D : Mat n n) : Mat n n :=
  invRootXi p q * D * invRootXi p q

theorem xi_posDef (p q : Vec n) (hp : ∀ i, 0 < p i) (hq : ∀ i, 0 < q i) :
    (Supply.xi p q).PosDef := Matrix.PosDef.diagonal (fun i => div_pos (hq i) (hp i))

theorem invRootXi_explicit (p q : Vec n) :
    invRootXi p q = diagonal (fun i => Real.sqrt (p i / q i)) := by
  simp [invRootXi, ← Real.sqrt_inv, inv_div]

theorem rootXi_sq (p q : Vec n) (hp : ∀ i, 0 < p i) (hq : ∀ i, 0 < q i) :
    rootXi p q * rootXi p q = Supply.xi p q := by
  rw [rootXi, Matrix.diagonal_mul_diagonal]
  congr 1
  funext i
  exact Real.mul_self_sqrt (le_of_lt (div_pos (hq i) (hp i)))

theorem rootXi_invRootXi (p q : Vec n) (hp : ∀ i, 0 < p i) (hq : ∀ i, 0 < q i) :
    rootXi p q * invRootXi p q = 1 := by
  simp only [rootXi, invRootXi, Matrix.diagonal_mul_diagonal]
  have he : (fun i => Real.sqrt (q i / p i) * (Real.sqrt (q i / p i))⁻¹) =
      (fun _ : Fin n => (1 : ℝ)) := by
    funext i
    exact mul_inv_cancel₀ (ne_of_gt (Real.sqrt_pos.mpr (div_pos (hq i) (hp i))))
  rw [he, Matrix.diagonal_one]

theorem invRootXi_rootXi (p q : Vec n) (hp : ∀ i, 0 < p i) (hq : ∀ i, 0 < q i) :
    invRootXi p q * rootXi p q = 1 := by
  simpa only [rootXi, invRootXi, Matrix.diagonal_mul_diagonal, mul_comm] using
    rootXi_invRootXi p q hp hq

theorem invRootXi_xi_invRootXi (p q : Vec n) (hp : ∀ i, 0 < p i) (hq : ∀ i, 0 < q i) :
    invRootXi p q * Supply.xi p q * invRootXi p q = 1 := by
  rw [← rootXi_sq p q hp hq, ← Matrix.mul_assoc, invRootXi_rootXi p q hp hq,
    Matrix.one_mul, rootXi_invRootXi p q hp hq]

theorem invRootXi_posDef (p q : Vec n) (hp : ∀ i, 0 < p i) (hq : ∀ i, 0 < q i) :
    (invRootXi p q).PosDef :=
  Matrix.PosDef.diagonal (fun i => inv_pos.mpr (Real.sqrt_pos.mpr (div_pos (hq i) (hp i))))

theorem normalizedDemand_posDef (p q : Vec n) (D : Mat n n)
    (hp : ∀ i, 0 < p i) (hq : ∀ i, 0 < q i) (hD : D.PosDef) :
    (normalizedDemand p q D).PosDef := by
  have hh := hD.conjTranspose_mul_mul_same (invRootXi_posDef p q hp hq).mulVec_injective
  simpa [normalizedDemand, invRootXi] using hh

noncomputable def demandLambda (p q : Vec n) (D : Mat n n)
    (hp : ∀ i, 0 < p i) (hq : ∀ i, 0 < q i) (hD : D.PosDef) (hn : 0 < n) : ℝ :=
  minEigen (normalizedDemand p q D) (normalizedDemand_posDef p q D hp hq hD).isHermitian hn

theorem demandLambda_pos (p q : Vec n) (D : Mat n n)
    (hp : ∀ i, 0 < p i) (hq : ∀ i, 0 < q i) (hD : D.PosDef) (hn : 0 < n) :
    0 < demandLambda p q D hp hq hD hn :=
  minEigen_pos _ (normalizedDemand_posDef p q D hp hq hD) hn

theorem demandLambda_isLeast_spectrum (p q : Vec n) (D : Mat n n)
    (hp : ∀ i, 0 < p i) (hq : ∀ i, 0 < q i) (hD : D.PosDef) (hn : 0 < n) :
    IsLeast (spectrum ℝ (normalizedDemand p q D)) (demandLambda p q D hp hq hD hn) :=
  minEigen_isLeast_spectrum _ (normalizedDemand_posDef p q D hp hq hD).isHermitian hn

theorem unnormalizeDemand (p q : Vec n) (D : Mat n n)
    (hp : ∀ i, 0 < p i) (hq : ∀ i, 0 < q i) :
    rootXi p q * normalizedDemand p q D * rootXi p q = D := by
  calc
    _ = (rootXi p q * invRootXi p q) * D * (invRootXi p q * rootXi p q) := by
      simp only [normalizedDemand, Matrix.mul_assoc]
    _ = D := by rw [rootXi_invRootXi p q hp hq, invRootXi_rootXi p q hp hq,
      Matrix.one_mul, Matrix.mul_one]

theorem demand_lower_bound (p q : Vec n) (D : Mat n n)
    (hp : ∀ i, 0 < p i) (hq : ∀ i, 0 < q i) (hD : D.PosDef) (hn : 0 < n) :
    (D - demandLambda p q D hp hq hD hn • Supply.xi p q).PosSemidef := by
  have hb := spectral_lower_bound (normalizedDemand p q D)
    (normalizedDemand_posDef p q D hp hq hD).isHermitian hn
  have hh := hb.conjTranspose_mul_mul_same (rootXi p q)
  have he : (rootXi p q).conjTranspose = rootXi p q := by simp [rootXi]
  rw [he, Matrix.mul_sub, Matrix.sub_mul, unnormalizeDemand p q D hp hq,
    Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, rootXi_sq p q hp hq] at hh
  exact hh

end CommodityClassification.Regularity
