module

public import LeanMath.CommodityClassification.FixedAnswerNecessity

/-!
# Lemma B.1: local equivalence and global extension




-/
public section
namespace CommodityClassification.FixedAnswer
open Matrix
variable {n k r : ℕ}

/-- Necessity of both moment identities in the nonzero-load branch. -/
theorem nonzeroLoad_necessary (a : Data n k r) (U : Set (Mat r k))
    (h : a.Hypotheses U) (hm : a.m₀ ≠ 0) (hc : a.ConstantOn U) :
    a.r_N = a.A_N *ᵥ a.y₀ ∧ a.S_NN = a.A_N * a.K₀⁻¹ * a.A_N.transpose :=
  ⟨firstMoment_of_constant_nonzero a U h hc hm,
    secondMoment_of_constant_nonzero a U h hc hm⟩

/-- The complete nonzero-load equivalence on the originally specified open set. -/
theorem nonzeroLoad_constantOn_iff (a : Data n k r) (U : Set (Mat r k))
    (h : a.Hypotheses U) (hm : a.m₀ ≠ 0) :
    a.ConstantOn U ↔
      a.r_N = a.A_N *ᵥ a.y₀ ∧ a.S_NN = a.A_N * a.K₀⁻¹ * a.A_N.transpose := by
  constructor
  · exact nonzeroLoad_necessary a U h hm
  · rintro ⟨hr,hS⟩ Z hZ
    exact congruence_sufficient_global a U h hr hS Z (h.K_posDef Z hZ)

/-- The zero-load sufficient condition extends to all coordinates. -/
theorem zeroLoad_constantOn_global (a : Data n k r) (hm : a.m₀ = 0) (hr : a.r_N = 0) :
    a.ConstantOn a.AdmissibleCoordinates := by
  intro Z _
  have hmZ : a.m (a.point Z) = 0 := by simp only [a.m_point, hm, hr, mulVec_zero, add_zero]
  have hF0 : a.F a.C₀ = 0 := by
    change dotProduct a.m₀ (a.K₀⁻¹ *ᵥ a.m₀) = 0
    simp only [hm, mulVec_zero, dotProduct_zero]
  rw [hF0]
  simp only [Data.F, hmZ, mulVec_zero, dotProduct_zero]

/-- B1.LOCAL, as a proof of the unchanged stage-1 proposition. -/
theorem lemmaB1_local (a : Data n k r) (U : Set (Mat r k)) :
    LemmaB1LocalStatement a U := by
  intro h
  constructor
  · intro hc
    by_cases hm : a.m₀ = 0
    · exact Or.inl ⟨hm, (zeroLoad_constantOn_iff a U h hm).mp hc⟩
    · exact Or.inr ⟨hm, nonzeroLoad_necessary a U h hm hc⟩
  · rintro (⟨hm,hr⟩ | ⟨hm,hr,hS⟩)
    · exact (zeroLoad_constantOn_iff a U h hm).mpr hr
    · exact (nonzeroLoad_constantOn_iff a U h hm).mpr ⟨hr,hS⟩

/-- B1.GLOBAL: all SPD points on the affine fiber, even outside the open neighborhood. -/
theorem lemmaB1_global (a : Data n k r) (U : Set (Mat r k)) :
    LemmaB1GlobalStatement a U := by
  intro h hc
  rcases hc with ⟨hm,hr⟩ | ⟨_hm,hr,hS⟩
  · exact zeroLoad_constantOn_global a hm hr
  · exact congruence_sufficient_global a U h hr hS

/-- Universal closure of both parts of the original Lemma B.1 target. -/
theorem lemmaB1_proved : LemmaB1Statement := by
  intro n k r a U
  exact ⟨lemmaB1_local a U, lemmaB1_global a U⟩

/-- Explicit degenerate-dimension specialization, with no condition on the load. -/
theorem constantOn_noHiddenDirections (a : Data n k 0) (U : Set (Mat 0 k)) :
    a.ConstantOn U := by
  intro Z _
  have hZ : Z = 0 := Subsingleton.elim _ _
  simp only [hZ, Data.point, Matrix.mul_zero, add_zero]

end CommodityClassification.FixedAnswer
