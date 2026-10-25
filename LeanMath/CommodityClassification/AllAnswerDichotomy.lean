module

public import LeanMath.CommodityClassification.AllAnswerAffinePropagation

/-! All-answer dichotomy on a full open parent coordinate class. -/
@[expose] public section
noncomputable section
namespace CommodityClassification.FixedAnswer
open Matrix
variable {n k r s : ℕ}

def MomentsPreserved (a : Data n k r) (U : Mat n s)
    (J : Mat s r) (Ω : Set (Mat s k)) : Prop :=
  ∀ Y ∈ Ω, ∀ Z : Mat r k, Y + J*Z ∈ Ω →
    a.m ((a.withDirections U).point (Y+J*Z)) = a.m ((a.withDirections U).point Y) ∧
    a.K ((a.withDirections U).point (Y+J*Z)) = a.K ((a.withDirections U).point Y)

theorem AllAnswersIdentified.structural_coefficients (a : Data n k r)
    (U : Mat n s) (J : Mat s r) (Ω : Set (Mat s k))
    (h : AllAnswerHypotheses a U J Ω) (hc : AllAnswersIdentified a U J Ω)
    (hnc : ¬ (a.withDirections U).ConstantOn Ω) :
    a.r_N = 0 ∧ a.A_N = 0 ∧ a.S_NN = 0 ∧ a.N.transpose * a.L * U = 0 := by
  obtain ⟨Y,hY,hm⟩ := a.exists_nonzero_load_of_nonconstant U Ω h.parent.origin_mem hnc
  have hs := hc.nonzero_residuals a U J Ω h Y hY hm
  have ha := hc.all_loading_zero a U J Ω h hnc Y
  obtain ⟨hA,hS⟩ := hc.affine_loading_coefficients_zero a U J Ω h hnc Y hY hm
  refine ⟨?_,hA,?_,hS⟩
  · simpa only [Data.linearResidual,ha,zero_mulVec,sub_zero,Data.r_N] using hs.2
  · simpa only [Data.schur,ha,Matrix.zero_mul,sub_zero,Data.S_NN] using hs.1

theorem AllAnswersIdentified.separate_preservation (a : Data n k r)
    (U : Mat n s) (J : Mat s r) (Ω : Set (Mat s k))
    (h : AllAnswerHypotheses a U J Ω) (hc : AllAnswersIdentified a U J Ω)
    (hnc : ¬ (a.withDirections U).ConstantOn Ω) :
    MomentsPreserved a U J Ω := by
  obtain ⟨hr,hA,hS,hNU⟩ := hc.structural_coefficients a U J Ω h hnc
  intro Y _ Z _
  rw [← a.hidden_translation U J h.inclusion Y Z]
  have hAY : (a.atParent U Y).A_N = 0 := hc.all_loading_zero a U J Ω h hnc Y
  have hrY : (a.atParent U Y).r_N = 0 := hr
  have hSY : (a.atParent U Y).S_NN = 0 := hS
  constructor
  · change (a.atParent U Y).m ((a.atParent U Y).point Z) = (a.atParent U Y).m₀
    rw [(a.atParent U Y).m_point,hrY,mulVec_zero,add_zero]
  · change (a.atParent U Y).K ((a.atParent U Y).point Z) = (a.atParent U Y).K₀
    rw [(a.atParent U Y).K_point h.parent.L_symmetric,hAY,hSY]
    simp only [transpose_zero,Matrix.zero_mul,Matrix.mul_zero,add_zero]

theorem all_answer_dichotomy (a : Data n k r)
    (U : Mat n s) (J : Mat s r) (Ω : Set (Mat s k))
    (h : AllAnswerHypotheses a U J Ω) (hc : AllAnswersIdentified a U J Ω) :
    (a.withDirections U).ConstantOn Ω ∨ MomentsPreserved a U J Ω := by
  by_cases hp : (a.withDirections U).ConstantOn Ω
  · exact Or.inl hp
  · exact Or.inr (hc.separate_preservation a U J Ω h hp)

theorem moments_preserved_identifies (a : Data n k r)
    (U : Mat n s) (J : Mat s r) (Ω : Set (Mat s k))
    (h : MomentsPreserved a U J Ω) : AllAnswersIdentified a U J Ω := by
  intro Y hY Z hZ
  obtain ⟨hm,hK⟩ := h Y hY Z hZ
  simp only [Data.F,hm,hK]

theorem parent_constant_identifies (a : Data n k r)
    (U : Mat n s) (J : Mat s r) (Ω : Set (Mat s k))
    (h : (a.withDirections U).ConstantOn Ω) : AllAnswersIdentified a U J Ω := by
  intro Y hY Z hZ
  exact (h _ hZ).trans (h _ hY).symm

theorem all_answer_identification_iff (a : Data n k r)
    (U : Mat n s) (J : Mat s r) (Ω : Set (Mat s k))
    (h : AllAnswerHypotheses a U J Ω) :
    AllAnswersIdentified a U J Ω ↔
      (a.withDirections U).ConstantOn Ω ∨ MomentsPreserved a U J Ω := by
  constructor
  · exact all_answer_dichotomy a U J Ω h
  · rintro (hp|hm)
    · exact parent_constant_identifies a U J Ω hp
    · exact moments_preserved_identifies a U J Ω hm

theorem no_relative_directions_parent_constant (a : Data n 0 r)
    (U : Mat n s) (Ω : Set (Mat s 0)) : (a.withDirections U).ConstantOn Ω := by
  intro Y _
  simp only [Data.F,dotProduct,Finset.univ_eq_empty,Finset.sum_empty]

theorem no_hidden_directions_moments (a : Data n k 0)
    (U : Mat n s) (J : Mat s 0) (Ω : Set (Mat s k)) : MomentsPreserved a U J Ω := by
  intro Y _ Z _
  have hZ : Z = 0 := Subsingleton.elim _ _
  simp only [hZ,Matrix.mul_zero,add_zero,and_self]

theorem no_new_answers_parent_constant (a : Data n k r)
    (U : Mat n s) (J : Mat s r) (Ω : Set (Mat s k))
    (h0 : (0:Mat s k) ∈ Ω) (hJ : Function.Surjective (fun Z : Mat r k => J*Z))
    (hc : AllAnswersIdentified a U J Ω) : (a.withDirections U).ConstantOn Ω := by
  intro Y hY
  change a.F ((a.withDirections U).point Y) = a.F a.C₀
  obtain ⟨Z,hZ⟩ := hJ Y
  have hh := hc 0 h0 Z (by simpa only [zero_add,hZ] using hY)
  simpa only [zero_add,hZ,Data.point,Data.withDirections,Matrix.mul_zero,add_zero] using hh

end CommodityClassification.FixedAnswer
