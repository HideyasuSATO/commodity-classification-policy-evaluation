module

public import LeanMath.CommodityClassification.SeparateMomentNecessity

/-! Linear structural restrictions are sufficient as well as necessary for m,K. -/
@[expose] public section
noncomputable section
namespace CommodityClassification.FixedAnswer
open Matrix
variable {n k r s : ℕ}

theorem Data.moments_preserved_of_linear_coefficients (a : Data n k r)
    (U : Mat n s) (J : Mat s r) (Ω : Set (Mat s k))
    (hL : a.L.transpose=a.L) (hN : a.N=U*J)
    (hr : a.r_N=0) (hA : a.A_N=0) (hNU : a.N.transpose*a.L*U=0) :
    MomentsPreserved a U J Ω := by
  have hS : a.S_NN=0 := by
    change a.N.transpose*a.L*a.N=0
    rw [hN,← Matrix.mul_assoc]
    have hh : (U*J).transpose*a.L*U=0 := by rwa [hN] at hNU
    rw [hh,Matrix.zero_mul]
  intro Y _ Z _
  rw [← a.hidden_translation U J hN Y Z]
  have hAY : (a.atParent U Y).A_N=0 := by
    change a.N.transpose*a.L*(a.C₀+U*Y)=0
    rw [Matrix.mul_add,← Matrix.mul_assoc,hNU,Matrix.zero_mul,add_zero]
    exact hA
  have hrY : (a.atParent U Y).r_N=0 := hr
  have hSY : (a.atParent U Y).S_NN=0 := hS
  constructor
  · change (a.atParent U Y).m ((a.atParent U Y).point Z)=(a.atParent U Y).m₀
    rw [(a.atParent U Y).m_point,hrY,mulVec_zero,add_zero]
  · change (a.atParent U Y).K ((a.atParent U Y).point Z)=(a.atParent U Y).K₀
    rw [(a.atParent U Y).K_point hL,hAY,hSY]
    simp only [transpose_zero,Matrix.zero_mul,Matrix.mul_zero,add_zero]

theorem moments_preserved_iff_linear_coefficients (a : Data n k r)
    (U : Mat n s) (J : Mat s r) (Ω : Set (Mat s k))
    (h : AllAnswerHypotheses a U J Ω) :
    MomentsPreserved a U J Ω ↔ a.r_N=0 ∧ a.A_N=0 ∧ a.N.transpose*a.L*U=0 := by
  constructor
  · exact fun hc => hc.linear_coefficients a U J Ω h
  · rintro ⟨hr,hA,hNU⟩
    exact a.moments_preserved_of_linear_coefficients U J Ω h.parent.L_symmetric h.inclusion hr hA hNU

end CommodityClassification.FixedAnswer
