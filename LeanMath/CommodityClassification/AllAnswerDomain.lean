module

public import LeanMath.CommodityClassification.AllAnswerLinearResidual
public import LeanMath.CommodityClassification.FixedAnswerComplete

/-! The full parent domain and its actual hidden-answer fibers. -/
@[expose] public section
noncomputable section
namespace CommodityClassification.FixedAnswer
open Matrix Filter
open scoped BigOperators Topology
variable {n k r s : ℕ}

def Data.atMatrix (a : Data n k r) (C : Mat n k) : Data n k r :=
  ⟨a.base,a.L,a.d,C,a.N⟩

def Data.atParent (a : Data n k r) (U : Mat n s) (Y : Mat s k) : Data n k r :=
  a.atMatrix ((a.withDirections U).point Y)

def hiddenDomain (Ω : Set (Mat s k)) (J : Mat s r) (Y : Mat s k) : Set (Mat r k) :=
  {Z | Y + J * Z ∈ Ω}

def translatedDomain (Ω : Set (Mat s k)) (Y : Mat s k) : Set (Mat s k) :=
  {Z | Y + Z ∈ Ω}

structure AllAnswerHypotheses (a : Data n k r) (U : Mat n s)
    (J : Mat s r) (Ω : Set (Mat s k)) : Prop where
  parent : (a.withDirections U).Hypotheses Ω
  hidden_independent : Function.Injective (fun z : Vec r => a.N *ᵥ z)
  inclusion : a.N = U * J

def AllAnswersIdentified (a : Data n k r) (U : Mat n s)
    (J : Mat s r) (Ω : Set (Mat s k)) : Prop :=
  ∀ Y ∈ Ω, ∀ Z : Mat r k, Y + J * Z ∈ Ω →
    a.F ((a.withDirections U).point (Y + J * Z)) = a.F ((a.withDirections U).point Y)

theorem Data.atMatrix_K (a : Data n k r) (C B : Mat n k) :
    (a.atMatrix C).K B = a.K B := rfl

theorem Data.atMatrix_m (a : Data n k r) (C B : Mat n k) :
    (a.atMatrix C).m B = a.m B := rfl

theorem Data.atMatrix_F (a : Data n k r) (C B : Mat n k) :
    (a.atMatrix C).F B = a.F B := rfl

theorem Data.parent_translation (a : Data n k r) (U : Mat n s) (Y Z : Mat s k) :
    ((a.atParent U Y).withDirections U).point Z = (a.withDirections U).point (Y+Z) := by
  simp only [Data.atParent,Data.atMatrix,Data.withDirections,Data.point,Matrix.mul_add]
  abel

theorem Data.hidden_translation (a : Data n k r) (U : Mat n s) (J : Mat s r)
    (hN : a.N = U * J) (Y : Mat s k) (Z : Mat r k) :
    (a.atParent U Y).point Z = (a.withDirections U).point (Y + J * Z) := by
  simp only [Data.atParent,Data.atMatrix,Data.withDirections,Data.point,hN,
    Matrix.mul_add,Matrix.mul_assoc]
  abel

theorem AllAnswerHypotheses.hidden_hypotheses (a : Data n k r)
    (U : Mat n s) (J : Mat s r) (Ω : Set (Mat s k))
    (h : AllAnswerHypotheses a U J Ω) (Y : Mat s k) (hY : Y ∈ Ω) :
    (a.atParent U Y).Hypotheses (hiddenDomain Ω J Y) := by
  refine ⟨h.parent.relative_dimension_positive,h.parent.base_symmetric,
    h.parent.L_symmetric,h.hidden_independent,?_,?_,?_⟩
  · exact h.parent.domain_open.preimage
      (continuous_const.add (continuous_const.matrix_mul continuous_id))
  · simpa only [hiddenDomain,Set.mem_ofPred_eq,Matrix.mul_zero,add_zero] using hY
  · intro Z hZ
    rw [a.hidden_translation U J h.inclusion Y Z]
    exact h.parent.K_posDef _ hZ

theorem AllAnswerHypotheses.parent_hypotheses (a : Data n k r)
    (U : Mat n s) (J : Mat s r) (Ω : Set (Mat s k))
    (h : AllAnswerHypotheses a U J Ω) (Y : Mat s k) (hY : Y ∈ Ω) :
    ((a.atParent U Y).withDirections U).Hypotheses (translatedDomain Ω Y) := by
  refine ⟨h.parent.relative_dimension_positive,h.parent.base_symmetric,
    h.parent.L_symmetric,h.parent.directions_independent,?_,?_,?_⟩
  · exact h.parent.domain_open.preimage (continuous_const.add continuous_id)
  · simpa only [translatedDomain,Set.mem_ofPred_eq,add_zero] using hY
  · intro Z hZ
    rw [a.parent_translation U Y Z]
    exact h.parent.K_posDef _ hZ

theorem AllAnswersIdentified.hidden_constant (a : Data n k r)
    (U : Mat n s) (J : Mat s r) (Ω : Set (Mat s k))
    (hN : a.N = U * J) (hc : AllAnswersIdentified a U J Ω)
    (Y : Mat s k) (hY : Y ∈ Ω) :
    (a.atParent U Y).ConstantOn (hiddenDomain Ω J Y) := by
  intro Z hZ
  rw [a.hidden_translation U J hN Y Z]
  exact hc Y hY Z hZ

theorem AllAnswersIdentified.nonzero_residuals (a : Data n k r)
    (U : Mat n s) (J : Mat s r) (Ω : Set (Mat s k))
    (h : AllAnswerHypotheses a U J Ω) (hc : AllAnswersIdentified a U J Ω)
    (Y : Mat s k) (hY : Y ∈ Ω) (hm : a.m ((a.withDirections U).point Y) ≠ 0) :
    a.schur a.N a.N ((a.withDirections U).point Y) = 0 ∧
      a.linearResidual a.N ((a.withDirections U).point Y) = 0 := by
  have hs := nonzeroLoad_necessary (a.atParent U Y) (hiddenDomain Ω J Y)
    (h.hidden_hypotheses a U J Ω Y hY) hm
    (hc.hidden_constant a U J Ω h.inclusion Y hY)
  exact ⟨sub_eq_zero.mpr hs.2,sub_eq_zero.mpr hs.1⟩

end CommodityClassification.FixedAnswer
