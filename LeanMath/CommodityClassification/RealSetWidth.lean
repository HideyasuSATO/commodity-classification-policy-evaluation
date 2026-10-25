module

public import LeanMath.CommodityClassification.RobustFamilyPerturbation

/-! Supremum-minus-infimum width of a nonempty bounded real value set. -/
@[expose] public section
noncomputable section
namespace CommodityClassification.Information

def setWidth (S : Set ℝ) : ℝ := sSup S-sInf S

theorem setWidth_nonneg (S : Set ℝ) (hne : S.Nonempty) (hu : BddAbove S) (hl : BddBelow S) :
    0≤setWidth S := by
  obtain ⟨x,hx⟩ := hne
  have h1 := csInf_le hl hx
  have h2 := le_csSup hu hx
  unfold setWidth
  linarith

theorem pair_le_setWidth (S : Set ℝ) (hu : BddAbove S) (hl : BddBelow S)
    (x y : ℝ) (hx : x∈S) (hy : y∈S) : |x-y|≤setWidth S := by
  have hxl := csInf_le hl hx
  have hxu := le_csSup hu hx
  have hyl := csInf_le hl hy
  have hyu := le_csSup hu hy
  unfold setWidth
  apply abs_le.mpr
  constructor <;> linarith

theorem setWidth_le_iff (S : Set ℝ) (hne : S.Nonempty) (hu : BddAbove S) (hl : BddBelow S)
    (eps : ℝ) : setWidth S≤eps ↔ ∀x∈S,∀y∈S,|x-y|≤eps := by
  constructor
  · intro he x hx y hy
    exact (pair_le_setWidth S hu hl x y hx hy).trans he
  · intro hh
    have hsup : sSup S≤sInf S+eps := by
      apply csSup_le hne
      intro x hx
      have hlow : x-eps≤sInf S := by
        apply le_csInf hne
        intro y hy
        have hp := (le_abs_self (x-y)).trans (hh x hx y hy)
        linarith
      linarith
    unfold setWidth
    linarith

theorem setWidth_mono {S T : Set ℝ} (hS : S.Nonempty) (hST : S⊆T)
    (hu : BddAbove T) (hl : BddBelow T) : setWidth S≤setWidth T := by
  apply (setWidth_le_iff S hS (hu.mono hST) (hl.mono hST) _).mpr
  intro x hx y hy
  exact pair_le_setWidth T hu hl x y (hST hx) (hST hy)

end CommodityClassification.Information
