module

public import LeanMath.CommodityClassification.UnknownSigmaWorstWidth

/-! Unrestricted scalar minimax recovery on bounded nonempty sets, including unattained endpoints. -/
@[expose] public section
noncomputable section
namespace CommodityClassification.Information

def valueMidpoint (S : Set ℝ) : ℝ := (sSup S+sInf S)/2
def maximalError (S : Set ℝ) (a : ℝ) : ℝ := sSup ((fun x => |a-x|) '' S)

theorem midpoint_error_bound (S : Set ℝ) (hu : BddAbove S) (hl : BddBelow S)
    (x : ℝ) (hx : x∈S) : |valueMidpoint S-x|≤setWidth S/2 := by
  have h1 := csInf_le hl hx
  have h2 := le_csSup hu hx
  unfold valueMidpoint setWidth
  exact abs_le.mpr ⟨by linarith,by linarith⟩

theorem error_values_bddAbove (S : Set ℝ) (hu : BddAbove S) (hl : BddBelow S) (a : ℝ) :
    BddAbove ((fun x => |a-x|) '' S) := by
  refine ⟨|a-valueMidpoint S|+setWidth S/2,?_⟩
  rintro z ⟨x,hx,rfl⟩
  calc
    |a-x|≤|a-valueMidpoint S|+|valueMidpoint S-x| := abs_sub_le _ _ _
    _≤|a-valueMidpoint S|+setWidth S/2 := by linarith [midpoint_error_bound S hu hl x hx]

theorem error_le_maximalError (S : Set ℝ) (hu : BddAbove S) (hl : BddBelow S)
    (a x : ℝ) (hx : x∈S) : |a-x|≤maximalError S a :=
  le_csSup (error_values_bddAbove S hu hl a) ⟨x,hx,rfl⟩

theorem half_width_le_maximalError (S : Set ℝ) (hne : S.Nonempty)
    (hu : BddAbove S) (hl : BddBelow S) (a : ℝ) : setWidth S/2≤maximalError S a := by
  have hh : setWidth S≤2*maximalError S a := by
    apply (setWidth_le_iff S hne hu hl _).mpr
    intro x hx y hy
    have h1 := error_le_maximalError S hu hl a x hx
    have h2 := error_le_maximalError S hu hl a y hy
    have ht := abs_sub_le x a y
    rw [abs_sub_comm x a] at ht
    linarith
  linarith

theorem midpoint_maximalError (S : Set ℝ) (hne : S.Nonempty)
    (hu : BddAbove S) (hl : BddBelow S) : maximalError S (valueMidpoint S)=setWidth S/2 := by
  apply le_antisymm _ (half_width_le_maximalError S hne hu hl _)
  apply csSup_le (hne.image _)
  rintro z ⟨x,hx,rfl⟩
  exact midpoint_error_bound S hu hl x hx

theorem maximalError_isLeast (S : Set ℝ) (hne : S.Nonempty)
    (hu : BddAbove S) (hl : BddBelow S) :
    IsLeast (maximalError S '' Set.univ) (setWidth S/2) := by
  refine ⟨⟨valueMidpoint S,Set.mem_univ _,midpoint_maximalError S hne hu hl⟩,?_⟩
  rintro r ⟨a,_,rfl⟩
  exact half_width_le_maximalError S hne hu hl a

end CommodityClassification.Information
