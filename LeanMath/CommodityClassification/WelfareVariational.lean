module
public import LeanMath.CommodityClassification.WelfareExpansionApplication
@[expose] public section
set_option maxHeartbeats 2000000
namespace CommodityClassification.Equilibrium
open Matrix
open scoped BigOperators
variable {n k : ℕ}
namespace Model
variable (E : Model n k)

/-- The manuscript's projected production substitution, using the existing definition. -/
noncomputable def substitutionMatrix : Mat k k :=
  Supply.substitution E.sigma E.R E.p E.q E.C

/-- The variational objective; the variable is a relative-price derivative. -/
noncomputable def adjustmentObjective (z : Vec k) : ℝ :=
  dotProduct (E.b+E.C *ᵥ z) (E.D *ᵥ (E.b+E.C *ᵥ z)) +
    dotProduct z (E.substitutionMatrix *ᵥ z)

theorem K_eq_demand_substitution : E.K = E.C.transpose * E.D * E.C + E.substitutionMatrix :=
  Regularity.K_eq_demand_add_substitution E.p E.q E.D E.R E.sigma E.C

theorem K_quadratic (z : Vec k) :
    dotProduct z (E.K *ᵥ z) =
      dotProduct (E.C *ᵥ z) (E.D *ᵥ (E.C *ᵥ z)) + dotProduct z (E.substitutionMatrix *ᵥ z) := by
  rw [E.K_eq_demand_substitution]
  simp only [Matrix.add_mulVec,←Matrix.mulVec_mulVec,dotProduct_add]
  rw [Matrix.dotProduct_transpose_mulVec,dotProduct_comm (E.D *ᵥ (E.C *ᵥ z))]

theorem adjustmentObjective_expansion (hD : E.D.PosDef) (z : Vec k) :
    E.adjustmentObjective z = dotProduct E.b (E.D *ᵥ E.b) +
      2 * dotProduct E.m z + dotProduct z (E.K *ᵥ z) := by
  have hx : dotProduct (E.C *ᵥ z) (E.D *ᵥ E.b) = dotProduct E.m z := by
    rw [hD.isHermitian.isSymm.dotProduct_mulVec_comm]
    exact E.demand_cross_moment hD z
  simp only [adjustmentObjective,Matrix.mulVec_add,add_dotProduct,dotProduct_add,
    hx,E.demand_cross_moment hD z,E.K_quadratic z]
  ring

theorem lossCoefficient_eq_value_linear :
    E.lossCoefficient = dotProduct E.b (E.D *ᵥ E.b) + dotProduct E.m E.zSolution := by
  simp only [lossCoefficient,zSolution,dotProduct_neg,sub_eq_add_neg]

theorem adjustmentObjective_complete_square (hD : E.D.PosDef) (hK : E.K.PosDef) (z : Vec k) :
    E.adjustmentObjective z = E.lossCoefficient +
      dotProduct (z-E.zSolution) (E.K *ᵥ (z-E.zSolution)) := by
  have hc : dotProduct E.zSolution (E.K *ᵥ z) = -dotProduct z E.m := by
    rw [hK.isHermitian.isSymm.dotProduct_mulVec_comm,E.K_zSolution hK,dotProduct_neg]
  rw [E.adjustmentObjective_expansion hD z,E.lossCoefficient_eq_value_linear]
  simp only [Matrix.mulVec_sub,dotProduct_sub,sub_dotProduct,E.K_zSolution hK,
    dotProduct_neg,hc]
  rw [dotProduct_comm z E.m,dotProduct_comm E.zSolution E.m]
  ring

theorem adjustmentObjective_at_solution (hD : E.D.PosDef) (hK : E.K.PosDef) :
    E.adjustmentObjective E.zSolution = E.lossCoefficient := by
  simp [E.adjustmentObjective_complete_square hD hK]

theorem adjustmentObjective_lower (hD : E.D.PosDef) (hK : E.K.PosDef) (z : Vec k) :
    E.lossCoefficient ≤ E.adjustmentObjective z := by
  rw [E.adjustmentObjective_complete_square hD hK]
  have hh := hK.posSemidef.dotProduct_mulVec_nonneg (z-E.zSolution)
  simpa only [star_trivial,le_add_iff_nonneg_right] using hh

theorem adjustmentObjective_strict (hD : E.D.PosDef) (hK : E.K.PosDef)
    (z : Vec k) (hz : z ≠ E.zSolution) : E.lossCoefficient < E.adjustmentObjective z := by
  rw [E.adjustmentObjective_complete_square hD hK]
  have hh := hK.dotProduct_mulVec_pos (sub_ne_zero.mpr hz)
  simpa only [star_trivial,lt_add_iff_pos_right] using hh

theorem adjustmentObjective_eq_iff (hD : E.D.PosDef) (hK : E.K.PosDef) (z : Vec k) :
    E.adjustmentObjective z = E.lossCoefficient ↔ z = E.zSolution := by
  constructor
  · intro hh
    by_contra hz
    have hs := E.adjustmentObjective_strict hD hK z hz
    linarith
  · rintro rfl
    exact E.adjustmentObjective_at_solution hD hK

theorem adjustmentObjective_isLeast (hD : E.D.PosDef) (hK : E.K.PosDef) :
    IsLeast (Set.range E.adjustmentObjective) E.lossCoefficient := by
  refine ⟨⟨E.zSolution,E.adjustmentObjective_at_solution hD hK⟩,?_⟩
  rintro _ ⟨z,rfl⟩
  exact E.adjustmentObjective_lower hD hK z

theorem adjustmentObjective_unique_minimizer (hD : E.D.PosDef) (hK : E.K.PosDef) :
    ∃! z, ∀ y, E.adjustmentObjective z ≤ E.adjustmentObjective y := by
  refine ⟨E.zSolution,?_,?_⟩
  · intro y
    rw [E.adjustmentObjective_at_solution hD hK]
    exact E.adjustmentObjective_lower hD hK y
  · intro z hz
    apply (E.adjustmentObjective_eq_iff hD hK z).mp
    apply le_antisymm
    · simpa only [E.adjustmentObjective_at_solution hD hK] using hz E.zSolution
    · exact E.adjustmentObjective_lower hD hK z

end Model
end CommodityClassification.Equilibrium
