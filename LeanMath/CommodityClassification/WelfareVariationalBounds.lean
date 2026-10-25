module
public import LeanMath.CommodityClassification.WelfareVariational
@[expose] public section
set_option maxHeartbeats 2000000
namespace CommodityClassification.Equilibrium
open Matrix
open scoped BigOperators
variable {n k g : ℕ}
namespace Model
variable (E : Model n k)

theorem adjustmentObjective_zero : E.adjustmentObjective 0 = dotProduct E.b (E.D *ᵥ E.b) := by
  simp [adjustmentObjective]

theorem adjustmentObjective_nonneg (hD : E.D.PosDef) (hT : E.substitutionMatrix.PosSemidef)
    (z : Vec k) : 0 ≤ E.adjustmentObjective z := by
  have hd := hD.posSemidef.dotProduct_mulVec_nonneg (E.b+E.C *ᵥ z)
  have ht := hT.dotProduct_mulVec_nonneg z
  simp only [star_trivial] at hd ht
  exact add_nonneg hd ht

theorem lossCoefficient_nonneg (hD : E.D.PosDef) (hK : E.K.PosDef)
    (hT : E.substitutionMatrix.PosSemidef) : 0 ≤ E.lossCoefficient := by
  rw [←E.adjustmentObjective_at_solution hD hK]
  exact E.adjustmentObjective_nonneg hD hT E.zSolution

theorem lossCoefficient_le_demand (hD : E.D.PosDef) (hK : E.K.PosDef) :
    E.lossCoefficient ≤ dotProduct E.b (E.D *ᵥ E.b) := by
  simpa only [E.adjustmentObjective_zero] using E.adjustmentObjective_lower hD hK 0

theorem adjustmentObjective_pos (hD : E.D.PosDef) (hT : E.substitutionMatrix.PosDef)
    (hb : E.b ≠ 0) (z : Vec k) : 0 < E.adjustmentObjective z := by
  by_cases hz : z=0
  · subst z
    rw [E.adjustmentObjective_zero]
    simpa only [star_trivial] using hD.dotProduct_mulVec_pos hb
  · have hd := hD.posSemidef.dotProduct_mulVec_nonneg (E.b+E.C *ᵥ z)
    have ht := hT.dotProduct_mulVec_pos hz
    simp only [star_trivial] at hd ht
    exact add_pos_of_nonneg_of_pos hd ht

theorem lossCoefficient_pos (hD : E.D.PosDef) (hK : E.K.PosDef)
    (hT : E.substitutionMatrix.PosDef) (hb : E.b ≠ 0) : 0 < E.lossCoefficient := by
  rw [←E.adjustmentObjective_at_solution hD hK]
  exact E.adjustmentObjective_pos hD hT hb E.zSolution

theorem substitutionMatrix_posDef (P : InputCoordinates.Partition n g) (J : Mat g k)
    (hreport : P.report E.q E.C=J) (hq : ∀ i, 0 < E.q i)
    (hI : ∀ j, 0 < Supply.totalInputs E.q E.A j) (hσ : 0 < E.sigma) :
    E.substitutionMatrix.PosDef :=
  Supply.candidate_substitution_posDef E.frame P E.p E.q J E.C E.C E.hp hq E.hw hI
    ⟨E.hC,hreport⟩ ⟨E.hC,hreport⟩ E.sigma hσ

/-- Variational representation and bounds for the welfare coefficient. -/
def VariationalCertificate : Prop :=
  IsLeast (Set.range E.adjustmentObjective) E.lossCoefficient ∧
  (∀ z, E.adjustmentObjective z=E.lossCoefficient ↔ z=E.zSolution) ∧
  0 ≤ E.lossCoefficient ∧ E.lossCoefficient ≤ dotProduct E.b (E.D *ᵥ E.b) ∧
  (E.b ≠ 0 → 0 < E.lossCoefficient)

theorem economic_variational_certificate (P : InputCoordinates.Partition n g) (J : Mat g k)
    (hreport : P.report E.q E.C=J) (hq : ∀ i, 0 < E.q i)
    (hI : ∀ j, 0 < Supply.totalInputs E.q E.A j) (hD : E.D.PosDef) (hσ : 0 < E.sigma) :
    E.VariationalCertificate := by
  have hK := E.K_posDef P J hreport hq hI hD hσ
  have hT := E.substitutionMatrix_posDef P J hreport hq hI hσ
  exact ⟨E.adjustmentObjective_isLeast hD hK,E.adjustmentObjective_eq_iff hD hK,
    E.lossCoefficient_nonneg hD hK hT.posSemidef,E.lossCoefficient_le_demand hD hK,
    E.lossCoefficient_pos hD hK hT⟩

theorem zero_policy_minimizer (hD : E.D.PosDef) (hK : E.K.PosDef) (hb : E.b=0) :
    E.lossCoefficient=0 ∧ E.zSolution=0 ∧ ∀ z, E.adjustmentObjective z=0 ↔ z=0 := by
  have hl := E.lossCoefficient_zero_policy hb
  have hz : E.zSolution=0 := by simp [zSolution,m,hb]
  exact ⟨hl,hz,fun z => by simpa only [hl,hz] using E.adjustmentObjective_eq_iff hD hK z⟩

theorem zero_relative_dimension_minimum (E0 : Model n 0) :
    E0.lossCoefficient=dotProduct E0.b (E0.D *ᵥ E0.b) ∧
    E0.adjustmentObjective E0.zSolution=E0.lossCoefficient ∧
    ∀ z : Vec 0, E0.adjustmentObjective z=E0.lossCoefficient ∧ z=E0.zSolution := by
  have hz (z : Vec 0) : z=0 := Subsingleton.elim _ _
  have hl := lossCoefficient_zero_relative_dimension E0
  have hv (z : Vec 0) : E0.adjustmentObjective z=E0.lossCoefficient := by
    rw [hz z,E0.adjustmentObjective_zero,hl]
  exact ⟨hl,hv _,fun z => ⟨hv z,Subsingleton.elim _ _⟩⟩

end Model
end CommodityClassification.Equilibrium
