module

public import LeanMath.CommodityClassification.RobustWelfareMatrix

/-! Loewner demand comparisons pass to the actual variational welfare minima. -/
@[expose] public section
noncomputable section
set_option maxHeartbeats 1800000
namespace CommodityClassification.Robust
open Matrix Equilibrium
variable {n k : ℕ}

theorem loewner_quadratic_lower (D D0 : Mat n n) (a : ℝ)
    (h : (D-a • D0).PosSemidef) (x : Vec n) :
    a*dotProduct x (D0 *ᵥ x)≤dotProduct x (D *ᵥ x) := by
  have hh := h.dotProduct_mulVec_nonneg x
  simpa only [star_trivial,Matrix.sub_mulVec,Matrix.smul_mulVec,dotProduct_sub,
    dotProduct_smul,smul_eq_mul,sub_nonneg] using hh

theorem loewner_quadratic_upper (D D0 : Mat n n) (a : ℝ)
    (h : (a • D0-D).PosSemidef) (x : Vec n) :
    dotProduct x (D *ᵥ x)≤a*dotProduct x (D0 *ᵥ x) := by
  have hh := h.dotProduct_mulVec_nonneg x
  simpa only [star_trivial,Matrix.sub_mulVec,Matrix.smul_mulVec,dotProduct_sub,
    dotProduct_smul,smul_eq_mul,sub_nonneg] using hh

theorem objective_loewner_comparison (E E0 : Model n k) (δ : ℝ) (hδ : 0≤δ)
    (hC : E.C=E0.C) (hT : E.substitutionMatrix=E0.substitutionMatrix) (hb : E.b=E0.b)
    (hT0 : E0.substitutionMatrix.PosSemidef)
    (hlo : (E.D-(1-δ) • E0.D).PosSemidef) (hhi : ((1+δ) • E0.D-E.D).PosSemidef)
    (z : Vec k) :
    (1-δ)*E0.adjustmentObjective z≤E.adjustmentObjective z ∧
      E.adjustmentObjective z≤(1+δ)*E0.adjustmentObjective z := by
  have hl := loewner_quadratic_lower E.D E0.D (1-δ) hlo (E0.b+E0.C *ᵥ z)
  have hu := loewner_quadratic_upper E.D E0.D (1+δ) hhi (E0.b+E0.C *ᵥ z)
  have ht := hT0.dotProduct_mulVec_nonneg z
  simp only [star_trivial] at ht
  have hprod := mul_nonneg hδ ht
  simp only [Model.adjustmentObjective,hC,hT,hb]
  constructor <;> nlinarith

theorem coefficient_loewner_comparison (E E0 : Model n k) (δ : ℝ)
    (hδ : 0≤δ) (hδ1 : δ≤1) (hC : E.C=E0.C)
    (hT : E.substitutionMatrix=E0.substitutionMatrix) (hb : E.b=E0.b)
    (hD : E.D.PosDef) (hD0 : E0.D.PosDef) (hK : E.K.PosDef) (hK0 : E0.K.PosDef)
    (hT0 : E0.substitutionMatrix.PosSemidef)
    (hlo : (E.D-(1-δ) • E0.D).PosSemidef) (hhi : ((1+δ) • E0.D-E.D).PosSemidef) :
    (1-δ)*E0.lossCoefficient≤E.lossCoefficient ∧ E.lossCoefficient≤(1+δ)*E0.lossCoefficient := by
  constructor
  · calc
      (1-δ)*E0.lossCoefficient≤(1-δ)*E0.adjustmentObjective E.zSolution :=
        mul_le_mul_of_nonneg_left (E0.adjustmentObjective_lower hD0 hK0 _) (sub_nonneg.mpr hδ1)
      _≤E.adjustmentObjective E.zSolution :=
        (objective_loewner_comparison E E0 δ hδ hC hT hb hT0 hlo hhi _).1
      _=E.lossCoefficient := E.adjustmentObjective_at_solution hD hK
  · calc
      E.lossCoefficient≤E.adjustmentObjective E0.zSolution := E.adjustmentObjective_lower hD hK _
      _≤(1+δ)*E0.adjustmentObjective E0.zSolution :=
        (objective_loewner_comparison E E0 δ hδ hC hT hb hT0 hlo hhi _).2
      _=(1+δ)*E0.lossCoefficient := by rw [E0.adjustmentObjective_at_solution hD0 hK0]

end CommodityClassification.Robust
