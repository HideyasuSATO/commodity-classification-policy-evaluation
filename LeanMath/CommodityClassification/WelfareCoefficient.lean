module
public import LeanMath.CommodityClassification.WelfarePathRegularity
@[expose] public section
set_option maxHeartbeats 1600000
namespace CommodityClassification.Equilibrium
open Matrix
open scoped BigOperators
variable {n k : ℕ}
namespace Model
variable (E : Model n k)

/-- The manuscript coefficient, using the existing economic K and m. -/
noncomputable def lossCoefficient : ℝ :=
  dotProduct E.b (E.D *ᵥ E.b)-dotProduct E.m (E.K⁻¹ *ᵥ E.m)

theorem demand_cross_moment (hD : E.D.PosDef) (z : Vec k) :
    dotProduct E.b (E.D *ᵥ (E.C *ᵥ z))=dotProduct E.m z := by
  rw [hD.isHermitian.isSymm.dotProduct_mulVec_comm]
  change dotProduct (E.C *ᵥ z) (E.D *ᵥ E.b)=dotProduct (E.C.transpose *ᵥ (E.D *ᵥ E.b)) z
  rw [dotProduct_comm (E.C.transpose *ᵥ (E.D *ᵥ E.b)),Matrix.dotProduct_transpose_mulVec,dotProduct_comm]

theorem lossCoefficient_eq_negative_quantity (hD : E.D.PosDef) :
    E.lossCoefficient = -dotProduct E.b E.qSolution := by
  rw [E.qSolution_formula,Matrix.mulVec_add,dotProduct_neg,neg_neg,dotProduct_add,
    E.demand_cross_moment hD,zSolution,dotProduct_neg]
  rfl

theorem lossCoefficient_zero_policy (hb : E.b=0) : E.lossCoefficient=0 := by
  simp [lossCoefficient,m,hb]

theorem lossCoefficient_zero_relative_dimension (E0 : Model n 0) :
    E0.lossCoefficient=dotProduct E0.b (E0.D *ᵥ E0.b) := by
  simp [lossCoefficient,dotProduct]

end Model
end CommodityClassification.Equilibrium
