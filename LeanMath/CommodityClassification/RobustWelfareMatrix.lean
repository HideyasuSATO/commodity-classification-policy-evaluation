module

public import LeanMath.CommodityClassification.PrecisionConcentratedDesign

/-! The welfare quadratic matrix for all policy directions on one fixed economy. -/
@[expose] public section
noncomputable section
set_option maxHeartbeats 1800000
namespace CommodityClassification.Equilibrium.Model
open Matrix
variable {n k : ℕ} (E : Equilibrium.Model n k)

def withPolicy (b : Equilibrium.Vec n) : Equilibrium.Model n k := {E with b:=b}

def welfareMatrix : Equilibrium.Mat n n := E.D-E.D*E.C*E.K⁻¹*E.C.transpose*E.D

theorem withPolicy_K (b : Equilibrium.Vec n) : (E.withPolicy b).K=E.K := rfl

theorem withPolicy_substitution (b : Equilibrium.Vec n) :
    (E.withPolicy b).substitutionMatrix=E.substitutionMatrix := rfl

theorem withPolicy_self : E.withPolicy E.b=E := by cases E;rfl

theorem welfareMatrix_quadratic (hD : E.D.PosDef) (b : Equilibrium.Vec n) :
    dotProduct b (E.welfareMatrix *ᵥ b)=(E.withPolicy b).lossCoefficient := by
  rw [welfareMatrix,Matrix.sub_mulVec,dotProduct_sub]
  simp only [←Matrix.mulVec_mulVec]
  change dotProduct b (E.D *ᵥ b)-
    dotProduct b (E.D *ᵥ (E.C *ᵥ (E.K⁻¹ *ᵥ (E.C.transpose *ᵥ (E.D *ᵥ b)))))=_
  have hx := (E.withPolicy b).demand_cross_moment hD
    (E.K⁻¹ *ᵥ (E.C.transpose *ᵥ (E.D *ᵥ b)))
  change dotProduct b (E.D *ᵥ (E.C *ᵥ (E.K⁻¹ *ᵥ (E.C.transpose *ᵥ (E.D *ᵥ b)))))=
    dotProduct (E.C.transpose *ᵥ (E.D *ᵥ b)) (E.K⁻¹ *ᵥ (E.C.transpose *ᵥ (E.D *ᵥ b))) at hx
  rw [hx]
  rfl

theorem welfareMatrix_correction_posSemidef (hD : E.D.PosDef) (hK : E.K.PosDef) :
    (E.D*E.C*E.K⁻¹*E.C.transpose*E.D).PosSemidef := by
  have hh := hK.inv.posSemidef.conjTranspose_mul_mul_same (E.C.transpose*E.D)
  simpa only [Matrix.conjTranspose_mul,Matrix.conjTranspose_eq_transpose_of_trivial,
    Matrix.transpose_mul,hD.isHermitian.isSymm.eq,Matrix.transpose_transpose,Matrix.mul_assoc] using hh

theorem welfareMatrix_isHermitian (hD : E.D.PosDef) (hK : E.K.PosDef) :
    E.welfareMatrix.IsHermitian :=
  hD.isHermitian.sub (E.welfareMatrix_correction_posSemidef hD hK).isHermitian

theorem welfareMatrix_posSemidef (hD : E.D.PosDef) (hK : E.K.PosDef)
    (hT : E.substitutionMatrix.PosSemidef) : E.welfareMatrix.PosSemidef := by
  apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg (E.welfareMatrix_isHermitian hD hK)
  intro b
  simp only [star_trivial]
  rw [E.welfareMatrix_quadratic hD b]
  exact (E.withPolicy b).lossCoefficient_nonneg hD hK hT

theorem welfareMatrix_le_demand (hD : E.D.PosDef) (hK : E.K.PosDef) :
    (E.D-E.welfareMatrix).PosSemidef := by
  rw [welfareMatrix,sub_sub_cancel]
  exact E.welfareMatrix_correction_posSemidef hD hK

theorem welfareMatrix_current_coefficient (hD : E.D.PosDef) :
    dotProduct E.b (E.welfareMatrix *ᵥ E.b)=E.lossCoefficient := by
  rw [E.welfareMatrix_quadratic hD,E.withPolicy_self]

end CommodityClassification.Equilibrium.Model
