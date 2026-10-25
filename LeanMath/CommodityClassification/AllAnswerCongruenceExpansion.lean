module

public import LeanMath.CommodityClassification.AllAnswerSchurDerivatives

/-! Exact matrix identities underlying the second-variation argument in B.2. -/
@[expose] public section
noncomputable section
namespace CommodityClassification.FixedAnswer
open Matrix
variable {n k r s : ℕ}

theorem Data.parent_congruence_with_residual (a : Data n k r) (U : Mat n s)
    (hL : a.L.transpose = a.L) (hK : a.K₀.PosDef) (Z : Mat s k) :
    a.K ((a.withDirections U).point Z) =
      (1 + a.K₀⁻¹ * (a.loading U a.C₀).transpose * Z).transpose * a.K₀ *
        (1 + a.K₀⁻¹ * (a.loading U a.C₀).transpose * Z) +
          Z.transpose * a.schur U U a.C₀ * Z := by
  have hi : (a.K₀⁻¹).transpose = a.K₀⁻¹ := hK.inv.isHermitian.isSymm
  have hu := a.K₀.isUnit_iff_isUnit_det.mp hK.isUnit
  change (a.withDirections U).K ((a.withDirections U).point Z) = _
  rw [(a.withDirections U).K_point hL]
  change a.K₀ + (a.loading U a.C₀).transpose * Z +
      Z.transpose * a.loading U a.C₀ + Z.transpose * (U.transpose * a.L * U) * Z = _
  simp only [Data.schur, transpose_add, transpose_one, transpose_mul,
    transpose_transpose, hi, Matrix.add_mul, Matrix.mul_add, Matrix.sub_mul,
    Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one, Matrix.mul_assoc]
  simp only [← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hu,
    Matrix.mul_nonsing_inv _ hu, Matrix.mul_one, Matrix.one_mul]
  simp only [Data.K₀]
  abel

theorem Data.loading_congruence_of_cross_zero (a : Data n k r) (U : Mat n s)
    (hcross : a.schur a.N U a.C₀ = 0) (Z : Mat s k) :
    a.loading a.N ((a.withDirections U).point Z) =
      a.A_N * (1 + a.K₀⁻¹ * (a.loading U a.C₀).transpose * Z) := by
  have hs : a.N.transpose * a.L * U =
      a.A_N * a.K₀⁻¹ * (a.loading U a.C₀).transpose := sub_eq_zero.mp hcross
  change a.N.transpose * a.L * (a.C₀ + U * Z) =
      a.A_N * (1 + a.K₀⁻¹ * (a.loading U a.C₀).transpose * Z)
  rw [Matrix.mul_add, ← Matrix.mul_assoc, hs]
  simp only [Data.A_N, Matrix.mul_add, Matrix.mul_one, Matrix.mul_assoc]

end CommodityClassification.FixedAnswer
