module

public import LeanMath.CommodityClassification.AllAnswerVariation

/-! Matrix inverse and Schur-residual derivatives in arbitrary finite dimensions. -/
@[expose] public section
noncomputable section
namespace CommodityClassification.FixedAnswer
open Matrix Filter
open scoped BigOperators Topology
variable {k r s v : ℕ}

local instance (u v : ℕ) : NormedAddCommGroup (Mat u v) :=
  inferInstanceAs (NormedAddCommGroup (Fin u → Fin v → ℝ))
local instance (u v : ℕ) : NormedSpace ℝ (Mat u v) :=
  inferInstanceAs (NormedSpace ℝ (Fin u → Fin v → ℝ))

theorem hasDerivAt_matrixInverse {A : ℝ → Mat k k} {A' : Mat k k} {t : ℝ}
    (hA : HasDerivAt A A' t) (hu : IsUnit (A t).det) :
    HasDerivAt (fun z => (A z)⁻¹) (-((A t)⁻¹ * A' * (A t)⁻¹)) t := by
  apply hasDerivAt_pi.mpr
  intro i
  apply hasDerivAt_pi.mpr
  intro j
  have hc := hasDerivAt_inverse_mulVec hA (hasDerivAt_const t (Pi.single j (1:ℝ))) hu
  simp only [zero_sub, mulVec_neg] at hc
  simp only [mulVec_mulVec] at hc
  simpa only [mulVec_single_one, col_apply, Pi.neg_apply, Matrix.neg_apply,
    Matrix.mul_assoc] using
    hasDerivAt_pi.mp hc i

theorem hasDerivAt_schurResidual {A : ℝ → Mat r k} {B : ℝ → Mat s k}
    {K : ℝ → Mat k k} (S : Mat r s) (P : Mat r v) (Q : Mat s v)
    (V : Mat v k) (X : Mat v k) {t : ℝ}
    (hA : HasDerivAt A (P * X) t) (hB : HasDerivAt B (Q * X) t)
    (hK : HasDerivAt K (V.transpose * X + X.transpose * V) t)
    (hu : IsUnit (K t).det) (hsym : ((K t)⁻¹).transpose = (K t)⁻¹) :
    HasDerivAt (fun z => S - A z * (K z)⁻¹ * (B z).transpose)
      (-((P - A t * (K t)⁻¹ * V.transpose) * X * (K t)⁻¹ * (B t).transpose) -
       A t * (K t)⁻¹ * X.transpose * (Q - B t * (K t)⁻¹ * V.transpose).transpose) t := by
  have hd := (hasDerivAt_const t S).sub
    (hasDerivAt_matrixMul (hasDerivAt_matrixMul hA (hasDerivAt_matrixInverse hK hu))
      (hasDerivAt_transpose hB))
  apply hd.congr_deriv
  simp only [transpose_sub, transpose_mul, transpose_transpose, hsym,
    Matrix.mul_add, Matrix.add_mul, Matrix.mul_sub, Matrix.sub_mul,
    Matrix.mul_neg, Matrix.neg_mul, Matrix.mul_assoc, zero_sub]
  abel

end CommodityClassification.FixedAnswer
