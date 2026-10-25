module

public import LeanMath.CommodityClassification.AllAnswerDifferentialTools

/-! Actual Schur residuals along affine changes of the reported answer. -/
@[expose] public section
noncomputable section
namespace CommodityClassification.FixedAnswer
open Matrix Filter
open scoped BigOperators Topology
variable {n k r s u v : ℕ}

local instance (a b : ℕ) : NormedAddCommGroup (Mat a b) :=
  inferInstanceAs (NormedAddCommGroup (Fin a → Fin b → ℝ))
local instance (a b : ℕ) : NormedSpace ℝ (Mat a b) :=
  inferInstanceAs (NormedSpace ℝ (Fin a → Fin b → ℝ))

def Data.withDirections (a : Data n k r) (U : Mat n s) : Data n k s :=
  ⟨a.base,a.L,a.d,a.C₀,U⟩

def Data.loading (a : Data n k r) (U : Mat n s) (C : Mat n k) : Mat s k :=
  U.transpose * a.L * C

def Data.schur (a : Data n k r) (U : Mat n s) (V : Mat n u)
    (C : Mat n k) : Mat s u :=
  U.transpose * a.L * V - a.loading U C * (a.K C)⁻¹ * (a.loading V C).transpose

theorem Data.schur_transpose (a : Data n k r) (U : Mat n s) (V : Mat n u)
    (C : Mat n k) (hL : a.L.transpose = a.L) (hK : (a.K C).PosDef) :
    (a.schur U V C).transpose = a.schur V U C := by
  have hi : ((a.K C)⁻¹).transpose = (a.K C)⁻¹ := hK.inv.isHermitian.isSymm
  simp only [Data.schur, transpose_sub, transpose_mul, transpose_transpose,
    hL, hi, Matrix.mul_assoc]

theorem Data.hasDerivAt_loadingAlong (a : Data n k r) (U : Mat n s)
    (W : Mat n v) (X : Mat v k) (t : ℝ) :
    HasDerivAt (fun z => a.loading U ((a.withDirections W).point (z • X)))
      (U.transpose * a.L * W * X) t := by
  have hd := hasDerivAt_matrixMul (hasDerivAt_const t (U.transpose * a.L))
    ((a.withDirections W).hasDerivAt_pointLine X t)
  simpa only [Data.loading, Data.withDirections, Matrix.zero_mul, zero_add,
    Matrix.mul_assoc] using hd

theorem Data.hasDerivAt_schurAlong (a : Data n k r) (U : Mat n s)
    (V : Mat n u) (W : Mat n v) (X : Mat v k) (t : ℝ)
    (hL : a.L.transpose = a.L)
    (hK : (a.K ((a.withDirections W).point (t • X))).PosDef) :
    HasDerivAt (fun z => a.schur U V ((a.withDirections W).point (z • X)))
      (-(a.schur U W ((a.withDirections W).point (t • X)) * X *
          (a.K ((a.withDirections W).point (t • X)))⁻¹ *
          (a.loading V ((a.withDirections W).point (t • X))).transpose) -
       a.loading U ((a.withDirections W).point (t • X)) *
         (a.K ((a.withDirections W).point (t • X)))⁻¹ * X.transpose *
         (a.schur V W ((a.withDirections W).point (t • X))).transpose) t := by
  exact hasDerivAt_schurResidual (U.transpose * a.L * V)
    (U.transpose * a.L * W) (V.transpose * a.L * W)
    (a.loading W ((a.withDirections W).point (t • X))) X
    (a.hasDerivAt_loadingAlong U W X t) (a.hasDerivAt_loadingAlong V W X t)
    ((a.withDirections W).hasDerivAt_KLine hL X t)
    ((a.K _).isUnit_iff_isUnit_det.mp hK.isUnit) hK.inv.isHermitian.isSymm

theorem Data.cross_equation (a : Data n k r) (U : Mat n s) (X : Mat s k)
    (hL : a.L.transpose = a.L) (hK : a.K₀.PosDef)
    (hz : ∀ᶠ t : ℝ in 𝓝 0,
      a.schur a.N a.N ((a.withDirections U).point (t • X)) = 0) :
    a.schur a.N U a.C₀ * X * (a.K₀⁻¹ * a.A_N.transpose) +
      (a.K₀⁻¹ * a.A_N.transpose).transpose * X.transpose *
        (a.schur a.N U a.C₀).transpose = 0 := by
  have hd := a.hasDerivAt_schurAlong a.N a.N U X 0 hL (by
    simpa only [zero_smul, Data.point, Data.withDirections, Data.K₀,
      Matrix.mul_zero, add_zero] using hK)
  have heq : (fun t : ℝ => a.schur a.N a.N ((a.withDirections U).point (t • X)))
      =ᶠ[𝓝 0] (fun _ => (0 : Mat r r)) := hz
  have he := (hd.congr_of_eventuallyEq heq.symm).unique (hasDerivAt_const 0 (0:Mat r r))
  simp only [zero_smul, Data.point, Data.withDirections, Matrix.mul_zero, add_zero] at he
  change -(a.schur a.N U a.C₀ * X * a.K₀⁻¹ * a.A_N.transpose) -
    a.A_N * a.K₀⁻¹ * X.transpose * (a.schur a.N U a.C₀).transpose = 0 at he
  have hi : (a.K₀⁻¹).transpose = a.K₀⁻¹ := hK.inv.isHermitian.isSymm
  simp only [transpose_mul, transpose_transpose, hi,
    Matrix.mul_assoc]
  have := congrArg Neg.neg he
  simpa only [neg_sub, neg_neg, neg_zero, sub_neg_eq_add, Matrix.mul_assoc,
    add_comm] using this

theorem Data.inverse_loading_ne_zero (a : Data n k r) (hK : a.K₀.PosDef)
    (hA : a.A_N ≠ 0) : a.K₀⁻¹ * a.A_N.transpose ≠ 0 := by
  intro he
  have hh := congrArg (fun E : Mat k r => a.K₀ * E) he
  rw [← Matrix.mul_assoc, Matrix.mul_nonsing_inv _
    (a.K₀.isUnit_iff_isUnit_det.mp hK.isUnit), Matrix.one_mul, Matrix.mul_zero] at hh
  exact hA (by simpa only [transpose_transpose, transpose_zero] using congrArg transpose hh)

theorem Data.cross_vanishes (a : Data n k r) (U : Mat n s)
    (hL : a.L.transpose = a.L) (hK : a.K₀.PosDef) (hA : a.A_N ≠ 0)
    (hz : ∀ X : Mat s k, ∀ᶠ t : ℝ in 𝓝 0,
      a.schur a.N a.N ((a.withDirections U).point (t • X)) = 0) :
    a.schur a.N U a.C₀ = 0 :=
  universal_cross_zero _ _ (a.inverse_loading_ne_zero hK hA)
    (fun X => a.cross_equation U X hL hK (hz X))

end CommodityClassification.FixedAnswer
