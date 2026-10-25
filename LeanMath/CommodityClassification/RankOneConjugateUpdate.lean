module

public import LeanMath.CommodityClassification.RankOneWelfareIdentity

/-! A rank-one row perturbation with vanishing mean cross terms. -/
@[expose] public section
noncomputable section
set_option maxHeartbeats 1000000
namespace CommodityClassification.RankOne
open Matrix InputCoordinates
variable {n k : ℕ}

theorem outer_conjugate (L : Mat n n) (v : Vec n) (u : Vec k) :
    (vecMulVec v u).transpose*L*vecMulVec v u=
      dotProduct v (L *ᵥ v) • vecMulVec u u := by
  rw [Matrix.transpose_vecMulVec,Matrix.mul_assoc,Matrix.mul_vecMulVec,
    Matrix.mul_vecMulVec,Matrix.vecMulVec_mulVec,op_smul_eq_smul,Matrix.smul_vecMulVec]

theorem mean_conjugate_update (L : Mat n n) (hL : L.IsSymm) (C : Mat n k)
    (v : Vec n) (u : Vec k) (hc : C.transpose *ᵥ (L *ᵥ v)=0) (t : ℝ) :
    (C+t • vecMulVec v u).transpose*L*(C+t • vecMulVec v u)=
      C.transpose*L*C+(t^2*dotProduct v (L *ᵥ v)) • vecMulVec u u := by
  have hx : C.transpose*L*vecMulVec v u=0 := by
    rw [Matrix.mul_vecMulVec,←Matrix.mulVec_mulVec,hc,Matrix.zero_vecMulVec]
  have hy : (vecMulVec v u).transpose*L*C=0 := by
    have hh := congrArg Matrix.transpose hx
    simpa only [Matrix.transpose_mul,Matrix.transpose_transpose,hL.eq,
      Matrix.transpose_zero,Matrix.mul_assoc] using hh
  simp only [Matrix.transpose_add,Matrix.transpose_smul,Matrix.add_mul,Matrix.mul_add,
    Matrix.smul_mul,Matrix.mul_smul,smul_smul,hx,hy,outer_conjugate,
    smul_zero,add_zero,zero_add]
  ext a b
  simp only [Matrix.add_apply,Matrix.smul_apply,smul_eq_mul]
  ring

end CommodityClassification.RankOne
