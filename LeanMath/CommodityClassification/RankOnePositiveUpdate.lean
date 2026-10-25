module

public import LeanMath.CommodityClassification.CompositeMatchedReports

/-! The rank-one denominator is positive when both matrices are positive definite. -/
@[expose] public section
noncomputable section
set_option maxHeartbeats 1000000
namespace CommodityClassification.RankOne
open Matrix InputCoordinates
variable {k : ℕ}

theorem mul_inverse_vector (K : Mat k k) (hK : K.PosDef) (v : Vec k) :
    K *ᵥ (K⁻¹ *ᵥ v)=v := by
  rw [Matrix.mulVec_mulVec,Matrix.mul_nonsing_inv _ (K.isUnit_iff_isUnit_det.mp hK.isUnit),Matrix.one_mulVec]

theorem inverse_vector_nonzero (K : Mat k k) (hK : K.PosDef) (v : Vec k) (hv : v≠0) :
    K⁻¹ *ᵥ v≠0 := by
  intro hz
  have hh := mul_inverse_vector K hK v
  rw [hz,Matrix.mulVec_zero] at hh
  exact hv hh.symm

theorem inverse_energy_pos (K : Mat k k) (hK : K.PosDef) (v : Vec k) (hv : v≠0) :
    0<dotProduct v (K⁻¹ *ᵥ v) := by
  simpa only [star_trivial] using hK.inv.dotProduct_mulVec_pos hv

theorem denominator_pos (K : Mat k k) (hK : K.PosDef) (u : Vec k) (δ : ℝ)
    (hB : (K+δ • vecMulVec u u).PosDef) :
    0<1+δ*dotProduct u (K⁻¹ *ᵥ u) := by
  by_cases hu : u=0
  · simp [hu]
  have hy := inverse_vector_nonzero K hK u hu
  have hc := inverse_energy_pos K hK u hu
  have hb : 0<dotProduct (K⁻¹ *ᵥ u) ((K+δ • vecMulVec u u) *ᵥ (K⁻¹ *ᵥ u)) := by
    simpa only [star_trivial] using hB.dotProduct_mulVec_pos hy
  simp only [Matrix.add_mulVec,Matrix.smul_mulVec,Matrix.vecMulVec_mulVec,
    dotProduct_add,dotProduct_smul,mul_inverse_vector K hK u,smul_eq_mul,op_smul_eq_mul] at hb
  rw [dotProduct_comm (K⁻¹ *ᵥ u) u] at hb
  have he : 0<dotProduct u (K⁻¹ *ᵥ u)*(1+δ*dotProduct u (K⁻¹ *ᵥ u)) := by
    nlinarith [hb]
  exact (mul_pos_iff_of_pos_left hc).mp he

theorem inverse_vector_update (K : Mat k k) (hK : K.PosDef) (u m : Vec k) (δ : ℝ)
    (hB : (K+δ • vecMulVec u u).PosDef) :
    (K+δ • vecMulVec u u)⁻¹ *ᵥ m=K⁻¹ *ᵥ m-
      (δ*dotProduct u (K⁻¹ *ᵥ m)/(1+δ*dotProduct u (K⁻¹ *ᵥ u))) • (K⁻¹ *ᵥ u) := by
  have hd := (denominator_pos K hK u δ hB).ne'
  apply hB.mulVec_injective
  rw [mul_inverse_vector _ hB m]
  simp only [Matrix.mulVec_sub,Matrix.mulVec_smul,Matrix.add_mulVec,Matrix.smul_mulVec,
    Matrix.vecMulVec_mulVec,mul_inverse_vector K hK m,mul_inverse_vector K hK u]
  ext l
  simp only [Pi.add_apply,Pi.sub_apply,Pi.smul_apply,smul_eq_mul,op_smul_eq_mul]
  field_simp [hd]
  ring

end CommodityClassification.RankOne
