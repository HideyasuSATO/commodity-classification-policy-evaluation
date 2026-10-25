module

public import LeanMath.CommodityClassification.QuadraticHalfSpace

/-! The explicit positive definite matrix mapping the fixed policy b to a. -/
@[expose] public section
noncomputable section
namespace CommodityClassification.Genericity
open Matrix FixedAnswer
variable {n : ℕ}

def policyResidual (b x : Vec n) : Vec n := x-(dotProduct b x/dotProduct b b) • b

theorem policyResidual_square (b x : Vec n) (hb : b≠0) :
    dotProduct (policyResidual b x) (policyResidual b x)=
      dotProduct x x-(dotProduct b x)^2/dotProduct b b := by
  have hbb : dotProduct b b≠0 := by simpa using hb
  simp only [policyResidual,sub_dotProduct,dotProduct_sub,smul_dotProduct,
    dotProduct_smul,smul_eq_mul,dotProduct_comm x b]
  field_simp
  ring

def interpolationMatrix (b a : Vec n) (γ : ℝ) : Mat n n :=
  (dotProduct b a)⁻¹ • vecMulVec a a+γ • (1-(dotProduct b b)⁻¹ • vecMulVec b b)

theorem interpolation_symmetric (b a : Vec n) (γ : ℝ) :
    (interpolationMatrix b a γ).transpose=interpolationMatrix b a γ := by
  simp only [interpolationMatrix,transpose_add,transpose_smul,transpose_vecMulVec,
    transpose_sub,transpose_one]

theorem interpolation_maps_policy (b a : Vec n) (γ : ℝ) (hba : 0<dotProduct b a) :
    interpolationMatrix b a γ *ᵥ b=a := by
  have hb : b≠0 := by intro hz; simp [hz] at hba
  have hbb : dotProduct b b≠0 := by simpa using hb
  simp only [interpolationMatrix,add_mulVec,smul_mulVec,sub_mulVec,one_mulVec,
    vecMulVec_mulVec,op_smul_eq_smul,smul_smul,dotProduct_comm a b]
  rw [inv_mul_cancel₀ hba.ne',inv_mul_cancel₀ hbb,one_smul,one_smul,sub_self,smul_zero,add_zero]

theorem interpolation_energy (b a x : Vec n) (γ : ℝ) (hb : b≠0) :
    dotProduct x (interpolationMatrix b a γ *ᵥ x)=
      (dotProduct a x)^2/dotProduct b a+
        γ*dotProduct (policyResidual b x) (policyResidual b x) := by
  rw [policyResidual_square b x hb]
  simp only [interpolationMatrix,add_mulVec,smul_mulVec,sub_mulVec,one_mulVec,
    vecMulVec_mulVec,op_smul_eq_smul,dotProduct_add,dotProduct_smul,dotProduct_sub,
    smul_eq_mul,dotProduct_comm x a,dotProduct_comm x b]
  ring

theorem policyResidual_zero_and_dot_zero (b a x : Vec n)
    (hba : 0<dotProduct b a) (hr : policyResidual b x=0) (ha : dotProduct a x=0) : x=0 := by
  have hx : x=(dotProduct b x/dotProduct b b) • b := sub_eq_zero.mp hr
  have ha' := ha
  rw [hx,dotProduct_smul,smul_eq_mul,dotProduct_comm a b] at ha'
  have hc : dotProduct b x/dotProduct b b=0 := (mul_eq_zero.mp ha').resolve_right hba.ne'
  rw [hx,hc,zero_smul]

theorem interpolation_posDef (b a : Vec n) (γ : ℝ)
    (hba : 0<dotProduct b a) (hγ : 0<γ) : (interpolationMatrix b a γ).PosDef := by
  have hb : b≠0 := by intro hz; simp [hz] at hba
  apply Matrix.posDef_iff_dotProduct_mulVec.mpr
  refine ⟨?_,?_⟩
  · simpa only [Matrix.IsHermitian,conjTranspose_eq_transpose_of_trivial] using
      interpolation_symmetric b a γ
  · intro x hx
    simp only [star_trivial]
    rw [interpolation_energy b a x γ hb]
    have ha0 : 0≤(dotProduct a x)^2/dotProduct b a := div_nonneg (sq_nonneg _) hba.le
    have hr0 : 0≤dotProduct (policyResidual b x) (policyResidual b x) := by
      simpa using dotProduct_star_self_nonneg (policyResidual b x)
    by_cases hr : policyResidual b x=0
    · have ha : dotProduct a x≠0 := fun ha => hx (policyResidual_zero_and_dot_zero b a x hba hr ha)
      exact add_pos_of_pos_of_nonneg (div_pos (sq_pos_of_ne_zero ha) hba) (mul_nonneg hγ.le hr0)
    · have hrp : 0<dotProduct (policyResidual b x) (policyResidual b x) := by
        simpa using (dotProduct_self_star_pos_iff.mpr hr)
      exact add_pos_of_nonneg_of_pos ha0 (mul_pos hγ hrp)

theorem exists_positive_interpolation (B : Mat n n) (hB : B.transpose=B) (hB0 : B≠0)
    (b : Vec n) (hb : b≠0) (γ : ℝ) (hγ : 0<γ) :
    ∃a : Vec n,0<dotProduct b a ∧ dotProduct a (B *ᵥ a)≠0 ∧
      (interpolationMatrix b a γ).PosDef ∧ interpolationMatrix b a γ *ᵥ b=a := by
  obtain ⟨a,ha,hq⟩ := exists_quadratic_nonzero_in_halfspace B hB hB0 b hb
  exact ⟨a,ha,hq,interpolation_posDef b a γ ha hγ,interpolation_maps_policy b a γ ha⟩

end CommodityClassification.Genericity
