module

public import LeanMath.CommodityClassification.RobustQuadraticCauchy

/-! Uniform policy and combined demand-policy perturbation constants. -/
@[expose] public section
noncomputable section
set_option maxHeartbeats 2000000
namespace CommodityClassification.Robust
open Matrix Equilibrium
variable {n k : ℕ}

def errorConstant (δ τ : ℝ) : ℝ := δ+(1+δ)*(2*τ+τ^2)

theorem errorConstant_nonneg (δ τ : ℝ) (hδ : 0≤δ) (hτ : 0≤τ) : 0≤errorConstant δ τ := by
  unfold errorConstant
  positivity

theorem relative_cross_and_energy (W D0 : Mat n n) (hW : W.PosSemidef) (hD0 : D0.PosSemidef)
    (a τ : ℝ) (ha : 0≤a) (hτ : 0≤τ) (hgap : (a • D0-W).PosSemidef)
    (b0 h : Vec n) (hh : dotProduct h (D0 *ᵥ h)≤τ^2*dotProduct b0 (D0 *ᵥ b0)) :
    |dotProduct h (W *ᵥ b0)|≤a*τ*dotProduct b0 (D0 *ᵥ b0) ∧
      dotProduct h (W *ᵥ h)≤a*τ^2*dotProduct b0 (D0 *ᵥ b0) := by
  have hν := hD0.dotProduct_mulVec_nonneg b0
  have hh0 := hW.dotProduct_mulVec_nonneg h
  have hb0 := hW.dotProduct_mulVec_nonneg b0
  simp only [star_trivial] at hν hh0 hb0
  have hwh : dotProduct h (W *ᵥ h)≤a*τ^2*dotProduct b0 (D0 *ᵥ b0) := by
    have hl := loewner_quadratic_upper W D0 a hgap h
    have hm := mul_le_mul_of_nonneg_left hh ha
    nlinarith
  refine ⟨?_,hwh⟩
  have hwb := loewner_quadratic_upper W D0 a hgap b0
  have hs := semidefinite_cauchy_sq W hW h b0
  have hp := mul_le_mul hwh hwb hb0 (mul_nonneg (mul_nonneg ha (sq_nonneg τ)) hν)
  have hab := mul_nonneg (mul_nonneg ha hτ) hν
  have he := sq_abs (dotProduct h (W *ᵥ b0))
  have hx := abs_nonneg (dotProduct h (W *ᵥ b0))
  nlinarith

theorem relative_policy_error (W D0 : Mat n n) (hW : W.PosSemidef) (hD0 : D0.PosSemidef)
    (a τ : ℝ) (ha : 0≤a) (hτ : 0≤τ) (hgap : (a • D0-W).PosSemidef)
    (b b0 : Vec n) (hh : dotProduct (b-b0) (D0 *ᵥ (b-b0))≤τ^2*dotProduct b0 (D0 *ᵥ b0)) :
    |dotProduct b (W *ᵥ b)-dotProduct b0 (W *ᵥ b0)|≤
      a*(2*τ+τ^2)*dotProduct b0 (D0 *ᵥ b0) := by
  have hb := relative_cross_and_energy W D0 hW hD0 a τ ha hτ hgap b0 (b-b0) hh
  have hh0 := hW.dotProduct_mulVec_nonneg (b-b0)
  simp only [star_trivial] at hh0
  rw [semidefinite_quadratic_subtraction W hW b b0]
  calc
    _≤|2*dotProduct (b-b0) (W *ᵥ b0)|+|dotProduct (b-b0) (W *ᵥ (b-b0))| := abs_add_le _ _
    _=2*|dotProduct (b-b0) (W *ᵥ b0)|+dotProduct (b-b0) (W *ᵥ (b-b0)) := by
      rw [abs_mul,abs_of_nonneg hh0]
      norm_num
    _≤a*(2*τ+τ^2)*dotProduct b0 (D0 *ᵥ b0) := by nlinarith [hb.1,hb.2]

theorem combined_coefficient_error (E E0 : Model n k) (δ τ : ℝ)
    (hδ : 0≤δ) (hδ1 : δ≤1) (hτ : 0≤τ)
    (hC : E.C=E0.C) (hT : E.substitutionMatrix=E0.substitutionMatrix)
    (hD : E.D.PosDef) (hD0 : E0.D.PosDef) (hK : E.K.PosDef) (hK0 : E0.K.PosDef)
    (hT0 : E0.substitutionMatrix.PosSemidef)
    (hlo : (E.D-(1-δ) • E0.D).PosSemidef) (hhi : ((1+δ) • E0.D-E.D).PosSemidef)
    (hh : dotProduct (E.b-E0.b) (E0.D *ᵥ (E.b-E0.b))≤τ^2*dotProduct E0.b (E0.D *ᵥ E0.b)) :
    |E.lossCoefficient-E0.lossCoefficient|≤errorConstant δ τ*dotProduct E0.b (E0.D *ᵥ E0.b) := by
  have hTE : E.substitutionMatrix.PosSemidef := hT ▸ hT0
  have hW := E.welfareMatrix_posSemidef hD hK hTE
  have hgap : ((1+δ) • E0.D-E.welfareMatrix).PosSemidef := by
    have hh' := hhi.add (E.welfareMatrix_le_demand hD hK)
    convert hh' using 1
    abel
  have hp := relative_policy_error E.welfareMatrix E0.D hW hD0.posSemidef
    (1+δ) τ (by linarith) hτ hgap E.b E0.b hh
  rw [E.welfareMatrix_current_coefficient hD,E.welfareMatrix_quadratic hD] at hp
  have hc := coefficient_loewner_comparison (E.withPolicy E0.b) E0 δ hδ hδ1 hC hT rfl
    hD hD0 hK hK0 hT0 hlo hhi
  have hb0 := E0.lossCoefficient_le_demand hD0 hK0
  have hscale := mul_le_mul_of_nonneg_left hb0 hδ
  have hbase : |(E.withPolicy E0.b).lossCoefficient-E0.lossCoefficient|≤
      δ*dotProduct E0.b (E0.D *ᵥ E0.b) := by
    apply abs_le.mpr
    constructor <;> nlinarith [hc.1,hc.2]
  calc
    |E.lossCoefficient-E0.lossCoefficient|≤
        |E.lossCoefficient-(E.withPolicy E0.b).lossCoefficient|+
        |(E.withPolicy E0.b).lossCoefficient-E0.lossCoefficient| := abs_sub_le _ _ _
    _≤errorConstant δ τ*dotProduct E0.b (E0.D *ᵥ E0.b) := by
      unfold errorConstant
      nlinarith

end CommodityClassification.Robust
