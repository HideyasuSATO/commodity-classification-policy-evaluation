module
public import LeanMath.CommodityClassification.CostInputConnection
public import LeanMath.CommodityClassification.EconomicReportFibers
@[expose] public section
set_option maxHeartbeats 1600000
namespace CommodityClassification.Supply
open Matrix
open scoped BigOperators Topology
abbrev Vec (n : ℕ) := Fin n → ℝ
abbrev Mat (n m : ℕ) := Matrix (Fin n) (Fin m) ℝ
variable {f k : ℕ}

noncomputable def curvature (a w : Vec f) (p : ℝ) : Mat f f :=
  diagonal (fun j => a j / w j) - p⁻¹ • vecMulVec a a

theorem curvature_symmetric (a w : Vec f) (p : ℝ) : (curvature a w p).IsHermitian := by
  unfold Matrix.IsHermitian
  ext i j
  simp [curvature, Matrix.conjTranspose_apply, Matrix.diagonal_apply, vecMulVec, mul_comm]
  split_ifs <;> simp_all

theorem curvature_quad (a w v : Vec f) (p : ℝ) :
    dotProduct v (curvature a w p *ᵥ v) =
      (∑ j, (a j/w j) * (v j)^2) - (dotProduct a v)^2/p := by
  simp only [curvature, Matrix.sub_mulVec, dotProduct_sub,
    Matrix.smul_mulVec, Matrix.vecMulVec_mulVec]
  simp only [dotProduct_smul, op_smul_eq_mul, smul_eq_mul, dotProduct_comm v a]
  congr 1
  · change (∑ j, v j * (diagonal (fun l => a l/w l) *ᵥ v) j) = _
    simp only [Matrix.mulVec_diagonal]
    apply Finset.sum_congr rfl
    intro j hj
    ring
  · ring

theorem curvature_variance (d : CESCost.Data f) (v : Vec f) :
    dotProduct v (curvature d.a d.w0 d.p *ᵥ v) =
      ∑ j, (d.a j/d.w0 j) * (v j - (dotProduct d.a v/d.p)*d.w0 j)^2 := by
  rw [curvature_quad]
  have hsum : (∑ j, (d.a j/d.w0 j) * (v j - (dotProduct d.a v/d.p)*d.w0 j)^2) =
      (∑ j, (d.a j/d.w0 j)*(v j)^2) -
        (2*(dotProduct d.a v/d.p))*dotProduct d.a v + (dotProduct d.a v/d.p)^2*d.p := by
    calc
      _ = ∑ j, ((d.a j/d.w0 j)*(v j)^2 -
          (2*(dotProduct d.a v/d.p))*(d.a j*v j) +
          (dotProduct d.a v/d.p)^2*(d.a j*d.w0 j)) := by
        apply Finset.sum_congr rfl
        intro j hj
        field_simp [(d.w0_pos j).ne',d.p_pos.ne']
        ring
      _ = _ := by
        simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum]
        change _ - _ * dotProduct d.a v + _ * dotProduct d.a d.w0 = _
        rw [d.cost_identity]
  rw [hsum]
  field_simp [d.p_pos.ne']
  ring

theorem curvature_nonneg (d : CESCost.Data f) (v : Vec f) :
    0 ≤ dotProduct v (curvature d.a d.w0 d.p *ᵥ v) := by
  rw [curvature_variance]
  exact Finset.sum_nonneg (fun j _ => mul_nonneg (div_pos (d.a_pos j) (d.w0_pos j)).le (sq_nonneg _))

theorem curvature_zero_iff (d : CESCost.Data f) (v : Vec f) :
    dotProduct v (curvature d.a d.w0 d.p *ᵥ v) = 0 ↔ ∃ t : ℝ, v = t • d.w0 := by
  rw [curvature_variance]
  constructor
  · intro hz
    refine ⟨dotProduct d.a v / d.p, ?_⟩
    ext j
    have hs := Finset.single_le_sum (s := Finset.univ)
      (fun l _ => mul_nonneg (div_pos (d.a_pos l) (d.w0_pos l)).le
        (sq_nonneg (v l - (dotProduct d.a v/d.p)*d.w0 l))) (Finset.mem_univ j)
    rw [hz] at hs
    have hsq : (v j - (dotProduct d.a v/d.p)*d.w0 j)^2 = 0 := by
      have hpos := div_pos (d.a_pos j) (d.w0_pos j)
      nlinarith [sq_nonneg (v j - (dotProduct d.a v/d.p)*d.w0 j)]
    simpa only [Pi.smul_apply, smul_eq_mul] using sub_eq_zero.mp (sq_eq_zero_iff.mp hsq)
  · rintro ⟨t,rfl⟩
    simp [dotProduct_smul, d.cost_identity, d.p_pos.ne']

theorem curvature_posSemidef (d : CESCost.Data f) :
    (curvature d.a d.w0 d.p).PosSemidef := by
  apply Matrix.posSemidef_iff_dotProduct_mulVec.mpr
  exact ⟨curvature_symmetric _ _ _, fun v => by simpa using curvature_nonneg d v⟩

theorem relative_not_proportional (e : InputCoordinates.Frame k) {z : Vec k} (hz : z ≠ 0) :
    ¬ ∃ t : ℝ, e.V *ᵥ z = t • e.w := by
  rintro ⟨t,ht⟩
  have hh := congrArg (dotProduct e.a0) ht
  have ht0 : t=0 := by simpa [e.a0_dot_V, dotProduct_smul, e.normalized] using hh.symm
  rw [ht0, zero_smul] at ht
  exact hz (e.independent (ht.trans (Matrix.mulVec_zero e.V).symm))

theorem curvature_relative_pos (e : InputCoordinates.Frame k) (d : CESCost.Data (k+1))
    (hw : d.w0 = e.w) {z : Vec k} (hz : z ≠ 0) :
    0 < dotProduct (e.V *ᵥ z) (curvature d.a d.w0 d.p *ᵥ (e.V *ᵥ z)) := by
  apply lt_of_le_of_ne (curvature_nonneg d _) (Ne.symm ?_)
  intro hh
  have hp := (curvature_zero_iff d _).mp hh
  rw [hw] at hp
  exact relative_not_proportional e hz hp

theorem quad_conjugate (B : Mat f f) (V : Mat f k) (z : Vec k) :
    dotProduct z ((V.transpose * B * V) *ᵥ z) =
      dotProduct (V *ᵥ z) (B *ᵥ (V *ᵥ z)) := by
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, dotProduct_mulVec]
  simp only [vecMul_transpose]

theorem curvature_relative_posDef (e : InputCoordinates.Frame k) (d : CESCost.Data (k+1))
    (hw : d.w0 = e.w) : (e.V.transpose * curvature d.a d.w0 d.p * e.V).PosDef := by
  apply Matrix.posDef_iff_dotProduct_mulVec.mpr
  refine ⟨?_,fun z hz => ?_⟩
  · simpa using Matrix.isHermitian_conjTranspose_mul_mul e.V (curvature_symmetric d.a d.w0 d.p)
  · simpa only [star_trivial, quad_conjugate] using curvature_relative_pos e d hw hz

theorem negative_cost_hessian (d : CESCost.Data f) (σ : ℝ) :
    -d.hessian σ = σ • curvature d.a d.w0 d.p := by
  rw [d.hessian_manuscript]
  ext i j
  simp [curvature]
  ring

theorem actual_cost_hessian (d : CESCost.Data f) (σ : ℝ) (j l : Fin f) :
    -CESCost.pricePartial (CESCost.pricePartial (d.cost σ) j) l d.w0 =
      (σ • curvature d.a d.w0 d.p) j l := by
  rw [d.cost_mixed_derivative]
  exact congrFun (congrFun (negative_cost_hessian d σ) j) l

end CommodityClassification.Supply
