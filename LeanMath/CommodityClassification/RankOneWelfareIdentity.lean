module

public import LeanMath.CommodityClassification.RankOnePositiveUpdate

/-! The exact welfare change from an actual rank-one update of K. -/
@[expose] public section
noncomputable section
set_option maxHeartbeats 1000000
namespace CommodityClassification.RankOne
open Matrix InputCoordinates
variable {k : ℕ}

theorem inverse_energy_change (K : Mat k k) (hK : K.PosDef) (u m : Vec k) (δ : ℝ)
    (hB : (K+δ • vecMulVec u u).PosDef) :
    dotProduct m (K⁻¹ *ᵥ m)-dotProduct m ((K+δ • vecMulVec u u)⁻¹ *ᵥ m)=
      δ*(dotProduct u (K⁻¹ *ᵥ m))^2/(1+δ*dotProduct u (K⁻¹ *ᵥ u)) := by
  rw [inverse_vector_update K hK u m δ hB,dotProduct_sub,dotProduct_smul]
  have hc : dotProduct m (K⁻¹ *ᵥ u)=dotProduct u (K⁻¹ *ᵥ m) :=
    hK.inv.isHermitian.isSymm.dotProduct_mulVec_comm
  rw [hc]
  ring

theorem welfare_change (K : Mat k k) (hK : K.PosDef) (u m : Vec k) (δ ν : ℝ)
    (hB : (K+δ • vecMulVec u u).PosDef) :
    (ν-dotProduct m ((K+δ • vecMulVec u u)⁻¹ *ᵥ m))-
      (ν-dotProduct m (K⁻¹ *ᵥ m))=
      δ*(dotProduct u (K⁻¹ *ᵥ m))^2/(1+δ*dotProduct u (K⁻¹ *ᵥ u)) := by
  have hh := inverse_energy_change K hK u m δ hB
  linarith

theorem welfare_change_nonzero (K : Mat k k) (hK : K.PosDef) (u m : Vec k) (δ ν : ℝ)
    (hB : (K+δ • vecMulVec u u).PosDef) (hδ : δ≠0) (hu : dotProduct u (K⁻¹ *ᵥ m)≠0) :
    ν-dotProduct m ((K+δ • vecMulVec u u)⁻¹ *ᵥ m)≠ν-dotProduct m (K⁻¹ *ᵥ m) := by
  apply sub_ne_zero.mp
  rw [welfare_change K hK u m δ ν hB]
  exact div_ne_zero (mul_ne_zero hδ (pow_ne_zero _ hu)) (denominator_pos K hK u δ hB).ne'

theorem response_direction_welfare_nonzero (K : Mat k k) (hK : K.PosDef) (m : Vec k) (δ ν : ℝ)
    (hm : m≠0) (hδ : δ≠0)
    (hB : (K+δ • vecMulVec (K⁻¹ *ᵥ m) (K⁻¹ *ᵥ m)).PosDef) :
    ν-dotProduct m ((K+δ • vecMulVec (K⁻¹ *ᵥ m) (K⁻¹ *ᵥ m))⁻¹ *ᵥ m)≠
      ν-dotProduct m (K⁻¹ *ᵥ m) := by
  apply welfare_change_nonzero K hK (K⁻¹ *ᵥ m) m δ ν hB hδ
  exact fun hz => inverse_vector_nonzero K hK m hm (dotProduct_self_eq_zero.mp hz)

end CommodityClassification.RankOne
