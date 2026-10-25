module

public import LeanMath.CommodityClassification.PrecisionTypeGuarantee
public import LeanMath.CommodityClassification.WelfareVariationalBounds

/-! Bounds for the normalized coefficient of each actual positive economy. -/
@[expose] public section
noncomputable section
namespace CommodityClassification.Precision.Data
open Matrix InputCoordinates
variable {n : ℕ} (d : Precision.Data n)

theorem normalizedWelfare_bounds (c : Vec n) (hc : d.Admissible c) :
    0 ≤ d.normalizedWelfare c ∧ d.normalizedWelfare c ≤ 1 := by
  let C := d.candidate c hc
  have hI := d.family.candidate_total_positive (d.family.total_positive_of_goods d.goods_nonempty) C
  have hV := (d.family.model C).economic_variational_certificate d.family.parents d.family.report
    C.property.2 d.family.hq hI d.family.hD d.family.hsigma
  have hl := hV.2.2.1
  have hu := hV.2.2.2.1
  change (d.family.model C).lossCoefficient ≤ dotProduct d.policy (d.demand *ᵥ d.policy) at hu
  rw [d.policy_energy] at hu
  rw [←d.actual_normalized_coefficient c hc]
  exact ⟨div_nonneg hl d.nu_pos.le,(div_le_one d.nu_pos).mpr hu⟩

theorem normalizedWelfare_pair_gap_le_one (c e : Vec n) (hc : d.Admissible c)
    (he : d.Admissible e) : |d.normalizedWelfare c-d.normalizedWelfare e| ≤ 1 := by
  have h0 := d.normalizedWelfare_bounds c hc
  have h1 := d.normalizedWelfare_bounds e he
  exact abs_le.mpr ⟨by linarith,by linarith⟩

end CommodityClassification.Precision.Data
