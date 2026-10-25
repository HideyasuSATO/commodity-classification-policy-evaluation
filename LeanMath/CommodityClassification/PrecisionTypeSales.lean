module

public import LeanMath.CommodityClassification.PrecisionWelfareReduction

/-! The predetermined balanced types each have one half of baseline sales. -/
@[expose] public section
noncomputable section
set_option maxHeartbeats 800000
namespace CommodityClassification.Precision.Data
open Matrix InputCoordinates
open scoped BigOperators
variable {n : ℕ} (d : Precision.Data n)

def typeSales (a : ℝ) : ℝ := ∑i∈Finset.univ.filter (fun i => d.v i=a),d.w i

theorem typeSales_sum : d.typeSales 1+d.typeSales (-1)=1 := by
  calc
    _=∑i,d.w i := by
      simp only [typeSales,Finset.sum_filter,←Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro i _
      rcases d.type_sign i with hi|hi <;> rw [hi] <;> norm_num
    _=1 := d.sum_w

theorem typeSales_difference : d.typeSales 1-d.typeSales (-1)=0 := by
  rw [←d.type_balance]
  simp only [typeSales,Finset.sum_filter,←Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _
  rcases d.type_sign i with hi|hi <;> rw [hi] <;> norm_num

theorem typeSales_half : d.typeSales 1=1/2 ∧ d.typeSales (-1)=1/2 := by
  have hs := d.typeSales_sum
  have hd := d.typeSales_difference
  constructor <;> linarith

end CommodityClassification.Precision.Data
