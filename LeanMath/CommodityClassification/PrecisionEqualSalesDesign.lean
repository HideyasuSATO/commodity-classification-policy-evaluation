module

public import LeanMath.CommodityClassification.PrecisionIllustrationParameters

/-! The actual 32-product equal-sales design and its four-group lower bound. -/
@[expose] public section
noncomputable section
set_option maxHeartbeats 2400000
namespace CommodityClassification.Precision.Illustration
open InputCoordinates
open scoped BigOperators

def types (i : Fin 32) : ℝ := if i.val<16 then 1 else -1

def equalSales : Data 32 where
  w _ := 1/32
  v := types
  hw _ := by norm_num
  sum_w := by norm_num
  type_sign i := by unfold types;split_ifs <;> simp
  type_balance := by norm_num [types,Fin.sum_univ_succ]
  eta := 9/4
  alpha := 9/4
  beta := 1/2
  sigma := 1
  heta := by norm_num
  halpha := by norm_num
  hbeta := by norm_num
  hsigma := by norm_num

theorem equalSales_parameters : equalSales.HasIllustrationParameters := by
  norm_num [Data.HasIllustrationParameters,equalSales]

theorem equalSales_largest (k : ℕ) : equalSales.largestSales k=(min k 32 : ℕ)/32 := by
  obtain ⟨S,hcard,hs⟩ := equalSales.largestSales_attained k
  rw [←hs]
  simp [equalSales,hcard]
  ring

theorem equalSales_coarseSales : equalSales.coarseSales 4=5/32 := by
  rw [Data.coarseSales,equalSales_largest]
  norm_num

theorem equalSales_coarseMoment : equalSales.coarseMoment 4=27/32 := by
  rw [Data.coarseMoment,equalSales_coarseSales,
    (equalSales.illustration_constants equalSales_parameters).2.2.2.2.1]
  norm_num

theorem equalSales_lowerWidth : equalSales.coarseLowerWidth 4=19/335 := by
  rw [Data.coarseLowerWidth,equalSales_coarseMoment,
    (equalSales.illustration_constants equalSales_parameters).2.2.2.2.1,
    equalSales.illustration_width_formula equalSales_parameters]
  norm_num

theorem equalSales_all_four_fail (P : Partition 32 4) : ¬equalSales.exAnteWidth P≤1/20 := by
  apply equalSales.all_partition_failure P
  rw [equalSales_lowerWidth]
  norm_num

theorem equalSales_interpolatedMoment :
    equalSales.interpolatedMoment (15/16) (equalSales.coarseMoment 4)=6323/8192 := by
  rw [Data.interpolatedMoment,equalSales_coarseMoment,
    (equalSales.illustration_constants equalSales_parameters).2.2.2.2.1]
  norm_num

theorem equalSales_interpolatedWidth :
    (1/20:ℝ)<equalSales.interpolatedWidth (15/16) (equalSales.coarseMoment 4) := by
  rw [Data.interpolatedWidth,equalSales_interpolatedMoment,
    (equalSales.illustration_constants equalSales_parameters).2.2.2.2.1]
  exact (equalSales.illustration_width_threshold equalSales_parameters _ (by norm_num)).mpr (by norm_num)

end CommodityClassification.Precision.Illustration
