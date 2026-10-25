module

public import LeanMath.CommodityClassification.PrecisionVarianceCapacity

/-! Summed capacities bound the residual moment range after group reports. -/
@[expose] public section
noncomputable section
namespace CommodityClassification.Precision.Data
open InputCoordinates
open scoped BigOperators
variable {n g : ℕ} (d : Precision.Data n)

theorem sum_cellVariance (P : Partition n g) (c : Vec n) :
    (∑a,d.cellVariance P a c)=d.residualVariance P c := by
  simp_rw [d.cellVariance_formula]
  rw [Finset.sum_sub_distrib,sum_by_partition P,d.residualVariance_identity]
  rfl

theorem residualVariance_le_capacity (P : Partition n g) (c : Vec n) (hc : ∀i,|c i|≤1) :
    d.residualVariance P c≤d.totalCapacity P := by
  rw [←d.sum_cellVariance]
  exact Finset.sum_le_sum (fun a _ => d.cellVariance_le_capacity P a c hc)

theorem totalCapacity_bounds (P : Partition n g) : 0≤d.totalCapacity P ∧ d.totalCapacity P≤1 := by
  constructor
  · exact Finset.sum_nonneg (fun a _ => (d.cellCapacity_bounds P a).1)
  · calc
      d.totalCapacity P≤∑a,d.groupWeight P a :=
        Finset.sum_le_sum (fun a _ => (d.cellCapacity_bounds P a).2)
      _=1 := by
        change (∑a,∑i∈P.cell a,d.w i)=1
        rw [sum_by_partition P,d.sum_w]

theorem report_moment_gap_le_capacity (P : Partition n g) (c e : Vec n)
    (he : e∈d.closedFiber P (d.groupTotal P c)) :
    d.secondMoment e-d.lowerMoment P (d.groupTotal P c)≤d.totalCapacity P := by
  have hh := d.residualVariance_le_capacity P e he.1
  rwa [d.residualVariance_identity,he.2] at hh

end CommodityClassification.Precision.Data
