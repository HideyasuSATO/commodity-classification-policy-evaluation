module

public import LeanMath.CommodityClassification.NestedCovarianceData

/-! The exact sales-weighted covariance, with no division by group sales. -/
@[expose] public section
noncomputable section
set_option maxHeartbeats 800000
namespace CommodityClassification.DemandNests.Data
open Matrix InputCoordinates
open scoped BigOperators
variable {n g k : ℕ} (d : DemandNests.Data n g)

theorem nestCovariance_sales_weighted (C : Mat n k) (a : Fin g) :
    d.nestCovariance C a=∑i∈d.partition.cell a,(d.p i*d.q i) •
      vecMulVec (fun l => C i l/d.p i-d.partition.report d.q C a l/d.partition.sales d.p d.q a)
        (fun l => C i l/d.p i-d.partition.report d.q C a l/d.partition.sales d.p d.q a) := by
  ext l m
  rw [d.nestCovariance_manuscript]
  simp only [Matrix.sub_apply,Matrix.smul_apply,smul_eq_mul,Matrix.vecMulVec_apply,Matrix.sum_apply]
  rw [d.nestSecondMoment_apply]
  let S := d.partition.sales d.p d.q a
  let u := d.partition.report d.q C a l
  let v := d.partition.report d.q C a m
  have hS : S≠0 := (d.partition.sales_pos d.p d.q d.hp d.hq a).ne'
  have hu : (∑i∈d.partition.cell a,d.q i*C i l)=u := (d.partition.report_apply d.q C a l).symm
  have hv : (∑i∈d.partition.cell a,d.q i*C i m)=v := (d.partition.report_apply d.q C a m).symm
  have hs : (∑i∈d.partition.cell a,d.p i*d.q i)=S := by
    simpa only [mul_comm] using (d.partition.sales_apply d.p d.q a).symm
  change (∑i∈d.partition.cell a,(d.q i/d.p i)*C i l*C i m)-S⁻¹*(u*v)=
    ∑i∈d.partition.cell a,(d.p i*d.q i)*((C i l/d.p i-u/S)*(C i m/d.p i-v/S))
  have he : (∑i∈d.partition.cell a,(d.p i*d.q i)*((C i l/d.p i-u/S)*(C i m/d.p i-v/S)))=
      (∑i∈d.partition.cell a,(d.q i/d.p i)*C i l*C i m)-(v/S)*u-(u/S)*v+(u*v/S^2)*S := by
    calc
      _=∑i∈d.partition.cell a,((d.q i/d.p i)*C i l*C i m-
          (v/S)*(d.q i*C i l)-(u/S)*(d.q i*C i m)+(u*v/S^2)*(d.p i*d.q i)) := by
        apply Finset.sum_congr rfl
        intro i _
        field_simp [(d.hp i).ne',hS]
        ring
      _=_ := by
        simp only [Finset.sum_add_distrib,Finset.sum_sub_distrib,←Finset.mul_sum,hu,hv,hs]
  rw [he]
  field_simp [hS]
  ring

theorem nestCovariance_quadratic (C : Mat n k) (a : Fin g) (z : Vec k) :
    dotProduct z (d.nestCovariance C a *ᵥ z)=
      ∑i∈d.partition.cell a,(d.p i*d.q i)*
        (dotProduct (fun l => C i l/d.p i-d.partition.report d.q C a l/d.partition.sales d.p d.q a) z)^2 := by
  rw [d.nestCovariance_sales_weighted]
  simp only [Matrix.sum_mulVec,dotProduct_sum,Matrix.smul_mulVec,dotProduct_smul,
    Matrix.vecMulVec_mulVec,smul_eq_mul,op_smul_eq_mul]
  apply Finset.sum_congr rfl
  intro i _
  rw [dotProduct_comm z]
  ring

theorem nestCovariance_zero_iff (C : Mat n k) (a : Fin g) :
    d.nestCovariance C a=0 ↔ ∀i∈d.partition.cell a,∀l,
      C i l/d.p i=d.partition.report d.q C a l/d.partition.sales d.p d.q a := by
  constructor
  · intro hzero i hi l
    have hh := d.nestCovariance_quadratic C a (Pi.single l 1)
    rw [hzero,Matrix.zero_mulVec,dotProduct_zero] at hh
    simp only [dotProduct_single,mul_one] at hh
    have hterm := Finset.single_le_sum (s := d.partition.cell a)
      (fun j _ => mul_nonneg (mul_pos (d.hp j) (d.hq j)).le (sq_nonneg
        (C j l/d.p j-d.partition.report d.q C a l/d.partition.sales d.p d.q a))) hi
    rw [←hh] at hterm
    have hs : (C i l/d.p i-d.partition.report d.q C a l/d.partition.sales d.p d.q a)^2=0 := by
      nlinarith [mul_pos (d.hp i) (d.hq i),sq_nonneg
        (C i l/d.p i-d.partition.report d.q C a l/d.partition.sales d.p d.q a)]
    exact sub_eq_zero.mp (sq_eq_zero_iff.mp hs)
  · intro hc
    rw [d.nestCovariance_sales_weighted]
    apply Finset.sum_eq_zero
    intro i hi
    have hz : (fun l => C i l/d.p i-d.partition.report d.q C a l/d.partition.sales d.p d.q a)=0 := by
      funext l
      exact sub_eq_zero.mpr (hc i hi l)
    rw [hz]
    simp

end CommodityClassification.DemandNests.Data
