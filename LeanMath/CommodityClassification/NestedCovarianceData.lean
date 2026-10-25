module

public import LeanMath.CommodityClassification.NestedCoarsestClassification

/-! Actual within-nest first and second moments, with original-product coordinates. -/
@[expose] public section
noncomputable section
set_option maxHeartbeats 600000
namespace CommodityClassification.DemandNest.Data
open Matrix
variable {n : ℕ} (d : DemandNest.Data n)

def momentCalibration : CESCost.Data n where
  p := d.sales
  w0 := d.p
  a := d.q
  p_pos := d.sales_pos
  w0_pos := d.hp
  a_pos := d.hq
  cost_identity := by rw [dotProduct_comm];rfl

end CommodityClassification.DemandNest.Data

namespace CommodityClassification.DemandNests.Data
open Matrix InputCoordinates
open scoped BigOperators
variable {n g k : ℕ} (d : DemandNests.Data n g)

def nestInputs (C : Mat n k) (a : Fin g) : Mat (d.size a) k := fun j => C (d.product a j)

def nestFirstMoment (C : Mat n k) (a : Fin g) : Vec k :=
  (d.nestInputs C a).transpose *ᵥ (d.nest a).q

def nestSecondMoment (C : Mat n k) (a : Fin g) : Mat k k :=
  (d.nestInputs C a).transpose * Supply.xi (d.nest a).p (d.nest a).q * d.nestInputs C a

def nestCovariance (C : Mat n k) (a : Fin g) : Mat k k :=
  d.nestSecondMoment C a-(d.nest a).sales⁻¹ • vecMulVec (d.nestFirstMoment C a) (d.nestFirstMoment C a)

theorem nestFirstMoment_eq_report (C : Mat n k) (a : Fin g) :
    d.nestFirstMoment C a=d.partition.report d.q C a := by
  funext l
  rw [d.partition.report_apply]
  change (∑j,C (d.product a j) l*d.q (d.product a j))=_
  simp_rw [mul_comm (C _ l)]
  exact d.sum_restrict a (fun i => d.q i*C i l)

theorem nestSecondMoment_apply (C : Mat n k) (a : Fin g) (l m : Fin k) :
    d.nestSecondMoment C a l m=∑i∈d.partition.cell a,(d.q i/d.p i)*C i l*C i m := by
  change ((d.nestInputs C a).transpose*diagonal (fun j => (d.nest a).q j/(d.nest a).p j)*
    d.nestInputs C a) l m=_
  rw [Matrix.mul_apply]
  simp only [Matrix.mul_diagonal,Matrix.transpose_apply]
  change (∑j,C (d.product a j) l*(d.q (d.product a j)/d.p (d.product a j))*C (d.product a j) m)=_
  calc
    _=∑j,(d.q (d.product a j)/d.p (d.product a j))*C (d.product a j) l*C (d.product a j) m := by
      apply Finset.sum_congr rfl
      intro j _
      ring
    _=_ := d.sum_restrict a (fun i => (d.q i/d.p i)*C i l*C i m)

theorem nestSecondMoment_sum (C : Mat n k) (a : Fin g) :
    d.nestSecondMoment C a=∑i∈d.partition.cell a,(d.q i/d.p i) • vecMulVec (C i) (C i) := by
  ext l m
  rw [d.nestSecondMoment_apply]
  simp only [Matrix.sum_apply,Matrix.smul_apply,smul_eq_mul,Matrix.vecMulVec_apply,mul_assoc]

theorem nestCovariance_manuscript (C : Mat n k) (a : Fin g) :
    d.nestCovariance C a=d.nestSecondMoment C a-
      (d.partition.sales d.p d.q a)⁻¹ •
        vecMulVec (d.partition.report d.q C a) (d.partition.report d.q C a) := by
  rw [nestCovariance,d.nestFirstMoment_eq_report,d.nest_sales]

theorem nestCovariance_conjugate (C : Mat n k) (a : Fin g) :
    d.nestCovariance C a=(d.nestInputs C a).transpose *
      Supply.curvature (d.nest a).q (d.nest a).p (d.nest a).sales*d.nestInputs C a := by
  have hv : (d.nest a).q ᵥ* d.nestInputs C a=(d.nestInputs C a).transpose *ᵥ (d.nest a).q := by
    funext l
    simp only [Matrix.vecMul,Matrix.mulVec,Matrix.transpose_apply,dotProduct,mul_comm]
  rw [Supply.curvature,Matrix.mul_sub,Matrix.sub_mul,Matrix.mul_smul,Matrix.smul_mul,
    Matrix.mul_vecMulVec,Matrix.vecMulVec_mul,hv]
  rfl

theorem nestCovariance_posSemidef (C : Mat n k) (a : Fin g) :
    (d.nestCovariance C a).PosSemidef := by
  rw [d.nestCovariance_conjugate]
  simpa only [Matrix.conjTranspose_eq_transpose_of_trivial,DemandNest.Data.momentCalibration] using
    (Supply.curvature_posSemidef (d.nest a).momentCalibration).conjTranspose_mul_mul_same
      (d.nestInputs C a)

end CommodityClassification.DemandNests.Data
