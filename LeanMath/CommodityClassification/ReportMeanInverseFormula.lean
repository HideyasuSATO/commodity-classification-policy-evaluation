module

public import LeanMath.CommodityClassification.PrecisionPredictionRisk

/-! The exact inverse-Xi formula for the positive group-mean lift. -/
@[expose] public section
noncomputable section
namespace CommodityClassification.InputCoordinates
open Matrix
variable {n g k : ℕ}

def Partition.inverseXiReportLift (P : Partition n g) (p q : Vec n) : Mat n g :=
  (Supply.xi p q)⁻¹*P.Q q*((P.Q q).transpose*(Supply.xi p q)⁻¹*P.Q q)⁻¹

theorem Partition.inverseXi_gram_formula (P : Partition n g) (p q : Vec n)
    (hp : ∀i,0<p i) (hq : ∀i,0<q i) :
    (P.Q q).transpose*(Supply.xi p q)⁻¹*P.Q q=diagonal (P.sales p q) := by
  rw [Matrix.mul_assoc,P.weighted_eq_lift_sales p q hp hq,←Matrix.mul_assoc]
  change P.report q (P.liftReport p q)*diagonal (P.sales p q)=_
  rw [P.report_lift p q hp hq,Matrix.one_mul]

theorem Partition.inverseXi_gram_posDef (P : Partition n g) (p q : Vec n)
    (hp : ∀i,0<p i) (hq : ∀i,0<q i) :
    ((P.Q q).transpose*(Supply.xi p q)⁻¹*P.Q q).PosDef := by
  rw [P.inverseXi_gram_formula p q hp hq]
  exact Matrix.PosDef.diagonal (P.sales_pos p q hp hq)

theorem Partition.inverseXi_gram_inverse (P : Partition n g) (p q : Vec n)
    (hp : ∀i,0<p i) (hq : ∀i,0<q i) :
    ((P.Q q).transpose*(Supply.xi p q)⁻¹*P.Q q)⁻¹=diagonal (fun a => (P.sales p q a)⁻¹) := by
  rw [P.inverseXi_gram_formula p q hp hq]
  apply Matrix.inv_eq_right_inv
  rw [Matrix.diagonal_mul_diagonal]
  have hh : (fun a => P.sales p q a*(P.sales p q a)⁻¹)=fun _ => (1:ℝ) := by
    funext a
    exact mul_inv_cancel₀ (ne_of_gt (P.sales_pos p q hp hq a))
  rw [hh,Matrix.diagonal_one]

theorem Partition.inverseXiReportLift_eq (P : Partition n g) (p q : Vec n)
    (hp : ∀i,0<p i) (hq : ∀i,0<q i) : P.inverseXiReportLift p q=P.liftReport p q := by
  rw [inverseXiReportLift,P.inverseXi_gram_inverse p q hp hq]
  exact (P.liftReport_weighted p q hp hq).symm

theorem Partition.mean_inverseXi_formula (P : Partition n g) (p q : Vec n)
    (hp : ∀i,0<p i) (hq : ∀i,0<q i) (C : Mat n k) :
    P.mean p q C=P.inverseXiReportLift p q*((P.Q q).transpose*C) := by
  rw [P.inverseXiReportLift_eq p q hp hq]
  exact P.mean_eq_lift p q C

end CommodityClassification.InputCoordinates
