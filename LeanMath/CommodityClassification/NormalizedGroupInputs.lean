module

public import LeanMath.CommodityClassification.UntaxedLiteralCost

/-! Unit inputs of composites with price one and baseline quantity group sales. -/
@[expose] public section
noncomputable section
set_option maxHeartbeats 1200000
namespace CommodityClassification.InputCoordinates
open Matrix
open scoped BigOperators
variable {n g f k : ℕ}

def Partition.normalizedReport (P : Partition n g) (p q : Vec n) (A : Mat n f) : Mat g f :=
  diagonal (fun a => (P.sales p q a)⁻¹)*P.report q A

theorem Partition.normalizedReport_apply (P : Partition n g) (p q : Vec n) (A : Mat n f)
    (a : Fin g) (j : Fin f) :
    P.normalizedReport p q A a j=(P.sales p q a)⁻¹*P.report q A a j := by
  simp only [Partition.normalizedReport,Matrix.diagonal_mul]

theorem Partition.normalizedReport_positive (P : Partition n g) (p q : Vec n)
    (hp : ∀i,0<p i) (hq : ∀i,0<q i) (A : Mat n f) (hA : Positive A) :
    Positive (P.normalizedReport p q A) := by
  intro a j
  rw [P.normalizedReport_apply]
  exact mul_pos (inv_pos.mpr (P.sales_pos p q hp hq a)) (P.report_positive q hq A hA a j)

theorem Partition.normalizedReport_cost (P : Partition n g) (e : Frame k) (p q : Vec n)
    (hp : ∀i,0<p i) (hq : ∀i,0<q i) (A : Mat n (k+1)) (hc : A *ᵥ e.w=p) :
    P.normalizedReport p q A *ᵥ e.w=(fun _ => 1) := by
  rw [Partition.normalizedReport,←Matrix.mulVec_mulVec,P.report_cost e p q A hc]
  ext a
  simp only [Matrix.mulVec_diagonal]
  exact inv_mul_cancel₀ (P.sales_pos p q hp hq a).ne'

theorem Partition.normalizedReport_mul (P : Partition n g) (p q : Vec n)
    (A : Mat n f) (B : Mat f k) :
    P.normalizedReport p q A*B=P.normalizedReport p q (A*B) := by
  simp only [Partition.normalizedReport,P.report_mul,Matrix.mul_assoc]

theorem Partition.normalizedReport_reconstruct (P : Partition n g) (e : Frame k)
    (p q : Vec n) (hp : ∀i,0<p i) (hq : ∀i,0<q i) (C : Mat n k) :
    e.reconstruct (fun _ => 1) (P.normalizedReport p q C)=
      P.normalizedReport p q (e.reconstruct p C) := by
  have hh := e.reconstruct_original (P.normalizedReport p q (e.reconstruct p C))
  rw [P.normalizedReport_cost e p q hp hq _ (e.reconstruct_cost p C),
    P.normalizedReport_mul,e.reconstruct_exposure] at hh
  exact hh

theorem Partition.normalizedReport_totalInputs (P : Partition n g) (p q : Vec n)
    (hp : ∀i,0<p i) (hq : ∀i,0<q i) (A : Mat n f) :
    Supply.totalInputs (P.sales p q) (P.normalizedReport p q A)=Supply.totalInputs q A := by
  ext j
  rw [←Supply.sum_report_eq_total P q A j]
  change (∑a,P.sales p q a*P.normalizedReport p q A a j)=_
  apply Finset.sum_congr rfl
  intro a _
  rw [P.normalizedReport_apply]
  field_simp [(P.sales_pos p q hp hq a).ne']

end CommodityClassification.InputCoordinates
