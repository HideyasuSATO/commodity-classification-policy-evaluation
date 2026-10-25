module
public import LeanMath.CommodityClassification.EconomicReportFibers
public import LeanMath.CommodityClassification.SupplyCandidates
@[expose] public section
set_option maxHeartbeats 2400000
namespace CommodityClassification.InputCoordinates
open Matrix
open scoped BigOperators Topology
variable {n g h k : ℕ}

noncomputable def Partition.liftReport (P : Partition n g) (p q : Vec n) : Mat n g :=
  fun i a => if P.group i=a then p i/P.sales p q a else 0

theorem Partition.liftReport_mul (P : Partition n g) (p q : Vec n) (J : Mat g k) :
    P.liftReport p q*J = fun i j => p i/P.sales p q (P.group i)*J (P.group i) j := by
  ext i j
  rw [Matrix.mul_apply,Finset.sum_eq_single (P.group i)]
  · simp [Partition.liftReport]
  · intro a _ ha
    simp [Partition.liftReport,Ne.symm ha]
  · simp

theorem Partition.mean_eq_lift (P : Partition n g) (p q : Vec n) (C : Mat n k) :
    P.mean p q C=P.liftReport p q*P.report q C := by
  rw [P.liftReport_mul]
  rfl

theorem Partition.report_lift (P : Partition n g) (p q : Vec n)
    (hp : ∀i,0<p i) (hq : ∀i,0<q i) : P.report q (P.liftReport p q)=1 := by
  ext a b
  rw [P.report_apply]
  change (∑i∈P.cell a,q i*(if P.group i=b then p i/P.sales p q b else 0))=
    if a=b then 1 else 0
  have he : (∑i∈P.cell a,q i*(if P.group i=b then p i/P.sales p q b else 0))=
      ∑i∈P.cell a,if a=b then q i*p i/P.sales p q b else 0 := by
    apply Finset.sum_congr rfl
    intro i hi
    rw [(P.mem_cell a i).mp hi]
    split_ifs <;> ring
  rw [he]
  by_cases hab : a=b
  · subst b
    simp only [ite_true,div_eq_mul_inv]
    rw [←Finset.sum_mul,←P.sales_apply]
    exact mul_inv_cancel₀ (P.sales_pos p q hp hq a).ne'
  · simp [hab]

noncomputable def Partition.meanProjection (P : Partition n g) (p q : Vec n) : Mat n n :=
  P.liftReport p q*(P.Q q).transpose

theorem Partition.projection_mul (P : Partition n g) (p q : Vec n) (C : Mat n k) :
    P.meanProjection p q*C=P.mean p q C := by
  rw [P.mean_eq_lift]
  exact Matrix.mul_assoc _ _ _

theorem Partition.projection_report (P : Partition n g) (p q : Vec n)
    (hp : ∀i,0<p i) (hq : ∀i,0<q i) :
    (P.Q q).transpose*P.meanProjection p q=(P.Q q).transpose := by
  rw [meanProjection,←Matrix.mul_assoc]
  change P.report q (P.liftReport p q)*(P.Q q).transpose=_
  rw [P.report_lift p q hp hq,Matrix.one_mul]

theorem Partition.projection_idempotent (P : Partition n g) (p q : Vec n)
    (hp : ∀i,0<p i) (hq : ∀i,0<q i) :
    P.meanProjection p q*P.meanProjection p q=P.meanProjection p q := by
  change (P.liftReport p q*(P.Q q).transpose)*P.meanProjection p q=_
  rw [Matrix.mul_assoc,P.projection_report p q hp hq]
  rfl

theorem Partition.projection_mul_lift (P : Partition n g) (p q : Vec n)
    (hp : ∀i,0<p i) (hq : ∀i,0<q i) :
    P.meanProjection p q*P.liftReport p q=P.liftReport p q := by
  rw [meanProjection,Matrix.mul_assoc]
  change P.liftReport p q*P.report q (P.liftReport p q)=_
  rw [P.report_lift p q hp hq,Matrix.mul_one]

theorem Partition.projection_hidden_zero (P : Partition n g) (p q : Vec n)
    (x : Vec n) (hx : (P.Q q).transpose *ᵥ x=0) : P.meanProjection p q *ᵥ x=0 := by
  rw [meanProjection,←Matrix.mulVec_mulVec,hx,Matrix.mulVec_zero]

theorem Partition.projection_residual_hidden (P : Partition n g) (p q : Vec n)
    (hp : ∀i,0<p i) (hq : ∀i,0<q i) (x : Vec n) :
    (P.Q q).transpose *ᵥ (x-P.meanProjection p q *ᵥ x)=0 := by
  rw [Matrix.mulVec_sub,Matrix.mulVec_mulVec,P.projection_report p q hp hq,sub_self]

theorem Refinement.projection_parent_report {P : Partition n g} {P0 : Partition n h}
    (R : Refinement P P0) (p q : Vec n) (hp : ∀i,0<p i) (hq : ∀i,0<q i) :
    (P0.Q q).transpose*P.meanProjection p q=(P0.Q q).transpose := by
  rw [R.Q_factor q,Matrix.transpose_mul,Matrix.mul_assoc,P.projection_report p q hp hq]

theorem Refinement.projection_preserves_parent_kernel {P : Partition n g} {P0 : Partition n h}
    (R : Refinement P P0) (p q : Vec n) (hp : ∀i,0<p i) (hq : ∀i,0<q i)
    (x : Vec n) (hx : (P0.Q q).transpose *ᵥ x=0) :
    (P0.Q q).transpose *ᵥ (P.meanProjection p q *ᵥ x)=0 := by
  rw [Matrix.mulVec_mulVec,R.projection_parent_report p q hp hq,hx]

/-- The lift uses precisely the inverse-Xi report columns in the manuscript. -/
theorem Partition.liftReport_weighted (P : Partition n g) (p q : Vec n)
    (hp : ∀i,0<p i) (hq : ∀i,0<q i) :
    P.liftReport p q=(Supply.xi p q)⁻¹*P.Q q*Matrix.diagonal (fun a => (P.sales p q a)⁻¹) := by
  have hi : (Supply.xi p q)⁻¹=Matrix.diagonal (fun i => p i/q i) := by
    apply Matrix.inv_eq_right_inv
    simp only [Supply.xi,Matrix.diagonal_mul_diagonal]
    have hh : (fun i => q i/p i*(p i/q i))=fun _ => (1:ℝ) := by
      ext i
      field_simp [(hp i).ne',(hq i).ne']
    rw [hh,Matrix.diagonal_one]
  rw [hi]
  ext i a
  simp only [Matrix.diagonal_mul,Matrix.mul_diagonal,Partition.Q,Partition.liftReport]
  split_ifs
  · field_simp [(hp i).ne',(hq i).ne']
  · simp

theorem Partition.weighted_eq_lift_sales (P : Partition n g) (p q : Vec n)
    (hp : ∀i,0<p i) (hq : ∀i,0<q i) :
    (Supply.xi p q)⁻¹*P.Q q=P.liftReport p q*Matrix.diagonal (P.sales p q) := by
  rw [P.liftReport_weighted p q hp hq,Matrix.mul_assoc,Matrix.diagonal_mul_diagonal]
  have he : (fun a => (P.sales p q a)⁻¹*P.sales p q a)=fun _ => (1:ℝ) := by
    ext a; exact inv_mul_cancel₀ (P.sales_pos p q hp hq a).ne'
  rw [he,Matrix.diagonal_one,Matrix.mul_one]

theorem Partition.projection_range_weighted (P : Partition n g) (p q : Vec n)
    (hp : ∀i,0<p i) (hq : ∀i,0<q i) (x : Vec n) :
    x∈LinearMap.range (P.meanProjection p q).mulVecLin ↔
      ∃v : Vec g,((Supply.xi p q)⁻¹*P.Q q) *ᵥ v=x := by
  constructor
  · rintro ⟨u,rfl⟩
    refine ⟨Matrix.diagonal (fun a => (P.sales p q a)⁻¹) *ᵥ ((P.Q q).transpose *ᵥ u),?_⟩
    rw [Matrix.mulVec_mulVec,←P.liftReport_weighted p q hp hq]
    change P.liftReport p q *ᵥ ((P.Q q).transpose *ᵥ u)=(P.liftReport p q*(P.Q q).transpose) *ᵥ u
    exact Matrix.mulVec_mulVec _ _ _
  · rintro ⟨v,rfl⟩
    refine ⟨((Supply.xi p q)⁻¹*P.Q q) *ᵥ v,?_⟩
    change P.meanProjection p q *ᵥ (_ *ᵥ v)=_
    rw [P.weighted_eq_lift_sales p q hp hq,Matrix.mulVec_mulVec,←Matrix.mul_assoc,
      P.projection_mul_lift p q hp hq]

end CommodityClassification.InputCoordinates
