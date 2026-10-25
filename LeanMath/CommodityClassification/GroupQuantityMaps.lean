module

public import LeanMath.CommodityClassification.ParentKernelFactorization

/-! Value-weighted group quantities and injectivity on parent report columns. -/
@[expose] public section
noncomputable section
namespace CommodityClassification.InputCoordinates
open Matrix
variable {n g h r : ℕ}

def Partition.valueAggregation (P : Partition n g) (p : Vec n) : Mat g n := (P.Q p).transpose

theorem Partition.valueAggregation_xi (P : Partition n g) (p q : Vec n)
    (hp : ∀i,0<p i) : P.valueAggregation p * Supply.xi p q=(P.Q q).transpose := by
  ext a i
  simp only [Partition.valueAggregation,Supply.xi,mul_diagonal,transpose_apply,Partition.Q]
  split_ifs
  · field_simp [(hp i).ne']
  · simp

theorem Partition.valueAggregation_eq_sales_lift (P : Partition n g) (p q : Vec n)
    (hp : ∀i,0<p i) (hq : ∀i,0<q i) :
    P.valueAggregation p=diagonal (P.sales p q)*(P.liftReport p q).transpose := by
  ext a i
  simp only [Partition.valueAggregation,diagonal_mul,transpose_apply,Partition.Q,Partition.liftReport]
  split_ifs
  · field_simp [(P.sales_pos p q hp hq a).ne']
  · simp

theorem Partition.valueAggregation_Q (P : Partition n g) (p q : Vec n)
    (hp : ∀i,0<p i) (hq : ∀i,0<q i) :
    P.valueAggregation p*P.Q q=diagonal (P.sales p q) := by
  have ht : (P.liftReport p q).transpose*P.Q q=1 := by
    simpa only [Partition.report,transpose_mul,transpose_transpose,transpose_one] using
      congrArg transpose (P.report_lift p q hp hq)
  rw [P.valueAggregation_eq_sales_lift p q hp hq,Matrix.mul_assoc,ht,Matrix.mul_one]

theorem Refinement.parent_surjective {P : Partition n g} {P0 : Partition n h}
    (R : Refinement P P0) : Function.Surjective R.parent := by
  intro a
  obtain ⟨i,hi⟩ := P0.onto a
  exact ⟨P.group i,(R.compatible i).symm.trans hi⟩

theorem Refinement.incidence_mulVec {P : Partition n g} {P0 : Partition n h}
    (R : Refinement P P0) (z : Vec h) (a : Fin g) :
    (R.incidence *ᵥ z) a=z (R.parent a) := by
  simp [Refinement.incidence,mulVec,dotProduct]

theorem Refinement.incidence_injective {P : Partition n g} {P0 : Partition n h}
    (R : Refinement P P0) : Function.Injective (fun z : Vec h => R.incidence *ᵥ z) := by
  intro x y he
  ext a
  obtain ⟨b,hb⟩ := R.parent_surjective a
  simpa only [R.incidence_mulVec,hb] using congrFun he b

theorem Refinement.valueAggregation_parent {P : Partition n g} {P0 : Partition n h}
    (R : Refinement P P0) (p q : Vec n) (hp : ∀i,0<p i) (hq : ∀i,0<q i) :
    P.valueAggregation p*P0.Q q=diagonal (P.sales p q)*R.incidence := by
  rw [R.Q_factor q,←Matrix.mul_assoc,P.valueAggregation_Q p q hp hq]

theorem Refinement.valueAggregation_parent_injective {P : Partition n g} {P0 : Partition n h}
    (R : Refinement P P0) (p q : Vec n) (hp : ∀i,0<p i) (hq : ∀i,0<q i) :
    Function.Injective (fun z : Vec h => (P.valueAggregation p*P0.Q q) *ᵥ z) := by
  intro x y he
  apply R.incidence_injective
  change (P.valueAggregation p*P0.Q q) *ᵥ x=(P.valueAggregation p*P0.Q q) *ᵥ y at he
  rw [R.valueAggregation_parent p q hp hq,←Matrix.mulVec_mulVec,←Matrix.mulVec_mulVec] at he
  ext a
  have hh := congrFun he a
  simp only [mulVec_diagonal] at hh
  exact mul_left_cancel₀ (P.sales_pos p q hp hq a).ne' hh

theorem Refinement.valueAggregation_parent_cancel {P : Partition n g} {P0 : Partition n h}
    (R : Refinement P P0) (p q : Vec n) (hp : ∀i,0<p i) (hq : ∀i,0<q i)
    (Γ : Mat h r) (hΓ : P.valueAggregation p*P0.Q q*Γ=0) : Γ=0 := by
  ext a j
  have hc : (fun a => Γ a j)=(0 : Vec h) := by
    apply R.valueAggregation_parent_injective p q hp hq
    change (P.valueAggregation p*P0.Q q) *ᵥ (fun a => Γ a j)=
      (P.valueAggregation p*P0.Q q) *ᵥ 0
    rw [Matrix.mulVec_zero]
    exact funext fun b => congrFun (congrFun hΓ b) j
  exact congrFun hc a

theorem Partition.valueAggregation_transpose_injective (P : Partition n g) (p q : Vec n)
    (hp : ∀i,0<p i) (hq : ∀i,0<q i) :
    Function.Injective (fun z : Vec g => (P.valueAggregation p).transpose *ᵥ z) := by
  intro x y he
  have ht : (P.Q q).transpose*(P.valueAggregation p).transpose=diagonal (P.sales p q) := by
    simpa only [transpose_mul,diagonal_transpose] using
      congrArg transpose (P.valueAggregation_Q p q hp hq)
  have hh := congrArg (fun z => (P.Q q).transpose *ᵥ z) he
  rw [Matrix.mulVec_mulVec,Matrix.mulVec_mulVec,ht] at hh
  ext a
  have ha := congrFun hh a
  simp only [mulVec_diagonal] at ha
  exact mul_left_cancel₀ (P.sales_pos p q hp hq a).ne' ha

end CommodityClassification.InputCoordinates
