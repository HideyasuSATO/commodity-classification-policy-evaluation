module

public import LeanMath.CommodityClassification.ResourceCancellationSpace

/-! Exact finite spanning of hidden reports by within-cell weighted exchanges. -/
@[expose] public section
noncomputable section
namespace CommodityClassification.InputCoordinates
open Matrix
open scoped BigOperators
variable {n g : ℕ}

def weightedExchange (q : Vec n) (i j : Fin n) : Vec n :=
  (q i)⁻¹ • Pi.single i (1:ℝ) - (q j)⁻¹ • Pi.single j (1:ℝ)

def Partition.representative (P : Partition n g) (a : Fin g) : Fin n :=
  (P.onto a).choose

theorem Partition.representative_group (P : Partition n g) (a : Fin g) :
    P.group (P.representative a)=a := (P.onto a).choose_spec

theorem Partition.weighted_exchange_hidden (P : Partition n g) (q : Vec n)
    (hq : ∀i,0<q i) (i j : Fin n) (hij : P.group i=P.group j) :
    (P.Q q).transpose *ᵥ weightedExchange q i j=0 := by
  ext a
  simp only [weightedExchange,mulVec_sub,mulVec_smul,mulVec_single_one,
    Pi.sub_apply,Pi.smul_apply,smul_eq_mul,col_apply,transpose_apply,Partition.Q]
  by_cases hi : P.group i=a
  · have hj : P.group j=a := hij.symm.trans hi
    simp [hi,hj,(hq i).ne',(hq j).ne']
  · have hj : P.group j≠a := fun he => hi (hij.trans he)
    simp [hi,hj]

theorem Partition.sum_by_group (P : Partition n g) (f : Vec n) (v : Fin g → Vec n) :
    (∑ i, f i • v (P.group i)) =
      ∑ a, (∑ i, if P.group i=a then f i else 0) • v a := by
  simp only [Finset.sum_smul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  simp only [ite_smul,zero_smul]
  simp

theorem Partition.hidden_cell_sum (P : Partition n g) (q x : Vec n)
    (hx : (P.Q q).transpose *ᵥ x=0) (a : Fin g) :
    (∑ i, if P.group i=a then q i*x i else 0)=0 := by
  have hh := congrFun hx a
  simpa only [mulVec,dotProduct,transpose_apply,Partition.Q,ite_mul,zero_mul,
    Pi.zero_apply] using hh

theorem weighted_single_sum (q x : Vec n) (hq : ∀i,0<q i) :
    (∑ i, (q i*x i) • ((q i)⁻¹ • Pi.single i (1:ℝ)))=x := by
  ext j
  simp only [smul_smul,Finset.sum_apply,Pi.smul_apply,smul_eq_mul,Pi.single_apply]
  rw [Finset.sum_eq_single j]
  · simp only [ite_true,mul_one]
    rw [mul_right_comm,mul_inv_cancel₀ (hq j).ne',one_mul]
  · intro i _ hij
    simp [Ne.symm hij]
  · simp

theorem Partition.hidden_exchange_expansion (P : Partition n g) (q x : Vec n)
    (hq : ∀i,0<q i) (hx : (P.Q q).transpose *ᵥ x=0) :
    x = ∑ i, (q i*x i) • weightedExchange q i (P.representative (P.group i)) := by
  simp only [weightedExchange,smul_sub,Finset.sum_sub_distrib]
  rw [weighted_single_sum q x hq]
  have hz : (∑ i, (q i*x i) •
      ((q (P.representative (P.group i)))⁻¹ • Pi.single (P.representative (P.group i)) (1:ℝ)))=0 := by
    let v : Fin g → Vec n := fun a =>
      (q (P.representative a))⁻¹ • (Pi.single (P.representative a) (1:ℝ) : Vec n)
    change (∑ i,(q i*x i) • v (P.group i))=0
    rw [P.sum_by_group (fun i => q i*x i) v]
    simp only [P.hidden_cell_sum q x hx,zero_smul,Finset.sum_const_zero]
  rw [hz,sub_zero]

theorem Partition.span_weighted_exchanges (P : Partition n g) (q : Vec n)
    (hq : ∀i,0<q i) :
    Submodule.span ℝ {v : Vec n | ∃ i j : Fin n,
      P.group i=P.group j ∧ v=weightedExchange q i j} =
      LinearMap.ker (P.Q q).transpose.mulVecLin := by
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro x ⟨i,j,hij,rfl⟩
    exact P.weighted_exchange_hidden q hq i j hij
  · intro x hx
    rw [P.hidden_exchange_expansion q x hq hx]
    apply Submodule.sum_mem
    intro i _
    apply Submodule.smul_mem
    apply Submodule.subset_span
    exact ⟨i,P.representative (P.group i),(P.representative_group _).symm,rfl⟩

end CommodityClassification.InputCoordinates
