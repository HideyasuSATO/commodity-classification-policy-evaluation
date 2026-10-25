module

public import LeanMath.CommodityClassification.AnswerMeanProjection
public import LeanMath.CommodityClassification.ReportKernelCoordinates

/-! Constructive factorization through observed parent totals. -/
@[expose] public section
noncomputable section
namespace CommodityClassification.InputCoordinates
open Matrix
variable {n k g r s : ℕ}

theorem Partition.annihilator_projection (P : Partition n g) (p q : Vec n)
    (hp : ∀i,0<p i) (hq : ∀i,0<q i) (H : HiddenBasis (P.Q q) s)
    (A : Mat r n) (hA : A*H.N=0) : A = A * P.meanProjection p q := by
  have hx (x : Vec n) : A *ᵥ x = A *ᵥ (P.meanProjection p q *ᵥ x) := by
    have hk := P.projection_residual_hidden p q hp hq x
    obtain ⟨z,hz⟩ := (H.spans _).mp hk
    have hh : A *ᵥ (x-P.meanProjection p q *ᵥ x)=0 := by
      rw [← hz,mulVec_mulVec,hA,zero_mulVec]
    exact sub_eq_zero.mp (by simpa only [mulVec_sub] using hh)
  ext i j
  have hh := congrFun (hx (Pi.single j 1)) i
  rw [mulVec_mulVec] at hh
  simpa only [mulVec_single_one,col_apply] using hh

theorem Partition.factor_through_report (P : Partition n g) (p q : Vec n)
    (hp : ∀i,0<p i) (hq : ∀i,0<q i) (H : HiddenBasis (P.Q q) s)
    (V : Mat n r) (hV : H.N.transpose*V=0) :
    V = P.Q q * ((P.liftReport p q).transpose * V) := by
  have ht : V.transpose*H.N=0 := by
    simpa only [transpose_mul,transpose_transpose,transpose_zero] using congrArg transpose hV
  have hh := P.annihilator_projection p q hp hq H V.transpose ht
  have he := congrArg transpose hh
  simpa only [transpose_mul,transpose_transpose,Partition.meanProjection,
    Matrix.mul_assoc] using he

theorem Partition.in_column_iff_annihilates_kernel (P : Partition n g) (p q : Vec n)
    (hp : ∀i,0<p i) (hq : ∀i,0<q i) (H : HiddenBasis (P.Q q) s)
    (V : Mat n r) : (∃ Γ : Mat g r,V=P.Q q*Γ) ↔ H.N.transpose*V=0 := by
  constructor
  · rintro ⟨Γ,rfl⟩
    have ht : H.N.transpose*P.Q q=0 := by
      simpa only [transpose_mul,transpose_transpose,transpose_zero] using
        congrArg transpose H.annihilates
    rw [← Matrix.mul_assoc,ht,Matrix.zero_mul]
  · intro hh
    exact ⟨(P.liftReport p q).transpose*V,P.factor_through_report p q hp hq H V hh⟩

theorem Partition.linear_restrictions_factor_iff (P : Partition n g) (p q : Vec n)
    (hp : ∀i,0<p i) (hq : ∀i,0<q i) (H : HiddenBasis (P.Q q) s)
    (L : Mat n n) (hL : L.transpose=L) (N : Mat n r) (C0 : Mat n k)
    (J0 : Mat g k) (hreport : P.report q C0=J0) :
    (N.transpose*L*C0=0 ∧ N.transpose*L*H.N=0) ↔
      ∃ Γ : Mat g r,L*N=P.Q q*Γ ∧ J0.transpose*Γ=0 := by
  have hrep : C0.transpose*P.Q q=J0.transpose := by
    simpa only [Partition.report,transpose_mul,transpose_transpose] using
      congrArg transpose hreport
  constructor
  · rintro ⟨hA,hS⟩
    have hSt : H.N.transpose*(L*N)=0 := by
      simpa only [transpose_mul,transpose_transpose,hL,Matrix.mul_assoc,transpose_zero] using
        congrArg transpose hS
    obtain ⟨Γ,hΓ⟩ := (P.in_column_iff_annihilates_kernel p q hp hq H (L*N)).mpr hSt
    refine ⟨Γ,hΓ,?_⟩
    have hAt : C0.transpose*(L*N)=0 := by
      simpa only [transpose_mul,transpose_transpose,hL,Matrix.mul_assoc,transpose_zero] using
        congrArg transpose hA
    rwa [hΓ,← Matrix.mul_assoc,hrep] at hAt
  · rintro ⟨Γ,hΓ,hJ⟩
    have hAt : C0.transpose*(L*N)=0 := by
      rw [hΓ,← Matrix.mul_assoc,hrep,hJ]
    have hSt := (P.in_column_iff_annihilates_kernel p q hp hq H (L*N)).mp ⟨Γ,hΓ⟩
    constructor
    · simpa only [transpose_mul,transpose_transpose,hL,transpose_zero,Matrix.mul_assoc] using
        congrArg transpose hAt
    · simpa only [transpose_mul,transpose_transpose,hL,transpose_zero,Matrix.mul_assoc] using
        congrArg transpose hSt

end CommodityClassification.InputCoordinates
