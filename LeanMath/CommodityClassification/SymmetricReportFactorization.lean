module

public import LeanMath.CommodityClassification.GroupQuantityMaps

/-! Symmetric matrices annihilating hidden directions factor through reports. -/
@[expose] public section
noncomputable section
namespace CommodityClassification.InputCoordinates
open Matrix
variable {n g r : ℕ}

def Partition.reportQuadratic (P : Partition n g) (p q : Vec n) (L : Mat n n) : Mat g g :=
  (P.liftReport p q).transpose*L*P.liftReport p q

theorem Partition.reportQuadratic_symmetric (P : Partition n g) (p q : Vec n)
    (L : Mat n n) (hL : L.transpose=L) : (P.reportQuadratic p q L).transpose=P.reportQuadratic p q L := by
  simp only [Partition.reportQuadratic,transpose_mul,transpose_transpose,hL,Matrix.mul_assoc]

theorem Partition.symmetric_annihilator_factorization (P : Partition n g) (p q : Vec n)
    (hp : ∀i,0<p i) (hq : ∀i,0<q i) (H : HiddenBasis (P.Q q) r)
    (L : Mat n n) (hL : L.transpose=L) (hLN : L*H.N=0) :
    L=P.Q q*P.reportQuadratic p q L*(P.Q q).transpose := by
  have ht : H.N.transpose*L=0 := by
    simpa only [transpose_mul,hL,transpose_zero] using congrArg transpose hLN
  have hf := P.factor_through_report p q hp hq H L ht
  have hr := P.annihilator_projection p q hp hq H L hLN
  calc
    L=L*P.meanProjection p q := hr
    _=(P.Q q*((P.liftReport p q).transpose*L))*P.meanProjection p q := by rw [←hf]
    _=P.Q q*P.reportQuadratic p q L*(P.Q q).transpose := by
      simp only [Partition.meanProjection,Partition.reportQuadratic,Matrix.mul_assoc]

theorem Partition.symmetric_annihilator_iff (P : Partition n g) (p q : Vec n)
    (hp : ∀i,0<p i) (hq : ∀i,0<q i) (H : HiddenBasis (P.Q q) r)
    (L : Mat n n) (hL : L.transpose=L) :
    L*H.N=0 ↔ ∃B : Mat g g,B.transpose=B ∧ L=P.Q q*B*(P.Q q).transpose := by
  constructor
  · intro hLN
    exact ⟨P.reportQuadratic p q L,P.reportQuadratic_symmetric p q L hL,
      P.symmetric_annihilator_factorization p q hp hq H L hL hLN⟩
  · rintro ⟨B,_,hB⟩
    rw [hB,Matrix.mul_assoc,H.annihilates,Matrix.mul_zero]

end CommodityClassification.InputCoordinates
