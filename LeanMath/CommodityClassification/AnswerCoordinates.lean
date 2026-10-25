module
public import LeanMath.CommodityClassification.AnswerComplement
@[expose] public section
set_option maxHeartbeats 2400000
namespace CommodityClassification.InputCoordinates
open Matrix Filter
open scoped BigOperators Topology
variable {n g h k m r : ℕ}

theorem Refinement.fine_mean_parent_mean {P : Partition n g} {P0 : Partition n h}
    (R : Refinement P P0) (p q : Vec n) (hp : ∀i,0<p i) (hq : ∀i,0<q i) (C : Mat n k) :
    P.mean p q (P0.mean p q C)=P0.mean p q C := by
  ext i j
  have he : P.report q (P0.mean p q C) (P.group i) j =
      P.sales p q (P.group i)*(P0.report q C (P0.group i) j/P0.sales p q (P0.group i)) := by
    rw [P.report_apply,P.sales_apply,Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro a ha
    have hg : P0.group a=P0.group i := by
      rw [R.compatible a,R.compatible i,(P.mem_cell (P.group i) a).mp ha]
    simp only [Partition.mean,hg]
    ring
  change p i/P.sales p q (P.group i)*P.report q (P0.mean p q C) (P.group i) j=_
  rw [he]
  change p i/P.sales p q (P.group i)*(P.sales p q (P.group i)*
    (P0.report q C (P0.group i) j/P0.sales p q (P0.group i)))=
    p i/P0.sales p q (P0.group i)*P0.report q C (P0.group i) j
  field_simp [(P.sales_pos p q hp hq (P.group i)).ne']

theorem answerBasis_projection (P : Partition n g) (P0 : Partition n h) (p q : Vec n)
    (hp : ∀i,0<p i) (hq : ∀i,0<q i) (B : VectorBasis (answerSubspace P P0 p q) m) :
    P.meanProjection p q*B.B=B.B := by
  ext i j
  have hh := answerBasis_fixed P P0 p q hp hq B (Pi.single j 1)
  rw [Matrix.mulVec_mulVec,Matrix.mulVec_single_one,Matrix.mulVec_single_one] at hh
  exact congrFun hh i

theorem hiddenBasis_projection (P : Partition n g) (p q : Vec n)
    (H : HiddenBasis (P.Q q) r) : P.meanProjection p q*H.N=0 := by
  rw [Partition.meanProjection,Matrix.mul_assoc,H.annihilates,Matrix.mul_zero]

theorem answer_representative_fixed (P : Partition n g) (P0 : Partition n h)
    (R : Refinement P P0) (p q : Vec n) (hp : ∀i,0<p i) (hq : ∀i,0<q i)
    (B : VectorBasis (answerSubspace P P0 p q) m) (Cref : Mat n k) (X : Mat m k) :
    P.mean p q (P0.mean p q Cref+B.B*X)=P0.mean p q Cref+B.B*X := by
  rw [←P.projection_mul,Matrix.mul_add,←Matrix.mul_assoc _ B.B X,
    answerBasis_projection P P0 p q hp hq B,P.projection_mul,R.fine_mean_parent_mean p q hp hq]

theorem split_mean (P : Partition n g) (P0 : Partition n h)
    (R : Refinement P P0) (p q : Vec n) (hp : ∀i,0<p i) (hq : ∀i,0<q i)
    (B : VectorBasis (answerSubspace P P0 p q) m) (H : HiddenBasis (P.Q q) r)
    (Cref : Mat n k) (X : Mat m k) (Z : Mat r k) :
    P.mean p q (P0.mean p q Cref+B.B*X+H.N*Z)=P0.mean p q Cref+B.B*X := by
  rw [←P.projection_mul,Matrix.mul_add,←Matrix.mul_assoc _ H.N Z,
    hiddenBasis_projection P p q H,Matrix.zero_mul,add_zero,P.projection_mul,
    answer_representative_fixed P P0 R p q hp hq B]

theorem parent_matrix_coordinates (P : Partition n g) (P0 : Partition n h)
    (R : Refinement P P0) (p q : Vec n) (hp : ∀i,0<p i) (hq : ∀i,0<q i)
    (B : VectorBasis (answerSubspace P P0 p q) m) (H : HiddenBasis (P.Q q) r)
    (C0 C : Mat n k) (hC : P0.report q C=P0.report q C0) :
    ∃!z : Mat m k × Mat r k,C=C0+B.B*z.1+H.N*z.2 := by
  have hz : (P0.Q q).transpose*(C-C0)=0 := by
    rw [Matrix.mul_sub]
    exact sub_eq_zero.mpr hC
  obtain ⟨z,hz,hu⟩ := answer_hidden_matrix_split P P0 R p q hp hq B H (C-C0) hz
  refine ⟨z,?_,?_⟩
  · change C=C0+B.B*z.1+H.N*z.2
    rw [add_assoc,hz,add_sub_cancel]
  · intro w hw
    apply hu
    rw [hw]
    abel

def jointPositiveDomain (e : Frame k) (p : Vec n) (C0 : Mat n k) (B : Mat n m) (N : Mat n r) :
    Set (Mat m k × Mat r k) := {z | C0+B*z.1+N*z.2∈e.PositiveDomain p}

theorem jointPositiveDomain_open (e : Frame k) (p : Vec n) (C0 : Mat n k)
    (B : Mat n m) (N : Mat n r) : IsOpen (jointPositiveDomain e p C0 B N) := by
  apply (e.positiveDomain_open p).preimage
  exact (continuous_const.add (continuous_const.matrix_mul continuous_fst)).add
    (continuous_const.matrix_mul continuous_snd)

theorem jointPositiveDomain_zero (e : Frame k) (p : Vec n) (C0 : Mat n k)
    (B : Mat n m) (N : Mat n r) (hC0 : C0∈e.PositiveDomain p) :
    (0 : Mat m k × Mat r k)∈jointPositiveDomain e p C0 B N := by
  simpa only [jointPositiveDomain,Set.mem_ofPred_eq,Prod.fst_zero,Prod.snd_zero,Matrix.mul_zero,add_zero] using hC0

theorem split_candidate_iff (e : Frame k) (P : Partition n g) (P0 : Partition n h)
    (R : Refinement P P0) (p q : Vec n)
    (B : VectorBasis (answerSubspace P P0 p q) m) (H : HiddenBasis (P.Q q) r)
    (J0 : Mat h k) (C0 : Mat n k) (hC0 : P0.report q C0=J0) (X : Mat m k) (Z : Mat r k) :
    C0+B.B*X+H.N*Z∈e.Candidates p q P0 J0 ↔
      (X,Z)∈jointPositiveDomain e p C0 B.B H.N := by
  have hN : (P0.Q q).transpose*H.N=0 := by
    rw [R.Q_factor q,Matrix.transpose_mul,Matrix.mul_assoc,H.annihilates,Matrix.mul_zero]
  have hr : P0.report q (C0+B.B*X+H.N*Z)=J0 := by
    simp only [Partition.report,Matrix.mul_add,←Matrix.mul_assoc,
      answerBasis_parent_zero P P0 p q B,hN,Matrix.zero_mul,add_zero]
    exact hC0
  exact ⟨fun hh => hh.1,fun hh => ⟨hh,hr⟩⟩

end CommodityClassification.InputCoordinates
