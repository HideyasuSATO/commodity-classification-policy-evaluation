module
public import LeanMath.CommodityClassification.AnswerCoordinates
@[expose] public section
set_option maxHeartbeats 2400000
namespace CommodityClassification.InputCoordinates
open Matrix Filter
open scoped BigOperators Topology
variable {n g h k m r : ℕ}

theorem split_same_answer_iff (P : Partition n g) (P0 : Partition n h)
    (R : Refinement P P0) (p q : Vec n) (hp : ∀i,0<p i) (hq : ∀i,0<q i)
    (B : VectorBasis (answerSubspace P P0 p q) m) (H : HiddenBasis (P.Q q) r)
    (Cref : Mat n k) (X Y : Mat m k) (Z W : Mat r k) :
    P.report q (P0.mean p q Cref+B.B*X+H.N*Z)=
      P.report q (P0.mean p q Cref+B.B*Y+H.N*W) ↔ X=Y := by
  constructor
  · intro hr
    have hm := congrArg (fun J => P.liftReport p q*J) hr
    rw [←P.mean_eq_lift,←P.mean_eq_lift,split_mean P P0 R p q hp hq B H,
      split_mean P P0 R p q hp hq B H] at hm
    exact B.mul_injective _ (add_left_cancel hm)
  · intro hxy
    subst Y
    exact (H.report_point _ Z).trans (H.report_point _ W).symm

theorem answer_positive_domain_open (e : Frame k) (p : Vec n) (C0 : Mat n k)
    (B : Mat n m) : IsOpen {X : Mat m k | C0+B*X∈e.PositiveDomain p} :=
  (e.positiveDomain_open p).preimage (continuous_const.add (continuous_const.matrix_mul continuous_id))

theorem answer_positive_domain_zero (e : Frame k) (p : Vec n) (C0 : Mat n k)
    (B : Mat n m) (hC0 : C0∈e.PositiveDomain p) :
    (0 : Mat m k)∈{X | C0+B*X∈e.PositiveDomain p} := by
  simpa only [Set.mem_ofPred_eq,Matrix.mul_zero,add_zero] using hC0

theorem Frame.parent_mean_candidate (e : Frame k) (P0 : Partition n h) (p q : Vec n)
    (hp : ∀i,0<p i) (hq : ∀i,0<q i) (J0 : Mat h k) (Cref : Mat n k)
    (href : Cref∈e.Candidates p q P0 J0) : P0.mean p q Cref∈e.Candidates p q P0 J0 := by
  let R : Refinement P0 P0 := ⟨id,fun _ => rfl⟩
  exact (e.mean_candidate p q hp hq R J0 Cref href).1

theorem Frame.positive_answer_representative (e : Frame k) (P : Partition n g)
    (P0 : Partition n h) (R : Refinement P P0) (p q : Vec n)
    (hp : ∀i,0<p i) (hq : ∀i,0<q i) (J0 : Mat h k) (Cref : Mat n k)
    (href : Cref∈e.Candidates p q P0 J0) (B : VectorBasis (answerSubspace P P0 p q) m)
    (H : HiddenBasis (P.Q q) r) (X : Mat m k) (Z : Mat r k)
    (hz : (X,Z)∈jointPositiveDomain e p (P0.mean p q Cref) B.B H.N) :
    P0.mean p q Cref+B.B*X∈e.Candidates p q P0 J0 ∧
      P.report q (P0.mean p q Cref+B.B*X)=P.report q (P0.mean p q Cref+B.B*X+H.N*Z) := by
  have hs := e.parent_mean_candidate P0 p q hp hq J0 Cref href
  have hc := (split_candidate_iff e P P0 R p q B H J0 _ hs.2 X Z).mpr hz
  have hm := e.mean_candidate p q hp hq R J0 _ hc
  rwa [split_mean P P0 R p q hp hq B H Cref X Z] at hm

theorem Frame.candidate_unique_answer_coordinates (e : Frame k) (P : Partition n g)
    (P0 : Partition n h) (R : Refinement P P0) (p q : Vec n)
    (hp : ∀i,0<p i) (hq : ∀i,0<q i) (J0 : Mat h k) (Cref : Mat n k)
    (href : Cref∈e.Candidates p q P0 J0) (B : VectorBasis (answerSubspace P P0 p q) m)
    (H : HiddenBasis (P.Q q) r) (C : Mat n k) (hC : C∈e.Candidates p q P0 J0) :
    ∃!z : Mat m k × Mat r k,z∈jointPositiveDomain e p (P0.mean p q Cref) B.B H.N ∧
      C=P0.mean p q Cref+B.B*z.1+H.N*z.2 := by
  have hs := e.parent_mean_candidate P0 p q hp hq J0 Cref href
  obtain ⟨z,hz,hu⟩ := parent_matrix_coordinates P P0 R p q hp hq B H
    (P0.mean p q Cref) C (hC.2.trans hs.2.symm)
  refine ⟨z,⟨?_,hz⟩,fun w hw => hu w hw.2⟩
  change P0.mean p q Cref+B.B*z.1+H.N*z.2∈e.PositiveDomain p
  rw [←hz]
  exact hC.1

/-- Construction of a complement and hidden-coordinate basis. -/
theorem Frame.exists_answer_coordinates (e : Frame k) (P : Partition n g)
    (P0 : Partition n h) (R : Refinement P P0) (p q : Vec n)
    (hp : ∀i,0<p i) (hq : ∀i,0<q i) (J0 : Mat h k) (Cref : Mat n k)
    (href : Cref∈e.Candidates p q P0 J0) :
    ∃m r,∃B : VectorBasis (answerSubspace P P0 p q) m,∃H : HiddenBasis (P.Q q) r,
      P0.mean p q Cref∈e.Candidates p q P0 J0 ∧
      P.mean p q (P0.mean p q Cref)=P0.mean p q Cref ∧
      IsOpen (jointPositiveDomain e p (P0.mean p q Cref) B.B H.N) ∧
      (0 : Mat m k × Mat r k)∈jointPositiveDomain e p (P0.mean p q Cref) B.B H.N ∧
      (∀C∈e.Candidates p q P0 J0,∃!z : Mat m k × Mat r k,
        z∈jointPositiveDomain e p (P0.mean p q Cref) B.B H.N ∧
        C=P0.mean p q Cref+B.B*z.1+H.N*z.2) ∧
      ∀X Z,(X,Z)∈jointPositiveDomain e p (P0.mean p q Cref) B.B H.N →
        P0.mean p q Cref+B.B*X∈e.Candidates p q P0 J0 ∧
        P.report q (P0.mean p q Cref+B.B*X)=P.report q (P0.mean p q Cref+B.B*X+H.N*Z) := by
  obtain ⟨m,⟨B⟩⟩ := exists_vectorBasis (answerSubspace P P0 p q)
  obtain ⟨r,⟨H⟩⟩ := exists_hiddenBasis (P.Q q)
  have hs := e.parent_mean_candidate P0 p q hp hq J0 Cref href
  refine ⟨m,r,B,H,hs,R.fine_mean_parent_mean p q hp hq Cref,
    jointPositiveDomain_open e p _ _ _,jointPositiveDomain_zero e p _ _ _ hs.1,
    ?_,?_⟩
  · exact fun C hC => e.candidate_unique_answer_coordinates P P0 R p q hp hq J0 Cref href B H C hC
  · exact fun X Z hz => e.positive_answer_representative P P0 R p q hp hq J0 Cref href B H X Z hz

/-- If the fine partition equals the parent there are no new answer directions. -/
theorem answerSubspace_self (P : Partition n g) (p q : Vec n)
    (hp : ∀i,0<p i) (hq : ∀i,0<q i) : answerSubspace P P p q=⊥ := by
  apply (Submodule.eq_bot_iff _).mpr
  intro x hx
  have hfix := P.projection_fixes_range p q hp hq x hx.1
  have hz := P.projection_hidden_zero p q x hx.2
  exact hfix.symm.trans hz

theorem no_answer_basis (P : Partition n g) (p q : Vec n)
    (hp : ∀i,0<p i) (hq : ∀i,0<q i) : Nonempty (VectorBasis (answerSubspace P P p q) 0) := by
  rw [answerSubspace_self P p q hp hq]
  refine ⟨{B:=0,independent:=fun _ _ _ => Subsingleton.elim _ _,spans:=?_}⟩
  intro x
  simp only [Submodule.mem_bot,Matrix.zero_mulVec]
  constructor
  · intro hx; exact ⟨0,hx.symm⟩
  · rintro ⟨_,hx⟩; exact hx.symm

end CommodityClassification.InputCoordinates
