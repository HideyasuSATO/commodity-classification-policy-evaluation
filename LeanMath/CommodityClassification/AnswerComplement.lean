module
public import LeanMath.CommodityClassification.AnswerMeanProjection
@[expose] public section
set_option maxHeartbeats 2400000
namespace CommodityClassification.InputCoordinates
open Matrix
open scoped BigOperators Topology
variable {n g h k m r : ℕ}

/-- A matrix basis of any finite-dimensional commodity-vector subspace. -/
structure VectorBasis (S : Submodule ℝ (Vec n)) (m : ℕ) where
  B : Mat n m
  independent : Function.Injective (fun x => B *ᵥ x)
  spans : ∀x : Vec n,x∈S ↔ ∃z : Vec m,B *ᵥ z=x

theorem exists_vectorBasis (S : Submodule ℝ (Vec n)) : ∃m,Nonempty (VectorBasis S m) := by
  let b := Module.finBasis ℝ S
  let B : Mat n (Module.finrank ℝ S) := fun i j => (b j).val i
  have he (z : Vec (Module.finrank ℝ S)) : B *ᵥ z=(b.equivFun.symm z).val := by
    ext i
    simp [B,Matrix.mulVec,dotProduct,Module.Basis.equivFun_symm_apply,mul_comm]
  refine ⟨Module.finrank ℝ S,⟨{B:=B,independent:=?_,spans:=?_}⟩⟩
  · intro x y hxy
    apply b.equivFun.symm.injective
    apply Subtype.ext
    simpa only [←he] using hxy
  · intro x
    constructor
    · intro hx
      let u : S := ⟨x,hx⟩
      exact ⟨b.equivFun u,by rw [he,b.equivFun.symm_apply_apply]⟩
    · rintro ⟨z,rfl⟩
      rw [he]
      exact (b.equivFun.symm z).property

theorem VectorBasis.mem (S : Submodule ℝ (Vec n)) (B : VectorBasis S m) (x : Vec m) : B.B *ᵥ x∈S :=
  (B.spans _).mpr ⟨x,rfl⟩

theorem VectorBasis.mul_injective (S : Submodule ℝ (Vec n)) (B : VectorBasis S m) :
    Function.Injective (fun X : Mat m k => B.B*X) := by
  intro X Y hXY
  have he (j : Fin k) : (fun a => X a j)=(fun a => Y a j) := by
    apply B.independent
    exact congrArg (fun M : Mat n k => fun i => M i j) hXY
  ext a j
  exact congrFun (he j) a

noncomputable def answerSubspace (P : Partition n g) (P0 : Partition n h) (p q : Vec n) :
    Submodule ℝ (Vec n) :=
  LinearMap.range (P.meanProjection p q).mulVecLin ⊓ LinearMap.ker (P0.Q q).transpose.mulVecLin

theorem Partition.projection_fixes_range (P : Partition n g) (p q : Vec n)
    (hp : ∀i,0<p i) (hq : ∀i,0<q i) (x : Vec n)
    (hx : x∈LinearMap.range (P.meanProjection p q).mulVecLin) :
    P.meanProjection p q *ᵥ x=x := by
  obtain ⟨u,rfl⟩ := hx
  change P.meanProjection p q *ᵥ (P.meanProjection p q *ᵥ u)=_
  rw [Matrix.mulVec_mulVec,P.projection_idempotent p q hp hq]
  rfl

theorem answerBasis_fixed (P : Partition n g) (P0 : Partition n h) (p q : Vec n)
    (hp : ∀i,0<p i) (hq : ∀i,0<q i) (B : VectorBasis (answerSubspace P P0 p q) m) (x : Vec m) :
    P.meanProjection p q *ᵥ (B.B *ᵥ x)=B.B *ᵥ x :=
  P.projection_fixes_range p q hp hq _ (B.mem _ x).1

theorem answerBasis_parent_zero (P : Partition n g) (P0 : Partition n h) (p q : Vec n)
    (B : VectorBasis (answerSubspace P P0 p q) m) : (P0.Q q).transpose*B.B=0 := by
  ext i j
  have hh := (B.mem _ (Pi.single j 1)).2
  change (P0.Q q).transpose *ᵥ (B.B *ᵥ Pi.single j 1)=0 at hh
  rw [Matrix.mulVec_mulVec,Matrix.mulVec_single_one] at hh
  exact congrFun hh i

theorem answerBasis_columns_weighted (P : Partition n g) (P0 : Partition n h) (p q : Vec n)
    (hp : ∀i,0<p i) (hq : ∀i,0<q i) (B : VectorBasis (answerSubspace P P0 p q) m) (j : Fin m) :
    ∃v : Vec g,((Supply.xi p q)⁻¹*P.Q q) *ᵥ v=fun i => B.B i j := by
  have hh := (P.projection_range_weighted p q hp hq (B.B *ᵥ Pi.single j 1)).mp (B.mem _ _).1
  obtain ⟨v,hv⟩ := hh
  refine ⟨v,?_⟩
  ext i
  simpa only [Matrix.mulVec_single_one,Matrix.col_apply] using congrFun hv i

theorem answer_hidden_injective (P : Partition n g) (P0 : Partition n h) (p q : Vec n)
    (hp : ∀i,0<p i) (hq : ∀i,0<q i) (B : VectorBasis (answerSubspace P P0 p q) m)
    (H : HiddenBasis (P.Q q) r) :
    Function.Injective (fun x : Vec m × Vec r => B.B *ᵥ x.1+H.N *ᵥ x.2) := by
  intro x y hxy
  change B.B *ᵥ x.1+H.N *ᵥ x.2=B.B *ᵥ y.1+H.N *ᵥ y.2 at hxy
  have hz (z : Vec r) : P.meanProjection p q *ᵥ (H.N *ᵥ z)=0 :=
    P.projection_hidden_zero p q _ ((H.spans _).mpr ⟨z,rfl⟩)
  have hb : x.1=y.1 := by
    apply B.independent
    have hh := congrArg (fun z => P.meanProjection p q *ᵥ z) hxy
    simpa only [Matrix.mulVec_add,answerBasis_fixed P P0 p q hp hq B,hz,add_zero] using hh
  have hn : x.2=y.2 := by
    apply H.independent
    rw [hb] at hxy
    exact add_left_cancel hxy
  exact Prod.ext hb hn

theorem answer_hidden_split (P : Partition n g) (P0 : Partition n h)
    (R : Refinement P P0) (p q : Vec n) (hp : ∀i,0<p i) (hq : ∀i,0<q i)
    (B : VectorBasis (answerSubspace P P0 p q) m) (H : HiddenBasis (P.Q q) r)
    (x : Vec n) (hx : (P0.Q q).transpose *ᵥ x=0) :
    ∃!z : Vec m × Vec r,B.B *ᵥ z.1+H.N *ᵥ z.2=x := by
  have ht : P.meanProjection p q *ᵥ x∈answerSubspace P P0 p q :=
    ⟨⟨x,rfl⟩,R.projection_preserves_parent_kernel p q hp hq x hx⟩
  obtain ⟨u,hu⟩ := (B.spans _).mp ht
  obtain ⟨v,hv⟩ := (H.spans _).mp (P.projection_residual_hidden p q hp hq x)
  refine ⟨(u,v),?_,?_⟩
  · change B.B *ᵥ u+H.N *ᵥ v=x
    rw [hu,hv,add_sub_cancel]
  · intro z hz
    apply answer_hidden_injective P P0 p q hp hq B H
    change B.B *ᵥ z.1+H.N *ᵥ z.2=B.B *ᵥ u+H.N *ᵥ v
    rw [hz,hu,hv,add_sub_cancel]

theorem answer_hidden_matrix_split (P : Partition n g) (P0 : Partition n h)
    (R : Refinement P P0) (p q : Vec n) (hp : ∀i,0<p i) (hq : ∀i,0<q i)
    (B : VectorBasis (answerSubspace P P0 p q) m) (H : HiddenBasis (P.Q q) r)
    (C : Mat n k) (hC : (P0.Q q).transpose*C=0) :
    ∃!z : Mat m k × Mat r k,B.B*z.1+H.N*z.2=C := by
  classical
  have hx (j : Fin k) : (P0.Q q).transpose *ᵥ (fun i => C i j)=0 := by
    exact congrArg (fun M : Mat h k => fun i => M i j) hC
  have hs (j : Fin k) := answer_hidden_split P P0 R p q hp hq B H (fun i => C i j) (hx j)
  choose z hz huniq using hs
  refine ⟨(fun a j => (z j).1 a,fun a j => (z j).2 a),?_,?_⟩
  · ext i j
    exact congrFun (hz j) i
  · intro w hw
    have he (j : Fin k) : (fun a => w.1 a j,fun a => w.2 a j)=z j := by
      apply huniq j
      exact congrArg (fun M : Mat n k => fun i => M i j) hw
    apply Prod.ext
    · ext a j
      exact congrFun (congrArg Prod.fst (he j)) a
    · ext a j
      exact congrFun (congrArg Prod.snd (he j)) a

end CommodityClassification.InputCoordinates
