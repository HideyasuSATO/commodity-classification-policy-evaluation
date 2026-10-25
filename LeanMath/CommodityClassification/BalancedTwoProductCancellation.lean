module

public import LeanMath.CommodityClassification.SparseReportCancellation

/-! The balanced two-product exception, keeping arbitrary other parents. -/
@[expose] public section
noncomputable section
namespace CommodityClassification.InputCoordinates
open Matrix
variable {n g k : ℕ}

theorem twoSupport_balanced_pair_iff (P : Partition n g) (q : Vec n) (hq : ∀i,0<q i)
    (J : Mat g k) (i j : Fin n) (hij : i≠j) (hgi : P.group j=P.group i)
    (honly : ∀l,P.group l=P.group i → l=i ∨ l=j) (hJ : J (P.group i)=0)
    (a b : ℝ) :
    twoSupport i j a b∈cancellationSpace (P.Q q) J ↔ a/q i+b/q j=0 := by
  constructor
  · intro hv
    obtain ⟨γ,hγ,_⟩ := (mem_cancellationSpace_iff _ _ _).mp hv
    have hi := congrFun hγ i
    have hj := congrFun hγ j
    rw [P.Q_mulVec_apply,twoSupport_at_left i j hij] at hi
    rw [P.Q_mulVec_apply,twoSupport_at_right i j hij,hgi] at hj
    rw [←hi,←neg_eq_iff_eq_neg.mpr hj]
    field_simp [(hq i).ne',(hq j).ne']
    ring
  · intro hbal
    apply (mem_cancellationSpace_iff _ _ _).mpr
    refine ⟨Pi.single (P.group i) (a/q i),?_,?_⟩
    · ext l
      rw [P.Q_mulVec_apply]
      by_cases hli : l=i
      · subst l
        rw [twoSupport_at_left i j hij]
        simp only [Pi.single_eq_same]
        field_simp [(hq i).ne']
      · by_cases hlj : l=j
        · subst l
          rw [twoSupport_at_right i j hij,hgi]
          simp only [Pi.single_eq_same]
          field_simp [(hq i).ne',(hq j).ne'] at hbal ⊢
          nlinarith
        · have hgl : P.group l≠P.group i := fun hg => (honly l hg).elim hli hlj
          rw [twoSupport_elsewhere i j l hli hlj]
          simp [hgl]
    · ext l
      simp [Matrix.mulVec_single,Matrix.col,Matrix.transpose,hJ]

end CommodityClassification.InputCoordinates
