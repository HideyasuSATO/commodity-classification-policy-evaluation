module

public import LeanMath.CommodityClassification.CoarsestCommodityClassification

/-! Two-product support restrictions with arbitrary other parent groups. -/
@[expose] public section
noncomputable section
namespace CommodityClassification.InputCoordinates
open Matrix
variable {n g k : ℕ}

def twoSupport (i j : Fin n) (a b : ℝ) : Vec n := Pi.single i a-Pi.single j b

theorem Partition.Q_mulVec_apply (P : Partition n g) (q : Vec n) (γ : Vec g) (i : Fin n) :
    (P.Q q *ᵥ γ) i=q i*γ (P.group i) := by
  simp [Partition.Q,Matrix.mulVec,dotProduct,ite_mul,Finset.sum_ite_eq]

theorem twoSupport_at_left (i j : Fin n) (hij : i≠j) (a b : ℝ) :
    twoSupport i j a b i=a := by simp [twoSupport,hij]

theorem twoSupport_at_right (i j : Fin n) (hij : i≠j) (a b : ℝ) :
    twoSupport i j a b j=-b := by simp [twoSupport,Ne.symm hij]

theorem twoSupport_elsewhere (i j l : Fin n) (hli : l≠i) (hlj : l≠j) (a b : ℝ) :
    twoSupport i j a b l=0 := by simp [twoSupport,hli,hlj]

theorem twoSupport_mem_of_zero (P : Partition n g) (q : Vec n) (J : Mat g k)
    (i j : Fin n) : twoSupport i j 0 0∈cancellationSpace (P.Q q) J := by
  simpa only [twoSupport,Pi.single_zero,sub_zero] using
    (cancellationSpace (P.Q q) J).zero_mem

theorem twoSupport_third_product_iff (P : Partition n g) (q : Vec n) (hq : ∀i,0<q i)
    (J : Mat g k) (i j l : Fin n) (hij : i≠j) (hgi : P.group j=P.group i)
    (hgl : P.group l=P.group i) (hli : l≠i) (hlj : l≠j) (a b : ℝ) :
    twoSupport i j a b∈cancellationSpace (P.Q q) J ↔ a=0 ∧ b=0 := by
  constructor
  · intro hv
    obtain ⟨γ,hγ,_⟩ := (mem_cancellationSpace_iff _ _ _).mp hv
    have hl := congrFun hγ l
    rw [P.Q_mulVec_apply,twoSupport_elsewhere i j l hli hlj,hgl] at hl
    have hg0 : γ (P.group i)=0 := (mul_eq_zero.mp hl).resolve_left (hq l).ne'
    have hi := congrFun hγ i
    have hj := congrFun hγ j
    rw [P.Q_mulVec_apply,twoSupport_at_left i j hij,hg0,mul_zero] at hi
    rw [P.Q_mulVec_apply,twoSupport_at_right i j hij,hgi,hg0,mul_zero] at hj
    exact ⟨hi.symm,by linarith⟩
  · rintro ⟨rfl,rfl⟩
    exact twoSupport_mem_of_zero P q J i j

theorem twoSupport_parent_coefficient (P : Partition n g) (q : Vec n) (hq : ∀i,0<q i)
    (i j : Fin n) (hgi : P.group j=P.group i) (a b : ℝ) (γ : Vec g)
    (hγ : P.Q q *ᵥ γ=twoSupport i j a b) :
    γ=Pi.single (P.group i) (γ (P.group i)) := by
  ext t
  by_cases ht : t=P.group i
  · subst t; simp
  · let l := P.representative t
    have hl : P.group l=t := P.representative_group t
    have hli : l≠i := fun he => ht (hl.symm.trans (congrArg P.group he))
    have hlj : l≠j := fun he => ht (hl.symm.trans ((congrArg P.group he).trans hgi))
    have hh := congrFun hγ l
    rw [P.Q_mulVec_apply,twoSupport_elsewhere i j l hli hlj,hl] at hh
    have hz : γ t=0 := (mul_eq_zero.mp hh).resolve_left (hq l).ne'
    simp [ht,hz]

theorem twoSupport_nonzero_parent_iff (P : Partition n g) (q : Vec n) (hq : ∀i,0<q i)
    (J : Mat g k) (i j : Fin n) (hij : i≠j) (hgi : P.group j=P.group i)
    (hJ : J (P.group i)≠0) (a b : ℝ) :
    twoSupport i j a b∈cancellationSpace (P.Q q) J ↔ a=0 ∧ b=0 := by
  constructor
  · intro hv
    obtain ⟨γ,hγ,hz⟩ := (mem_cancellationSpace_iff _ _ _).mp hv
    have hs := twoSupport_parent_coefficient P q hq i j hgi a b γ hγ
    have hrow : γ (P.group i) • J (P.group i)=0 := by
      rw [hs] at hz
      ext l
      change γ (P.group i)*J (P.group i) l=0
      have hl := congrFun hz l
      simpa [Matrix.mulVec,Matrix.transpose,dotProduct,Pi.single_apply,mul_ite,mul_comm] using hl
    have hg0 : γ (P.group i)=0 := (smul_eq_zero.mp hrow).resolve_right hJ
    have hi := congrFun hγ i
    have hj := congrFun hγ j
    rw [P.Q_mulVec_apply,twoSupport_at_left i j hij,hg0,mul_zero] at hi
    rw [P.Q_mulVec_apply,twoSupport_at_right i j hij,hgi,hg0,mul_zero] at hj
    exact ⟨hi.symm,by linarith⟩
  · rintro ⟨rfl,rfl⟩
    exact twoSupport_mem_of_zero P q J i j

end CommodityClassification.InputCoordinates
