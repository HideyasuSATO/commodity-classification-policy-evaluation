module

public import LeanMath.CommodityClassification.ExactCommodityPairRule

/-! One-parent resource cancellation and exact policy attributes. -/
@[expose] public section
noncomputable section
namespace CommodityClassification.InputCoordinates
open Matrix
variable {n k : ℕ}

theorem Partition.single_parent_Q_mulVec (P : Partition n 1) (q : Vec n) (γ : Vec 1) :
    P.Q q *ᵥ γ=γ 0 • q := by
  ext i
  simp [Partition.Q,Matrix.mulVec,dotProduct,Subsingleton.elim (P.group i) 0,mul_comm]

theorem single_row_transpose_mulVec (J : Mat 1 k) (γ : Vec 1) :
    J.transpose *ᵥ γ=γ 0 • J 0 := by
  ext j
  simp [Matrix.mulVec,dotProduct,mul_comm]

theorem mem_single_parent_cancellation (P : Partition n 1) (q : Vec n)
    (J : Mat 1 k) (v : Vec n) :
    v∈cancellationSpace (P.Q q) J ↔ ∃t : ℝ,t • q=v ∧ t • J 0=0 := by
  rw [mem_cancellationSpace_iff]
  constructor
  · rintro ⟨γ,hv,hJ⟩
    exact ⟨γ 0,(P.single_parent_Q_mulVec q γ).symm.trans hv,
      (single_row_transpose_mulVec J γ).symm.trans hJ⟩
  · rintro ⟨t,hv,hJ⟩
    refine ⟨(fun _ => t),?_,?_⟩
    · rw [P.single_parent_Q_mulVec];exact hv
    · rw [single_row_transpose_mulVec];exact hJ

theorem single_parent_cancellation_nonzero (P : Partition n 1) (q : Vec n)
    (J : Mat 1 k) (hJ : J≠0) : cancellationSpace (P.Q q) J=⊥ := by
  apply (Submodule.eq_bot_iff _).mpr
  intro v hv
  obtain ⟨t,ht,hz⟩ := (mem_single_parent_cancellation P q J v).mp hv
  have hr : J 0≠0 := by
    intro hr
    apply hJ
    ext a b
    rw [Subsingleton.elim a 0]
    exact congrFun hr b
  have ht0 : t=0 := (smul_eq_zero.mp hz).resolve_right hr
  simpa only [ht0,zero_smul] using ht.symm

theorem single_parent_cancellation_zero (P : Partition n 1) (q : Vec n) :
    cancellationSpace (P.Q q) (0 : Mat 1 k)=Submodule.span ℝ {q} := by
  ext v
  rw [mem_single_parent_cancellation,Submodule.mem_span_singleton]
  change (∃t : ℝ,t • q=v ∧ t • (0 : Vec k)=0) ↔ ∃t : ℝ,t • q=v
  simp only [smul_zero,and_true]

theorem single_parent_cancellation_zero_relative (P : Partition n 1) (q : Vec n)
    (J : Mat 1 0) : cancellationSpace (P.Q q) J=Submodule.span ℝ {q} := by
  have hz : J=0 := Subsingleton.elim _ _
  rw [hz,single_parent_cancellation_zero]

end CommodityClassification.InputCoordinates

namespace CommodityClassification.Equilibrium.BenchmarkFamily
open Matrix InputCoordinates
variable {n k : ℕ} (F : BenchmarkFamily n k 1)

theorem single_parent_attributes_nonzero (hJ : F.report≠0) (i j : Fin n) :
    F.SamePolicyAttributes i j ↔
      (F.D *ᵥ F.b) i/F.q i=(F.D *ᵥ F.b) j/F.q j ∧
      (fun a => Regularity.adjustedDemand F.p F.q F.D F.sigma a i/F.q i)=
        (fun a => Regularity.adjustedDemand F.p F.q F.D F.sigma a j/F.q j) := by
  unfold SamePolicyAttributes
  rw [single_parent_cancellation_nonzero F.parents F.q F.report hJ,Submodule.mem_bot]
  apply and_congr_right
  intro _
  change ((fun a => Regularity.adjustedDemand F.p F.q F.D F.sigma a i/F.q i)-
    (fun a => Regularity.adjustedDemand F.p F.q F.D F.sigma a j/F.q j)=0) ↔ _
  exact sub_eq_zero

theorem single_parent_attributes_zero (hJ : F.report=0) (i j : Fin n) :
    F.SamePolicyAttributes i j ↔
      (F.D *ᵥ F.b) i/F.q i=(F.D *ᵥ F.b) j/F.q j ∧
      ∃t : ℝ,t • F.q=(fun a => Regularity.adjustedDemand F.p F.q F.D F.sigma a i/F.q i-
        Regularity.adjustedDemand F.p F.q F.D F.sigma a j/F.q j) := by
  unfold SamePolicyAttributes
  rw [hJ,single_parent_cancellation_zero,Submodule.mem_span_singleton]

end CommodityClassification.Equilibrium.BenchmarkFamily
