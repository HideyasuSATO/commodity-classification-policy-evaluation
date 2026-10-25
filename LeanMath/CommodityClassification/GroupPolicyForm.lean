module

public import LeanMath.CommodityClassification.GroupDemandCurvature
public import LeanMath.CommodityClassification.SparseReportCancellation

/-! The fixed policy satisfies the bridge restriction exactly at proportional cells. -/
@[expose] public section
noncomputable section
namespace CommodityClassification.InputCoordinates
open Matrix
variable {n g r : ℕ}

theorem Partition.normalized_policy_iff (P : Partition n g) (p b : Vec n)
    (hp : ∀i,0<p i) :
    (∀i j,P.group i=P.group j → b i/p i=b j/p j) ↔
      ∃β : Vec g,b=P.Q p *ᵥ β := by
  constructor
  · intro he
    refine ⟨fun a => b (P.representative a)/p (P.representative a),?_⟩
    ext i
    rw [P.Q_mulVec_apply]
    have hh := he i (P.representative (P.group i)) (P.representative_group _).symm
    rw [←hh]
    field_simp [(hp i).ne']
  · rintro ⟨β,rfl⟩ i j hij
    rw [P.Q_mulVec_apply,P.Q_mulVec_apply,hij]
    field_simp [(hp i).ne',(hp j).ne']

theorem xi_policy_ratio (p q b : Vec n) (hq : ∀i,0<q i) (i : Fin n) :
    (Supply.xi p q *ᵥ b) i/q i=b i/p i := by
  simp only [Supply.xi,mulVec_diagonal]
  field_simp [(hq i).ne']

theorem HiddenBasis.xi_policy_iff (P : Partition n g) (p q b : Vec n)
    (hp : ∀i,0<p i) (hq : ∀i,0<q i) (H : HiddenBasis (P.Q q) r) :
    H.N.transpose *ᵥ (Supply.xi p q *ᵥ b)=0 ↔ ∃β : Vec g,b=P.Q p *ᵥ β := by
  rw [H.annihilator_pair_iff P q _ hq]
  simp only [xi_policy_ratio p q b hq]
  exact P.normalized_policy_iff p b hp

theorem hidden_demand_load_under_annihilation (p q b : Vec n) (D : Mat n n)
    (σ : ℝ) (N : Mat n r) (hL : (Regularity.adjustedDemand p q D σ).transpose=
      Regularity.adjustedDemand p q D σ) (hLN : Regularity.adjustedDemand p q D σ*N=0) :
    N.transpose *ᵥ (D *ᵥ b)=σ • (N.transpose *ᵥ (Supply.xi p q *ᵥ b)) := by
  have ht : N.transpose*Regularity.adjustedDemand p q D σ=0 := by
    simpa only [transpose_mul,hL,transpose_zero] using congrArg transpose hLN
  have hm : N.transpose*D=σ • (N.transpose*Supply.xi p q) := by
    apply sub_eq_zero.mp
    simpa only [Regularity.adjustedDemand,Matrix.mul_sub,Matrix.mul_smul] using ht
  rw [Matrix.mulVec_mulVec,hm,Matrix.smul_mulVec,←Matrix.mulVec_mulVec]

theorem Partition.strong_report_form_iff (P : Partition n g) (p q b : Vec n)
    (hp : ∀i,0<p i) (hq : ∀i,0<q i) (D : Mat n n) (σ : ℝ) (hσ : 0<σ)
    (H : HiddenBasis (P.Q q) r)
    (hL : (Regularity.adjustedDemand p q D σ).transpose=Regularity.adjustedDemand p q D σ) :
    (Regularity.adjustedDemand p q D σ*H.N=0 ∧ H.N.transpose *ᵥ (D *ᵥ b)=0) ↔
      ∃B : Mat g g,∃β : Vec g,B.transpose=B ∧
        D=σ • Supply.xi p q+P.Q q*B*(P.Q q).transpose ∧ b=P.Q p *ᵥ β := by
  have hf (B : Mat g g) :
      Regularity.adjustedDemand p q D σ=P.Q q*B*(P.Q q).transpose ↔
        D=σ • Supply.xi p q+P.Q q*B*(P.Q q).transpose := by
    unfold Regularity.adjustedDemand
    constructor
    · intro h
      rw [←h]
      abel
    · intro h
      rw [h]
      abel
  have hl (hLN : Regularity.adjustedDemand p q D σ*H.N=0) :
      H.N.transpose *ᵥ (D *ᵥ b)=0 ↔ ∃β : Vec g,b=P.Q p *ᵥ β := by
    rw [hidden_demand_load_under_annihilation p q b D σ H.N hL hLN]
    rw [smul_eq_zero]
    simp only [hσ.ne',false_or]
    exact H.xi_policy_iff P p q b hp hq
  constructor
  · rintro ⟨hLN,hload⟩
    obtain ⟨B,hB,hform⟩ := (P.symmetric_annihilator_iff p q hp hq H _ hL).mp hLN
    obtain ⟨β,hβ⟩ := (hl hLN).mp hload
    exact ⟨B,β,hB,(hf B).mp hform,hβ⟩
  · rintro ⟨B,β,hB,hform,hβ⟩
    have hLN := (P.symmetric_annihilator_iff p q hp hq H _ hL).mpr
      ⟨B,hB,(hf B).mpr hform⟩
    exact ⟨hLN,(hl hLN).mpr ⟨β,hβ⟩⟩

end CommodityClassification.InputCoordinates
