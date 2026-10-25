module

public import LeanMath.CommodityClassification.AllAnswerDichotomy
public import LeanMath.CommodityClassification.EconomicFixedAnswerCriterion

/-! Embedding actual report kernels into the parent coordinate class. -/
@[expose] public section
namespace CommodityClassification.InputCoordinates
open Matrix
variable {n k g h r s : ℕ}

def Refinement.refl (P : Partition n g) : Refinement P P := ⟨id,fun _ => rfl⟩

theorem Refinement.hidden_embedding {P : Partition n g} {P0 : Partition n h}
    (R : Refinement P P0) (q : Vec n)
    (H : HiddenBasis (P.Q q) r) (H0 : HiddenBasis (P0.Q q) s) :
    ∃ J : Mat s r, H.N = H0.N * J := by
  have hf : P.report q H.N = P.report q (0:Mat n r) := by
    simpa only [Partition.report,Matrix.mul_zero] using H.annihilates
  obtain ⟨J,hJ⟩ := (H0.fiber_exists_iff (0:Mat n r) H.N).mp (R.report_preserved q _ _ hf)
  exact ⟨J,by simpa only [zero_add] using hJ⟩

theorem Frame.parent_coordinate_candidate (e : Frame k) (p q : Vec n)
    (P0 : Partition n h) (J0 : Mat h k) (C0 : Mat n k)
    (hC0 : C0 ∈ e.Candidates p q P0 J0) (H0 : HiddenBasis (P0.Q q) s)
    (Y : Mat s k) (hY : Y ∈ e.FiberDomain p H0 C0) :
    C0 + H0.N * Y ∈ e.Candidates p q P0 J0 :=
  ⟨hY,(H0.report_point C0 Y).trans hC0.2⟩

theorem Frame.candidate_parent_coordinates (e : Frame k) (p q : Vec n)
    (P0 : Partition n h) (J0 : Mat h k) (C0 : Mat n k)
    (hC0 : C0 ∈ e.Candidates p q P0 J0) (H0 : HiddenBasis (P0.Q q) s)
    (C : Mat n k) (hC : C ∈ e.Candidates p q P0 J0) :
    ∃ Y ∈ e.FiberDomain p H0 C0, C = C0 + H0.N*Y := by
  obtain ⟨Y,hY⟩ := (H0.fiber_exists_iff C0 C).mp (hC.2.trans hC0.2.symm)
  exact ⟨Y,by change C0+H0.N*Y ∈ e.PositiveDomain p; rw [← hY]; exact hC.1,hY⟩

theorem hidden_embedding_point (C0 : Mat n k) (U : Mat n s) (N : Mat n r)
    (J : Mat s r) (hN : N = U*J) (Y : Mat s k) (Z : Mat r k) :
    C0 + U*(Y+J*Z) = (C0+U*Y)+N*Z := by
  rw [Matrix.mul_add,← Matrix.mul_assoc,← hN]
  abel

end CommodityClassification.InputCoordinates
