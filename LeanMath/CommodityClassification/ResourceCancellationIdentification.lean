module

public import LeanMath.CommodityClassification.ResourceCancellationMoments

/-! Identification on the full candidate class. -/
@[expose] public section
noncomputable section
set_option maxHeartbeats 2400000
namespace CommodityClassification.ResourceCancellation
open Matrix InputCoordinates

theorem balanced_parameterization (C : Mat 3 1) (hC : parent.report e C=0) :
    C=coordinates (-C 2 0/2) ((C 0 0-C 1 0)/2) := by
  have hs := congrFun (congrFun hC 0) 0
  norm_num [Partition.report,Partition.Q,parent,e,Matrix.mul_apply,transpose_apply,
    Fin.sum_univ_succ] at hs
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [coordinates,visible,hidden] <;> linarith

theorem all_candidates_parameterized (C : family.Candidate) :
    ∃x z : ℝ,C.val=coordinates x z := by
  refine ⟨-C.val 2 0/2,(C.val 0 0-C.val 1 0)/2,?_⟩
  exact balanced_parameterization C.val C.property.2

theorem all_candidate_m (C : family.Candidate) (x z : ℝ) (hc : C.val=coordinates x z) :
    (family.model C).m=![24*x/25] := by
  change C.val.transpose *ᵥ (demand *ᵥ policy)=_
  rw [hc,moment_m]

theorem all_candidate_K (C : family.Candidate) (x z : ℝ) (hc : C.val=coordinates x z) :
    (family.model C).K=![![3+18*x^2/5]] := by
  rw [family.candidate_K_answer C family.reference (0 : Mat 3 0)]
  change Regularity.K e e demand family.fixedR 1 C.val=_
  rw [hc,moment_K]

theorem fine_preserves_moments : family.ReportMomentsPreserved fine := by
  intro C E he
  obtain ⟨x,z,hc⟩ := all_candidates_parameterized C
  obtain ⟨a,t,hd⟩ := all_candidates_parameterized E
  change fine.report e C.val=fine.report e E.val at he
  rw [hc,hd] at he
  have hxa := (fine_report_iff x z a t).mp he
  subst a
  exact ⟨(all_candidate_m C x z hc).trans (all_candidate_m E x t hd).symm,
    (all_candidate_K C x z hc).trans (all_candidate_K E x t hd).symm⟩

theorem fine_identifies_welfare : family.ReportIdentified fine :=
  family.report_moments_identifies fine fine_preserves_moments

theorem scalar_inverse (a : ℝ) :
    @Inv.inv (Matrix (Fin 1) (Fin 1) ℝ) Matrix.inv ![![a]]=![![a⁻¹]] := by
  refine (Matrix.inv_subsingleton (![![a]] : Matrix (Fin 1) (Fin 1) ℝ)).trans ?_
  ext i j; fin_cases i; fin_cases j
  simp [Ring.inverse_eq_inv]

theorem coefficient_formula (x z : ℝ) :
    family.coefficient (coordinates x z)=3051/1000-(24*x/25)^2/(3+18*x^2/5) := by
  change dotProduct policy (demand *ᵥ policy)-
    dotProduct ((coordinates x z).transpose *ᵥ (demand *ᵥ policy))
      ((Regularity.K e e demand family.fixedR 1 (coordinates x z))⁻¹ *ᵥ
        ((coordinates x z).transpose *ᵥ (demand *ᵥ policy)))=_
  rw [nu_exact,moment_m,moment_K]
  have hh := congrArg (fun M : Mat 1 1 => (3051/1000 : ℝ)-
    dotProduct (![24*x/25] : Vec 1) (M *ᵥ ![24*x/25])) (scalar_inverse (3+18*x^2/5))
  refine hh.trans ?_
  simp [dotProduct,Matrix.mulVec,div_eq_mul_inv]
  ring

theorem parent_not_identified : ¬family.ParentIdentified := by
  intro h
  have he := h (candidate (1/8) 0 (by norm_num) (by norm_num))
  change family.coefficient (coordinates (1/8) 0)=family.coefficient (coordinates 0 0) at he
  rw [coefficient_formula,coefficient_formula] at he
  norm_num at he

end CommodityClassification.ResourceCancellation
