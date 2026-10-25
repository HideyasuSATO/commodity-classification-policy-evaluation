module

public import LeanMath.CommodityClassification.UnknownSigmaAttainment

/-! Exact worst widths of the actual observation fibers with unknown common substitution. -/
@[expose] public section
noncomputable section
namespace CommodityClassification.Precision.Data
open InputCoordinates Information
variable {n : ℕ} (d : Precision.Data n)

theorem sigma_full_worst_width (l u : ℝ) (hl : 0<l) (hlu : l≤u) :
    worstWidth (d.sigmaDomain l u) (fun x => d.inputs x.1)
      (fun x => d.sigmaWelfare x.2 x.1)=d.sigmaFloor l u := by
  have hn := d.sigmaDomain_nonempty l u hlu
  have hb := d.sigmaDomain_bounded l u hl
  apply le_antisymm
  · apply (worstWidth_le_iff _ hn _ _ hb _).mpr
    intro x hx
    rw [d.sigma_full_answer_width l u x.1 hx.1]
    exact d.sigmaConditionalWidth_le_floor l u hl hlu x.1 hx.1
  · have hc := d.sigmaCriticalInputs_admissible l u hl (hl.trans_le hlu)
    have he := (worstWidth_le_iff (d.sigmaDomain l u) hn (fun x => d.inputs x.1)
      (fun x => d.sigmaWelfare x.2 x.1) hb _).mp le_rfl
        (d.sigmaCriticalInputs l u,l) ⟨hc,le_rfl,hlu⟩
    change Information.answerWidth _ _ _ (d.inputs (d.sigmaCriticalInputs l u))≤_ at he
    rw [d.sigma_full_answer_width l u _ hc,d.sigmaCriticalInputs_attain l u hl hlu] at he
    exact he

theorem sigma_moment_worst_width (l u : ℝ) (hl : 0<l) (hlu : l≤u) :
    worstWidth (d.sigmaDomain l u) (fun x => d.momentReport x.1)
      (fun x => d.sigmaWelfare x.2 x.1)=d.sigmaFloor l u := by
  rw [←d.sigma_worst_widths_equal l u hl hlu,d.sigma_full_worst_width l u hl hlu]

theorem sigma_any_input_report_lower {A : Type*} (O : Vec n→A)
    (l u : ℝ) (hl : 0<l) (hlu : l≤u) :
    d.sigmaFloor l u≤worstWidth (d.sigmaDomain l u) (fun x => O x.1)
      (fun x => d.sigmaWelfare x.2 x.1) := by
  let c := d.sigmaCriticalInputs l u
  have hc := d.sigmaCriticalInputs_admissible l u hl (hl.trans_le hlu)
  have hh := pair_le_worstWidth (d.sigmaDomain l u) (d.sigmaDomain_nonempty l u hlu)
    (fun x => O x.1) (fun x => d.sigmaWelfare x.2 x.1) (d.sigmaDomain_bounded l u hl)
    (c,u) (c,l) ⟨hc,hlu,le_rfl⟩ ⟨hc,le_rfl,hlu⟩ rfl
  change |d.sigmaWelfare u c-d.sigmaWelfare l c|≤_ at hh
  rw [←d.sigmaConditionalWidth_endpoints l u hl hlu c hc,
    d.sigmaCriticalInputs_attain l u hl hlu] at hh
  exact (le_abs_self _).trans hh

theorem sigma_input_information_failure {A : Type*} (O : Vec n→A)
    (l u eps : ℝ) (hl : 0<l) (hlu : l≤u) (hε : eps<d.sigmaFloor l u) :
    ¬worstWidth (d.sigmaDomain l u) (fun x => O x.1)
      (fun x => d.sigmaWelfare x.2 x.1)≤eps :=
  not_le.mpr (hε.trans_le (d.sigma_any_input_report_lower O l u hl hlu))

theorem sigma_full_known_width (l : ℝ) (hl : 0<l) :
    worstWidth (d.sigmaDomain l l) (fun x => d.inputs x.1) (fun x => d.sigmaWelfare x.2 x.1)=0 := by
  rw [d.sigma_full_worst_width l l hl le_rfl,d.sigmaFloor_known]

theorem sigma_moment_known_width (l : ℝ) (hl : 0<l) :
    worstWidth (d.sigmaDomain l l) (fun x => d.momentReport x.1) (fun x => d.sigmaWelfare x.2 x.1)=0 := by
  rw [d.sigma_moment_worst_width l l hl le_rfl,d.sigmaFloor_known]

end CommodityClassification.Precision.Data
