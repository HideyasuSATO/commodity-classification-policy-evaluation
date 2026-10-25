module

public import LeanMath.CommodityClassification.UnknownSigmaModel

/-! Full product inputs and the two original moments give exactly the same welfare set at each answer. -/
@[expose] public section
noncomputable section
namespace CommodityClassification.Precision.Data
open InputCoordinates Information
variable {n : ℕ} (d : Precision.Data n)

theorem sigma_full_values (l u : ℝ) (c : Vec n) (hc : d.Admissible c) :
    values (d.sigmaDomain l u) (fun x => d.inputs x.1)
      (fun x => d.sigmaWelfare x.2 x.1) (d.inputs c)=d.sigmaValues l u c := by
  ext z
  constructor
  · rintro ⟨x,hx,rfl⟩
    have he := d.productInputs_injective hx.2
    exact ⟨x.2,hx.1.2,congrArg (d.sigmaWelfare x.2) he.symm⟩
  · rintro ⟨s,hs,rfl⟩
    exact ⟨(c,s),⟨⟨hc,hs⟩,rfl⟩,rfl⟩

theorem sigma_moment_values (l u : ℝ) (c : Vec n) (hc : d.Admissible c) :
    values (d.sigmaDomain l u) (fun x => d.momentReport x.1)
      (fun x => d.sigmaWelfare x.2 x.1) (d.momentReport c)=d.sigmaValues l u c := by
  ext z
  constructor
  · rintro ⟨x,hx,rfl⟩
    exact ⟨x.2,hx.1.2,(d.sigmaWelfare_moment_sufficient x.2 x.1 c hx.2).symm⟩
  · rintro ⟨s,hs,rfl⟩
    exact ⟨(c,s),⟨⟨hc,hs⟩,rfl⟩,rfl⟩

theorem sigma_answer_sets_equal (l u : ℝ) (c : Vec n) (hc : d.Admissible c) :
    values (d.sigmaDomain l u) (fun x => d.inputs x.1)
      (fun x => d.sigmaWelfare x.2 x.1) (d.inputs c)=
    values (d.sigmaDomain l u) (fun x => d.momentReport x.1)
      (fun x => d.sigmaWelfare x.2 x.1) (d.momentReport c) := by
  rw [d.sigma_full_values l u c hc,d.sigma_moment_values l u c hc]

theorem sigma_answer_widths_equal (l u : ℝ) (c : Vec n) (hc : d.Admissible c) :
    Information.answerWidth (d.sigmaDomain l u) (fun x => d.inputs x.1)
      (fun x => d.sigmaWelfare x.2 x.1) (d.inputs c)=
    Information.answerWidth (d.sigmaDomain l u) (fun x => d.momentReport x.1)
      (fun x => d.sigmaWelfare x.2 x.1) (d.momentReport c) := by
  unfold Information.answerWidth
  rw [d.sigma_answer_sets_equal l u c hc]

theorem sigma_worst_widths_equal (l u : ℝ) (hl : 0<l) (hlu : l≤u) :
    worstWidth (d.sigmaDomain l u) (fun x => d.inputs x.1) (fun x => d.sigmaWelfare x.2 x.1)=
    worstWidth (d.sigmaDomain l u) (fun x => d.momentReport x.1) (fun x => d.sigmaWelfare x.2 x.1) := by
  have hn := d.sigmaDomain_nonempty l u hlu
  have hb := d.sigmaDomain_bounded l u hl
  apply le_antisymm
  · apply (worstWidth_le_iff _ hn _ _ hb _).mpr
    intro x hx
    rw [d.sigma_answer_widths_equal l u x.1 hx.1]
    exact (worstWidth_le_iff _ hn _ _ hb _).mp le_rfl x hx
  · apply (worstWidth_le_iff _ hn _ _ hb _).mpr
    intro x hx
    rw [←d.sigma_answer_widths_equal l u x.1 hx.1]
    exact (worstWidth_le_iff _ hn _ _ hb _).mp le_rfl x hx

end CommodityClassification.Precision.Data
