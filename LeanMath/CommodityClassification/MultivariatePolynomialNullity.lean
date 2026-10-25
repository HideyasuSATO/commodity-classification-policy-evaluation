module

public import LeanMath.CommodityClassification.PolynomialZeroSections

/-! Induction over arbitrary finite variable types, including the empty type. -/
@[expose] public section
noncomputable section
namespace CommodityClassification.Genericity
open MeasureTheory MeasureTheory.Measure MvPolynomial

theorem polynomialNullity_equiv {α β : Type*} [Fintype α] [Fintype β]
    (e : α ≃ β) (ih : PolynomialNullity α) : PolynomialNullity β := by
  intro p hp
  have hpn : rename e.symm p≠0 := by
    intro hz
    exact hp ((rename_injective e.symm e.symm.injective) (hz.trans (map_zero _).symm))
  have hnull := ih (rename e.symm p) hpn
  let f := MeasurableEquiv.piCongrLeft (fun _ : β => ℝ) e
  have hmap : (volume : Measure (α → ℝ)).map f=(volume : Measure (β → ℝ)) :=
    (volume_measurePreserving_piCongrLeft (fun _ : β => ℝ) e).map_eq
  rw [←hmap,Measure.map_apply f.measurable
    (isClosed_eq p.continuous_eval continuous_const).measurableSet]
  have hs : f ⁻¹' {x : β → ℝ | eval x p=0}={x : α → ℝ | eval x (rename e.symm p)=0} := by
    ext x
    simp only [Set.mem_preimage,Set.mem_ofPred_eq,eval_rename]
    have he : f x=x ∘ e.symm := by
      funext i
      simp [f,MeasurableEquiv.piCongrLeft,Equiv.piCongrLeft]
    rw [he]
  rw [hs]
  exact hnull

theorem polynomial_zero_null {ι : Type*} [Fintype ι] (p : MvPolynomial ι ℝ) (hp : p≠0) :
    volume {x : ι → ℝ | eval x p=0}=0 := by
  have hall : PolynomialNullity ι := by
    apply Fintype.induction_empty_option (P:=fun α _ => PolynomialNullity α)
    · intro α β _ e ih
      let _ : Fintype α := Fintype.ofEquiv β e.symm
      exact polynomialNullity_equiv e ih
    · exact polynomialNullity_empty
    · intro α _ ih
      exact polynomialNullity_option ih
  exact hall p hp

theorem polynomial_ae_nonzero {ι : Type*} [Fintype ι] (p : MvPolynomial ι ℝ) (hp : p≠0) :
    ∀ᵐx : ι → ℝ,eval x p≠0 :=
  compl_mem_ae_iff.mpr (polynomial_zero_null p hp)

end CommodityClassification.Genericity
