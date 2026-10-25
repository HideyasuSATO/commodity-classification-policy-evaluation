module

public import LeanMath.CommodityClassification.ParentPolynomialNonidentity
public import Mathlib.Algebra.MvPolynomial.Equiv
public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.MeasureTheory.Measure.Prod

/-! Finite roots and Fubini for the standard nullity of polynomial zero sets. -/
@[expose] public section
noncomputable section
namespace CommodityClassification.Genericity
open MeasureTheory MeasureTheory.Measure MvPolynomial Filter

def PolynomialNullity (ι : Type*) [Fintype ι] : Prop :=
  ∀p : MvPolynomial ι ℝ,p≠0 → volume {x : ι → ℝ | eval x p=0}=0

theorem univariate_zero_null (p : Polynomial ℝ) (hp : p≠0) :
    volume {x : ℝ | p.eval x=0}=0 :=
  (Polynomial.finite_setOfPred_isRoot hp).measure_zero volume

theorem polynomialNullity_empty : PolynomialNullity PEmpty := by
  intro p hp
  let c := isEmptyRingEquiv ℝ PEmpty p
  have hc : c≠0 := by
    intro h
    exact hp ((isEmptyRingEquiv ℝ PEmpty).injective (h.trans (map_zero _).symm))
  have he : p=C c := by simpa only [isEmptyRingEquiv_symm_apply] using
    ((isEmptyRingEquiv ℝ PEmpty).symm_apply_apply p).symm
  simp only [he,eval_C,hc,Set.ofPred_false,measure_empty]

theorem option_polynomial_nonzero_section {ι : Type*}
    (p : MvPolynomial (Option ι) ℝ) (m : ℕ) (x : ι → ℝ)
    (hx : eval x ((optionEquivLeft ℝ ι p).coeff m)≠0) :
    Polynomial.map (eval x) (optionEquivLeft ℝ ι p)≠0 := by
  intro h
  have hc := congrArg (fun q : Polynomial ℝ => q.coeff m) h
  simp only [Polynomial.coeff_map,Polynomial.coeff_zero] at hc
  exact hx hc

theorem polynomialNullity_option {ι : Type*} [Fintype ι]
    (ih : PolynomialNullity ι) : PolynomialNullity (Option ι) := by
  intro p hp
  let Q := optionEquivLeft ℝ ι p
  have hQ : Q≠0 := by
    intro h
    exact hp ((optionEquivLeft ℝ ι).injective (h.trans (map_zero _).symm))
  obtain ⟨m,hm⟩ : ∃m : ℕ,Q.coeff m≠0 := by
    by_contra hh
    push Not at hh
    exact hQ (Polynomial.ext (by simpa using hh))
  have hae : ∀ᵐx : ι → ℝ,eval x (Q.coeff m)≠0 :=
    compl_mem_ae_iff.mpr (ih _ hm)
  let e := (MeasurableEquiv.piOptionEquivProd (fun _ : Option ι => ℝ)).symm
  have he (x : ι → ℝ) (y : ℝ) : e (x,y)=fun a => Option.elim a y x := by
    funext a
    cases a <;> rfl
  let Z : Set ((ι → ℝ) × ℝ) := {z | eval (e z) p=0}
  have hmZ : MeasurableSet Z :=
    (isClosed_eq p.continuous_eval continuous_const).measurableSet.preimage e.measurable
  have hnull : ((volume : Measure (ι → ℝ)).prod (volume : Measure ℝ)) Z=0 := by
    apply measure_prod_null_of_ae_null hmZ
    filter_upwards [hae] with x hx
    have hpx := option_polynomial_nonzero_section p m x hx
    have hz : Prod.mk x ⁻¹' Z={y : ℝ | (Polynomial.map (eval x) Q).eval y=0} := by
      ext y
      simp only [Set.mem_preimage,Z,Set.mem_ofPred_eq,he,optionEquivLeft_elim_eval,Q]
    rw [hz]
    exact univariate_zero_null _ hpx
  have hmap : ((volume : Measure (ι → ℝ)).prod (volume : Measure ℝ)).map e=
      (volume : Measure (Option ι → ℝ)) := pi_map_piOptionEquivProd (fun _ => volume)
  rw [←hmap,Measure.map_apply e.measurable
    (isClosed_eq p.continuous_eval continuous_const).measurableSet]
  exact hnull

end CommodityClassification.Genericity
