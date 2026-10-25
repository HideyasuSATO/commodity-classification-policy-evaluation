module

public import LeanMath.CommodityClassification.SeparablePolicyAttributes

/-! The separable-demand rule, including the balanced two-product exception. -/
@[expose] public section
noncomputable section
namespace CommodityClassification.Equilibrium.BenchmarkFamily
open Matrix InputCoordinates
variable {n k h g : ℕ} (F : BenchmarkFamily n k h)

theorem separable_third_product_iff (η : Vec n)
    (hD : F.D=diagonal (fun i => η i*F.q i/F.p i))
    (i j l : Fin n) (hij : i≠j) (hgi : F.parents.group j=F.parents.group i)
    (hgl : F.parents.group l=F.parents.group i) (hli : l≠i) (hlj : l≠j) :
    F.SamePolicyAttributes i j ↔
      η i=F.sigma ∧ η j=F.sigma ∧ F.b i/F.p i=F.b j/F.p j := by
  rw [F.separable_attributes_iff η hD i j hij,
    twoSupport_third_product_iff F.parents F.q F.hq F.report i j l hij hgi hgl hli hlj]
  exact F.separable_rigid_algebra η i j

theorem separable_nonzero_parent_iff (η : Vec n)
    (hD : F.D=diagonal (fun i => η i*F.q i/F.p i))
    (i j : Fin n) (hij : i≠j) (hgi : F.parents.group j=F.parents.group i)
    (hJ : F.report (F.parents.group i)≠0) :
    F.SamePolicyAttributes i j ↔
      η i=F.sigma ∧ η j=F.sigma ∧ F.b i/F.p i=F.b j/F.p j := by
  rw [F.separable_attributes_iff η hD i j hij,
    twoSupport_nonzero_parent_iff F.parents F.q F.hq F.report i j hij hgi hJ]
  exact F.separable_rigid_algebra η i j

theorem separable_balanced_pair_iff (η : Vec n)
    (hD : F.D=diagonal (fun i => η i*F.q i/F.p i))
    (i j : Fin n) (hij : i≠j) (hgi : F.parents.group j=F.parents.group i)
    (honly : ∀l,F.parents.group l=F.parents.group i → l=i ∨ l=j)
    (hJ : F.report (F.parents.group i)=0) :
    F.SamePolicyAttributes i j ↔
      η i*F.b i/F.p i=η j*F.b j/F.p j ∧
      (η i-F.sigma)/(F.p i*F.q i)+(η j-F.sigma)/(F.p j*F.q j)=0 := by
  rw [F.separable_attributes_iff η hD i j hij,
    twoSupport_balanced_pair_iff F.parents F.q F.hq F.report i j hij hgi honly hJ]
  simp only [div_div]

theorem separable_attributes_of_rigid (η : Vec n)
    (hD : F.D=diagonal (fun i => η i*F.q i/F.p i)) (i j : Fin n) (hij : i≠j)
    (hi : η i=F.sigma) (hj : η j=F.sigma) (hb : F.b i/F.p i=F.b j/F.p j) :
    F.SamePolicyAttributes i j := by
  apply (F.separable_attributes_iff η hD i j hij).mpr
  have ha := (F.separable_rigid_algebra η i j).mpr ⟨hi,hj,hb⟩
  exact ⟨ha.1,by rw [ha.2.1,ha.2.2];exact twoSupport_mem_of_zero F.parents F.q F.report i j⟩

def SeparablePairAllowed (η : Vec n) (i j : Fin n) : Prop :=
  (η i=F.sigma ∧ η j=F.sigma ∧ F.b i/F.p i=F.b j/F.p j) ∨
  ((∀l,F.parents.group l=F.parents.group i → l=i ∨ l=j) ∧
    F.report (F.parents.group i)=0 ∧
    η i*F.b i/F.p i=η j*F.b j/F.p j ∧
    (η i-F.sigma)/(F.p i*F.q i)+(η j-F.sigma)/(F.p j*F.q j)=0)

theorem separable_pair_iff (η : Vec n)
    (hD : F.D=diagonal (fun i => η i*F.q i/F.p i))
    (i j : Fin n) (hij : i≠j) (hgi : F.parents.group j=F.parents.group i) :
    F.SamePolicyAttributes i j ↔ F.SeparablePairAllowed η i j := by
  classical
  constructor
  · intro ha
    by_cases hthird : ∃l,F.parents.group l=F.parents.group i ∧ l≠i ∧ l≠j
    · obtain ⟨l,hgl,hli,hlj⟩ := hthird
      exact Or.inl ((F.separable_third_product_iff η hD i j l hij hgi hgl hli hlj).mp ha)
    · have honly : ∀l,F.parents.group l=F.parents.group i → l=i ∨ l=j := by
        intro l hl
        by_cases hi : l=i
        · exact Or.inl hi
        · exact Or.inr (by by_contra hj;exact hthird ⟨l,hl,hi,hj⟩)
      by_cases hJ : F.report (F.parents.group i)=0
      · exact Or.inr ⟨honly,hJ,(F.separable_balanced_pair_iff η hD i j hij hgi honly hJ).mp ha⟩
      · exact Or.inl ((F.separable_nonzero_parent_iff η hD i j hij hgi hJ).mp ha)
  · rintro (⟨hi,hj,hb⟩|⟨honly,hJ,hb,hbalance⟩)
    · exact F.separable_attributes_of_rigid η hD i j hij hi hj hb
    · exact (F.separable_balanced_pair_iff η hD i j hij hgi honly hJ).mpr ⟨hb,hbalance⟩

theorem separable_report_identification_iff (hn : 0<n) (η : Vec n)
    (hD : F.D=diagonal (fun i => η i*F.q i/F.p i))
    (P : Partition n g) (R : Refinement P F.parents) (hnc : ¬F.ParentIdentified) :
    F.ReportIdentified P ↔
      ∀i j : Fin n,i≠j → P.group i=P.group j → F.SeparablePairAllowed η i j := by
  rw [F.exact_commodity_pair_rule_of_goods hn P R hnc]
  constructor
  · intro hp i j hij hgroup
    have hgi := (P.refinement_iff F.parents).mp ⟨R⟩ j i hgroup.symm
    exact (F.separable_pair_iff η hD i j hij hgi).mp (hp i j hgroup)
  · intro hp i j hgroup
    by_cases hij : i=j
    · subst j;exact F.samePolicyAttributes_refl i
    · have hgi := (P.refinement_iff F.parents).mp ⟨R⟩ j i hgroup.symm
      exact (F.separable_pair_iff η hD i j hij hgi).mpr (hp i j hij hgroup)

end CommodityClassification.Equilibrium.BenchmarkFamily
