module

public import LeanMath.CommodityClassification.SymmetricPositiveDomain
public import LeanMath.CommodityClassification.GenericPairEconomicConsequence

/-! A single generic demand set works for every reporting refinement. -/
@[expose] public section
noncomputable section
namespace CommodityClassification.Equilibrium.BenchmarkFamily
open Matrix InputCoordinates Genericity MeasureTheory MeasureTheory.Measure
open scoped Topology
variable {n k g : ℕ} (F : BenchmarkFamily n k g)

def SingletonClassificationAt (D : SymmetricDemand n) (hD : D.val.PosDef) : Prop :=
  ¬(F.withDemand D.val hD).ParentIdentified ∧
  ∀h : ℕ,∀P : Partition n h,∀_R : Refinement P F.parents,
    (F.withDemand D.val hD).ReportIdentified P ↔ Function.Injective P.group

theorem singleton_exception_closed_null (hk : 0<k) (hb : F.b≠0)
    (i j : Fin n) (hij : i≠j) (hgroup : F.parents.group i=F.parents.group j)
    (μ : Measure (SymmetricDemand n)) [IsAddHaarMeasure μ] :
    ∃Z : Set (SymmetricDemand n),IsClosed Z ∧ μ Z=0 ∧
      ∀D : SymmetricDemand n,D∉Z → ∀hD : D.val.PosDef,F.SingletonClassificationAt D hD := by
  obtain ⟨Z,hclosed,hnull,_,_,_,hc⟩ := F.parent_identification_nongeneric hk hb i j hij hgroup μ
  refine ⟨Z ∪ exceptionalPairs F.parents F.q F.b,
    hclosed.union (exceptionalPairs_closed F.parents F.q F.b),
    measure_union_null hnull (exceptionalPairs_null F.parents F.q F.b F.hq hb μ),?_⟩
  intro D hnot hD
  have hp : D∉Z := fun h => hnot (Or.inl h)
  have he : D∉exceptionalPairs F.parents F.q F.b := fun h => hnot (Or.inr h)
  have hnc : ¬(F.withDemand D.val hD).ParentIdentified := fun h => hp (hc D hD h)
  refine ⟨hnc,?_⟩
  intro h P R
  apply (F.withDemand D.val hD).off_pair_hyperplanes_singletons (Nat.zero_lt_of_lt i.isLt) _ P R hnc
  exact he

theorem generic_singleton_open_dense_full_measure (hk : 0<k) (hb : F.b≠0)
    (i j : Fin n) (hij : i≠j) (hgroup : F.parents.group i=F.parents.group j)
    (μ : Measure (SymmetricDemand n)) [IsAddHaarMeasure μ] :
    ∃U : Set (SymmetricDemand n),U⊆positiveDemandCone n ∧ IsOpen U ∧
      Dense {D : ↥(positiveDemandCone n) | D.val∈U} ∧
      μ.restrict (positiveDemandCone n) Uᶜ=0 ∧
      ∀D∈U,∀hD : D.val.PosDef,F.SingletonClassificationAt D hD := by
  obtain ⟨Z,hclosed,hnull,hgood⟩ := F.singleton_exception_closed_null hk hb i j hij hgroup μ
  let U : Set (SymmetricDemand n) := positiveDemandCone n ∩ Zᶜ
  have ho : IsOpen U := positiveDemandCone_isOpen.inter hclosed.isOpen_compl
  have hd : Dense {D : ↥(positiveDemandCone n) | D.val∉Z} :=
    dense_relative_positive_domain (interior_eq_empty_iff_dense_compl.mp
      (interior_eq_empty_of_null hnull))
  refine ⟨U,Set.inter_subset_left,ho,?_,?_,?_⟩
  · have he : {D : ↥(positiveDemandCone n) | D.val∈U}=
        {D : ↥(positiveDemandCone n) | D.val∉Z} := by
      ext D
      simp only [U,Set.mem_ofPred_eq,Set.mem_inter_iff,Set.mem_compl_iff,D.property,true_and]
    rw [he]
    exact hd
  · rw [Measure.restrict_apply ho.isClosed_compl.measurableSet]
    apply measure_mono_null _ hnull
    intro D hD
    by_contra hz
    exact hD.1 ⟨hD.2,hz⟩
  · intro D hD hp
    exact hgood D hD.2 hp

theorem generic_singleton_ae (hk : 0<k) (hb : F.b≠0)
    (i j : Fin n) (hij : i≠j) (hgroup : F.parents.group i=F.parents.group j)
    (μ : Measure (SymmetricDemand n)) [IsAddHaarMeasure μ] :
    ∀ᵐD ∂μ.restrict (positiveDemandCone n),∀hD : D.val.PosDef,F.SingletonClassificationAt D hD := by
  obtain ⟨U,_,_,_,hfull,hgood⟩ :=
    F.generic_singleton_open_dense_full_measure hk hb i j hij hgroup μ
  have hu : ∀ᵐD ∂μ.restrict (positiveDemandCone n),D∈U :=
    by simpa only [Filter.Eventually,Set.ofPred_mem_eq] using (mem_ae_iff.mpr hfull)
  filter_upwards [hu] with D hD hp
  exact hgood D hD hp

end CommodityClassification.Equilibrium.BenchmarkFamily
