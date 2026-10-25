module

public import LeanMath.CommodityClassification.SymmetricPolynomialNullity

/-! A single fixed closed null exceptional set contains parent identification. -/
@[expose] public section
noncomputable section
namespace CommodityClassification.Equilibrium.BenchmarkFamily
open Matrix InputCoordinates Genericity MeasureTheory MeasureTheory.Measure
open scoped Topology
variable {n k g : ℕ} (F : BenchmarkFamily n k g)

theorem parent_identification_nongeneric (hk : 0<k) (hb : F.b≠0)
    (i j : Fin n) (hij : i≠j) (hgroup : F.parents.group i=F.parents.group j)
    (μ : Measure (SymmetricDemand n)) [IsAddHaarMeasure μ] :
    ∃Z : Set (SymmetricDemand n),IsClosed Z ∧ μ Z=0 ∧ interior Z=∅ ∧
      IsOpen Zᶜ ∧ Dense Zᶜ ∧
      ∀D : SymmetricDemand n,∀hD : D.val.PosDef,
        (F.withDemand D.val hD).ParentIdentified → D∈Z := by
  obtain ⟨C,hP,hclosed,hcontain⟩ := F.exists_nonzero_parent_polynomial hk hb i j hij hgroup
  let P := F.gainDifferencePolynomial C.val F.parentMean
  refine ⟨{D : SymmetricDemand n | MvPolynomial.eval (symmetricCoordinates D) P=0},
    hclosed,symmetric_polynomial_zero_null P hP μ,
    symmetric_polynomial_empty_interior P hP μ,
    (symmetric_polynomial_open_dense P hP μ).1,
    (symmetric_polynomial_open_dense P hP μ).2,hcontain⟩

theorem parent_identification_ae_failure (hk : 0<k) (hb : F.b≠0)
    (i j : Fin n) (hij : i≠j) (hgroup : F.parents.group i=F.parents.group j)
    (μ : Measure (SymmetricDemand n)) [IsAddHaarMeasure μ] :
    ∀ᵐD ∂μ,∀hD : D.val.PosDef,¬(F.withDemand D.val hD).ParentIdentified := by
  obtain ⟨Z,_,hnull,_,_,_,hc⟩ := F.parent_identification_nongeneric hk hb i j hij hgroup μ
  have hz : ∀ᵐD ∂μ,D∉Z := compl_mem_ae_iff.mpr hnull
  filter_upwards [hz] with D hDnot hD hp
  exact hDnot (hc D hD hp)

end CommodityClassification.Equilibrium.BenchmarkFamily
