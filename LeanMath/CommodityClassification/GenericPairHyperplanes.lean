module

public import LeanMath.CommodityClassification.SymmetricDemandFunctionals

/-! A finite union of proper load hyperplanes, with its exact measure space. -/
@[expose] public section
noncomputable section
namespace CommodityClassification.Genericity
open Matrix InputCoordinates MeasureTheory MeasureTheory.Measure
open scoped Topology
variable {n g : ℕ}

theorem weighted_exchange_nonzero (q : Vec n) (hq : ∀i,0<q i)
    (i j : Fin n) (hij : i≠j) : weightedExchange q i j≠0 := by
  intro he
  have hi := congrFun he i
  have hi0 : (q i)⁻¹=0 := by simpa [weightedExchange,hij] using hi
  exact (inv_ne_zero (hq i).ne') hi0

theorem pairFunctional_exchange (q b : Vec n) (i j : Fin n) (D : SymmetricDemand n) :
    pairFunctional b (weightedExchange q i j) D=
      (D.val *ᵥ b) i/q i-(D.val *ᵥ b) j/q j :=
  weighted_exchange_dot q (D.val *ᵥ b) i j

abbrev ParentPair (P : Partition n g) :=
  {ij : Fin n × Fin n // ij.1≠ij.2 ∧ P.group ij.1=P.group ij.2}

def exceptionalPairs (P : Partition n g) (q b : Vec n) : Set (SymmetricDemand n) :=
  ⋃e : ParentPair P,(LinearMap.ker (pairFunctional b (weightedExchange q e.val.1 e.val.2)) :
    Set (SymmetricDemand n))

theorem exceptionalPairs_closed (P : Partition n g) (q b : Vec n) :
    IsClosed (exceptionalPairs P q b) :=
  isClosed_iUnion_of_finite (fun e => pairFunctional_kernel_closed b (weightedExchange q e.val.1 e.val.2))

theorem exceptionalPairs_null (P : Partition n g) (q b : Vec n)
    (hq : ∀i,0<q i) (hb : b≠0)
    (μ : Measure (SymmetricDemand n)) [IsAddHaarMeasure μ] :
    μ (exceptionalPairs P q b)=0 := by
  apply measure_iUnion_null
  intro e
  exact pairFunctional_kernel_null b (weightedExchange q e.val.1 e.val.2) hb
    (weighted_exchange_nonzero q hq _ _ e.property.1) μ

theorem exceptionalPairs_empty_interior (P : Partition n g) (q b : Vec n)
    (hq : ∀i,0<q i) (hb : b≠0)
    (μ : Measure (SymmetricDemand n)) [IsAddHaarMeasure μ] :
    interior (exceptionalPairs P q b)=∅ :=
  interior_eq_empty_of_null (exceptionalPairs_null P q b hq hb μ)

theorem exceptionalPairs_open_dense_complement (P : Partition n g) (q b : Vec n)
    (hq : ∀i,0<q i) (hb : b≠0)
    (μ : Measure (SymmetricDemand n)) [IsAddHaarMeasure μ] :
    IsOpen (exceptionalPairs P q b)ᶜ ∧ Dense (exceptionalPairs P q b)ᶜ :=
  ⟨(exceptionalPairs_closed P q b).isOpen_compl,
    interior_eq_empty_iff_dense_compl.mp (exceptionalPairs_empty_interior P q b hq hb μ)⟩

theorem exceptionalPairs_ae_avoid (P : Partition n g) (q b : Vec n)
    (hq : ∀i,0<q i) (hb : b≠0)
    (μ : Measure (SymmetricDemand n)) [IsAddHaarMeasure μ] :
    ∀ᵐD ∂μ,D∉exceptionalPairs P q b := by
  exact compl_mem_ae_iff.mpr (exceptionalPairs_null P q b hq hb μ)

theorem not_exceptional_pair_loads (P : Partition n g) (q b : Vec n) (D : SymmetricDemand n)
    (hD : D∉exceptionalPairs P q b) (i j : Fin n) (hij : i≠j)
    (hgroup : P.group i=P.group j) : (D.val *ᵥ b) i/q i≠(D.val *ᵥ b) j/q j := by
  intro he
  apply hD
  apply Set.mem_iUnion.mpr
  refine ⟨⟨(i,j),hij,hgroup⟩,?_⟩
  change pairFunctional b (weightedExchange q i j) D=0
  rw [pairFunctional_exchange,he,sub_self]

end CommodityClassification.Genericity
