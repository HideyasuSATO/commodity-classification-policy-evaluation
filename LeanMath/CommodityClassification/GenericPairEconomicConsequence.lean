module

public import LeanMath.CommodityClassification.GenericPairHyperplanes
public import LeanMath.CommodityClassification.CoarsestCommodityClassification

/-! Outside the pair hyperplanes, the pair theorem permits only singleton cells. -/
@[expose] public section
noncomputable section
namespace CommodityClassification.Equilibrium.BenchmarkFamily
open Matrix InputCoordinates Genericity
variable {n k h g : ℕ} (F : BenchmarkFamily n k h)

def symmetricDemand : SymmetricDemand n := ⟨F.D,F.hD.isHermitian.isSymm⟩

theorem off_pair_hyperplanes_singletons (hn : 0<n)
    (hgeneric : F.symmetricDemand∉exceptionalPairs F.parents F.q F.b)
    (P : Partition n g) (R : Refinement P F.parents) (hnc : ¬F.ParentIdentified) :
    F.ReportIdentified P ↔ Function.Injective P.group := by
  rw [F.exact_commodity_pair_rule_of_goods hn P R hnc]
  constructor
  · intro hp i j hij
    by_contra hne
    have hparent := (P.refinement_iff F.parents).mp ⟨R⟩ i j hij
    exact (not_exceptional_pair_loads F.parents F.q F.b F.symmetricDemand hgeneric i j hne hparent)
      (hp i j hij).1
  · intro hinj i j hij
    have he : i=j := hinj hij
    subst j
    exact F.samePolicyAttributes_refl i

end CommodityClassification.Equilibrium.BenchmarkFamily
