module

public import LeanMath.CommodityClassification.CompositeCostMinimum

/-! The optimized composite is built from actual candidate product technologies. -/
@[expose] public section
noncomputable section
set_option maxHeartbeats 600000
namespace CommodityClassification.Equilibrium.BenchmarkFamily
open Matrix InputCoordinates
variable {n k h g : ℕ} (F : BenchmarkFamily n k h)

def nestProduction (G : Partition n g) (η : Vec g) (hη : ∀a,0<η a)
    (C : F.Candidate) (a : Fin g) : Composite.Data ((F.nestData G η hη).size a) (k+1) where
  nest := (F.nestData G η hη).nest a
  A := (F.nestData G η hη).nestInputs (F.model C).A a
  w0 := F.frame.w
  sigma := F.sigma
  hA := fun j l => C.property.1 ((F.nestData G η hη).product a j) l
  hw := F.hw
  hcost := by
    funext j
    exact congrFun (F.frame.reconstruct_cost F.p C.val) ((F.nestData G η hη).product a j)
  hsigma := F.hsigma

theorem nestProduction_costs (G : Partition n g) (η : Vec g) (hη : ∀a,0<η a)
    (C : F.Candidate) (a : Fin g) (w : Vec (k+1)) :
    (F.nestProduction G η hη C a).costs w=
      (F.nestData G η hη).restrict a ((F.model C).costs w) := rfl

theorem nestProduction_compositeCost (G : Partition n g) (η : Vec g) (hη : ∀a,0<η a)
    (C : F.Candidate) (a : Fin g) (w : Vec (k+1)) :
    (F.nestProduction G η hη C a).compositeCost w=
      ((F.nestData G η hη).nest a).expenditureIndex
        ((F.nestData G η hη).restrict a ((F.model C).costs w)) := rfl

theorem nestProduction_actual_minimum (G : Partition n g) (η : Vec g) (hη : ∀a,0<η a)
    (C : F.Candidate) (a : Fin g) {w : Vec (k+1)} (hw : ∀j,0<w j) :
    IsLeast {v : ℝ | ∃x : Vec ((F.nestData G η hη).size a),
      (∀i,0≤x i) ∧ 1≤((F.nestData G η hη).nest a).quantityOnNonnegative x ∧
      v=dotProduct ((F.nestData G η hη).restrict a ((F.model C).costs w)) x}
      ((F.nestProduction G η hη C a).compositeCost w) :=
  (F.nestProduction G η hη C a).compositeCost_isLeast hw

theorem nestProduction_meanInputs (G : Partition n g) (η : Vec g) (hη : ∀a,0<η a)
    (C : F.Candidate) (a : Fin g) :
    (F.nestProduction G η hη C a).meanInputs=
      (G.sales F.p F.q a)⁻¹ • G.report F.q (F.model C).A a := by
  rw [(F.nestProduction G η hη C a).meanInputs_total]
  change ((F.nestData G η hη).nest a).sales⁻¹ •
    (F.nestData G η hη).nestFirstMoment (F.model C).A a=_
  rw [(F.nestData G η hη).nestFirstMoment_eq_report,(F.nestData G η hη).nest_sales]
  rfl

end CommodityClassification.Equilibrium.BenchmarkFamily
