module

public import LeanMath.CommodityClassification.NestedConditionalDerivative

/-! Differentiate the actual composition of outer and conditional quantities. -/
@[expose] public section
noncomputable section
set_option maxHeartbeats 600000
namespace CommodityClassification.DemandNests.Data
open Matrix InputCoordinates Filter
open scoped BigOperators Topology
variable {n g : ℕ} (d : DemandNests.Data n g)

def demand (outer : Vec g → Vec g) (r : Vec n) : Vec n := fun i =>
  outer (d.priceMap r) (d.partition.group i)*d.conditionalQuantities r i

def demandDerivative (DG : Matrix (Fin g) (Fin g) ℝ) : Vec n →L[ℝ] Vec n :=
  ContinuousLinearMap.pi (fun i =>
    (d.q i/d.partition.sales d.p d.q (d.partition.group i)) •
      ((ContinuousLinearMap.proj (d.partition.group i)).comp
        ((-Equilibrium.matCLM DG).comp d.priceDerivative)) +
    (d.partition.sales d.p d.q (d.partition.group i)) •
      ((ContinuousLinearMap.proj i).comp d.conditionalDerivative))

theorem demand_benchmark (outer : Vec g → Vec g)
    (hbase : outer (fun _ => 1)=d.partition.sales d.p d.q) : d.demand outer d.p=d.q := by
  funext i
  change outer (d.priceMap d.p) (d.partition.group i)*d.conditionalQuantities d.p i=d.q i
  rw [d.priceMap_benchmark,hbase,d.conditionalQuantities_benchmark]
  field_simp [(d.partition.sales_pos d.p d.q d.hp d.hq _).ne']

theorem demand_hasFDerivAt (outer : Vec g → Vec g) (DG : Matrix (Fin g) (Fin g) ℝ)
    (hbase : outer (fun _ => 1)=d.partition.sales d.p d.q)
    (houter : HasFDerivAt outer (-Equilibrium.matCLM DG) (fun _ => 1)) :
    HasFDerivAt (d.demand outer) (d.demandDerivative DG) d.p := by
  have ho : HasFDerivAt (fun r => outer (d.priceMap r))
      ((-Equilibrium.matCLM DG).comp d.priceDerivative) d.p := by
    have hh : HasFDerivAt outer (-Equilibrium.matCLM DG) (d.priceMap d.p) := by
      rw [d.priceMap_benchmark]
      exact houter
    exact hh.comp d.p d.priceMap_hasFDerivAt
  apply hasFDerivAt_pi.mpr
  intro i
  have hi := (hasFDerivAt_pi'.mp ho (d.partition.group i)).mul
    (hasFDerivAt_pi'.mp d.conditionalQuantities_hasFDerivAt i)
  convert hi using 1 <;>
    simp [demand,d.priceMap_benchmark,hbase,d.conditionalQuantities_benchmark,add_comm]
  rfl

theorem demandDerivative_apply (DG : Matrix (Fin g) (Fin g) ℝ) (h : Vec n) (i : Fin n) :
    d.demandDerivative DG h i=
      -(d.q i/d.partition.sales d.p d.q (d.partition.group i))*
        (DG *ᵥ d.priceDerivative h) (d.partition.group i)+
      d.eta (d.partition.group i)*d.q i*
        (d.priceDerivative h (d.partition.group i)-h i/d.p i) := by
  change ((d.q i/d.partition.sales d.p d.q (d.partition.group i)) •
      ((ContinuousLinearMap.proj (d.partition.group i)).comp
        ((-Equilibrium.matCLM DG).comp d.priceDerivative)) +
    (d.partition.sales d.p d.q (d.partition.group i)) •
      ((ContinuousLinearMap.proj i).comp d.conditionalDerivative)) h=_
  simp only [_root_.add_apply,_root_.smul_apply,_root_.neg_apply,
    ContinuousLinearMap.comp_apply,ContinuousLinearMap.proj_apply,
    Equilibrium.matCLM_apply,smul_eq_mul,d.conditionalDerivative_apply,Pi.neg_apply]
  field_simp [(d.partition.sales_pos d.p d.q d.hp d.hq _).ne']

end CommodityClassification.DemandNests.Data
