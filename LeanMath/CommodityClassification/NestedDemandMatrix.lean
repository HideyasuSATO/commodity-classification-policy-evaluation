module

public import LeanMath.CommodityClassification.NestedDemandDerivative

/-! Identify the actual nested-demand derivative with the manuscript matrix. -/
@[expose] public section
noncomputable section
set_option maxHeartbeats 600000
namespace CommodityClassification.DemandNests.Data
open Matrix InputCoordinates
open scoped BigOperators
variable {n g : ℕ} (d : DemandNests.Data n g)

def outerAdjustment (DG : Matrix (Fin g) (Fin g) ℝ) : Matrix (Fin g) (Fin g) ℝ :=
  diagonal (fun a => (d.partition.sales d.p d.q a)⁻¹)*
    (DG-diagonal (fun a => d.eta a*d.partition.sales d.p d.q a))*
      diagonal (fun a => (d.partition.sales d.p d.q a)⁻¹)

def demandMatrix (DG : Matrix (Fin g) (Fin g) ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  diagonal (fun i => d.eta (d.partition.group i))*Supply.xi d.p d.q+
    d.partition.Q d.q*d.outerAdjustment DG*(d.partition.Q d.q).transpose

theorem demandMatrix_apply (DG : Matrix (Fin g) (Fin g) ℝ) (h : Vec n) (i : Fin n) :
    (d.demandMatrix DG *ᵥ h) i=
      d.eta (d.partition.group i)*(d.q i/d.p i)*h i+
      (d.q i/d.partition.sales d.p d.q (d.partition.group i))*
        (DG *ᵥ d.priceDerivative h) (d.partition.group i)-
      d.eta (d.partition.group i)*d.q i*d.priceDerivative h (d.partition.group i) := by
  have hy : diagonal (fun a => (d.partition.sales d.p d.q a)⁻¹) *ᵥ
      ((d.partition.Q d.q).transpose *ᵥ h)=d.priceDerivative h := by
    rw [Matrix.mulVec_mulVec]
    exact (d.priceDerivative_matrix h).symm
  simp only [demandMatrix,outerAdjustment,Matrix.add_mulVec,←Matrix.mulVec_mulVec,Pi.add_apply]
  rw [hy,d.partition.Q_mulVec_apply]
  simp only [Supply.xi,Matrix.mulVec_diagonal,Matrix.sub_mulVec,Pi.sub_apply]
  field_simp [(d.partition.sales_pos d.p d.q d.hp d.hq _).ne']
  ring

theorem demandDerivative_eq_matrix (DG : Matrix (Fin g) (Fin g) ℝ) :
    d.demandDerivative DG= -Equilibrium.matCLM (d.demandMatrix DG) := by
  apply ContinuousLinearMap.ext
  intro h
  funext i
  rw [d.demandDerivative_apply]
  simp only [_root_.neg_apply,Equilibrium.matCLM_apply,Pi.neg_apply]
  rw [d.demandMatrix_apply]
  ring

theorem demand_actual_matrix_derivative (outer : Vec g → Vec g)
    (DG : Matrix (Fin g) (Fin g) ℝ)
    (hbase : outer (fun _ => 1)=d.partition.sales d.p d.q)
    (houter : HasFDerivAt outer (-Equilibrium.matCLM DG) (fun _ => 1)) :
    HasFDerivAt (d.demand outer) (-Equilibrium.matCLM (d.demandMatrix DG)) d.p := by
  rw [←d.demandDerivative_eq_matrix]
  exact d.demand_hasFDerivAt outer DG hbase houter

end CommodityClassification.DemandNests.Data
