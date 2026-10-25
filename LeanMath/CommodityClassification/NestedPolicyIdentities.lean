module

public import LeanMath.CommodityClassification.NestedOrthogonalQuadratic

/-! The proportional-within-nest policy formulas, including zero nest taxes. -/
@[expose] public section
noncomputable section
set_option maxHeartbeats 600000
namespace CommodityClassification.DemandNests.Data
open Matrix InputCoordinates
open scoped BigOperators
variable {n g : ℕ} (d : DemandNests.Data n g)

def proportionalPolicy (β : Vec g) : Vec n := d.partition.Q d.p *ᵥ β

theorem proportionalPolicy_apply (β : Vec g) (i : Fin n) :
    d.proportionalPolicy β i=d.p i*β (d.partition.group i) :=
  d.partition.Q_mulVec_apply d.p β i

theorem proportional_price_response (β : Vec g) : d.priceDerivative (d.proportionalPolicy β)=β := by
  funext a
  rw [d.priceDerivative_apply]
  have hs : (∑i∈d.partition.cell a,d.q i*d.proportionalPolicy β i)=
      d.partition.sales d.p d.q a*β a := by
    rw [d.partition.sales_apply,Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i hi
    rw [d.proportionalPolicy_apply,(d.partition.mem_cell a i).mp hi]
    ring
  rw [hs]
  field_simp [(d.partition.sales_pos d.p d.q d.hp d.hq a).ne']

theorem demand_policy_apply (DG : Matrix (Fin g) (Fin g) ℝ) (β : Vec g) (i : Fin n) :
    (d.demandMatrix DG *ᵥ d.proportionalPolicy β) i=
      (d.q i/d.partition.sales d.p d.q (d.partition.group i))*(DG *ᵥ β) (d.partition.group i) := by
  rw [d.demandMatrix_apply,d.proportional_price_response,d.proportionalPolicy_apply]
  field_simp [(d.hp i).ne']
  ring

theorem demand_policy_matrix (DG : Matrix (Fin g) (Fin g) ℝ) (β : Vec g) :
    d.demandMatrix DG *ᵥ d.proportionalPolicy β=
      d.partition.Q d.q *ᵥ (diagonal (fun a => (d.partition.sales d.p d.q a)⁻¹) *ᵥ (DG *ᵥ β)) := by
  funext i
  rw [d.demand_policy_apply,d.partition.Q_mulVec_apply,Matrix.mulVec_diagonal]
  ring

theorem proportional_policy_energy (DG : Matrix (Fin g) (Fin g) ℝ) (β : Vec g) :
    dotProduct (d.proportionalPolicy β) (d.demandMatrix DG *ᵥ d.proportionalPolicy β)=
      dotProduct β (DG *ᵥ β) := by
  have hQ : (d.partition.Q d.p).transpose*d.partition.Q d.q=
      diagonal (d.partition.sales d.p d.q) := d.partition.valueAggregation_Q d.p d.q d.hp d.hq
  have hs : diagonal (d.partition.sales d.p d.q)*
      diagonal (fun a => (d.partition.sales d.p d.q a)⁻¹)=(1 : Matrix (Fin g) (Fin g) ℝ) := by
    rw [diagonal_mul_diagonal]
    have he : (fun a => d.partition.sales d.p d.q a*(d.partition.sales d.p d.q a)⁻¹)=fun _ => (1:ℝ) := by
      funext a
      exact mul_inv_cancel₀ (d.partition.sales_pos d.p d.q d.hp d.hq a).ne'
    rw [he,diagonal_one]
  rw [d.demand_policy_matrix]
  change dotProduct (d.partition.Q d.p *ᵥ β) _=_
  rw [dotProduct_comm,←Matrix.dotProduct_transpose_mulVec,Matrix.mulVec_mulVec,
    hQ,Matrix.mulVec_mulVec,hs,Matrix.one_mulVec]

theorem actual_proportional_quantity_derivative (outer : Vec g → Vec g)
    (DG : Matrix (Fin g) (Fin g) ℝ)
    (hbase : outer (fun _ => 1)=d.partition.sales d.p d.q)
    (houter : HasFDerivAt outer (-Equilibrium.matCLM DG) (fun _ => 1)) (β : Vec g) :
    fderiv ℝ (d.demand outer) d.p (d.proportionalPolicy β)=
      -(d.partition.Q d.q *ᵥ (diagonal (fun a => (d.partition.sales d.p d.q a)⁻¹) *ᵥ (DG *ᵥ β))) := by
  rw [(d.demand_actual_matrix_derivative outer DG hbase houter).fderiv]
  simp only [_root_.neg_apply,Equilibrium.matCLM_apply,d.demand_policy_matrix]

end CommodityClassification.DemandNests.Data
