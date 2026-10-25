module

public import LeanMath.CommodityClassification.NestedOrthogonalCoordinates

/-! The exact normalized orthogonal quadratic identity printed in the manuscript. -/
@[expose] public section
noncomputable section
set_option maxHeartbeats 600000
namespace CommodityClassification.DemandNests.Data
open Matrix InputCoordinates
open scoped BigOperators
variable {n g : ℕ} (d : DemandNests.Data n g)

theorem root_price_diagonal_energy (h : Vec n) :
    dotProduct (Regularity.rootXi d.p d.q *ᵥ h)
      (diagonal (fun i => d.eta (d.partition.group i)) *ᵥ (Regularity.rootXi d.p d.q *ᵥ h))=
      ∑i,d.eta (d.partition.group i)*(d.q i/d.p i)*(h i)^2 := by
  simp only [dotProduct,Regularity.rootXi,Matrix.mulVec_diagonal]
  apply Finset.sum_congr rfl
  intro i _
  calc
    _=d.eta (d.partition.group i)*(Real.sqrt (d.q i/d.p i))^2*(h i)^2 := by ring
    _=_ := by rw [Real.sq_sqrt (div_pos (d.hq i) (d.hp i)).le]

theorem aggregate_diagonal_energy (h : Vec n) :
    dotProduct (d.aggregateCoordinate h) (diagonal d.eta *ᵥ d.aggregateCoordinate h)=
      ∑a,d.eta a*d.partition.sales d.p d.q a*(d.priceDerivative h a)^2 := by
  rw [d.aggregateCoordinate_eq_root_price]
  simp only [dotProduct,nestRoot,Regularity.rootXi,Matrix.mulVec_diagonal,div_one]
  apply Finset.sum_congr rfl
  intro a _
  calc
    _=d.eta a*(Real.sqrt (d.partition.sales d.p d.q a))^2*(d.priceDerivative h a)^2 := by ring
    _=_ := by rw [Real.sq_sqrt (d.partition.sales_pos d.p d.q d.hp d.hq a).le]

theorem aggregate_outer_energy (DG : Matrix (Fin g) (Fin g) ℝ) (h : Vec n) :
    dotProduct (d.priceDerivative h) (DG *ᵥ d.priceDerivative h)=
      dotProduct (d.aggregateCoordinate h)
        ((d.nestInvRoot*DG*d.nestInvRoot) *ᵥ d.aggregateCoordinate h) := by
  rw [d.price_response_eq_invRoot_coordinate h]
  have he := Supply.quad_conjugate DG d.nestInvRoot (d.aggregateCoordinate h)
  simpa only [nestInvRoot,Regularity.invRootXi,diagonal_transpose] using he.symm

theorem normalized_elasticity_energy (h : Vec n) :
    dotProduct (Regularity.rootXi d.p d.q *ᵥ h)
      (diagonal (fun i => d.eta (d.partition.group i)) *ᵥ (Regularity.rootXi d.p d.q *ᵥ h))=
    dotProduct (d.aggregateCoordinate h) (diagonal d.eta *ᵥ d.aggregateCoordinate h)+
    dotProduct (d.perpendicularCoordinate h)
      (diagonal (fun i => d.eta (d.partition.group i)) *ᵥ d.perpendicularCoordinate h) := by
  have hm : d.normalizedMembership.transpose*diagonal (fun i => d.eta (d.partition.group i))*
      d.normalizedMembership=diagonal d.eta := by
    rw [Matrix.mul_assoc,d.elasticity_membership_invariant,←Matrix.mul_assoc,
      d.normalizedMembership_gram,Matrix.one_mul]
  have he : dotProduct (d.normalizedMembership *ᵥ d.aggregateCoordinate h)
      (diagonal (fun i => d.eta (d.partition.group i)) *ᵥ
        (d.normalizedMembership *ᵥ d.aggregateCoordinate h))=
      dotProduct (d.aggregateCoordinate h) (diagonal d.eta *ᵥ d.aggregateCoordinate h) := by
    rw [←Supply.quad_conjugate,hm]
  have hc1 : dotProduct (d.normalizedMembership *ᵥ d.aggregateCoordinate h)
      (diagonal (fun i => d.eta (d.partition.group i)) *ᵥ d.perpendicularCoordinate h)=0 := by
    rw [dotProduct_comm,←Matrix.dotProduct_transpose_mulVec,d.perpendicular_elasticity_orthogonal,
      dotProduct_zero]
  have hc2 : dotProduct (d.perpendicularCoordinate h)
      (diagonal (fun i => d.eta (d.partition.group i)) *ᵥ
        (d.normalizedMembership *ᵥ d.aggregateCoordinate h))=0 := by
    rw [Matrix.mulVec_mulVec,d.elasticity_membership_invariant,←Matrix.mulVec_mulVec,
      ←Matrix.dotProduct_transpose_mulVec,d.perpendicular_orthogonal,dotProduct_zero]
  rw [d.normalized_decomposition h]
  simp only [Matrix.mulVec_add,add_dotProduct,dotProduct_add]
  rw [he,hc1,hc2]
  ring

theorem manuscript_orthogonal_quadratic (DG : Matrix (Fin g) (Fin g) ℝ) (h : Vec n) :
    dotProduct h (d.demandMatrix DG *ᵥ h)=
      dotProduct (d.perpendicularCoordinate h)
        (diagonal (fun i => d.eta (d.partition.group i)) *ᵥ d.perpendicularCoordinate h)+
      dotProduct (d.aggregateCoordinate h)
        ((d.nestInvRoot*DG*d.nestInvRoot) *ᵥ d.aggregateCoordinate h) := by
  rw [d.quadratic_diagonal_part,←d.root_price_diagonal_energy,
    ←d.aggregate_diagonal_energy,d.aggregate_outer_energy,d.normalized_elasticity_energy]
  ring

end CommodityClassification.DemandNests.Data
