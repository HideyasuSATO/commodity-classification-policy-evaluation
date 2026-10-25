module

public import LeanMath.CommodityClassification.NestedNormalizedMembership

/-! Exact normalized aggregate and orthogonal price components. -/
@[expose] public section
noncomputable section
set_option maxHeartbeats 600000
namespace CommodityClassification.DemandNests.Data
open Matrix InputCoordinates
open scoped BigOperators
variable {n g : ℕ} (d : DemandNests.Data n g)

def aggregateCoordinate (h : Vec n) : Vec g :=
  d.normalizedMembership.transpose *ᵥ (Regularity.rootXi d.p d.q *ᵥ h)

def perpendicularCoordinate (h : Vec n) : Vec n :=
  Regularity.rootXi d.p d.q *ᵥ h-d.normalizedMembership *ᵥ d.aggregateCoordinate h

theorem normalized_decomposition (h : Vec n) :
    Regularity.rootXi d.p d.q *ᵥ h=
      d.normalizedMembership *ᵥ d.aggregateCoordinate h+d.perpendicularCoordinate h := by
  unfold perpendicularCoordinate
  abel

theorem perpendicular_orthogonal (h : Vec n) :
    d.normalizedMembership.transpose *ᵥ d.perpendicularCoordinate h=0 := by
  rw [perpendicularCoordinate,Matrix.mulVec_sub,
    Matrix.mulVec_mulVec (d.aggregateCoordinate h) d.normalizedMembership.transpose d.normalizedMembership,
    d.normalizedMembership_gram,Matrix.one_mulVec]
  exact sub_self _

theorem transpose_membership_root :
    d.normalizedMembership.transpose*Regularity.rootXi d.p d.q=
      d.nestInvRoot*(d.partition.Q d.q).transpose := by
  have ht := congrArg transpose d.rootXi_normalizedMembership
  simpa only [transpose_mul,nestInvRoot,Regularity.rootXi,Regularity.invRootXi,diagonal_transpose]
    using ht

theorem report_price_response (h : Vec n) :
    (d.partition.Q d.q).transpose *ᵥ h=
      diagonal (d.partition.sales d.p d.q) *ᵥ d.priceDerivative h := by
  funext a
  rw [Matrix.mulVec_diagonal]
  exact (d.partition.sales_apply h d.q a).trans (d.cell_price_sum h a)

theorem aggregateCoordinate_eq_root_price (h : Vec n) :
    d.aggregateCoordinate h=d.nestRoot *ᵥ d.priceDerivative h := by
  rw [aggregateCoordinate,Matrix.mulVec_mulVec,d.transpose_membership_root,
    ←Matrix.mulVec_mulVec,d.report_price_response,Matrix.mulVec_mulVec,
    ←d.nestRoot_square,←Matrix.mul_assoc,d.nestInvRoot_root,Matrix.one_mul]

theorem price_response_eq_invRoot_coordinate (h : Vec n) :
    d.priceDerivative h=d.nestInvRoot *ᵥ d.aggregateCoordinate h := by
  rw [d.aggregateCoordinate_eq_root_price,Matrix.mulVec_mulVec,d.nestInvRoot_root,Matrix.one_mulVec]

theorem elasticity_membership_invariant :
    diagonal (fun i => d.eta (d.partition.group i))*d.normalizedMembership=
      d.normalizedMembership*diagonal d.eta := by
  ext i a
  simp only [diagonal_mul,mul_diagonal,normalizedMembership,Regularity.invRootXi,
    nestInvRoot,diagonal_mul,mul_diagonal,Partition.Q]
  split_ifs with hia
  · rw [hia]
    ring
  · ring

theorem perpendicular_elasticity_orthogonal (h : Vec n) :
    d.normalizedMembership.transpose *ᵥ
      (diagonal (fun i => d.eta (d.partition.group i)) *ᵥ d.perpendicularCoordinate h)=0 := by
  have ht := congrArg transpose d.elasticity_membership_invariant
  simp only [transpose_mul,diagonal_transpose] at ht
  rw [Matrix.mulVec_mulVec,ht,←Matrix.mulVec_mulVec,d.perpendicular_orthogonal,Matrix.mulVec_zero]

end CommodityClassification.DemandNests.Data
