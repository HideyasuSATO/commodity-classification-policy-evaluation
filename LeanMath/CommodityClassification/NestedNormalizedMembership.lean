module

public import LeanMath.CommodityClassification.NestedDemandPositivity

/-! The manuscript's actual square-root normalized membership matrix. -/
@[expose] public section
noncomputable section
set_option maxHeartbeats 600000
namespace CommodityClassification.DemandNests.Data
open Matrix InputCoordinates
open scoped BigOperators
variable {n g : ℕ} (d : DemandNests.Data n g)

def nestRoot : Matrix (Fin g) (Fin g) ℝ :=
  Regularity.rootXi (fun _ => 1) (d.partition.sales d.p d.q)

def nestInvRoot : Matrix (Fin g) (Fin g) ℝ :=
  Regularity.invRootXi (fun _ => 1) (d.partition.sales d.p d.q)

def normalizedMembership : Matrix (Fin n) (Fin g) ℝ :=
  Regularity.invRootXi d.p d.q*d.partition.Q d.q*d.nestInvRoot

theorem nestRoot_square : d.nestRoot*d.nestRoot=diagonal (d.partition.sales d.p d.q) := by
  simpa only [nestRoot,Supply.xi,div_one] using Regularity.rootXi_sq
    (fun _ : Fin g => 1) (d.partition.sales d.p d.q) (fun _ => zero_lt_one)
      (d.partition.sales_pos d.p d.q d.hp d.hq)

theorem nestRoot_invRoot : d.nestRoot*d.nestInvRoot=1 :=
  Regularity.rootXi_invRootXi (fun _ => 1) _ (fun _ => zero_lt_one)
    (d.partition.sales_pos d.p d.q d.hp d.hq)

theorem nestInvRoot_root : d.nestInvRoot*d.nestRoot=1 :=
  Regularity.invRootXi_rootXi (fun _ => 1) _ (fun _ => zero_lt_one)
    (d.partition.sales_pos d.p d.q d.hp d.hq)

theorem nestInvRoot_sales_invRoot :
    d.nestInvRoot*diagonal (d.partition.sales d.p d.q)*d.nestInvRoot=1 := by
  simpa only [nestInvRoot,Supply.xi,div_one] using Regularity.invRootXi_xi_invRootXi
    (fun _ : Fin g => 1) (d.partition.sales d.p d.q) (fun _ => zero_lt_one)
      (d.partition.sales_pos d.p d.q d.hp d.hq)

theorem product_invRoot_square :
    Regularity.invRootXi d.p d.q*Regularity.invRootXi d.p d.q=(Supply.xi d.p d.q)⁻¹ := by
  have hh : Supply.xi d.p d.q*(Regularity.invRootXi d.p d.q*Regularity.invRootXi d.p d.q)=1 := by
    rw [←Regularity.rootXi_sq d.p d.q d.hp d.hq]
    calc
      _=Regularity.rootXi d.p d.q*(Regularity.rootXi d.p d.q*Regularity.invRootXi d.p d.q)*
        Regularity.invRootXi d.p d.q := by simp only [Matrix.mul_assoc]
      _=1 := by rw [Regularity.rootXi_invRootXi d.p d.q d.hp d.hq,Matrix.mul_one,
        Regularity.rootXi_invRootXi d.p d.q d.hp d.hq]
  exact (Matrix.inv_eq_right_inv hh).symm

theorem report_inverseXi_gram :
    (d.partition.Q d.q).transpose*(Supply.xi d.p d.q)⁻¹*d.partition.Q d.q=
      diagonal (d.partition.sales d.p d.q) := by
  rw [Matrix.mul_assoc,d.partition.weighted_eq_lift_sales d.p d.q d.hp d.hq,←Matrix.mul_assoc]
  change d.partition.report d.q (d.partition.liftReport d.p d.q)*diagonal (d.partition.sales d.p d.q)=_
  rw [d.partition.report_lift d.p d.q d.hp d.hq,Matrix.one_mul]

theorem normalizedMembership_gram : d.normalizedMembership.transpose*d.normalizedMembership=1 := by
  have ht : d.nestInvRoot.transpose=d.nestInvRoot := by simp only [nestInvRoot,Regularity.invRootXi,diagonal_transpose]
  have hx : (Regularity.invRootXi d.p d.q).transpose=Regularity.invRootXi d.p d.q := by
    simp only [Regularity.invRootXi,diagonal_transpose]
  simp only [normalizedMembership,transpose_mul,ht,hx]
  calc
    _=d.nestInvRoot*((d.partition.Q d.q).transpose*
      (Regularity.invRootXi d.p d.q*Regularity.invRootXi d.p d.q)*d.partition.Q d.q)*
        d.nestInvRoot := by simp only [Matrix.mul_assoc]
    _=1 := by rw [d.product_invRoot_square,d.report_inverseXi_gram,d.nestInvRoot_sales_invRoot]

theorem rootXi_normalizedMembership :
    Regularity.rootXi d.p d.q*d.normalizedMembership=d.partition.Q d.q*d.nestInvRoot := by
  simp only [normalizedMembership,←Matrix.mul_assoc]
  rw [Regularity.rootXi_invRootXi d.p d.q d.hp d.hq,Matrix.one_mul]

end CommodityClassification.DemandNests.Data
