module

public import LeanMath.CommodityClassification.SymmetricReportFactorization
public import LeanMath.CommodityClassification.DemandSpectralBound

/-! Curvature of value-weighted group quantities, with actual SPD inheritance. -/
@[expose] public section
noncomputable section
namespace CommodityClassification.InputCoordinates
open Matrix
variable {n g : ℕ}

def Partition.groupDemand (P : Partition n g) (p : Vec n) (D : Mat n n) : Mat g g :=
  P.valueAggregation p*D*(P.valueAggregation p).transpose

theorem Partition.groupDemand_xi (P : Partition n g) (p q : Vec n)
    (hp : ∀i,0<p i) (hq : ∀i,0<q i) :
    P.groupDemand p (Supply.xi p q)=diagonal (P.sales p q) := by
  have ht := congrArg transpose (P.valueAggregation_Q p q hp hq)
  simp only [transpose_mul,diagonal_transpose] at ht
  unfold Partition.groupDemand
  rw [P.valueAggregation_xi p q hp]
  exact ht

theorem Partition.groupDemand_report_quadratic (P : Partition n g) (p q : Vec n)
    (hp : ∀i,0<p i) (hq : ∀i,0<q i) (B : Mat g g) :
    P.groupDemand p (P.Q q*B*(P.Q q).transpose)=
      diagonal (P.sales p q)*B*diagonal (P.sales p q) := by
  have ht := congrArg transpose (P.valueAggregation_Q p q hp hq)
  simp only [transpose_mul,diagonal_transpose] at ht
  unfold Partition.groupDemand
  calc
    _=(P.valueAggregation p*P.Q q)*B*((P.Q q).transpose*(P.valueAggregation p).transpose) := by
      simp only [Matrix.mul_assoc]
    _=_ := by rw [P.valueAggregation_Q p q hp hq,ht]

theorem Partition.groupDemand_decomposition (P : Partition n g) (p q : Vec n)
    (hp : ∀i,0<p i) (hq : ∀i,0<q i) (σ : ℝ) (B : Mat g g) :
    P.groupDemand p (σ • Supply.xi p q+P.Q q*B*(P.Q q).transpose)=
      σ • diagonal (P.sales p q)+diagonal (P.sales p q)*B*diagonal (P.sales p q) := by
  have he : P.groupDemand p (σ • Supply.xi p q+P.Q q*B*(P.Q q).transpose)=
      σ • P.groupDemand p (Supply.xi p q)+P.groupDemand p (P.Q q*B*(P.Q q).transpose) := by
    simp only [Partition.groupDemand,Matrix.mul_add,Matrix.add_mul,Matrix.mul_smul,Matrix.smul_mul]
  rw [he,P.groupDemand_xi p q hp hq,P.groupDemand_report_quadratic p q hp hq]

theorem Partition.groupDemand_posDef (P : Partition n g) (p q : Vec n)
    (hp : ∀i,0<p i) (hq : ∀i,0<q i) (D : Mat n n) (hD : D.PosDef) :
    (P.groupDemand p D).PosDef := by
  have hh := hD.conjTranspose_mul_mul_same (P.valueAggregation_transpose_injective p q hp hq)
  simpa only [Partition.groupDemand,conjTranspose_eq_transpose_of_trivial,transpose_transpose] using hh

end CommodityClassification.InputCoordinates
