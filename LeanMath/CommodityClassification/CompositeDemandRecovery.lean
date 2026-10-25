module

public import LeanMath.CommodityClassification.CompositeInputCalibration

/-! Recover the given local demand with matched nests and the reduced demand matrix. -/
@[expose] public section
noncomputable section
set_option maxHeartbeats 1200000
namespace CommodityClassification.InputCoordinates
open Matrix
variable {n g : ℕ}

def Partition.inverseSales (P : Partition n g) (p q : Vec n) : Mat g g :=
  diagonal (fun a => (P.sales p q a)⁻¹)

theorem Partition.inverseSales_mul_sales (P : Partition n g) (p q : Vec n)
    (hp : ∀i,0<p i) (hq : ∀i,0<q i) :
    P.inverseSales p q*diagonal (P.sales p q)=1 := by
  rw [Partition.inverseSales,diagonal_mul_diagonal]
  convert (diagonal_one : diagonal (fun _ : Fin g => (1:ℝ))=1) using 1
  congr 1
  funext a
  exact inv_mul_cancel₀ (P.sales_pos p q hp hq a).ne'

theorem Partition.sales_mul_inverseSales (P : Partition n g) (p q : Vec n)
    (hp : ∀i,0<p i) (hq : ∀i,0<q i) :
    diagonal (P.sales p q)*P.inverseSales p q=1 := by
  simpa only [Partition.inverseSales,transpose_mul,diagonal_transpose,transpose_one] using
    congrArg transpose (P.inverseSales_mul_sales p q hp hq)

theorem Partition.groupDemand_sandwich (P : Partition n g) (p q : Vec n)
    (hp : ∀i,0<p i) (hq : ∀i,0<q i) (σ : ℝ) (B : Mat g g)
    (D : Mat n n) (hD : D=σ • Supply.xi p q+P.Q q*B*(P.Q q).transpose) :
    P.inverseSales p q*(P.groupDemand p D-σ • diagonal (P.sales p q))*
      P.inverseSales p q=B := by
  rw [hD,P.groupDemand_decomposition p q hp hq,add_sub_cancel_left]
  calc
    _=(P.inverseSales p q*diagonal (P.sales p q))*B*
        (diagonal (P.sales p q)*P.inverseSales p q) := by simp only [Matrix.mul_assoc]
    _=B := by rw [P.inverseSales_mul_sales p q hp hq,P.sales_mul_inverseSales p q hp hq,
      Matrix.one_mul,Matrix.mul_one]

theorem Partition.groupDemand_scaled (P : Partition n g) (p q : Vec n)
    (hp : ∀i,0<p i) (hq : ∀i,0<q i) (σ : ℝ) (B : Mat g g)
    (D : Mat n n) (hD : D=σ • Supply.xi p q+P.Q q*B*(P.Q q).transpose) :
    P.groupDemand p D*P.inverseSales p q=σ • (1 : Mat g g)+diagonal (P.sales p q)*B := by
  rw [hD,P.groupDemand_decomposition p q hp hq,Matrix.add_mul,Matrix.smul_mul,
    P.sales_mul_inverseSales p q hp hq,Matrix.mul_assoc,
    P.sales_mul_inverseSales p q hp hq,Matrix.mul_one]

theorem Partition.valueAggregation_demand_factor (P : Partition n g) (p q : Vec n)
    (hp : ∀i,0<p i) (hq : ∀i,0<q i) (σ : ℝ) (B : Mat g g)
    (D : Mat n n) (hD : D=σ • Supply.xi p q+P.Q q*B*(P.Q q).transpose) :
    P.valueAggregation p*D=P.groupDemand p D*P.inverseSales p q*(P.Q q).transpose := by
  rw [P.groupDemand_scaled p q hp hq σ B D hD]
  rw [hD,Matrix.mul_add,Matrix.mul_smul,P.valueAggregation_xi p q hp]
  rw [←Matrix.mul_assoc,←Matrix.mul_assoc,P.valueAggregation_Q p q hp hq]
  simp only [Matrix.add_mul,Matrix.smul_mul,Matrix.one_mul]

end CommodityClassification.InputCoordinates

namespace CommodityClassification.Equilibrium.BenchmarkFamily
open Matrix InputCoordinates
variable {n k h g : ℕ} (F : BenchmarkFamily n k h)

theorem composite_demand_recovery (P : Partition n g) (B : Mat g g)
    (hD : F.D=F.sigma • Supply.xi F.p F.q+P.Q F.q*B*(P.Q F.q).transpose) :
    F.D=(F.nestData P (fun _ => F.sigma) (fun _ => F.hsigma)).demandMatrix
      (P.groupDemand F.p F.D) := by
  have hs := P.groupDemand_sandwich F.p F.q F.hp F.hq F.sigma B F.D hD
  have hd : diagonal (fun _ : Fin g => F.sigma)*diagonal (P.sales F.p F.q)=
      F.sigma • diagonal (P.sales F.p F.q) := by
    ext a b
    simp only [Matrix.diagonal_mul,Matrix.smul_apply,smul_eq_mul]
  have he : diagonal (fun a => F.sigma*P.sales F.p F.q a)=
      F.sigma • diagonal (P.sales F.p F.q) := by rw [←diagonal_mul_diagonal];exact hd
  change F.D=diagonal (fun _ : Fin n => F.sigma)*Supply.xi F.p F.q+
    P.Q F.q*(P.inverseSales F.p F.q*
      (P.groupDemand F.p F.D-diagonal (fun a => F.sigma*P.sales F.p F.q a))*
        P.inverseSales F.p F.q)*(P.Q F.q).transpose
  rw [he,hs]
  rw [hD]
  congr 1
  ext i j
  simp only [Matrix.diagonal_mul,Matrix.smul_apply,smul_eq_mul]

theorem composite_groupDemand_posDef (P : Partition n g) :
    (P.groupDemand F.p F.D).PosDef :=
  P.groupDemand_posDef F.p F.q F.hp F.hq F.D F.hD

theorem composite_actual_nested_demand_derivative (P : Partition n g) (B : Mat g g)
    (hD : F.D=F.sigma • Supply.xi F.p F.q+P.Q F.q*B*(P.Q F.q).transpose) :
    HasFDerivAt
      ((F.nestData P (fun _ => F.sigma) (fun _ => F.hsigma)).demand
        ((F.nestData P (fun _ => F.sigma) (fun _ => F.hsigma)).quadraticOuter
          (P.groupDemand F.p F.D))) (-matCLM F.D) F.p := by
  have hd := (F.nestData P (fun _ => F.sigma) (fun _ => F.hsigma)).quadratic_nested_derivative
    (P.groupDemand F.p F.D)
  rw [←F.composite_demand_recovery P B hD] at hd
  exact hd

end CommodityClassification.Equilibrium.BenchmarkFamily
