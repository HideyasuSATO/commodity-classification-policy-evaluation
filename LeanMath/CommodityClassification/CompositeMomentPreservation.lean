module

public import LeanMath.CommodityClassification.CompositeDemandRecovery

/-! Exact preservation of the local policy moments by the reduced coordinates. -/
@[expose] public section
noncomputable section
set_option maxHeartbeats 1200000
namespace CommodityClassification.Equilibrium.BenchmarkFamily
open Matrix InputCoordinates
variable {n k h g : ℕ} (F : BenchmarkFamily n k h)
variable (P : Partition n g) (B : Mat g g) (β : Vec g)
  (hD : F.D=F.sigma • Supply.xi F.p F.q+P.Q F.q*B*(P.Q F.q).transpose)
  (hb : F.b=P.Q F.p *ᵥ β)

include hb in
theorem composite_energy_preserved :
    dotProduct β (P.groupDemand F.p F.D *ᵥ β)=dotProduct F.b (F.D *ᵥ F.b) := by
  rw [hb]
  change dotProduct β (((P.Q F.p).transpose*F.D*(P.Q F.p)) *ᵥ β)=_
  rw [←Matrix.mulVec_mulVec,←Matrix.mulVec_mulVec,Matrix.dotProduct_mulVec,Matrix.vecMul_transpose]

include hD hb in
theorem composite_m_preserved (C : F.Candidate) :
    (F.compositeCoordinates P C).transpose *ᵥ (P.groupDemand F.p F.D *ᵥ β)=(F.model C).m := by
  rw [F.nested_candidate_m P (fun _ => F.sigma) (fun _ => F.hsigma)
    (P.groupDemand F.p F.D) β (F.composite_demand_recovery P B hD) hb C]
  simp only [compositeCoordinates,Partition.normalizedReport,nestReportedLoad,
    Matrix.transpose_mul,Matrix.diagonal_transpose,←Matrix.mulVec_mulVec]

include hD in
theorem composite_K_preserved (C : F.Candidate) :
    Regularity.K (fun _ => 1) (P.sales F.p F.q) (P.groupDemand F.p F.D)
      (F.model C).R F.sigma (F.compositeCoordinates P C)=(F.model C).K := by
  have hh := (F.nestData P (fun _ => F.sigma) (fun _ => F.hsigma)).nest_K_decomposition
    (P.groupDemand F.p F.D) (F.model C).R F.sigma C.val
  rw [←F.composite_demand_recovery P B hD] at hh
  rw [(F.nestData P (fun _ => F.sigma) (fun _ => F.hsigma)).covarianceCorrection_matching
    C.val F.sigma (fun _ => rfl),add_zero] at hh
  change _=Regularity.K F.p F.q F.D (F.model C).R F.sigma C.val
  apply Eq.trans _ hh.symm
  have hx : Supply.xi (fun _ : Fin g => (1:ℝ)) (P.sales F.p F.q)=
      diagonal (P.sales F.p F.q) := by simp only [Supply.xi,div_one]
  simp only [Regularity.K,Regularity.adjustedDemand,hx,compositeCoordinates,
    Partition.normalizedReport,Matrix.transpose_mul,Matrix.diagonal_transpose,
    DemandNests.Data.meanAdjustment,Matrix.mul_assoc]
  rfl

include hD in
theorem composite_demand_coordinates (C : F.Candidate) :
    P.valueAggregation F.p*F.D*C.val=
      P.groupDemand F.p F.D*F.compositeCoordinates P C := by
  rw [P.valueAggregation_demand_factor F.p F.q F.hp F.hq F.sigma B F.D hD]
  simp only [compositeCoordinates,Partition.normalizedReport,Partition.inverseSales,
    Partition.report,Matrix.mul_assoc]

include hD hb in
theorem composite_quantity_response (C : F.Candidate) (z : Vec k) :
    P.valueAggregation F.p *ᵥ (F.D *ᵥ (F.b+C.val *ᵥ z))=
      P.groupDemand F.p F.D *ᵥ (β+F.compositeCoordinates P C *ᵥ z) := by
  have ht : P.valueAggregation F.p *ᵥ (F.D *ᵥ F.b)=P.groupDemand F.p F.D *ᵥ β := by
    rw [hb]
    simp only [Partition.groupDemand,Partition.valueAggregation,transpose_transpose,
      Matrix.mulVec_mulVec,Matrix.mul_assoc]
  rw [Matrix.mulVec_add,Matrix.mulVec_add,ht,Matrix.mulVec_add]
  congr 1
  simp only [Matrix.mulVec_mulVec,←Matrix.mul_assoc]
  rw [F.composite_demand_coordinates P B hD C]

end CommodityClassification.Equilibrium.BenchmarkFamily
