module

public import LeanMath.CommodityClassification.GroupPolicyForm

/-! The right-hand equivalence in eq:bridge for the actual economic family. -/
@[expose] public section
noncomputable section
namespace CommodityClassification.Equilibrium.BenchmarkFamily
open Matrix InputCoordinates
variable {n k h g r : ℕ} (F : BenchmarkFamily n k h)

def StrongReportRestrictions (N : Mat n r) : Prop :=
  Regularity.adjustedDemand F.p F.q F.D F.sigma*N=0 ∧ N.transpose *ᵥ (F.D *ᵥ F.b)=0

def PolicyDemandForm (P : Partition n g) : Prop :=
  ∃B : Mat g g,∃β : Vec g,B.transpose=B ∧
    F.D=F.sigma • Supply.xi F.p F.q+P.Q F.q*B*(P.Q F.q).transpose ∧ F.b=P.Q F.p *ᵥ β

theorem adjustedDemand_transpose :
    (Regularity.adjustedDemand F.p F.q F.D F.sigma).transpose=
      Regularity.adjustedDemand F.p F.q F.D F.sigma := by
  have hD : F.D.transpose=F.D := F.hD.isHermitian.isSymm
  simp only [Regularity.adjustedDemand,transpose_sub,transpose_smul,Supply.xi,
    diagonal_transpose,hD]

theorem strong_report_restrictions_iff_policy_demand (P : Partition n g)
    (H : HiddenBasis (P.Q F.q) r) : F.StrongReportRestrictions H.N ↔ F.PolicyDemandForm P :=
  P.strong_report_form_iff F.p F.q F.b F.hp F.hq F.D F.sigma F.hsigma H F.adjustedDemand_transpose

end CommodityClassification.Equilibrium.BenchmarkFamily
