module

public import LeanMath.CommodityClassification.NormalizedGroupInputs

/-! Actual unit inputs and optimized costs of the locally reduced economy. -/
@[expose] public section
noncomputable section
set_option maxHeartbeats 1200000
namespace CommodityClassification.Equilibrium.BenchmarkFamily
open Matrix InputCoordinates
open scoped BigOperators
variable {n k h g : ℕ} (F : BenchmarkFamily n k h)

def compositeInputs (P : Partition n g) (C : F.Candidate) : Mat g (k+1) :=
  P.normalizedReport F.p F.q (F.model C).A

def compositeCoordinates (P : Partition n g) (C : F.Candidate) : Mat g k :=
  P.normalizedReport F.p F.q C.val

theorem compositeInputs_positive (P : Partition n g) (C : F.Candidate) :
    Positive (F.compositeInputs P C) :=
  P.normalizedReport_positive F.p F.q F.hp F.hq _ C.property.1

theorem compositeInputs_cost (P : Partition n g) (C : F.Candidate) :
    F.compositeInputs P C *ᵥ F.frame.w=(fun _ => 1) :=
  P.normalizedReport_cost F.frame F.p F.q F.hp F.hq _
    (F.frame.reconstruct_cost F.p C.val)

theorem compositeInputs_exposure (P : Partition n g) (C : F.Candidate) :
    F.compositeInputs P C*F.frame.V=F.compositeCoordinates P C := by
  change P.normalizedReport F.p F.q (F.frame.reconstruct F.p C.val)*F.frame.V=_
  rw [P.normalizedReport_mul,F.frame.reconstruct_exposure]
  rfl

theorem compositeCoordinates_reconstruct (P : Partition n g) (C : F.Candidate) :
    F.frame.reconstruct (fun _ => 1) (F.compositeCoordinates P C)=F.compositeInputs P C :=
  P.normalizedReport_reconstruct F.frame F.p F.q F.hp F.hq C.val

theorem compositeCoordinates_positive (P : Partition n g) (C : F.Candidate) :
    F.compositeCoordinates P C ∈ F.frame.PositiveDomain (fun _ => 1) := by
  change Positive (F.frame.reconstruct _ _)
  rw [F.compositeCoordinates_reconstruct]
  exact F.compositeInputs_positive P C

theorem compositeInputs_total (P : Partition n g) (C : F.Candidate) :
    Supply.totalInputs (P.sales F.p F.q) (F.compositeInputs P C)=
      Supply.totalInputs F.q (F.model C).A :=
  P.normalizedReport_totalInputs F.p F.q F.hp F.hq _

theorem composite_R_preserved (P : Partition n g) (C : F.Candidate) :
    Supply.candidateR F.frame (fun _ => 1) (P.sales F.p F.q)
      (F.compositeCoordinates P C)=(F.model C).R := by
  unfold Supply.candidateR
  rw [F.compositeCoordinates_reconstruct,F.compositeInputs_total]
  rfl

def compositeCostData (P : Partition n g) (C : F.Candidate) (a : Fin g) : CESCost.Data (k+1) :=
  CESCost.ofInputs (F.compositeInputs P C) (fun _ => 1) F.frame.w
    (F.compositeInputs_positive P C) (fun _ => zero_lt_one) F.hw
    (F.compositeInputs_cost P C) a

theorem compositeCostData_meanInputs (P : Partition n g) (C : F.Candidate) (a : Fin g) :
    (F.compositeCostData P C a).a=
      (F.nestProduction P (fun _ => F.sigma) (fun _ => F.hsigma) C a).meanInputs := by
  rw [F.nestProduction_meanInputs]
  ext j
  exact P.normalizedReport_apply F.p F.q (F.model C).A a j

theorem compositeCostData_actual_cost (P : Partition n g) (C : F.Candidate) (a : Fin g)
    {w : Vec (k+1)} (hw : ∀j,0<w j) :
    (F.compositeCostData P C a).cost F.sigma w=
      (F.nestProduction P (fun _ => F.sigma) (fun _ => F.hsigma) C a).compositeCost w := by
  rw [F.nested_matched_composite_cost P (fun _ => F.sigma) (fun _ => F.hsigma) C a rfl hw]
  exact (F.compositeCostData P C a).cost_eq_of_primitives
    (F.nestProduction P (fun _ => F.sigma) (fun _ => F.hsigma) C a).meanCostData rfl rfl
    (F.compositeCostData_meanInputs P C a) F.sigma w

theorem compositeCostData_actual_minimum (P : Partition n g) (C : F.Candidate) (a : Fin g)
    {w : Vec (k+1)} (hw : ∀j,0<w j) :
    IsLeast {v : ℝ | ∃x : Vec ((F.nestData P (fun _ => F.sigma) (fun _ => F.hsigma)).size a),
      (∀i,0≤x i) ∧
      1≤((F.nestData P (fun _ => F.sigma) (fun _ => F.hsigma)).nest a).quantityOnNonnegative x ∧
      v=dotProduct ((F.nestData P (fun _ => F.sigma) (fun _ => F.hsigma)).restrict a
        ((F.model C).costs w)) x}
      ((F.compositeCostData P C a).cost F.sigma w) := by
  rw [F.compositeCostData_actual_cost P C a hw]
  exact F.nestProduction_actual_minimum P (fun _ => F.sigma) (fun _ => F.hsigma) C a hw

end CommodityClassification.Equilibrium.BenchmarkFamily
