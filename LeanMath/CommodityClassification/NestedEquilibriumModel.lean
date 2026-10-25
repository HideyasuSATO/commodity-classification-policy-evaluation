module

public import LeanMath.CommodityClassification.NestedUtilityCompatibility
public import LeanMath.CommodityClassification.NestedDirectWitness

/-! Actual nested demand in the general GE model, with unchanged local data. -/
@[expose] public section
noncomputable section
set_option maxHeartbeats 1000000
namespace CommodityClassification.Equilibrium.BenchmarkFamily
open Matrix InputCoordinates Filter
open scoped Topology
variable {n k h g : ℕ} (F : BenchmarkFamily n k h)

def nestedModel (G : Partition n g) (η : Vec g) (hη : ∀a,0<η a)
    (DG : Mat g g) (hD : F.D=(F.nestData G η hη).demandMatrix DG) (C : F.Candidate) : Model n k :=
  { F.model C with
    demand := (F.nestData G η hη).demand ((F.nestData G η hη).quadraticOuter DG)
    demand_base := (F.nestData G η hη).quadratic_nested_benchmark DG
    demand_deriv := by
      change HasFDerivAt _ (-matCLM F.D) F.p
      rw [hD]
      exact (F.nestData G η hη).quadratic_nested_derivative DG }

variable (G : Partition n g) (η : Vec g) (hη : ∀a,0<η a)
  (DG : Mat g g) (hD : F.D=(F.nestData G η hη).demandMatrix DG) (C : F.Candidate)

theorem nestedModel_production_data :
    (F.nestedModel G η hη DG hD C).A=(F.model C).A ∧
    (F.nestedModel G η hη DG hD C).costs=(F.model C).costs ∧
    (F.nestedModel G η hη DG hD C).currentInputs=(F.model C).currentInputs := ⟨rfl,rfl,rfl⟩

theorem nestedModel_local_data :
    (F.nestedModel G η hη DG hD C).R=(F.model C).R ∧
    (F.nestedModel G η hη DG hD C).K=(F.model C).K ∧
    (F.nestedModel G η hη DG hD C).m=(F.model C).m := ⟨rfl,rfl,rfl⟩

theorem nestedModel_lossCoefficient :
    (F.nestedModel G η hη DG hD C).lossCoefficient=F.coefficient C.val :=
  F.candidate_lossCoefficient C

theorem nestedModel_common_endowment (s0 : ℝ) :
    (F.nestedModel G η hη DG hD C).endowment s0=F.commonEndowment s0 :=
  F.candidate_endowment C s0

theorem nestedModel_demandC1 : (F.nestedModel G η hη DG hD C).DemandC1 :=
  ((F.nestData G η hη).quadratic_nested_smooth DG F.hp).of_le (by simp)

theorem nestedModel_utility_compatible (hDG : DG.PosDef) (c : ℝ) :
    (F.nestedModel G η hη DG hD C).UtilityCompatible ((F.nestData G η hη).nestedUtility DG c) :=
  (F.nestData G η hη).quadratic_nested_utility_compatible DG hDG c

theorem nestedModel_K_posDef (hn : 0<n) : (F.nestedModel G η hη DG hD C).K.PosDef :=
  F.candidate_model_K_posDef hn C

end CommodityClassification.Equilibrium.BenchmarkFamily
