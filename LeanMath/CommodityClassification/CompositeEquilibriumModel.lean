module

public import LeanMath.CommodityClassification.CompositeMomentPreservation

/-! A genuine reduced economy, with local data connected to the original model. -/
@[expose] public section
noncomputable section
set_option maxHeartbeats 1200000
namespace CommodityClassification.Equilibrium.BenchmarkFamily
open Matrix InputCoordinates
variable {n k h g : ℕ} (F : BenchmarkFamily n k h)

def compositeModel (P : Partition n g) (β : Vec g) (C : F.Candidate) : Model g k :=
  Model.ofAffine F.frame (fun _ => 1) (P.sales F.p F.q) (F.compositeCoordinates P C)
    (P.groupDemand F.p F.D) β F.sigma (fun _ => zero_lt_one) F.hw
    (F.compositeCoordinates_positive P C)

def compositeUtility (P : Partition n g) (c : ℝ) : Vec g → ℝ :=
  benchmarkUtility (fun _ => 1) (P.sales F.p F.q) (P.groupDemand F.p F.D) c

theorem compositeModel_inputs (P : Partition n g) (β : Vec g) (C : F.Candidate) :
    (F.compositeModel P β C).A=F.compositeInputs P C :=
  F.compositeCoordinates_reconstruct P C

theorem compositeModel_cost (P : Partition n g) (β : Vec g) (C : F.Candidate)
    (a : Fin g) (w : Vec (k+1)) :
    (F.compositeModel P β C).costs w a=(F.compositeCostData P C a).cost F.sigma w := by
  apply ((F.compositeModel P β C).costData a).cost_eq_of_primitives
    (F.compositeCostData P C a) rfl rfl _ F.sigma w
  exact congrFun (F.compositeModel_inputs P β C) a

theorem compositeModel_genuine_cost (P : Partition n g) (β : Vec g) (C : F.Candidate)
    (a : Fin g) {w : Vec (k+1)} (hw : ∀j,0<w j) :
    (F.compositeModel P β C).costs w a=
      (F.nestProduction P (fun _ => F.sigma) (fun _ => F.hsigma) C a).compositeCost w := by
  rw [F.compositeModel_cost,F.compositeCostData_actual_cost P C a hw]

theorem compositeModel_totalInputs (P : Partition n g) (β : Vec g) (C : F.Candidate) :
    Supply.totalInputs (F.compositeModel P β C).q (F.compositeModel P β C).A=
      Supply.totalInputs F.q (F.model C).A := by
  rw [F.compositeModel_inputs]
  exact F.compositeInputs_total P C

theorem compositeModel_endowment (P : Partition n g) (β : Vec g) (C : F.Candidate) (s0 : ℝ) :
    (F.compositeModel P β C).endowment s0=F.commonEndowment s0 := by
  rw [←F.candidate_endowment C s0]
  have ht := F.compositeModel_totalInputs P β C
  change (F.compositeModel P β C).A.transpose *ᵥ (F.compositeModel P β C).q+s0 • F.frame.a0=
    (F.model C).A.transpose *ᵥ F.q+s0 • F.frame.a0
  congr 1
  ext j
  simpa only [Supply.totalInputs,Matrix.mulVec,Matrix.transpose_apply,dotProduct,mul_comm]
    using congrFun ht j

theorem compositeModel_R (P : Partition n g) (β : Vec g) (C : F.Candidate) :
    (F.compositeModel P β C).R=(F.model C).R := F.composite_R_preserved P C

theorem compositeModel_demandC1 (P : Partition n g) (β : Vec g) (C : F.Candidate) :
    (F.compositeModel P β C).DemandC1 :=
  Model.ofAffine_demandC1 _ _ _ _ _ _ _ _ _ _

theorem compositeModel_benchmark (P : Partition n g) (β : Vec g) (C : F.Candidate)
    (s0 c : ℝ) (hs : 0<s0) :
    (F.compositeModel P β C).BenchmarkEquilibrium (F.compositeUtility P c)
      (F.commonEndowment s0) s0 := by
  rw [←F.compositeModel_endowment P β C s0]
  exact (F.compositeModel P β C).benchmark_equilibrium (F.composite_groupDemand_posDef P)
    F.hsigma (P.sales_pos F.p F.q F.hp F.hq) (fun j => (F.ha0 j).le) hs c

theorem compositeModel_total_positive (P : Partition n g) (β : Vec g) (C : F.Candidate)
    (hn : 0<n) :
    ∀j,0<Supply.totalInputs (F.compositeModel P β C).q (F.compositeModel P β C).A j := by
  rw [F.compositeModel_totalInputs]
  exact F.candidate_total_positive (F.total_positive_of_goods hn) C

variable (P : Partition n g) (B : Mat g g) (β : Vec g)
  (hD : F.D=F.sigma • Supply.xi F.p F.q+P.Q F.q*B*(P.Q F.q).transpose)
  (hb : F.b=P.Q F.p *ᵥ β)

include hD hb in
theorem compositeModel_m (C : F.Candidate) :
    (F.compositeModel P β C).m=(F.model C).m :=
  F.composite_m_preserved P B β hD hb C

include hD in
theorem compositeModel_K (C : F.Candidate) :
    (F.compositeModel P β C).K=(F.model C).K := by
  unfold Model.K
  rw [F.compositeModel_R]
  exact F.composite_K_preserved P B hD C

include hD hb in
theorem compositeModel_lossCoefficient (C : F.Candidate) :
    (F.compositeModel P β C).lossCoefficient=(F.model C).lossCoefficient := by
  unfold Model.lossCoefficient
  rw [F.compositeModel_m P B β hD hb C,F.compositeModel_K P B β hD C]
  congr 1
  exact F.composite_energy_preserved P β hb

include hD hb in
theorem compositeModel_zSolution (C : F.Candidate) :
    (F.compositeModel P β C).zSolution=(F.model C).zSolution := by
  simp only [Model.zSolution,F.compositeModel_m P B β hD hb C,F.compositeModel_K P B β hD C]

include hD hb in
theorem compositeModel_qSolution (C : F.Candidate) :
    (F.compositeModel P β C).qSolution=F.groupQuantityResponse P C := by
  rw [(F.compositeModel P β C).qSolution_formula,F.compositeModel_zSolution P B β hD hb C,
    groupQuantityResponse,(F.model C).qSolution_formula,Matrix.mulVec_neg]
  exact congrArg Neg.neg (F.composite_quantity_response P B β hD hb C (F.model C).zSolution).symm

end CommodityClassification.Equilibrium.BenchmarkFamily
