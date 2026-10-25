module

public import LeanMath.CommodityClassification.RobustNormalization

/-! Supply regularity supplies the perturbation theorem uniformly on the fixed candidate family. -/
@[expose] public section
noncomputable section
set_option maxHeartbeats 2200000
namespace CommodityClassification.Equilibrium.BenchmarkFamily
open Matrix
variable {n k g : ℕ} (F : Equilibrium.BenchmarkFamily n k g)

def withDemandPolicy (D : Equilibrium.Mat n n) (hD : D.PosDef) (b : Equilibrium.Vec n) :
    Equilibrium.BenchmarkFamily n k g := {F with D:=D,hD:=hD,b:=b}

def benchmarkEnergy : ℝ := dotProduct F.b (F.D *ᵥ F.b)

theorem withDemandPolicy_candidates (D : Equilibrium.Mat n n) (hD : D.PosDef) (b : Equilibrium.Vec n) :
    (F.withDemandPolicy D hD b).Candidate=F.Candidate := rfl

theorem withDemandPolicy_endowment (D : Equilibrium.Mat n n) (hD : D.PosDef)
    (b : Equilibrium.Vec n) (s0 : ℝ) :
    (F.withDemandPolicy D hD b).commonEndowment s0=F.commonEndowment s0 := rfl

theorem withDemandPolicy_substitution (D : Equilibrium.Mat n n) (hD : D.PosDef)
    (b : Equilibrium.Vec n) (C : F.Candidate) :
    ((F.withDemandPolicy D hD b).model C).substitutionMatrix=(F.model C).substitutionMatrix := rfl

theorem perturbation_demand_posDef (D : Equilibrium.Mat n n) (δ : ℝ) (hδ1 : δ<1)
    (hlo : (D-(1-δ) • F.D).PosSemidef) : D.PosDef :=
  Regularity.posDef_of_positive_lower_bound D F.D (1-δ) hlo F.hD (sub_pos.mpr hδ1)

theorem candidate_perturbation_error (D : Equilibrium.Mat n n) (b : Equilibrium.Vec n)
    (δ τ : ℝ) (hδ : 0≤δ) (hδ1 : δ<1) (hτ : 0≤τ)
    (hlo : (D-(1-δ) • F.D).PosSemidef) (hhi : ((1+δ) • F.D-D).PosSemidef)
    (hh : dotProduct (b-F.b) (F.D *ᵥ (b-F.b))≤τ^2*F.benchmarkEnergy)
    (hI : ∀j,0<Supply.totalInputs F.q (F.frame.reconstruct F.p F.reference) j) :
    let hD := F.perturbation_demand_posDef D δ hδ1 hlo
    ∀C : F.Candidate,|(F.withDemandPolicy D hD b).coefficient C.val-F.coefficient C.val|≤
      Robust.errorConstant δ τ*F.benchmarkEnergy := by
  dsimp only
  intro C
  let hD := F.perturbation_demand_posDef D δ hδ1 hlo
  let G := F.withDemandPolicy D hD b
  have hK0 := (F.model C).K_posDef F.parents F.report C.property.2 F.hq
    (F.candidate_total_positive hI C) F.hD F.hsigma
  have hK := (G.model C).K_posDef G.parents G.report C.property.2 G.hq
    (G.candidate_total_positive hI C) G.hD G.hsigma
  have hT0 := (F.model C).substitutionMatrix_posDef F.parents F.report C.property.2 F.hq
    (F.candidate_total_positive hI C) F.hsigma
  have he := Robust.combined_coefficient_error (G.model C) (F.model C) δ τ
    hδ hδ1.le hτ rfl rfl G.hD F.hD hK hK0 hT0.posSemidef hlo hhi hh
  rw [G.candidate_lossCoefficient C,F.candidate_lossCoefficient C] at he
  exact he

theorem perturbation_energy_bounds (D : Equilibrium.Mat n n) (b : Equilibrium.Vec n)
    (δ τ : ℝ) (hδ : 0≤δ) (hδ1 : δ<1) (hτ : 0≤τ) (hτ1 : τ<1)
    (hlo : (D-(1-δ) • F.D).PosSemidef) (hhi : ((1+δ) • F.D-D).PosSemidef)
    (hh : dotProduct (b-F.b) (F.D *ᵥ (b-F.b))≤τ^2*F.benchmarkEnergy) :
    let hD := F.perturbation_demand_posDef D δ hδ1 hlo
    Robust.normalizationLower δ τ*F.benchmarkEnergy≤(F.withDemandPolicy D hD b).benchmarkEnergy ∧
      (F.withDemandPolicy D hD b).benchmarkEnergy≤Robust.normalizationUpper δ τ*F.benchmarkEnergy :=
  Robust.normalization_bounds D F.D F.hD.posSemidef b F.b δ τ hδ hδ1.le hτ hτ1.le hlo hhi hh

theorem perturbation_energy_positive (D : Equilibrium.Mat n n) (b : Equilibrium.Vec n)
    (δ τ : ℝ) (hδ : 0≤δ) (hδ1 : δ<1) (hτ : 0≤τ) (hτ1 : τ<1)
    (hlo : (D-(1-δ) • F.D).PosSemidef) (hhi : ((1+δ) • F.D-D).PosSemidef)
    (hh : dotProduct (b-F.b) (F.D *ᵥ (b-F.b))≤τ^2*F.benchmarkEnergy)
    (hν : 0<F.benchmarkEnergy) :
    let hD := F.perturbation_demand_posDef D δ hδ1 hlo
    0<(F.withDemandPolicy D hD b).benchmarkEnergy := by
  have hn := F.perturbation_energy_bounds D b δ τ hδ hδ1 hτ hτ1 hlo hhi hh
  exact (mul_pos (Robust.normalization_factors_positive δ τ hδ hδ1 hτ hτ1).1 hν).trans_le hn.1

end CommodityClassification.Equilibrium.BenchmarkFamily
