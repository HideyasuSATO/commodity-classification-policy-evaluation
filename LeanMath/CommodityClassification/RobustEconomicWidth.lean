module

public import LeanMath.CommodityClassification.ObservationWidthCongruence

/-! Perturbed widths of actual general-equilibrium welfare coefficients on unchanged inputs. -/
@[expose] public section
noncomputable section
set_option maxHeartbeats 2200000
namespace CommodityClassification.Equilibrium.BenchmarkFamily
open Matrix Information
variable {n k g : ℕ} (F : Equilibrium.BenchmarkFamily n k g) {A B : Type*}

def observationWidth (S : Set A) (O : A→B) (C : A→Equilibrium.Mat n k) : ℝ :=
  worstWidth S O (fun x => F.coefficient (C x)/F.benchmarkEnergy)

theorem candidate_coefficient_bounds
    (hI : ∀j,0<Supply.totalInputs F.q (F.frame.reconstruct F.p F.reference) j)
    (C : F.Candidate) : 0≤F.coefficient C.val ∧ F.coefficient C.val≤F.benchmarkEnergy := by
  have hV := (F.model C).economic_variational_certificate F.parents F.report C.property.2
    F.hq (F.candidate_total_positive hI C) F.hD F.hsigma
  have hl := hV.2.2.1
  have hu := hV.2.2.2.1
  rw [F.candidate_lossCoefficient C] at hl hu
  exact ⟨hl,hu⟩

theorem coefficient_bounded (S : Set A) (C : A→Equilibrium.Mat n k)
    (hc : ∀x∈S,C x∈F.frame.Candidates F.p F.q F.parents F.report)
    (hI : ∀j,0<Supply.totalInputs F.q (F.frame.reconstruct F.p F.reference) j) :
    BoundedValues S (fun x => F.coefficient (C x)) := by
  constructor
  · refine ⟨F.benchmarkEnergy,?_⟩
    rintro y ⟨x,hx,rfl⟩
    exact (F.candidate_coefficient_bounds hI ⟨C x,hc x hx⟩).2
  · refine ⟨0,?_⟩
    rintro y ⟨x,hx,rfl⟩
    exact (F.candidate_coefficient_bounds hI ⟨C x,hc x hx⟩).1

theorem observationWidth_perturbation (S : Set A) (hne : S.Nonempty)
    (O : A→B) (C : A→Equilibrium.Mat n k)
    (hc : ∀x∈S,C x∈F.frame.Candidates F.p F.q F.parents F.report)
    (D : Equilibrium.Mat n n) (b : Equilibrium.Vec n) (δ τ : ℝ)
    (hδ : 0≤δ) (hδ1 : δ<1) (hτ : 0≤τ) (hτ1 : τ<1)
    (hlo : (D-(1-δ) • F.D).PosSemidef) (hhi : ((1+δ) • F.D-D).PosSemidef)
    (hh : dotProduct (b-F.b) (F.D *ᵥ (b-F.b))≤τ^2*F.benchmarkEnergy)
    (hI : ∀j,0<Supply.totalInputs F.q (F.frame.reconstruct F.p F.reference) j)
    (hν : 0<F.benchmarkEnergy) :
    let G := F.withDemandPolicy D (F.perturbation_demand_posDef D δ hδ1 hlo) b
    max (F.observationWidth S O C-2*Robust.errorConstant δ τ) 0/Robust.normalizationUpper δ τ
        ≤G.observationWidth S O C ∧
      G.observationWidth S O C≤
        (F.observationWidth S O C+2*Robust.errorConstant δ τ)/Robust.normalizationLower δ τ := by
  dsimp only
  let G := F.withDemandPolicy D (F.perturbation_demand_posDef D δ hδ1 hlo) b
  have he := F.perturbation_energy_bounds D b δ τ hδ hδ1 hτ hτ1 hlo hhi hh
  have hn := F.perturbation_energy_positive D b δ τ hδ hδ1 hτ hτ1 hlo hhi hh hν
  have ha := Robust.normalization_factors_positive δ τ hδ hδ1 hτ hτ1
  apply self_normalized_width_comparison S hne O
    (fun x => G.coefficient (C x)) (fun x => F.coefficient (C x))
    (F.coefficient_bounded S C hc hI) (Robust.errorConstant δ τ)
    F.benchmarkEnergy G.benchmarkEnergy (Robust.normalizationLower δ τ)
    (Robust.normalizationUpper δ τ) hν hn ha.1 ha.2 he.1 he.2
  intro x hx
  exact F.candidate_perturbation_error D b δ τ hδ hδ1 hτ hlo hhi hh hI ⟨C x,hc x hx⟩

end CommodityClassification.Equilibrium.BenchmarkFamily
