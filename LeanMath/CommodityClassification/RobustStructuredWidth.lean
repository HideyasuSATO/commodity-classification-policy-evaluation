module

public import LeanMath.CommodityClassification.RobustEconomicWidth

/-! Stability of the structured classification frontier under general known SPD demand perturbations. -/
@[expose] public section
noncomputable section
set_option maxHeartbeats 2200000
namespace CommodityClassification.Precision.Data
open Matrix InputCoordinates Information
variable {n : ℕ} (d : Precision.Data n) {A : Type*}

def perturbedWidth (D : Mat n n) (hD : D.PosDef) (b : Vec n) (O : Vec n→A) : ℝ :=
  (d.family.withDemandPolicy D hD b).observationWidth {c | d.Admissible c} O d.coordinates

theorem family_benchmarkEnergy : d.family.benchmarkEnergy=d.nu := d.policy_energy

theorem family_observationWidth (O : Vec n→A) :
    d.family.observationWidth {c | d.Admissible c} O d.coordinates=d.observationExAnteWidth O := by
  unfold Equilibrium.BenchmarkFamily.observationWidth
  rw [d.family_benchmarkEnergy]
  rw [worstWidth_congr _ O _ d.normalizedWelfare (fun c hc => d.normalized_coefficient c hc.2)]
  exact d.general_observation_width O

theorem perturbed_width_bounds (D : Mat n n) (b : Vec n) (δ τ : ℝ)
    (hδ : 0≤δ) (hδ1 : δ<1) (hτ : 0≤τ) (hτ1 : τ<1)
    (hlo : (D-(1-δ) • d.demand).PosSemidef) (hhi : ((1+δ) • d.demand-D).PosSemidef)
    (hh : dotProduct (b-d.policy) (d.demand *ᵥ (b-d.policy))≤τ^2*d.nu) (O : Vec n→A) :
    let hD := d.family.perturbation_demand_posDef D δ hδ1 hlo
    max (d.observationExAnteWidth O-2*Robust.errorConstant δ τ) 0/Robust.normalizationUpper δ τ
        ≤d.perturbedWidth D hD b O ∧
      d.perturbedWidth D hD b O≤
        (d.observationExAnteWidth O+2*Robust.errorConstant δ τ)/Robust.normalizationLower δ τ := by
  have he := d.family.observationWidth_perturbation {c | d.Admissible c}
    ⟨0,d.zero_admissible⟩ O d.coordinates (fun c hc => (d.candidate c hc).property)
    D b δ τ hδ hδ1 hτ hτ1 hlo hhi
    (by rw [d.family_benchmarkEnergy]; exact hh)
    (d.family.total_positive_of_goods d.goods_nonempty)
    (by rw [d.family_benchmarkEnergy]; exact d.nu_pos)
  rw [d.family_observationWidth O] at he
  exact he

theorem perturbed_moment_width_bound (D : Mat n n) (b : Vec n) (δ τ : ℝ)
    (hδ : 0≤δ) (hδ1 : δ<1) (hτ : 0≤τ) (hτ1 : τ<1)
    (hlo : (D-(1-δ) • d.demand).PosSemidef) (hhi : ((1+δ) • d.demand-D).PosSemidef)
    (hh : dotProduct (b-d.policy) (d.demand *ᵥ (b-d.policy))≤τ^2*d.nu) :
    let hD := d.family.perturbation_demand_posDef D δ hδ1 hlo
    d.perturbedWidth D hD b d.momentReport≤
      2*Robust.errorConstant δ τ/Robust.normalizationLower δ τ := by
  have he := (d.perturbed_width_bounds D b δ τ hδ hδ1 hτ hτ1 hlo hhi hh d.momentReport).2
  simpa only [d.momentReport_exAnte_zero,zero_add] using he

theorem perturbed_partition_width_lower {m : ℕ} (P : Partition n m)
    (D : Mat n n) (b : Vec n) (δ τ : ℝ)
    (hδ : 0≤δ) (hδ1 : δ<1) (hτ : 0≤τ) (hτ1 : τ<1)
    (hlo : (D-(1-δ) • d.demand).PosSemidef) (hhi : ((1+δ) • d.demand-D).PosSemidef)
    (hh : dotProduct (b-d.policy) (d.demand *ᵥ (b-d.policy))≤τ^2*d.nu) :
    let hD := d.family.perturbation_demand_posDef D δ hδ1 hlo
    (d.coarseLowerWidth m-2*Robust.errorConstant δ τ)/Robust.normalizationUpper δ τ≤
      d.perturbedWidth D hD b (d.groupTotal P) := by
  have he := (d.perturbed_width_bounds D b δ τ hδ hδ1 hτ hτ1 hlo hhi hh (d.groupTotal P)).1
  rw [d.observation_partition_exAnte P] at he
  apply le_trans _ he
  apply div_le_div_of_nonneg_right _
    (Robust.normalization_factors_positive δ τ hδ hδ1 hτ hτ1).2.le
  exact (sub_le_sub_right (d.all_partition_lower P) _).trans (le_max_left _ _)

theorem perturbed_strict_margin (m : ℕ) (D : Mat n n) (b : Vec n) (δ τ eps : ℝ)
    (hδ : 0≤δ) (hδ1 : δ<1) (hτ : 0≤τ) (hτ1 : τ<1)
    (hlo : (D-(1-δ) • d.demand).PosSemidef) (hhi : ((1+δ) • d.demand-D).PosSemidef)
    (hh : dotProduct (b-d.policy) (d.demand *ᵥ (b-d.policy))≤τ^2*d.nu)
    (hεlo : 2*Robust.errorConstant δ τ/Robust.normalizationLower δ τ≤eps)
    (hεhi : eps<(d.coarseLowerWidth m-2*Robust.errorConstant δ τ)/Robust.normalizationUpper δ τ) :
    let hD := d.family.perturbation_demand_posDef D δ hδ1 hlo
    d.perturbedWidth D hD b d.momentReport≤eps ∧
      ∀P : Partition n m,eps<d.perturbedWidth D hD b (d.groupTotal P) := by
  refine ⟨(d.perturbed_moment_width_bound D b δ τ hδ hδ1 hτ hτ1 hlo hhi hh).trans hεlo,?_⟩
  intro P
  exact hεhi.trans_le (d.perturbed_partition_width_lower P D b δ τ hδ hδ1 hτ hτ1 hlo hhi hh)

end CommodityClassification.Precision.Data
