module
public import LeanMath.CommodityClassification.CandidateRegularity
public import LeanMath.CommodityClassification.SupplyBoundaryExample
@[expose] public section
namespace CommodityClassification.Regularity.BoundaryExample
open Matrix
open scoped Topology
open Supply.Example

theorem ones_positive : ∀ i, 0 < ones i := by
  intro i; fin_cases i <;> norm_num [ones]

theorem frame_prices_positive : ∀ j, 0 < frame.w j := by
  intro j; fin_cases j <;> norm_num [frame]

theorem total_positive : ∀ j, 0 < Supply.totalInputs ones (frame.reconstruct ones (path 1)) j := by
  rw [path_reconstruct, path_total]
  exact ones_positive

/-- Demand Xi suffices even when the residual supply curvature is exactly zero. -/
theorem boundary_K_eq_R (σ : ℝ) :
    K ones ones (Supply.xi ones ones) (Supply.candidateR frame ones ones (path 1)) σ (path 0) =
      Supply.candidateR frame ones ones (path 1) := by
  rw [K_eq_demand_add_substitution, Supply.substitution, boundary_zero, smul_zero, add_zero]
  have hh := boundary_zero
  unfold Supply.residual at hh
  exact (sub_eq_zero.mp hh).symm

theorem boundary_K_value (σ : ℝ) :
    K ones ones (Supply.xi ones ones) (Supply.candidateR frame ones ones (path 1)) σ (path 0) =
      ![![2]] := by rw [boundary_K_eq_R, fixed_R]

theorem boundary_K_posDef (σ : ℝ) (hσ : 0 < σ) :
    (K ones ones (Supply.xi ones ones) (Supply.candidateR frame ones ones (path 1)) σ
      (path 0)).PosDef := by
  have hc := candidate_closure_certificate frame parent ones ones 0 (path 1)
    (Supply.xi ones ones) σ ones_positive ones_positive frame_prices_positive total_positive
    interior_positive.1 (xi_posDef ones ones ones_positive ones_positive) hσ
  exact (hc.2.2 (path 0) boundary_in_actual_closure).2.1

theorem boundary_supply_zero_but_K_regular (σ : ℝ) (hσ : 0 < σ) :
    path 0 ∈ closure (frame.Candidates ones ones parent 0) ∧
    Supply.residual (Supply.candidateR frame ones ones (path 1)) ones ones (path 0) = 0 ∧
    (K ones ones (Supply.xi ones ones) (Supply.candidateR frame ones ones (path 1)) σ
      (path 0)).PosDef :=
  ⟨boundary_in_actual_closure, boundary_zero, boundary_K_posDef σ hσ⟩

end CommodityClassification.Regularity.BoundaryExample
