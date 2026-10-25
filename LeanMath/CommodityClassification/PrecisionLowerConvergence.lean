module

public import LeanMath.CommodityClassification.PrecisionFiniteError

/-! Varying finite economies with fixed preference and substitution parameters. -/
@[expose] public section
noncomputable section
set_option maxHeartbeats 1400000
namespace CommodityClassification.Precision.Data
open Matrix InputCoordinates Filter
open scoped Topology
variable {n : ℕ} (d : Precision.Data n)

theorem precisionFloor_parameters_eq {n' : ℕ} (e : Precision.Data n')
    (hη : d.eta=e.eta) (hα : d.alpha=e.alpha) (hβ : d.beta=e.beta) (hσ : d.sigma=e.sigma) :
    d.precisionFloor=e.precisionFloor := by
  simp only [precisionFloor,policyShare,nu,totalElasticity,minElasticity,maxElasticity]
  rw [hη,hα,hβ,hσ]

theorem coarseErrorConstant_parameters_eq {n' : ℕ} (e : Precision.Data n')
    (hη : d.eta=e.eta) (hα : d.alpha=e.alpha) (hβ : d.beta=e.beta) (hσ : d.sigma=e.sigma) :
    d.coarseErrorConstant=e.coarseErrorConstant := by
  simp only [coarseErrorConstant,lossScale,criticalExposure,policyShare,nu,
    totalElasticity,minElasticity,maxElasticity]
  rw [hη,hα,hβ,hσ]

theorem lowerWidth_tendsto_constants {N : ℕ → ℕ} (E : ∀j,Precision.Data (N j)) (m : ℕ → ℕ)
    (G C : ℝ) (hG : ∀j,(E j).precisionFloor=G) (hC : ∀j,(E j).coarseErrorConstant=C)
    (hm : Tendsto (fun j => (E j).coarseSales (m j)) atTop (𝓝 0)) :
    Tendsto (fun j => (E j).coarseLowerWidth (m j)) atTop (𝓝 G) := by
  have h0 : ∀j,0≤G-(E j).coarseLowerWidth (m j) := by
    intro j
    simpa only [hG j] using ((E j).precisionFloor_error_bound (m j)).1
  have hle : ∀j,G-(E j).coarseLowerWidth (m j)≤C*(E j).coarseSales (m j) := by
    intro j
    simpa only [hG j,hC j] using ((E j).precisionFloor_error_bound (m j)).2
  have hlim : Tendsto (fun j => C*(E j).coarseSales (m j)) atTop (𝓝 0) := by
    simpa only [mul_zero] using tendsto_const_nhds.mul hm
  have hg := squeeze_zero h0 hle hlim
  have hout : Tendsto (fun j => G-(G-(E j).coarseLowerWidth (m j))) atTop (𝓝 (G-0)) :=
    tendsto_const_nhds.sub hg
  simpa only [sub_sub_cancel,sub_zero] using hout

theorem lowerWidth_tendsto {N : ℕ → ℕ} (E : ∀j,Precision.Data (N j)) (m : ℕ → ℕ)
    (hη : ∀j,(E j).eta=d.eta) (hα : ∀j,(E j).alpha=d.alpha)
    (hβ : ∀j,(E j).beta=d.beta) (hσ : ∀j,(E j).sigma=d.sigma)
    (hm : Tendsto (fun j => (E j).coarseSales (m j)) atTop (𝓝 0)) :
    Tendsto (fun j => (E j).coarseLowerWidth (m j)) atTop (𝓝 d.precisionFloor) :=
  lowerWidth_tendsto_constants E m d.precisionFloor d.coarseErrorConstant
    (fun j => (E j).precisionFloor_parameters_eq d (hη j) (hα j) (hβ j) (hσ j))
    (fun j => (E j).coarseErrorConstant_parameters_eq d (hη j) (hα j) (hβ j) (hσ j)) hm

theorem eventually_all_partitions_fail {N : ℕ → ℕ} (E : ∀j,Precision.Data (N j)) (m : ℕ → ℕ)
    (hη : ∀j,(E j).eta=d.eta) (hα : ∀j,(E j).alpha=d.alpha)
    (hβ : ∀j,(E j).beta=d.beta) (hσ : ∀j,(E j).sigma=d.sigma)
    (hm : Tendsto (fun j => (E j).coarseSales (m j)) atTop (𝓝 0))
    (eps : ℝ) (hε : eps<d.precisionFloor) :
    ∀ᶠj in atTop,∀P : Partition (N j) (m j),¬(E j).exAnteWidth P≤eps := by
  have hg := (d.lowerWidth_tendsto E m hη hα hβ hσ hm).eventually (eventually_gt_nhds hε)
  filter_upwards [hg] with j hj
  intro P
  exact (E j).all_partition_failure P eps hj

theorem eventually_positive_witnesses {N : ℕ → ℕ} (E : ∀j,Precision.Data (N j)) (m : ℕ → ℕ)
    (hη : ∀j,(E j).eta=d.eta) (hα : ∀j,(E j).alpha=d.alpha)
    (hβ : ∀j,(E j).beta=d.beta) (hσ : ∀j,(E j).sigma=d.sigma)
    (hm : Tendsto (fun j => (E j).coarseSales (m j)) atTop (𝓝 0))
    (eps : ℝ) (hε : eps<d.precisionFloor) :
    ∀ᶠj in atTop,∀P : Partition (N j) (m j),∃e,(E j).Admissible e ∧
      (E j).groupTotal P e=(E j).groupTotal P (E j).criticalInputs ∧
      (E j).theta e=(E j).theta (E j).criticalInputs ∧
      eps < |(E j).normalizedWelfare (E j).criticalInputs-(E j).normalizedWelfare e| := by
  have hg := (d.lowerWidth_tendsto E m hη hα hβ hσ hm).eventually (eventually_gt_nhds hε)
  filter_upwards [hg] with j hj
  intro P
  exact (E j).all_partition_positive_witness P eps hj

end CommodityClassification.Precision.Data
