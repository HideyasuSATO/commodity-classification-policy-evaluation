module
public import LeanMath.CommodityClassification.EquilibriumLocalSmoothness
@[expose] public section
set_option maxHeartbeats 2000000
namespace CommodityClassification.Equilibrium
open Matrix Filter
open scoped BigOperators Topology ContDiff
variable {n k : ℕ}
namespace Model
variable (E : Model n k)

noncomputable def endowment (s0 : ℝ) : Vec (k+1) := E.A.transpose *ᵥ E.q + s0 • E.frame.a0

theorem reduced_base (s0 : ℝ) : E.reduced (E.endowment s0) 0 = 0 := by
  rw [E.reduced_eq_project_excess (E.endowment s0) 0 s0]
  change E.frame.V.transpose *ᵥ E.excess (E.A.transpose *ᵥ E.q + s0 • E.frame.a0) (0,s0) = 0
  rw [E.excess_base s0, Matrix.mulVec_zero]

/-- The actual implicit function of the nonlinear CES clearing residual. -/
noncomputable def localPricePath (h : E.DemandC1) (hK : E.K.PosDef) (s0 : ℝ) : ℝ → Vec k :=
  (E.reduced_contDiffAt h (E.endowment s0)).implicitFunction (by norm_num)
    (E.price_partial_invertible (E.endowment s0) hK)

theorem localPricePath_base (h : E.DemandC1) (hK : E.K.PosDef) (s0 : ℝ) :
    E.localPricePath h hK s0 0 = 0 :=
  ContDiffAt.implicitFunction_apply_self _ _ _

theorem localPricePath_contDiffAt (h : E.DemandC1) (hK : E.K.PosDef) (s0 : ℝ) :
    ContDiffAt ℝ 1 (E.localPricePath h hK s0) 0 :=
  ContDiffAt.contDiffAt_implicitFunction _ _ _

theorem localPricePath_clears (h : E.DemandC1) (hK : E.K.PosDef) (s0 : ℝ) :
    ∀ᶠ t in 𝓝 (0 : ℝ), E.reduced (E.endowment s0) (t,E.localPricePath h hK s0 t) = 0 := by
  have hh := ContDiffAt.eventually_apply_implicitFunction
    (E.reduced_contDiffAt h (E.endowment s0)) (by norm_num : (1 : ℕ∞ω) ≠ 0)
    (E.price_partial_invertible (E.endowment s0) hK)
  simpa only [localPricePath,E.reduced_base,Prod.fst_zero] using hh

theorem localPricePath_unique (h : E.DemandC1) (hK : E.K.PosDef) (s0 : ℝ) :
    ∀ᶠ y in 𝓝 (0 : PolicyPrice k),
      E.reduced (E.endowment s0) y = 0 ↔ E.localPricePath h hK s0 y.1 = y.2 := by
  have hh := ContDiffAt.eventually_apply_eq_iff_implicitFunction
    (E.reduced_contDiffAt h (E.endowment s0)) (by norm_num : (1 : ℕ∞ω) ≠ 0)
    (E.price_partial_invertible (E.endowment s0) hK)
  simpa only [localPricePath,E.reduced_base] using hh

/-- A single neighborhood in the product of tax and relative prices. -/
theorem localPricePath_unique_open (h : E.DemandC1) (hK : E.K.PosDef) (s0 : ℝ) :
    ∃ U : Set (PolicyPrice k), IsOpen U ∧ 0 ∈ U ∧
      ∀ y ∈ U, E.reduced (E.endowment s0) y = 0 ↔ E.localPricePath h hK s0 y.1 = y.2 := by
  obtain ⟨U,hU,hopen,hzero⟩ := mem_nhds_iff.mp (E.localPricePath_unique h hK s0)
  exact ⟨U,hopen,hzero,fun y hy => hU hy⟩
end Model
end CommodityClassification.Equilibrium
