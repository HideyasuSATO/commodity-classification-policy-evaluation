module
public import LeanMath.CommodityClassification.EquilibriumImplicitPath
@[expose] public section
set_option maxHeartbeats 2000000
namespace CommodityClassification.Equilibrium
open Matrix Filter
open scoped BigOperators Topology
variable {n k : ℕ}
namespace Model
variable (E : Model n k)

noncomputable def recoveredNumeraire (abar : Vec (k+1)) (y : PolicyPrice k) : ℝ :=
  dotProduct E.frame.w (abar - E.factorDemand y)

theorem recoveredNumeraire_base (s0 : ℝ) : E.recoveredNumeraire (E.endowment s0) 0 = s0 := by
  simp only [recoveredNumeraire, endowment, E.factorDemand_zero, add_sub_cancel_left,
    dotProduct_smul, smul_eq_mul]
  rw [dotProduct_comm E.frame.w E.frame.a0,E.frame.normalized,mul_one]

theorem recoveredNumeraire_clears (abar : Vec (k+1)) (y : PolicyPrice k)
    (hy : E.reduced abar y = 0) : E.excess abar (y,E.recoveredNumeraire abar y) = 0 := by
  have hv : E.frame.V.transpose *ᵥ (E.factorDemand y - abar) = 0 := hy
  have hh := numeraire_adjustment E.frame (E.factorDemand y - abar) hv
  have hs : E.recoveredNumeraire abar y = -dotProduct E.frame.w (E.factorDemand y - abar) := by
    simp only [recoveredNumeraire, dotProduct_sub]
    ring
  rw [hs]
  change E.factorDemand y + (-dotProduct E.frame.w (E.factorDemand y - abar)) • E.frame.a0 - abar = 0
  convert hh using 1; abel

theorem recoveredNumeraire_unique (abar : Vec (k+1)) (y : PolicyPrice k) (s : ℝ)
    (hs : E.excess abar (y,s) = 0) : s = E.recoveredNumeraire abar y := by
  have hv : (E.factorDemand y - abar) + s • E.frame.a0 = 0 := by
    change E.factorDemand y + s • E.frame.a0 - abar = 0 at hs
    convert hs using 1; abel
  have hh := numeraire_adjustment_unique E.frame (E.factorDemand y - abar) s hv
  rw [hh]
  simp only [recoveredNumeraire, dotProduct_sub]
  ring

theorem full_clearing_iff (abar : Vec (k+1)) (y : PolicyPrice k) (s : ℝ) :
    E.excess abar (y,s) = 0 ↔ E.reduced abar y = 0 ∧ s = E.recoveredNumeraire abar y := by
  constructor
  · intro h
    exact ⟨by rw [E.reduced_eq_project_excess abar y s,h,Matrix.mulVec_zero],
      E.recoveredNumeraire_unique abar y s h⟩
  · rintro ⟨hr,rfl⟩
    exact E.recoveredNumeraire_clears abar y hr

theorem recoveredNumeraire_contDiffAt (h : E.DemandC1) (abar : Vec (k+1)) :
    ContDiffAt ℝ 1 (E.recoveredNumeraire abar) 0 := by
  change ContDiffAt ℝ 1 (fun y => dotProduct E.frame.w (abar-E.factorDemand y)) 0
  simpa only [Function.comp_def,CESCost.weightedLinear_apply] using
    (CESCost.weightedLinear E.frame.w).contDiff.contDiffAt.comp 0
      ((contDiffAt_const (c := abar)).sub (E.factorDemand_contDiffAt h))

noncomputable def localNumerairePath (h : E.DemandC1) (hK : E.K.PosDef) (s0 : ℝ) : ℝ → ℝ :=
  fun t => E.recoveredNumeraire (E.endowment s0) (t,E.localPricePath h hK s0 t)

theorem localNumerairePath_base (h : E.DemandC1) (hK : E.K.PosDef) (s0 : ℝ) :
    E.localNumerairePath h hK s0 0 = s0 := by
  simp only [localNumerairePath,E.localPricePath_base]
  exact E.recoveredNumeraire_base s0

theorem localNumerairePath_contDiffAt (h : E.DemandC1) (hK : E.K.PosDef) (s0 : ℝ) :
    ContDiffAt ℝ 1 (E.localNumerairePath h hK s0) 0 := by
  have hc : ContDiffAt ℝ 1 (E.recoveredNumeraire (E.endowment s0)) (0,E.localPricePath h hK s0 0) := by
    rw [E.localPricePath_base]
    exact E.recoveredNumeraire_contDiffAt h _
  exact hc.comp 0 (contDiffAt_id.prodMk (E.localPricePath_contDiffAt h hK s0))

theorem local_full_clearing (h : E.DemandC1) (hK : E.K.PosDef) (s0 : ℝ) :
    ∀ᶠ t in 𝓝 (0 : ℝ), E.excess (E.endowment s0)
      ((t,E.localPricePath h hK s0 t),E.localNumerairePath h hK s0 t) = 0 := by
  filter_upwards [E.localPricePath_clears h hK s0] with t ht
  exact E.recoveredNumeraire_clears _ _ ht

theorem local_full_uniqueness (h : E.DemandC1) (hK : E.K.PosDef) (s0 : ℝ) :
    ∀ᶠ y in 𝓝 (0 : PolicyPrice k), ∀ s : ℝ,
      E.excess (E.endowment s0) (y,s) = 0 ↔
      y.2 = E.localPricePath h hK s0 y.1 ∧ s = E.localNumerairePath h hK s0 y.1 := by
  filter_upwards [E.localPricePath_unique h hK s0] with y hy
  intro s
  rw [E.full_clearing_iff,hy]
  constructor
  · rintro ⟨hu,hs⟩
    refine ⟨hu.symm,?_⟩
    rw [hs]
    change E.recoveredNumeraire (E.endowment s0) y = E.recoveredNumeraire (E.endowment s0) (y.1,_)
    rw [hu]
  · rintro ⟨hu,hs⟩
    refine ⟨hu.symm,?_⟩
    rw [hs]
    change E.recoveredNumeraire (E.endowment s0) (y.1,_) = E.recoveredNumeraire (E.endowment s0) y
    rw [←hu]
end Model
end CommodityClassification.Equilibrium
