module
public import LeanMath.CommodityClassification.WelfareBudget
public import Mathlib.Analysis.Convex.Function
@[expose] public section
set_option maxHeartbeats 2400000
namespace CommodityClassification.Equilibrium
open Matrix Filter
open scoped BigOperators Topology
variable {n : ℕ}

/-- One explicit continuation of the local quadratic implementation. -/
noncomputable def benchmarkUtility (p q : Vec n) (D : Mat n n) (c : ℝ) (r : Vec n) : ℝ :=
  c + quadraticUtility p D (r-q)

noncomputable def benchmarkGradient (p q : Vec n) (D : Mat n n) (r : Vec n) : Vec n :=
  p-D⁻¹ *ᵥ (r-q)

theorem benchmarkUtility_value (p q : Vec n) (D : Mat n n) (c : ℝ) :
    benchmarkUtility p q D c q = c := by
  simp [benchmarkUtility,quadraticUtility]

theorem benchmarkUtility_derivative (p q : Vec n) (D : Mat n n) (hD : D.PosDef)
    (c : ℝ) (r : Vec n) :
    HasFDerivAt (benchmarkUtility p q D c) (CESCost.weightedLinear (benchmarkGradient p q D r)) r :=
  shifted_quadratic_derivative p q D hD c r

theorem benchmarkUtility_derivative_base (p q : Vec n) (D : Mat n n) (hD : D.PosDef)
    (c : ℝ) : HasFDerivAt (benchmarkUtility p q D c) (CESCost.weightedLinear p) q := by
  simpa [benchmarkGradient] using benchmarkUtility_derivative p q D hD c q

/-- Derivative of the benchmark marginal-utility vector. -/
theorem benchmarkGradient_derivative (p q : Vec n) (D : Mat n n) (r : Vec n) :
    HasFDerivAt (benchmarkGradient p q D) (-matCLM D⁻¹) r := by
  have hh := ((matCLM D⁻¹).hasFDerivAt.comp r ((hasFDerivAt_id r).sub_const q)).const_sub p
  simpa [benchmarkGradient,Function.comp_def,matCLM_apply] using hh

theorem benchmarkGradient_continuous (p q : Vec n) (D : Mat n n) :
    Continuous (benchmarkGradient p q D) :=
  continuous_iff_continuousAt.mpr (fun r => (benchmarkGradient_derivative p q D r).continuousAt)

theorem benchmarkUtility_marginals_positive_near (p q : Vec n) (D : Mat n n)
    (hp : ∀i,0<p i) (hq : ∀i,0<q i) :
    ∀ᶠ r in 𝓝 q, (∀i,0<r i) ∧ ∀i,0<benchmarkGradient p q D r i := by
  have hg : benchmarkGradient p q D q ∈ CESCost.PositivePrices n := by
    simpa [benchmarkGradient,CESCost.PositivePrices] using hp
  have hq' : q ∈ CESCost.PositivePrices n := hq
  have h1 : ∀ᶠ r in 𝓝 q, r ∈ CESCost.PositivePrices n := CESCost.positivePrices_open.mem_nhds hq'
  have h2 : ∀ᶠ r in 𝓝 q, benchmarkGradient p q D r ∈ CESCost.PositivePrices n :=
    (benchmarkGradient_continuous p q D).continuousAt (CESCost.positivePrices_open.mem_nhds hg)
  exact h1.and h2

theorem benchmarkUtility_combination_gap (p q : Vec n) (D : Mat n n) (hD : D.PosDef)
    (c : ℝ) (r t : Vec n) (a b : ℝ) (hab : a+b=1) :
    benchmarkUtility p q D c (a • r+b • t) -
      (a*benchmarkUtility p q D c r+b*benchmarkUtility p q D c t) =
      (a*b/2)*dotProduct (r-t) (D⁻¹ *ᵥ (r-t)) := by
  have ht : a • r+b • t-q=a • (r-q)+b • (t-q) := by
    ext i
    change a*r i+b*t i-q i=a*(r i-q i)+b*(t i-q i)
    nlinarith [congrArg (fun s : ℝ => s*q i) hab]
  have hrt : r-t=(r-q)-(t-q) := by abel
  rw [benchmarkUtility,ht]
  simp only [benchmarkUtility,quadraticUtility,hrt,Matrix.mulVec_add,Matrix.mulVec_smul,
    Matrix.mulVec_sub,add_dotProduct,dotProduct_add,smul_dotProduct,dotProduct_smul,
    sub_dotProduct,dotProduct_sub,smul_eq_mul]
  simp only [hD.inv.isHermitian.isSymm.dotProduct_mulVec_comm]
  have hb : b=1-a := by linarith
  rw [hb]
  ring

theorem benchmarkUtility_strictConcave (p q : Vec n) (D : Mat n n) (hD : D.PosDef) (c : ℝ) :
    StrictConcaveOn ℝ Set.univ (benchmarkUtility p q D c) := by
  refine ⟨convex_univ, ?_⟩
  intro r hr t ht hne a b ha hb hab
  have hn := hD.inv.dotProduct_mulVec_pos (sub_ne_zero.mpr hne)
  simp only [star_trivial] at hn
  have hg := benchmarkUtility_combination_gap p q D hD c r t a b hab
  have hpos : 0 < a*b/2*dotProduct (r-t) (D⁻¹ *ᵥ (r-t)) :=
    mul_pos (div_pos (mul_pos ha hb) (by norm_num)) hn
  change a*benchmarkUtility p q D c r+b*benchmarkUtility p q D c t < _
  linarith

theorem benchmarkUtility_increment (p q : Vec n) (D : Mat n n) (hD : D.PosDef)
    (c : ℝ) (r t : Vec n) :
    benchmarkUtility p q D c t-benchmarkUtility p q D c r =
      (1/2 : ℝ)*dotProduct (benchmarkGradient p q D r+benchmarkGradient p q D t) (t-r) := by
  have ht : t-r=(t-q)-(r-q) := by abel
  simp only [benchmarkUtility,benchmarkGradient,quadraticUtility,ht,add_dotProduct,
    sub_dotProduct,dotProduct_sub,Matrix.mulVec_sub]
  simp only [dotProduct_comm (D⁻¹ *ᵥ r),dotProduct_comm (D⁻¹ *ᵥ q),dotProduct_comm (D⁻¹ *ᵥ t)]
  simp only [hD.inv.isHermitian.isSymm.dotProduct_mulVec_comm]
  ring

/-- Local componentwise strict increase wherever the two marginal vectors are positive. -/
theorem benchmarkUtility_strict_increase (p q : Vec n) (D : Mat n n) (hD : D.PosDef)
    (c : ℝ) (r t : Vec n) (hr : ∀i,0<benchmarkGradient p q D r i)
    (ht : ∀i,0<benchmarkGradient p q D t i) (hle : r ≤ t) (hne : r ≠ t) :
    benchmarkUtility p q D c r < benchmarkUtility p q D c t := by
  have hex : ∃i, r i < t i := by
    by_contra! hh
    apply hne
    exact funext fun i => le_antisymm (hle i) (hh i)
  obtain ⟨i,hi⟩ := hex
  have hp : 0 < dotProduct (benchmarkGradient p q D r+benchmarkGradient p q D t) (t-r) := by
    apply Finset.sum_pos'
    · intro j _
      exact mul_nonneg (add_pos (hr j) (ht j)).le (sub_nonneg.mpr (hle j))
    · exact ⟨i,Finset.mem_univ i,mul_pos (add_pos (hr i) (ht i)) (sub_pos.mpr hi)⟩
  have hh := benchmarkUtility_increment p q D hD c r t
  linarith

theorem benchmarkUtility_surplus_maximum (p q v r : Vec n) (D : Mat n n)
    (hD : D.PosDef) (c : ℝ) :
    benchmarkUtility p q D c r-dotProduct v r ≤
      benchmarkUtility p q D c (affineDemand p q D v)-dotProduct v (affineDemand p q D v) := by
  have hh := quadraticSurplus_maximum p v (r-q) D hD
  rw [affineDemand_eq_choice]
  simp only [benchmarkUtility,add_sub_cancel_left,dotProduct_add]
  simp only [quadraticSurplus,dotProduct_sub] at hh
  linarith

theorem benchmarkUtility_household (p q v : Vec n) (D : Mat n n) (hD : D.PosDef)
    (c s income : ℝ) (hb : dotProduct v (affineDemand p q D v)+s=income) :
    ∀r : Vec n, ∀z : ℝ, dotProduct v r+z ≤ income →
      benchmarkUtility p q D c r+z ≤ benchmarkUtility p q D c (affineDemand p q D v)+s := by
  intro r z h
  have hh := benchmarkUtility_surplus_maximum p q v r D hD c
  linarith

/-- A locally matching utility needs only a local consumption comparison. -/
theorem matching_utility_benchmark_household (p q : Vec n) (D : Mat n n) (hD : D.PosDef)
    (utility : Vec n → ℝ) (c s income : ℝ) (U : Set (Vec n)) (hq : q ∈ U)
    (hmatch : ∀r∈U,utility r=benchmarkUtility p q D c r)
    (hb : dotProduct p q+s=income) :
    ∀r∈U,∀z : ℝ,dotProduct p r+z ≤ income → utility r+z ≤ utility q+s := by
  intro r hr z hz
  rw [hmatch r hr,hmatch q hq]
  have hh := benchmarkUtility_household p q p D hD c s income
  simpa only [affineDemand_base] using hh (by simpa only [affineDemand_base] using hb) r z hz

end CommodityClassification.Equilibrium
