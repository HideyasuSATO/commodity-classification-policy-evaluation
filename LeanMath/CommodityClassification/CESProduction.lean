module
public import LeanMath.CommodityClassification.CESCostSupport
@[expose] public section
set_option maxHeartbeats 1600000
namespace CommodityClassification.CESCost
open Matrix
open scoped BigOperators
variable {f : ℕ}

/-- A single price-independent production set. The price is universally bound. -/
def Data.Feasible (d : Data f) (σ y : ℝ) (x : Vec f) : Prop :=
  0 ≤ y ∧ (∀j, 0 ≤ x j) ∧ ∀v ∈ PositivePrices f, y*d.cost σ v ≤ dotProduct v x

noncomputable def Data.optimalInput (d : Data f) (σ : ℝ) (w : Vec f) (y : ℝ) : Vec f :=
  y • (fun j => pricePartial (d.cost σ) j w)

theorem Data.feasible_zero (d : Data f) (σ : ℝ) : d.Feasible σ 0 0 := by
  refine ⟨le_rfl, fun j => le_rfl, ?_⟩
  intro v hv; simp

theorem Data.feasible_scale (d : Data f) (σ : ℝ) {y : ℝ} {x : Vec f}
    (h : d.Feasible σ y x) {a : ℝ} (ha : 0 ≤ a) : d.Feasible σ (a*y) (a • x) := by
  refine ⟨mul_nonneg ha h.1, fun j => mul_nonneg ha (h.2.1 j), ?_⟩
  intro v hv
  simpa only [dotProduct_smul, smul_eq_mul, mul_assoc] using mul_le_mul_of_nonneg_left (h.2.2 v hv) ha

theorem Data.feasible_add (d : Data f) (σ : ℝ) {y z : ℝ} {x u : Vec f}
    (h : d.Feasible σ y x) (h' : d.Feasible σ z u) : d.Feasible σ (y+z) (x+u) := by
  refine ⟨add_nonneg h.1 h'.1, fun j => add_nonneg (h.2.1 j) (h'.2.1 j), ?_⟩
  intro v hv
  simpa only [add_mul, dotProduct_add] using add_le_add (h.2.2 v hv) (h'.2.2 v hv)

theorem Data.feasible_convex (d : Data f) (σ : ℝ) :
    Convex ℝ {z : ℝ × Vec f | d.Feasible σ z.1 z.2} := by
  intro z hz u hu a b ha hb hab
  exact d.feasible_add σ (d.feasible_scale σ hz ha) (d.feasible_scale σ hu hb)

theorem Data.feasible_disposal (d : Data f) (σ : ℝ) {y z : ℝ} {x u : Vec f}
    (h : d.Feasible σ y x) (hz : 0 ≤ z) (hzy : z ≤ y) (hxu : ∀j, x j ≤ u j) :
    d.Feasible σ z u := by
  refine ⟨hz, fun j => (h.2.1 j).trans (hxu j), ?_⟩
  intro v hv
  exact (mul_le_mul_of_nonneg_right hzy (d.cost_pos σ hv).le).trans
    ((h.2.2 v hv).trans (Finset.sum_le_sum (fun j _ => mul_le_mul_of_nonneg_left (hxu j) (hv j).le)))

theorem Data.optimalInput_feasible (d : Data f) {σ : ℝ} (hs : 0 < σ)
    {w : Vec f} (hw : w ∈ PositivePrices f) {y : ℝ} (hy : 0 ≤ y) :
    d.Feasible σ y (d.optimalInput σ w y) := by
  refine ⟨hy, fun j => mul_nonneg hy (d.cost_partial_pos σ hw j).le, ?_⟩
  intro v hv
  rw [Data.optimalInput, dotProduct_smul, smul_eq_mul]
  exact mul_le_mul_of_nonneg_left (by simpa only [dotProduct_comm] using d.cost_support hs hv hw) hy

theorem Data.optimalInput_expenditure (d : Data f) (σ : ℝ)
    {w : Vec f} (hw : w ∈ PositivePrices f) (y : ℝ) :
    dotProduct w (d.optimalInput σ w y) = y*d.cost σ w := by
  rw [Data.optimalInput, dotProduct_smul, smul_eq_mul, d.cost_euler σ hw, dotProduct_comm]

theorem Data.feasible_expenditure_lower (d : Data f) (σ : ℝ)
    {w : Vec f} (hw : w ∈ PositivePrices f) {y : ℝ} {x : Vec f}
    (h : d.Feasible σ y x) : y*d.cost σ w ≤ dotProduct w x := h.2.2 w hw

theorem Data.production_cost_isLeast (d : Data f) {σ : ℝ} (hs : 0 < σ)
    {w : Vec f} (hw : w ∈ PositivePrices f) {y : ℝ} (hy : 0 ≤ y) :
    IsLeast {e : ℝ | ∃x, d.Feasible σ y x ∧ dotProduct w x=e} (y*d.cost σ w) := by
  refine ⟨⟨d.optimalInput σ w y, d.optimalInput_feasible hs hw hy,
    d.optimalInput_expenditure σ hw y⟩, ?_⟩
  rintro e ⟨x,hx,rfl⟩
  exact d.feasible_expenditure_lower σ hw hx

theorem Data.unit_cost_isLeast (d : Data f) {σ : ℝ} (hs : 0 < σ)
    {w : Vec f} (hw : w ∈ PositivePrices f) :
    IsLeast {e : ℝ | ∃x, d.Feasible σ 1 x ∧ dotProduct w x=e} (d.cost σ w) := by
  simpa only [one_mul] using d.production_cost_isLeast hs hw (y := 1) zero_le_one

theorem Data.feasible_profit_nonpos (d : Data f) (σ : ℝ)
    {w : Vec f} (hw : w ∈ PositivePrices f) {y : ℝ} {x : Vec f}
    (h : d.Feasible σ y x) : d.cost σ w*y-dotProduct w x ≤ 0 := by
  have hh := d.feasible_expenditure_lower σ hw h
  nlinarith

theorem Data.optimalInput_profit_zero (d : Data f) (σ : ℝ)
    {w : Vec f} (hw : w ∈ PositivePrices f) (y : ℝ) :
    d.cost σ w*y-dotProduct w (d.optimalInput σ w y) = 0 := by
  rw [d.optimalInput_expenditure σ hw]; ring

theorem Data.production_profit_isGreatest (d : Data f) (σ : ℝ)
    {w : Vec f} (hw : w ∈ PositivePrices f) :
    IsGreatest {π : ℝ | ∃y x, d.Feasible σ y x ∧ d.cost σ w*y-dotProduct w x=π} 0 := by
  refine ⟨⟨0,0,d.feasible_zero σ,by simp⟩, ?_⟩
  rintro π ⟨y,x,h,rfl⟩
  exact d.feasible_profit_nonpos σ hw h

theorem Data.benchmark_production (d : Data f) {σ : ℝ} (hs : 0 < σ)
    {y : ℝ} (hy : 0 ≤ y) :
    d.Feasible σ y (y • d.a) ∧ dotProduct d.w0 (y • d.a)=y*d.p ∧
    d.p*y-dotProduct d.w0 (y • d.a)=0 ∧
    (∀x, d.Feasible σ y x → y*d.p ≤ dotProduct d.w0 x) := by
  have hinput : d.optimalInput σ d.w0 y = y • d.a := by
    simp only [Data.optimalInput,d.cost_gradient]
  refine ⟨?_,?_,?_,?_⟩
  · simpa only [hinput] using d.optimalInput_feasible hs d.benchmark_mem hy
  · simpa only [hinput,d.cost_benchmark] using d.optimalInput_expenditure σ d.benchmark_mem y
  · simpa only [hinput,d.cost_benchmark] using d.optimalInput_profit_zero σ d.benchmark_mem y
  · intro x hx; simpa only [d.cost_benchmark] using d.feasible_expenditure_lower σ d.benchmark_mem hx

theorem Data.zero_output (d : Data f) (σ : ℝ) (w : Vec f) :
    d.optimalInput σ w 0 = 0 ∧ d.Feasible σ 0 (d.optimalInput σ w 0) := by
  simp only [Data.optimalInput,zero_smul]
  exact ⟨True.intro,d.feasible_zero σ⟩

theorem zero_factors_impossible (d : Data 0) : False := by
  have h := d.cost_identity
  have hp := d.p_pos
  simp only [dotProduct, Fin.sum_univ_zero] at h
  linarith

theorem one_factor_cost (d : Data 1) (σ : ℝ) {w : Vec 1}
    (hw : w ∈ PositivePrices 1) : d.cost σ w = d.a 0 * w 0 := by
  have hw' : w = (w 0 / d.w0 0) • d.w0 := by
    ext j; have hj : j=0 := Subsingleton.elim _ _; subst j
    simp only [Pi.smul_apply,smul_eq_mul]
    field_simp [(d.w0_pos 0).ne']
  have hident : d.a 0*d.w0 0=d.p := by simpa [dotProduct,Fin.sum_univ_succ] using d.cost_identity
  calc
    d.cost σ w = (w 0/d.w0 0)*d.cost σ d.w0 := by
      conv_lhs => rw [hw']
      exact d.cost_smul σ _ (div_pos (hw 0) (d.w0_pos 0)) d.benchmark_mem
    _ = d.a 0*w 0 := by rw [d.cost_benchmark,←hident]; field_simp [(d.w0_pos 0).ne']

end CommodityClassification.CESCost
