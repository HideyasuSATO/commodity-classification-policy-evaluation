module
public import LeanMath.CommodityClassification.CostHomogeneity
public import LeanMath.CommodityClassification.WelfareUtility
@[expose] public section
set_option maxHeartbeats 2000000
namespace CommodityClassification.Equilibrium
open Matrix Filter
open scoped BigOperators Topology
variable {n k : ℕ}

theorem hasDerivAt_dot (f g : ℝ → Vec n) (df dg : Vec n) (t : ℝ)
    (hf : HasDerivAt f df t) (hg : HasDerivAt g dg t) :
    HasDerivAt (fun x => dotProduct (f x) (g x))
      (dotProduct df (g t)+dotProduct (f t) dg) t := by
  have hh := HasDerivAt.fun_sum (u := Finset.univ)
    (fun i _ => (hasDerivAt_pi.mp hf i).mul (hasDerivAt_pi.mp hg i))
  simpa only [dotProduct, Pi.mul_apply, Finset.sum_add_distrib] using hh

namespace Model
variable (E : Model n k)

theorem costs_eq_inputs_mulVec {w : Vec (k+1)} (hw : w ∈ CESCost.PositivePrices (k+1)) :
    E.costs w = E.currentInputs w *ᵥ w := by
  ext i
  exact (E.costData i).cost_euler E.sigma hw

theorem unit_margin_zero {w : Vec (k+1)} (hw : w ∈ CESCost.PositivePrices (k+1)) (i : Fin n) :
    E.costs w i-dotProduct (E.currentInputs w i) w=0 := by
  rw [E.costs_eq_inputs_mulVec hw]
  exact sub_self _

theorem costs_hasFDerivAt_current {w : Vec (k+1)} (hw : w ∈ CESCost.PositivePrices (k+1)) :
    HasFDerivAt E.costs (matCLM (E.currentInputs w)) w := by
  apply hasFDerivAt_pi'.mpr
  intro i
  exact (E.costData i).hasFDerivAt_cost_current E.sigma hw

noncomputable def taxTransfer (y : PolicyPrice k) : ℝ := y.1 * dotProduct E.b (E.quantities y)
noncomputable def householdIncome (abar : Vec (k+1)) (y : PolicyPrice k) : ℝ :=
  dotProduct (E.currentPrice y.2) abar + E.taxTransfer y

theorem resource_value {abar : Vec (k+1)} {y : PolicyPrice k} {s : ℝ}
    (hw : E.currentPrice y.2 ∈ CESCost.PositivePrices (k+1))
    (hc : E.excess abar (y,s)=0) :
    dotProduct (E.costs (E.currentPrice y.2)) (E.quantities y)+s =
      dotProduct (E.currentPrice y.2) abar := by
  have hclear : E.factorDemand y+s • E.frame.a0=abar := sub_eq_zero.mp hc
  have hh := congrArg (dotProduct (E.currentPrice y.2)) hclear
  have hn : dotProduct (E.currentPrice y.2) E.frame.a0=1 := by
    rw [dotProduct_comm]; exact E.currentPrice_normalized y.2
  rw [dotProduct_add,dotProduct_smul,hn,smul_eq_mul,mul_one] at hh
  rw [factorDemand,Matrix.dotProduct_transpose_mulVec,←E.costs_eq_inputs_mulVec hw,
    dotProduct_comm (E.quantities y)] at hh
  exact hh

theorem household_budget {abar : Vec (k+1)} {y : PolicyPrice k} {s : ℝ}
    (hw : E.currentPrice y.2 ∈ CESCost.PositivePrices (k+1))
    (hc : E.excess abar (y,s)=0) :
    dotProduct (E.prices y) (E.quantities y)+s=E.householdIncome abar y := by
  have hh := E.resource_value (abar := abar) (y := y) (s := s) hw hc
  simp only [prices,add_dotProduct,smul_dotProduct,smul_eq_mul,householdIncome,taxTransfer]
  linarith

theorem factor_price_derivative_at (u : ℝ → Vec k) (z : Vec k) (t : ℝ)
    (hu : HasDerivAt u z t) :
    HasDerivAt (fun x => E.currentPrice (u x)) (E.frame.V *ᵥ z) t := by
  simpa only [Function.comp_def,matCLM_apply] using
    (E.currentPrice_hasFDerivAt (u t)).comp_hasDerivAt t hu

/-- Differentiate value clearing, cancel input-price changes by physical clearing.
The scalar tax is unrestricted in sign. -/
theorem resource_derivative (abar : Vec (k+1)) (u : ℝ → Vec k) (s : ℝ → ℝ)
    (t : ℝ) (z : Vec k) (ds : ℝ) (dQ : Vec n)
    (hu : HasDerivAt u z t) (hs : HasDerivAt s ds t)
    (hQ : HasDerivAt (fun x => E.quantities (x,u x)) dQ t)
    (hw : E.currentPrice (u t) ∈ CESCost.PositivePrices (k+1))
    (hclear : ∀ᶠ x in 𝓝 t, E.excess abar ((x,u x),s x)=0) :
    dotProduct (E.costs (E.currentPrice (u t))) dQ+ds=0 := by
  have hdw := E.factor_price_derivative_at u z t hu
  have hdg := (E.costs_hasFDerivAt_current hw).comp_hasDerivAt t hdw
  have hdl := (hasDerivAt_dot (fun x => E.costs (E.currentPrice (u x)))
    (fun x => E.quantities (x,u x)) (E.currentInputs (E.currentPrice (u t)) *ᵥ (E.frame.V *ᵥ z)) dQ t
    (by simpa only [matCLM_apply,Function.comp_def] using hdg) hQ).add hs
  have hdr := (CESCost.weightedLinear abar).hasFDerivAt.comp_hasDerivAt t hdw
  have hpos : ∀ᶠ x in 𝓝 t, E.currentPrice (u x) ∈ CESCost.PositivePrices (k+1) :=
    hdw.continuousAt (CESCost.positivePrices_open.mem_nhds hw)
  have heq : (fun x => dotProduct (E.costs (E.currentPrice (u x))) (E.quantities (x,u x))+s x)
      =ᶠ[𝓝 t] (fun x => dotProduct (E.currentPrice (u x)) abar) := by
    filter_upwards [hpos,hclear] with x hx hc
    exact E.resource_value (abar := abar) (y := (x,u x)) (s := s x) hx hc
  have hdr' : HasDerivAt (fun x => dotProduct (E.currentPrice (u x)) abar)
      (dotProduct (E.frame.V *ᵥ z) abar) t := by
    simpa only [Function.comp_def,CESCost.weightedLinear_apply,dotProduct_comm] using hdr
  have hd := (hdl.congr_of_eventuallyEq heq.symm).unique hdr'
  have hc : E.factorDemand (t,u t)+s t • E.frame.a0=abar :=
    sub_eq_zero.mp hclear.self_of_nhds
  have hcancel : dotProduct (E.frame.V *ᵥ z) abar =
      dotProduct (E.currentInputs (E.currentPrice (u t)) *ᵥ (E.frame.V *ᵥ z)) (E.quantities (t,u t)) := by
    rw [←hc,dotProduct_add,dotProduct_smul]
    have hn : dotProduct (E.frame.V *ᵥ z) E.frame.a0=0 := by
      rw [dotProduct_comm]; exact E.frame.a0_dot_V z
    rw [hn,smul_zero,add_zero,factorDemand,Matrix.dotProduct_transpose_mulVec,dotProduct_comm]
  rw [hcancel] at hd
  linarith

end Model
end CommodityClassification.Equilibrium
