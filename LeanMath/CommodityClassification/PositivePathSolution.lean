module

public import LeanMath.CommodityClassification.CompositeEquilibriumModel

/-! Every regular positive C1 clearing path has the previously derived solution. -/
@[expose] public section
noncomputable section
set_option maxHeartbeats 1000000
namespace CommodityClassification.Equilibrium.Model
open Matrix Filter
open scoped Topology
variable {n k : ℕ} (E : Model n k)

theorem positive_path_solution (hK : E.K.PosDef) (s0 : ℝ)
    (u : ℝ → Vec k) (s : ℝ → ℝ) (hp : E.PositiveLocalPath s0 u s) :
    HasDerivAt u E.zSolution 0 ∧ HasDerivAt s E.sSolution 0 ∧
      HasDerivAt (fun t => E.quantities (t,u t)) E.qSolution 0 := by
  obtain ⟨I,hIo,hI0,hI⟩ := hp.neighborhood
  have hu : HasDerivAt u (deriv u 0) 0 :=
    ((hI 0 hI0).2.2.1.differentiableAt (by norm_num)).hasDerivAt
  have hs : HasDerivAt s (deriv s 0) 0 :=
    ((hI 0 hI0).2.2.2.differentiableAt (by norm_num)).hasDerivAt
  have hc : ∀ᶠt : ℝ in 𝓝 0,E.excess (E.endowment s0) ((t,u t),s t)=0 := by
    filter_upwards [hIo.mem_nhds hI0] with t ht
    exact (hI t ht).1
  have hl := E.clearing_path_linearized (E.endowment s0) s0 u s (deriv u 0) (deriv s 0)
    hp.price_base hp.numeraire_base hu hs hc
  have he := E.linearized_unique hK _ _ _ hl
  exact ⟨hu.congr_deriv he.2.1,hs.congr_deriv he.2.2,
    (E.quantity_path_derivative u (deriv u 0) hp.price_base hu).congr_deriv he.1⟩

end CommodityClassification.Equilibrium.Model
