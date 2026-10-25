module
public import LeanMath.CommodityClassification.WelfareExpansion
@[expose] public section
set_option maxHeartbeats 2400000
namespace CommodityClassification.Equilibrium
open Matrix Filter Asymptotics
open scoped BigOperators Topology
variable {n k g : ℕ}
namespace Model
variable (E : Model n k)

theorem quadratic_welfare_expansion (h : E.DemandC1)
    (P : InputCoordinates.Partition n g) (J : Mat g k)
    (hreport : P.report E.q E.C=J) (hq : ∀ i, 0 < E.q i)
    (hI : ∀ j, 0 < Supply.totalInputs E.q E.A j) (hD : E.D.PosDef) (hσ : 0 < E.sigma)
    (s0 : ℝ) (hs0 : 0 < s0) (haff : E.demand=affineDemand E.p E.q E.D)
    (utility : Vec n → ℝ) (c : ℝ) (U : Set (Vec n)) (hU : U ∈ 𝓝 E.q)
    (hmatch : ∀ r ∈ U, utility r=c+quadraticUtility E.p E.D (r-E.q)) :
    ∃ u : ℝ → Vec k, ∃ s : ℝ → ℝ, E.PositiveLocalPath s0 u s ∧
      E.QuadraticWelfareNeighborhood s0 utility U u s ∧
      HasDerivAt (fun t => E.quantities (t,u t)) E.qSolution 0 ∧
      E.WelfareExpansion utility u s := by
  let hK := E.K_posDef P J hreport hq hI hD hσ
  have hcompat := E.quadratic_utility_compatible hD haff utility c U hU hmatch
  exact ⟨E.localPricePath h hK s0,E.localNumerairePath h hK s0,
    E.constructed_positive_path h hK hq s0 hs0,
    E.constructed_quadratic_welfare h hK hq s0 hs0 hD haff utility c U hU hmatch,
    (E.constructed_path_derivatives h P J hreport hq hI hD hσ s0).2.2,
    E.constructed_welfare_expansion h P J hreport hq hI hD hσ s0 hs0 utility hcompat⟩

theorem ofAffine_welfare_expansion (e : InputCoordinates.Frame k) (p q : Vec n) (C : Mat n k)
    (D : Mat n n) (b : Vec n) (σ : ℝ) (hp : ∀ i, 0 < p i) (hw : ∀ j, 0 < e.w j)
    (hC : C ∈ e.PositiveDomain p) (P : InputCoordinates.Partition n g) (J : Mat g k)
    (hreport : P.report q C=J) (hq : ∀ i, 0 < q i)
    (hI : ∀ j, 0 < Supply.totalInputs q (e.reconstruct p C) j) (hD : D.PosDef) (hσ : 0 < σ)
    (s0 : ℝ) (hs0 : 0 < s0) (utility : Vec n → ℝ) (c : ℝ) (U : Set (Vec n)) (hU : U ∈ 𝓝 q)
    (hmatch : ∀ r ∈ U, utility r=c+quadraticUtility p D (r-q)) :
    let E := Model.ofAffine e p q C D b σ hp hw hC
    ∃ u : ℝ → Vec k, ∃ s : ℝ → ℝ, E.PositiveLocalPath s0 u s ∧
      E.QuadraticWelfareNeighborhood s0 utility U u s ∧
      HasDerivAt (fun t => E.quantities (t,u t)) E.qSolution 0 ∧
      E.WelfareExpansion utility u s := by
  exact (Model.ofAffine e p q C D b σ hp hw hC).quadratic_welfare_expansion
    (ofAffine_demandC1 e p q C D b σ hp hw hC) P J hreport hq hI hD hσ s0 hs0 rfl utility c U hU hmatch

theorem WelfareExpansion.zero_coefficient {E : Model n k} {utility : Vec n → ℝ}
    {u : ℝ → Vec k} {s : ℝ → ℝ} (h : E.WelfareExpansion utility u s)
    (h0 : E.lossCoefficient=0) :
    (fun t => E.welfare utility u s 0-E.welfare utility u s t) =o[𝓝 (0 : ℝ)] (fun t : ℝ => t^2) := by
  simpa only [WelfareExpansion,h0,mul_zero,sub_zero] using h

end Model

namespace Example
open Supply.Example
theorem concrete_lossCoefficient : model.lossCoefficient=(7/8 : ℝ) := by
  rw [model.lossCoefficient_eq_negative_quantity Matrix.PosDef.one,concrete_solution.1]
  norm_num [model,Model.ofAffine,dotProduct,Fin.sum_univ_succ]

theorem concrete_welfare_expansion :
    ∃ u : ℝ → Vec 1, ∃ s : ℝ → ℝ, model.PositiveLocalPath 1 u s ∧
      model.QuadraticWelfareNeighborhood 1 utility Set.univ u s ∧
      (fun t => model.welfare utility u s 0-model.welfare utility u s t-(7/16 : ℝ)*t^2)
        =o[𝓝 (0 : ℝ)] (fun t : ℝ => t^2) := by
  have he := model.quadratic_welfare_expansion model_demandC1 parent 0 model_report ones_pos
    model_total_pos Matrix.PosDef.one (by norm_num [model,Model.ofAffine]) 1 (by norm_num) rfl utility 0 Set.univ
    (by simp) (by intro r _; simp only [utility,zero_add]; rfl)
  obtain ⟨u,s,hp,hw,_,hex⟩ := he
  refine ⟨u,s,hp,hw,?_⟩
  unfold Model.WelfareExpansion at hex
  rw [concrete_lossCoefficient] at hex
  convert hex using 1
  funext t
  ring
end Example
end CommodityClassification.Equilibrium
