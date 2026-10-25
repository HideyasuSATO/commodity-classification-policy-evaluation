module
public import LeanMath.CommodityClassification.WelfareVariationalBounds
@[expose] public section
set_option maxHeartbeats 2400000
namespace CommodityClassification.Equilibrium
open Matrix Filter Asymptotics
open scoped BigOperators Topology
variable {n k g : ℕ}
namespace Model
variable (E : Model n k)

theorem economic_variational_welfare (h : E.DemandC1)
    (P : InputCoordinates.Partition n g) (J : Mat g k)
    (hreport : P.report E.q E.C=J) (hq : ∀ i, 0 < E.q i)
    (hI : ∀ j, 0 < Supply.totalInputs E.q E.A j) (hD : E.D.PosDef) (hσ : 0 < E.sigma)
    (s0 : ℝ) (hs0 : 0 < s0) (utility : Vec n → ℝ) (hutility : E.UtilityCompatible utility) :
    ∃ u : ℝ → Vec k, ∃ s : ℝ → ℝ, E.PositiveLocalPath s0 u s ∧
      E.WelfareNeighborhood s0 utility u s ∧ HasDerivAt u E.zSolution 0 ∧
      HasDerivAt (fun t => E.quantities (t,u t)) E.qSolution 0 ∧
      E.WelfareExpansion utility u s ∧ E.VariationalCertificate := by
  let hK := E.K_posDef P J hreport hq hI hD hσ
  have hd := E.constructed_path_derivatives h P J hreport hq hI hD hσ s0
  exact ⟨E.localPricePath h hK s0,E.localNumerairePath h hK s0,
    E.constructed_positive_path h hK hq s0 hs0,
    E.constructed_welfare_neighborhood h hK hq s0 hs0 utility hutility,hd.1,hd.2.2,
    E.constructed_welfare_expansion h P J hreport hq hI hD hσ s0 hs0 utility hutility,
    E.economic_variational_certificate P J hreport hq hI hD hσ⟩

theorem quadratic_variational_welfare (h : E.DemandC1)
    (P : InputCoordinates.Partition n g) (J : Mat g k)
    (hreport : P.report E.q E.C=J) (hq : ∀ i, 0 < E.q i)
    (hI : ∀ j, 0 < Supply.totalInputs E.q E.A j) (hD : E.D.PosDef) (hσ : 0 < E.sigma)
    (s0 : ℝ) (hs0 : 0 < s0) (haff : E.demand=affineDemand E.p E.q E.D)
    (utility : Vec n → ℝ) (c : ℝ) (U : Set (Vec n)) (hU : U ∈ 𝓝 E.q)
    (hmatch : ∀ r ∈ U, utility r=c+quadraticUtility E.p E.D (r-E.q)) :
    ∃ u : ℝ → Vec k, ∃ s : ℝ → ℝ, E.PositiveLocalPath s0 u s ∧
      E.QuadraticWelfareNeighborhood s0 utility U u s ∧ HasDerivAt u E.zSolution 0 ∧
      HasDerivAt (fun t => E.quantities (t,u t)) E.qSolution 0 ∧
      E.WelfareExpansion utility u s ∧ E.VariationalCertificate := by
  let hK := E.K_posDef P J hreport hq hI hD hσ
  have hd := E.constructed_path_derivatives h P J hreport hq hI hD hσ s0
  have hcompat := E.quadratic_utility_compatible hD haff utility c U hU hmatch
  exact ⟨E.localPricePath h hK s0,E.localNumerairePath h hK s0,
    E.constructed_positive_path h hK hq s0 hs0,
    E.constructed_quadratic_welfare h hK hq s0 hs0 hD haff utility c U hU hmatch,hd.1,hd.2.2,
    E.constructed_welfare_expansion h P J hreport hq hI hD hσ s0 hs0 utility hcompat,
    E.economic_variational_certificate P J hreport hq hI hD hσ⟩

theorem ofAffine_variational_welfare (e : InputCoordinates.Frame k) (p q : Vec n) (C : Mat n k)
    (D : Mat n n) (b : Vec n) (σ : ℝ) (hp : ∀ i, 0 < p i) (hw : ∀ j, 0 < e.w j)
    (hC : C ∈ e.PositiveDomain p) (P : InputCoordinates.Partition n g) (J : Mat g k)
    (hreport : P.report q C=J) (hq : ∀ i, 0 < q i)
    (hI : ∀ j, 0 < Supply.totalInputs q (e.reconstruct p C) j) (hD : D.PosDef) (hσ : 0 < σ)
    (s0 : ℝ) (hs0 : 0 < s0) (utility : Vec n → ℝ) (c : ℝ) (U : Set (Vec n)) (hU : U ∈ 𝓝 q)
    (hmatch : ∀ r ∈ U, utility r=c+quadraticUtility p D (r-q)) :
    let E := Model.ofAffine e p q C D b σ hp hw hC
    ∃ u : ℝ → Vec k, ∃ s : ℝ → ℝ, E.PositiveLocalPath s0 u s ∧
      E.QuadraticWelfareNeighborhood s0 utility U u s ∧ HasDerivAt u E.zSolution 0 ∧
      HasDerivAt (fun t => E.quantities (t,u t)) E.qSolution 0 ∧
      E.WelfareExpansion utility u s ∧ E.VariationalCertificate := by
  exact (Model.ofAffine e p q C D b σ hp hw hC).quadratic_variational_welfare
    (ofAffine_demandC1 e p q C D b σ hp hw hC) P J hreport hq hI hD hσ s0 hs0 rfl utility c U hU hmatch

end Model
namespace Example
open Supply.Example

theorem concrete_variational :
    model.adjustmentObjective ![-1/4]=(7/8 : ℝ) ∧
    IsLeast (Set.range model.adjustmentObjective) (7/8 : ℝ) ∧
    (∀ z, model.adjustmentObjective z=(7/8 : ℝ) ↔ z= ![-1/4]) ∧
    0 < model.lossCoefficient ∧ model.lossCoefficient ≤ dotProduct model.b (model.D *ᵥ model.b) := by
  have hc := model.economic_variational_certificate parent 0 model_report ones_pos model_total_pos
    Matrix.PosDef.one (by norm_num [model,Model.ofAffine])
  have hb : model.b ≠ 0 := by
    intro he
    have h0 := congrFun he 0
    norm_num [model,Model.ofAffine] at h0
  refine ⟨?_,?_,?_,hc.2.2.2.2 hb,hc.2.2.2.1⟩
  · simpa only [concrete_solution.2.1,concrete_lossCoefficient] using
      model.adjustmentObjective_at_solution Matrix.PosDef.one model_K_posDef
  · simpa only [concrete_lossCoefficient] using hc.1
  · intro z
    simpa only [concrete_lossCoefficient,concrete_solution.2.1] using hc.2.1 z

theorem concrete_variational_welfare :
    ∃ u : ℝ → Vec 1, ∃ s : ℝ → ℝ, model.PositiveLocalPath 1 u s ∧
      model.QuadraticWelfareNeighborhood 1 utility Set.univ u s ∧
      HasDerivAt u ![-1/4] 0 ∧
      (fun t => model.welfare utility u s 0-model.welfare utility u s t-(7/16 : ℝ)*t^2)
        =o[𝓝 (0 : ℝ)] (fun t : ℝ => t^2) ∧
      IsLeast (Set.range model.adjustmentObjective) (7/8 : ℝ) := by
  have he := model.quadratic_variational_welfare model_demandC1 parent 0 model_report ones_pos
    model_total_pos Matrix.PosDef.one (by norm_num [model,Model.ofAffine]) 1 (by norm_num) rfl utility 0 Set.univ
    (by simp) (by intro r _; simp only [utility,zero_add]; rfl)
  obtain ⟨u,s,hp,hw,hu,_,hex,hc⟩ := he
  refine ⟨u,s,hp,hw,?_,?_,concrete_variational.2.1⟩
  · simpa only [concrete_solution.2.1] using hu
  · unfold Model.WelfareExpansion at hex
    rw [concrete_lossCoefficient] at hex
    convert hex using 1
    funext t
    ring

end Example
end CommodityClassification.Equilibrium
