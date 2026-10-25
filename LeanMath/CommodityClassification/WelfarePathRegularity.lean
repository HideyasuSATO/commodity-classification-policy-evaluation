module
public import LeanMath.CommodityClassification.WelfareApplication
@[expose] public section
set_option maxHeartbeats 1800000
namespace CommodityClassification.Equilibrium
open Matrix Filter
open scoped BigOperators Topology ContDiff
variable {n k g : ℕ}
namespace Model
variable (E : Model n k)

theorem quantity_path_contDiffAt (h : E.DemandC1) (hK : E.K.PosDef) (s0 : ℝ) :
    ContDiffAt ℝ 1 (fun t => E.quantities (t,E.localPricePath h hK s0 t)) 0 := by
  have hq : ContDiffAt ℝ 1 E.quantities (0,E.localPricePath h hK s0 0) := by
    rw [E.localPricePath_base]
    exact E.quantities_contDiffAt h
  exact ContDiffAt.comp (f := fun t : ℝ => (t,E.localPricePath h hK s0 t))
    (g := E.quantities) 0 hq (contDiffAt_id.prodMk (E.localPricePath_contDiffAt h hK s0))

theorem quantity_path_C1_neighborhood (h : E.DemandC1) (hK : E.K.PosDef) (s0 : ℝ) :
    ∃ I : Set ℝ, IsOpen I ∧ 0 ∈ I ∧ ∀ t ∈ I,
      ContDiffAt ℝ 1 (fun t => E.quantities (t,E.localPricePath h hK s0 t)) t := by
  have he := (E.quantity_path_contDiffAt h hK s0).eventually (by norm_num)
  obtain ⟨I,hI,ho,h0⟩ := mem_nhds_iff.mp he
  exact ⟨I,ho,h0,fun t ht => hI ht⟩

theorem quantity_derivative_continuous (h : E.DemandC1) (hK : E.K.PosDef) (s0 : ℝ) :
    ContinuousAt (deriv (fun t => E.quantities (t,E.localPricePath h hK s0 t))) 0 := by
  have hc := (E.quantity_path_contDiffAt h hK s0).continuousAt_fderiv (by norm_num)
  exact hc.clm_apply (continuousAt_const (y := (1 : ℝ)))

theorem weighted_quantity_derivative_continuous (h : E.DemandC1) (hK : E.K.PosDef) (s0 : ℝ) :
    ContinuousAt (fun t => dotProduct E.b (deriv (fun x => E.quantities (x,E.localPricePath h hK s0 x)) t)) 0 := by
  simpa only [Function.comp_def,CESCost.weightedLinear_apply] using
    (CESCost.weightedLinear E.b).continuous.continuousAt.comp
    (E.quantity_derivative_continuous h hK s0)

theorem quantity_derivative_zero (h : E.DemandC1)
    (P : InputCoordinates.Partition n g) (J : Mat g k)
    (hreport : P.report E.q E.C=J) (hq : ∀ i, 0 < E.q i)
    (hI : ∀ j, 0 < Supply.totalInputs E.q E.A j) (hD : E.D.PosDef) (hσ : 0 < E.sigma) (s0 : ℝ) :
    let hK := E.K_posDef P J hreport hq hI hD hσ
    deriv (fun t => E.quantities (t,E.localPricePath h hK s0 t)) 0=E.qSolution := by
  exact (E.constructed_path_derivatives h P J hreport hq hI hD hσ s0).2.2.deriv

end Model
end CommodityClassification.Equilibrium
