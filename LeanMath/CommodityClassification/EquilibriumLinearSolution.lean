module
public import LeanMath.CommodityClassification.EquilibriumProjection
public import LeanMath.CommodityClassification.EquilibriumNumeraire
@[expose] public section
set_option maxHeartbeats 2000000
namespace CommodityClassification.Equilibrium
open Matrix Filter
open scoped BigOperators Topology
variable {n k g : ℕ}
namespace Model
variable (E : Model n k)
noncomputable def zSolution : Vec k := -(E.K⁻¹ *ᵥ E.m)
noncomputable def qSolution : Vec n := E.quantityChange (1,E.zSolution)
noncomputable def sSolution : ℝ := -dotProduct E.frame.w (E.factorChange (1,E.zSolution))
def Linearized (dq : Vec n) (z : Vec k) (ds : ℝ) : Prop :=
  dq = -(E.D *ᵥ (E.C *ᵥ z + E.b)) ∧
    E.A.transpose *ᵥ dq + E.aggregateHessian *ᵥ (E.frame.V *ᵥ z) + ds • E.frame.a0 = 0

theorem K_zSolution (hK : E.K.PosDef) : E.K *ᵥ E.zSolution = -E.m := by
  rw [zSolution, Matrix.mulVec_neg, Matrix.mulVec_mulVec,
    (Regularity.inverse_identities E.K hK).2.1, Matrix.one_mulVec]
theorem zSolution_unique (hK : E.K.PosDef) (z : Vec k) (hz : E.K *ᵥ z = -E.m) : z = E.zSolution :=
  hK.mulVec_injective (hz.trans (E.K_zSolution hK).symm)
theorem qSolution_formula : E.qSolution = -(E.D *ᵥ (E.b + E.C *ᵥ E.zSolution)) := by
  simp [qSolution, E.quantityChange_apply, add_comm]
theorem solution_projected (hK : E.K.PosDef) : E.frame.V.transpose *ᵥ E.factorChange (1,E.zSolution) = 0 := by
  rw [E.projected_factorChange, E.K_zSolution hK]
  simp
theorem solution_linearized (hK : E.K.PosDef) : E.Linearized E.qSolution E.zSolution E.sSolution := by
  constructor
  · simp [qSolution, E.quantityChange_apply]
  · have hs := numeraire_adjustment E.frame (E.factorChange (1,E.zSolution)) (E.solution_projected hK)
    simpa only [E.factorChange_apply, qSolution, sSolution] using hs

theorem linearized_iff_change (dq : Vec n) (z : Vec k) (ds : ℝ) :
    E.Linearized dq z ds ↔ dq = E.quantityChange (1,z) ∧ E.factorChange (1,z) + ds • E.frame.a0 = 0 := by
  simp only [Linearized, E.quantityChange_apply, one_smul]
  constructor
  · rintro ⟨rfl,hh⟩
    exact ⟨rfl, by simpa only [E.factorChange_apply, E.quantityChange_apply, one_smul] using hh⟩
  · rintro ⟨rfl,hh⟩
    exact ⟨rfl, by simpa only [E.factorChange_apply, E.quantityChange_apply, one_smul] using hh⟩

theorem linearized_unique (hK : E.K.PosDef) (dq : Vec n) (z : Vec k) (ds : ℝ)
    (hh : E.Linearized dq z ds) : dq = E.qSolution ∧ z = E.zSolution ∧ ds = E.sSolution := by
  obtain ⟨hq,hs⟩ := (E.linearized_iff_change dq z ds).mp hh
  have hp := congrArg (fun v => E.frame.V.transpose *ᵥ v) hs
  simp only [Matrix.mulVec_add, Matrix.mulVec_smul, E.frame.annihilates,
    smul_zero, add_zero, Matrix.mulVec_zero, E.projected_factorChange] at hp
  have hz : E.K *ᵥ z = -E.m := by
    ext j
    have hj := congrFun hp j
    simp only [neg_smul, one_smul, Pi.sub_apply, Pi.neg_apply, Pi.zero_apply] at hj ⊢
    linarith
  have hz' := E.zSolution_unique hK z hz
  subst z
  exact ⟨hq, rfl, numeraire_adjustment_unique E.frame _ ds hs⟩

theorem linearized_existsUnique (hK : E.K.PosDef) :
    ∃! sol : Vec n × Vec k × ℝ, E.Linearized sol.1 sol.2.1 sol.2.2 := by
  refine ⟨(E.qSolution,E.zSolution,E.sSolution), E.solution_linearized hK, ?_⟩
  intro sol hsol
  obtain ⟨hq,hz,hs⟩ := E.linearized_unique hK _ _ _ hsol
  exact Prod.ext hq (Prod.ext hz hs)

/-- Economic conclusion: K regularity is derived from the existing parent-report
candidate theorem, not postulated as an additional primitive. -/
theorem economic_linearized_solution (P : InputCoordinates.Partition n g) (J : Mat g k)
    (hreport : P.report E.q E.C = J) (hq : ∀ i, 0 < E.q i)
    (hI : ∀ j, 0 < Supply.totalInputs E.q E.A j) (hD : E.D.PosDef) (hσ : 0 < E.sigma) :
    E.Linearized E.qSolution E.zSolution E.sSolution ∧
    (∀ dq z ds, E.Linearized dq z ds → dq = E.qSolution ∧ z = E.zSolution ∧ ds = E.sSolution) := by
  have hK := E.K_posDef P J hreport hq hI hD hσ
  exact ⟨E.solution_linearized hK, E.linearized_unique hK⟩
end Model
end CommodityClassification.Equilibrium
