module
public import LeanMath.CommodityClassification.EquilibriumResidualDerivatives
@[expose] public section
set_option maxHeartbeats 2000000
namespace CommodityClassification.Equilibrium
open Matrix Filter
open scoped BigOperators Topology
variable {n k g r : ℕ}
namespace Model
variable (E : Model n k)

theorem projected_hessian :
    E.frame.V.transpose * E.aggregateHessian * E.frame.V =
      -Supply.substitution E.sigma E.R E.p E.q E.C := by
  have hh := Supply.aggregate_negative_hessian E.A E.p E.q E.frame.w E.frame.V
    E.hC E.hp E.hw (E.frame.reconstruct_cost E.p E.C) E.sigma
  have hc : E.A * E.frame.V = E.C := E.frame.reconstruct_exposure E.p E.C
  rw [hc] at hh
  have he : E.frame.V.transpose * E.aggregateHessian * E.frame.V =
      ∑ i, E.q i • (E.frame.V.transpose * E.hessian i * E.frame.V) := by
    simp [aggregateHessian, Matrix.mul_sum, Matrix.sum_mul, Matrix.mul_smul, Matrix.smul_mul]
  rw [he]
  exact neg_eq_iff_eq_neg.mp hh

theorem project_physical_change (dq : Vec n) (z : Vec k) :
    E.frame.V.transpose *ᵥ (E.A.transpose *ᵥ dq + E.aggregateHessian *ᵥ (E.frame.V *ᵥ z)) =
      E.C.transpose *ᵥ dq - Supply.substitution E.sigma E.R E.p E.q E.C *ᵥ z := by
  rw [Matrix.mulVec_add, Matrix.mulVec_mulVec, ← Matrix.transpose_mul,
    A, E.frame.reconstruct_exposure]
  rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, E.projected_hessian]
  simp [Matrix.neg_mulVec, sub_eq_add_neg]

theorem projected_factorChange (y : PolicyPrice k) :
    E.frame.V.transpose *ᵥ E.factorChange y = -y.1 • E.m - E.K *ᵥ y.2 := by
  rw [E.factorChange_apply, E.project_physical_change, E.quantityChange_apply]
  simp only [K, Regularity.K_eq_demand_add_substitution, m, Matrix.mulVec_neg,
    Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.add_mulVec, ← Matrix.mulVec_mulVec, neg_smul]
  abel

noncomputable def reducedChange : PolicyPrice k →L[ℝ] Vec k :=
  (matCLM E.frame.V.transpose).comp E.factorChange
theorem reducedChange_apply (y : PolicyPrice k) : E.reducedChange y = -y.1 • E.m - E.K *ᵥ y.2 := by
  simpa only [reducedChange, ContinuousLinearMap.comp_apply, matCLM_apply] using E.projected_factorChange y
theorem reduced_derivative_apply (abar : Vec (k+1)) (y : PolicyPrice k) :
    fderiv ℝ (E.reduced abar) 0 y = -y.1 • E.m - E.K *ᵥ y.2 := by
  rw [(E.reduced_hasFDerivAt abar).fderiv]
  simpa only [ContinuousLinearMap.comp_apply, matCLM_apply] using E.projected_factorChange y

theorem price_jacobian (abar : Vec (k+1)) :
    HasFDerivAt (fun u => E.reduced abar (0,u)) (-matCLM E.K) 0 := by
  let inj : Vec k →L[ℝ] PolicyPrice k := (0 : Vec k →L[ℝ] ℝ).prod (ContinuousLinearMap.id ℝ (Vec k))
  have hh := (E.reduced_hasFDerivAt abar).comp (0 : Vec k) inj.hasFDerivAt
  apply hh.congr_fderiv
  apply ContinuousLinearMap.ext
  intro u
  simp only [ContinuousLinearMap.comp_apply, inj, ContinuousLinearMap.prod_apply,
    _root_.zero_apply, ContinuousLinearMap.id_apply, _root_.neg_apply, matCLM_apply]
  rw [E.projected_factorChange]
  simp

theorem tax_derivative (abar : Vec (k+1)) :
    HasDerivAt (fun t : ℝ => E.reduced abar (t,0)) (-E.m) 0 := by
  let inj : ℝ →L[ℝ] PolicyPrice k := (ContinuousLinearMap.id ℝ ℝ).prod 0
  have hh := (E.reduced_hasFDerivAt abar).comp (0 : ℝ) inj.hasFDerivAt
  convert hh.hasDerivAt using 1
  · rfl
  · simp only [ContinuousLinearMap.comp_apply, inj, ContinuousLinearMap.prod_apply,
      _root_.zero_apply, ContinuousLinearMap.id_apply, matCLM_apply]
    rw [E.projected_factorChange]
    simp

theorem m_eq_fixedAnswer (C0 : Mat n k) (N : Mat n r) :
    (Regularity.fixedAnswerData E.p E.q E.D E.R E.sigma E.b C0 N).m E.C = E.m := rfl

theorem R_eq_parent (P : InputCoordinates.Partition n g) (J : Mat g k) (Cref : Mat n k)
    (href : Cref ∈ E.frame.Candidates E.p E.q P J) (hreport : P.report E.q E.C = J) :
    E.R = Supply.candidateR E.frame E.p E.q Cref :=
  Supply.candidate_R_eq E.frame P E.p E.q J Cref E.C href ⟨E.hC,hreport⟩

theorem K_posDef (P : InputCoordinates.Partition n g) (J : Mat g k)
    (hreport : P.report E.q E.C = J) (hq : ∀ i, 0 < E.q i)
    (hI : ∀ j, 0 < Supply.totalInputs E.q E.A j) (hD : E.D.PosDef) (hσ : 0 < E.sigma) :
    E.K.PosDef :=
  Regularity.candidate_K_posDef E.frame P E.p E.q J E.C E.C E.D E.sigma E.hp hq E.hw hI
    ⟨E.hC,hreport⟩ ⟨E.hC,hreport⟩ hD hσ
end Model
end CommodityClassification.Equilibrium
