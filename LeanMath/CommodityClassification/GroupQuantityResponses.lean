module

public import LeanMath.CommodityClassification.EconomicStrongReportForm

/-! Group responses are derivatives of the existing actual local quantity paths. -/
@[expose] public section
noncomputable section
namespace CommodityClassification.Equilibrium.BenchmarkFamily
open Matrix InputCoordinates
variable {n k h g r : ℕ} (F : BenchmarkFamily n k h)

def responseY (C : F.Candidate) : Vec k := (F.model C).K⁻¹ *ᵥ (F.model C).m

def groupQuantityResponse (P : Partition n g) (C : F.Candidate) : Vec g :=
  P.valueAggregation F.p *ᵥ (F.model C).qSolution

def GroupQuantitiesIdentified (P : Partition n g) : Prop :=
  ∀C E : F.Candidate,P.report F.q C.val=P.report F.q E.val →
    F.groupQuantityResponse P C=F.groupQuantityResponse P E

theorem candidate_zSolution (C : F.Candidate) : (F.model C).zSolution= -F.responseY C := rfl

theorem responseY_eq_of_moments (C E : F.Candidate)
    (hm : (F.model C).m=(F.model E).m) (hK : (F.model C).K=(F.model E).K) :
    F.responseY C=F.responseY E := by
  simp only [responseY,hm,hK]

theorem groupQuantityResponse_formula (P : Partition n g) (C : F.Candidate) :
    F.groupQuantityResponse P C= -(P.valueAggregation F.p *ᵥ (F.D *ᵥ F.b))+
      (P.valueAggregation F.p*F.D*C.val) *ᵥ F.responseY C := by
  rw [groupQuantityResponse,(F.model C).qSolution_formula,F.candidate_zSolution]
  change P.valueAggregation F.p *ᵥ (-(F.D *ᵥ (F.b+C.val *ᵥ (-F.responseY C))))=_
  simp only [Matrix.mulVec_neg,Matrix.mulVec_add,Matrix.mulVec_mulVec,Matrix.mul_assoc,neg_add_rev,neg_neg]
  abel

theorem groupQuantityResponse_variation (P : Partition n g) (C E : F.Candidate)
    (N : Mat n r) (Z : Mat r k) (hC : C.val=E.val+N*Z)
    (hy : F.responseY C=F.responseY E) :
    F.groupQuantityResponse P C-F.groupQuantityResponse P E=
      (P.valueAggregation F.p*F.D*N*Z) *ᵥ F.responseY E := by
  rw [F.groupQuantityResponse_formula P C,F.groupQuantityResponse_formula P E,hC,hy]
  simp only [Matrix.mul_add,Matrix.add_mulVec,Matrix.mul_assoc]
  abel

theorem groupQuantityResponse_path (hn : 0<n) (P : Partition n g) (C : F.Candidate)
    (s0 : ℝ) (hs : 0<s0) :
    ∃u : ℝ → Vec k,∃s : ℝ → ℝ,(F.model C).PositiveLocalPath s0 u s ∧
      HasDerivAt (fun t => P.valueAggregation F.p *ᵥ (F.model C).quantities (t,u t))
        (F.groupQuantityResponse P C) 0 := by
  have hc : (F.model C).DemandC1 :=
    Model.ofAffine_demandC1 F.frame F.p F.q C.val F.D F.b F.sigma F.hp F.hw C.property.1
  obtain ⟨u,s,hpath,_,_,hq⟩ := (F.model C).economic_local_existence hc F.parents F.report
    C.property.2 F.hq (F.candidate_total_positive (F.total_positive_of_goods hn) C)
    F.hD F.hsigma s0 hs
  refine ⟨u,s,hpath,?_⟩
  have hd := (matCLM (P.valueAggregation F.p)).hasFDerivAt.comp_hasDerivAt (0 : ℝ) hq
  simpa only [matCLM_apply,Function.comp_def,groupQuantityResponse] using hd

end CommodityClassification.Equilibrium.BenchmarkFamily
