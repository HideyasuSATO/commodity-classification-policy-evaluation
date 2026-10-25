module

public import LeanMath.CommodityClassification.GenericPairEconomicConsequence
public import LeanMath.CommodityClassification.ObservableParentTest

/-! Positive report-preserving perturbations around the observable parent mean. -/
@[expose] public section
noncomputable section
namespace CommodityClassification.InputCoordinates
open Matrix
variable {n g : ℕ}

theorem Partition.transpose_lift_xi (P : Partition n g) (p q : Vec n)
    (hp : ∀i,0<p i) :
    (P.liftReport p q).transpose * Supply.xi p q =
      diagonal (fun a => (P.sales p q a)⁻¹) * (P.Q q).transpose := by
  ext a i
  simp only [Supply.xi,mul_diagonal,diagonal_mul,transpose_apply,Partition.liftReport,Partition.Q]
  split_ifs
  · field_simp [(hp i).ne']
  · simp

end CommodityClassification.InputCoordinates

namespace CommodityClassification.Equilibrium.BenchmarkFamily
open Matrix InputCoordinates Filter
open scoped Topology
variable {n k g : ℕ} (F : BenchmarkFamily n k g)

theorem parentMean_eq_lift_report : F.parentMean=F.parents.liftReport F.p F.q*F.report := by
  rw [F.parents.liftReport_mul]
  rfl

theorem parentMean_hidden_orthogonal (v : Vec n)
    (hv : (F.parents.Q F.q).transpose *ᵥ v=0) :
    F.parentMean.transpose *ᵥ (Supply.xi F.p F.q *ᵥ v)=0 := by
  rw [F.parentMean_eq_lift_report,transpose_mul,mulVec_mulVec,
    Matrix.mul_assoc,F.parents.transpose_lift_xi F.p F.q F.hp]
  simp only [←mulVec_mulVec,hv,mulVec_zero]

def parentPerturbation (v : Vec n) (z : Vec k) (t : ℝ) : Mat n k :=
  F.parentMean+t • vecMulVec v z

theorem parentPerturbation_report (v : Vec n) (z : Vec k)
    (hv : (F.parents.Q F.q).transpose *ᵥ v=0) (t : ℝ) :
    F.parents.report F.q (F.parentPerturbation v z t)=F.report := by
  change (F.parents.Q F.q).transpose*(F.parentMean+t • vecMulVec v z)=_
  rw [Matrix.mul_add,Matrix.mul_smul,Matrix.mul_vecMulVec,hv]
  simp only [zero_vecMulVec,smul_zero,add_zero]
  exact F.parentMean_report

theorem parentPerturbation_candidates (v : Vec n) (z : Vec k)
    (hv : (F.parents.Q F.q).transpose *ᵥ v=0) :
    ∀ᶠ t : ℝ in 𝓝 0,F.parentPerturbation v z t∈
      F.frame.Candidates F.p F.q F.parents F.report := by
  have hc : Continuous (F.parentPerturbation v z) := by
    unfold parentPerturbation
    fun_prop
  have ht := hc.continuousAt.preimage_mem_nhds
    (show F.frame.PositiveDomain F.p∈𝓝 (F.parentPerturbation v z 0) from by
      simpa only [parentPerturbation,zero_smul,add_zero] using
        (F.frame.positiveDomain_open F.p).mem_nhds F.parentMean_candidate.1)
  filter_upwards [ht] with t hpos
  exact ⟨hpos,F.parentPerturbation_report v z hv t⟩

theorem parentPerturbation_weighted_exposure (v : Vec n) (z : Vec k)
    (hv : (F.parents.Q F.q).transpose *ᵥ v=0) (t : ℝ) :
    (F.parentPerturbation v z t).transpose *ᵥ (Supply.xi F.p F.q *ᵥ v)=
      (t*dotProduct v (Supply.xi F.p F.q *ᵥ v)) • z := by
  simp only [parentPerturbation,transpose_add,transpose_smul,transpose_vecMulVec,
    add_mulVec,F.parentMean_hidden_orthogonal v hv,zero_add,smul_mulVec,
    vecMulVec_mulVec,op_smul_eq_smul,smul_smul]

theorem parentPerturbation_weighted_exposure_ne (v : Vec n) (z : Vec k)
    (hv : (F.parents.Q F.q).transpose *ᵥ v=0) (hv0 : v≠0) (hz : z≠0)
    (t : ℝ) (ht : t≠0) :
    (F.parentPerturbation v z t).transpose *ᵥ (Supply.xi F.p F.q *ᵥ v)≠0 := by
  rw [F.parentPerturbation_weighted_exposure v z hv t]
  have hp : 0<dotProduct v (Supply.xi F.p F.q *ᵥ v) := by
    simpa using (Regularity.xi_posDef F.p F.q F.hp F.hq).dotProduct_mulVec_pos hv0
  exact smul_ne_zero (mul_ne_zero ht hp.ne') hz

theorem exists_nonzero_hidden (i j : Fin n) (hij : i≠j)
    (hgroup : F.parents.group i=F.parents.group j) :
    ∃v : Vec n,v≠0 ∧ (F.parents.Q F.q).transpose *ᵥ v=0 :=
  ⟨weightedExchange F.q i j,Genericity.weighted_exchange_nonzero F.q F.hq i j hij,
    F.parents.weighted_exchange_hidden F.q F.hq i j hgroup⟩

theorem exists_nonzero_relative (hk : 0<k) : ∃z : Vec k,z≠0 := by
  let j : Fin k := ⟨0,hk⟩
  refine ⟨Pi.single j 1,?_⟩
  intro hz
  have hj := congrFun hz j
  simp at hj

end CommodityClassification.Equilibrium.BenchmarkFamily
