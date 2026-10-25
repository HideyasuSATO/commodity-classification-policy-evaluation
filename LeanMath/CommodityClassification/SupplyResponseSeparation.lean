module

public import LeanMath.CommodityClassification.ParentMeanPerturbation
public import LeanMath.CommodityClassification.WelfareVariationalBounds

/-! Two positive technologies with the same parent reports and distinct supply responses. -/
@[expose] public section
noncomputable section
namespace CommodityClassification.Equilibrium.BenchmarkFamily
open Matrix InputCoordinates Filter
open scoped Topology
variable {n k g : ℕ} (F : BenchmarkFamily n k g)

def supplyT (C : Mat n k) : Mat k k :=
  Supply.substitution F.sigma F.fixedR F.p F.q C

def supplyResponse (C : Mat n k) : Mat n n := C*(F.supplyT C)⁻¹*C.transpose

theorem supplyT_posDef (hn : 0<n) (C : F.Candidate) : (F.supplyT C.val).PosDef :=
  Supply.candidate_substitution_posDef F.frame F.parents F.p F.q F.report F.reference
    C.val F.hp F.hq F.hw (F.total_positive_of_goods hn) F.reference_mem C.property F.sigma F.hsigma

theorem supplyT_actual (C : F.Candidate) : F.supplyT C.val=(F.model C).substitutionMatrix := by
  change Supply.substitution F.sigma F.fixedR F.p F.q C.val=
    Supply.substitution F.sigma (F.model C).R F.p F.q C.val
  rw [F.candidate_R_fixed C]

theorem supplyResponse_symmetric (hn : 0<n) (C : F.Candidate) :
    (F.supplyResponse C.val).transpose=F.supplyResponse C.val := by
  have hi : ((F.supplyT C.val)⁻¹).transpose=(F.supplyT C.val)⁻¹ :=
    (F.supplyT_posDef hn C).inv.isHermitian.isSymm
  simp only [supplyResponse,transpose_mul,transpose_transpose,hi,Matrix.mul_assoc]

theorem supplyResponse_quadratic (C : Mat n k) (u : Vec n) :
    dotProduct u (F.supplyResponse C *ᵥ u)=
      dotProduct (C.transpose *ᵥ u) ((F.supplyT C)⁻¹ *ᵥ (C.transpose *ᵥ u)) := by
  simp only [supplyResponse,←mulVec_mulVec,dotProduct_mulVec,mulVec_transpose]

theorem supplyResponse_mean_zero (v : Vec n)
    (hv : (F.parents.Q F.q).transpose *ᵥ v=0) :
    dotProduct (Supply.xi F.p F.q *ᵥ v)
      (F.supplyResponse F.parentMean *ᵥ (Supply.xi F.p F.q *ᵥ v))=0 := by
  rw [F.supplyResponse_quadratic,F.parentMean_hidden_orthogonal v hv]
  simp

theorem supplyResponse_perturbation_positive (hn : 0<n) (v : Vec n) (z : Vec k)
    (hv : (F.parents.Q F.q).transpose *ᵥ v=0) (hv0 : v≠0) (hz : z≠0)
    (t : ℝ) (ht : t≠0)
    (hC : F.parentPerturbation v z t∈F.frame.Candidates F.p F.q F.parents F.report) :
    0<dotProduct (Supply.xi F.p F.q *ᵥ v)
      (F.supplyResponse (F.parentPerturbation v z t) *ᵥ (Supply.xi F.p F.q *ᵥ v)) := by
  rw [F.supplyResponse_quadratic]
  simpa using (F.supplyT_posDef hn ⟨_,hC⟩).inv.dotProduct_mulVec_pos
    (F.parentPerturbation_weighted_exposure_ne v z hv hv0 hz t ht)

theorem supplyResponse_difference_nonzero (hn : 0<n) (v : Vec n) (z : Vec k)
    (hv : (F.parents.Q F.q).transpose *ᵥ v=0) (hv0 : v≠0) (hz : z≠0)
    (t : ℝ) (ht : t≠0)
    (hC : F.parentPerturbation v z t∈F.frame.Candidates F.p F.q F.parents F.report) :
    F.supplyResponse (F.parentPerturbation v z t)-F.supplyResponse F.parentMean≠0 := by
  intro he
  have heq := sub_eq_zero.mp he
  have hp := F.supplyResponse_perturbation_positive hn v z hv hv0 hz t ht hC
  rw [heq,F.supplyResponse_mean_zero v hv] at hp
  exact (lt_irrefl 0) hp

theorem arbitrarily_close_supply_separation (hn : 0<n) (v : Vec n) (z : Vec k)
    (hv : (F.parents.Q F.q).transpose *ᵥ v=0) (hv0 : v≠0) (hz : z≠0)
    (U : Set ℝ) (hU : U∈𝓝 0) :
    ∃t : ℝ,t∈U ∧ 0<t ∧
      F.parentPerturbation v z t∈F.frame.Candidates F.p F.q F.parents F.report ∧
      F.supplyResponse (F.parentPerturbation v z t)-F.supplyResponse F.parentMean≠0 := by
  obtain ⟨l,u,hu,hs⟩ := mem_nhds_iff_exists_Ioo_subset.mp
    (inter_mem hU (F.parentPerturbation_candidates v z hv))
  obtain ⟨t,ht,htu⟩ := exists_between hu.2
  have hc := hs ⟨lt_trans hu.1 ht,htu⟩
  exact ⟨t,hc.1,ht,hc.2,F.supplyResponse_difference_nonzero hn v z hv hv0 hz t ht.ne' hc.2⟩

theorem same_parent_distinct_supply_responses (hk : 0<k)
    (i j : Fin n) (hij : i≠j) (hgroup : F.parents.group i=F.parents.group j) :
    ∃C : F.Candidate,F.supplyResponse C.val-F.supplyResponse F.parentMean≠0 := by
  obtain ⟨v,hv0,hv⟩ := F.exists_nonzero_hidden i j hij hgroup
  obtain ⟨z,hz⟩ := exists_nonzero_relative hk
  obtain ⟨t,_,_,hc,hne⟩ := F.arbitrarily_close_supply_separation (Nat.zero_lt_of_lt i.isLt)
    v z hv hv0 hz Set.univ (Filter.univ_mem)
  exact ⟨⟨_,hc⟩,hne⟩

theorem same_parent_supply_separation_equilibria (hk : 0<k)
    (i j : Fin n) (hij : i≠j) (hgroup : F.parents.group i=F.parents.group j)
    (s0 c : ℝ) (hs : 0<s0) :
    ∃C : F.Candidate,F.supplyResponse C.val-F.supplyResponse F.parentMean≠0 ∧
      F.parents.report F.q (F.frame.reconstruct F.p C.val)=
        F.parents.report F.q (F.frame.reconstruct F.p F.parentMean) ∧
      (F.model C).BenchmarkEquilibrium (F.commonUtility c) (F.commonEndowment s0) s0 ∧
      (F.model F.parentMeanCandidate).BenchmarkEquilibrium
        (F.commonUtility c) (F.commonEndowment s0) s0 := by
  obtain ⟨C,hC⟩ := F.same_parent_distinct_supply_responses hk i j hij hgroup
  refine ⟨C,hC,?_,F.every_candidate_equilibrium hs c C,
    F.every_candidate_equilibrium hs c F.parentMeanCandidate⟩
  rw [F.parents.report_reconstruct,F.parents.report_reconstruct,C.property.2,F.parentMean_report]

end CommodityClassification.Equilibrium.BenchmarkFamily
