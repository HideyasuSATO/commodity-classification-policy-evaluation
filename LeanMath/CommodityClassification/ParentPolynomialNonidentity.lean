module

public import LeanMath.CommodityClassification.ParentGainPolynomial

/-! Parent identification is contained in a proper polynomial zero set on symmetric demands. -/
@[expose] public section
noncomputable section
namespace CommodityClassification.Equilibrium.BenchmarkFamily
open Matrix InputCoordinates Genericity
variable {n k g : ℕ} (F : BenchmarkFamily n k g)

theorem demandK_posDef (hn : 0<n) (D : Mat n n) (hD : D.PosDef) (C : F.Candidate) :
    (Regularity.K F.p F.q D F.fixedR F.sigma C.val).PosDef :=
  Regularity.candidate_K_posDef F.frame F.parents F.p F.q F.report F.reference C.val
    D F.sigma F.hp F.hq F.hw (F.total_positive_of_goods hn) F.reference_mem C.property hD F.hsigma

theorem gainDifferencePolynomial_zero_iff (hn : 0<n) (D : SymmetricDemand n)
    (hD : D.val.PosDef) (C1 C0 : F.Candidate) :
    MvPolynomial.eval (symmetricCoordinates D) (F.gainDifferencePolynomial C1.val C0.val)=0 ↔
      F.demandGain D.val C1.val=F.demandGain D.val C0.val := by
  have h1 := (F.demandK_posDef hn D.val hD C1).det_pos.ne'
  have h0 := (F.demandK_posDef hn D.val hD C0).det_pos.ne'
  rw [F.gainDifferencePolynomial_eval D C1.val C0.val h1 h0]
  simp only [mul_eq_zero,h1,h0,false_or,sub_eq_zero]

theorem parentIdentification_polynomial_zero (hn : 0<n) (C : F.Candidate)
    (D : SymmetricDemand n) (hD : D.val.PosDef)
    (hp : (F.withDemand D.val hD).ParentIdentified) :
    MvPolynomial.eval (symmetricCoordinates D) (F.gainDifferencePolynomial C.val F.parentMean)=0 := by
  apply (F.gainDifferencePolynomial_zero_iff hn D hD C F.parentMeanCandidate).mpr
  let C1 : (F.withDemand D.val hD).Candidate := ⟨C.val,C.property⟩
  let C0 : (F.withDemand D.val hD).Candidate := ⟨F.parentMean,F.parentMean_candidate⟩
  have he : (F.withDemand D.val hD).coefficient C.val=
      (F.withDemand D.val hD).coefficient F.parentMean := (hp C1).trans (hp C0).symm
  rw [F.withDemand_coefficient,F.withDemand_coefficient] at he
  exact sub_right_inj.mp he

theorem gainDifferencePolynomial_nonzero_of_witness (hn : 0<n) (C : F.Candidate)
    (D : Mat n n) (hD : D.PosDef)
    (hneq : F.demandGain D C.val≠F.demandGain D F.parentMean) :
    F.gainDifferencePolynomial C.val F.parentMean≠0 := by
  intro hp
  let S : SymmetricDemand n := ⟨D,hD.isHermitian.isSymm⟩
  have hz : MvPolynomial.eval (symmetricCoordinates S)
      (F.gainDifferencePolynomial C.val F.parentMean)=0 := by rw [hp,map_zero]
  exact hneq ((F.gainDifferencePolynomial_zero_iff hn S hD C F.parentMeanCandidate).mp hz)

theorem exists_nonzero_parent_polynomial (hk : 0<k) (hb : F.b≠0)
    (i j : Fin n) (hij : i≠j) (hgroup : F.parents.group i=F.parents.group j) :
    ∃C : F.Candidate,
      F.gainDifferencePolynomial C.val F.parentMean≠0 ∧
      IsClosed {D : SymmetricDemand n |
        MvPolynomial.eval (symmetricCoordinates D) (F.gainDifferencePolynomial C.val F.parentMean)=0} ∧
      ∀D : SymmetricDemand n,∀hD : D.val.PosDef,
        (F.withDemand D.val hD).ParentIdentified →
        MvPolynomial.eval (symmetricCoordinates D) (F.gainDifferencePolynomial C.val F.parentMean)=0 := by
  obtain ⟨C,D,hD,hneq⟩ := F.exists_spd_demand_witness hk hb i j hij hgroup
  have hn : 0<n := Nat.zero_lt_of_lt i.isLt
  exact ⟨C,F.gainDifferencePolynomial_nonzero_of_witness hn C D hD hneq,
    symmetric_polynomial_zero_closed _,fun S hS hp => F.parentIdentification_polynomial_zero hn C S hS hp⟩

end CommodityClassification.Equilibrium.BenchmarkFamily
