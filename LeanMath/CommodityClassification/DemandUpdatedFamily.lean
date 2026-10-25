module

public import LeanMath.CommodityClassification.SmallDemandInverseEnergy

/-! Varying only the demand matrix, with supply primitives and observed parent reports fixed. -/
@[expose] public section
noncomputable section
namespace CommodityClassification.Equilibrium.BenchmarkFamily
open Matrix InputCoordinates Genericity Filter Asymptotics
open scoped Topology
variable {n k g : ℕ} (F : BenchmarkFamily n k g)

def withDemand (D : Mat n n) (hD : D.PosDef) : BenchmarkFamily n k g := { F with D:=D,hD:=hD }

theorem withDemand_candidates (D : Mat n n) (hD : D.PosDef) :
    (F.withDemand D hD).Candidate=F.Candidate := rfl

theorem withDemand_supply (D : Mat n n) (hD : D.PosDef) (C : Mat n k) :
    (F.withDemand D hD).fixedR=F.fixedR ∧
      (F.withDemand D hD).parentMean=F.parentMean ∧
      (F.withDemand D hD).supplyT C=F.supplyT C := ⟨rfl,rfl,rfl⟩

def demandGain (D : Mat n n) (C : Mat n k) : ℝ :=
  dotProduct (C.transpose *ᵥ (D *ᵥ F.b))
    ((Regularity.K F.p F.q D F.fixedR F.sigma C)⁻¹ *ᵥ (C.transpose *ᵥ (D *ᵥ F.b)))

theorem withDemand_coefficient (D : Mat n n) (hD : D.PosDef) (C : Mat n k) :
    (F.withDemand D hD).coefficient C=dotProduct F.b (D *ᵥ F.b)-F.demandGain D C := rfl

theorem demandGain_original (C : Mat n k) :
    F.coefficient C=dotProduct F.b (F.D *ᵥ F.b)-F.demandGain F.D C := rfl

theorem scaled_demand_K (E : Mat n n) (C : Mat n k) (r : ℝ) :
    Regularity.K F.p F.q (r • E) F.fixedR F.sigma C=
      F.supplyT C+r • (C.transpose*E*C) := by
  rw [Regularity.K_eq_demand_add_substitution,Matrix.mul_smul,Matrix.smul_mul]
  exact add_comm _ _

theorem demandGain_scaled (E : Mat n n) (a : Vec n) (hE : E *ᵥ F.b=a)
    (C : Mat n k) (r : ℝ) :
    F.demandGain (r • E) C=r^2*smallInverseEnergy (F.supplyT C)
      (C.transpose*E*C) (C.transpose *ᵥ a) r := by
  simp only [demandGain,F.scaled_demand_K,smul_mulVec,hE,mulVec_smul,
    smul_dotProduct,dotProduct_smul,smul_eq_mul,smallInverseEnergy]
  ring

theorem demandGain_cubic_remainder (hn : 0<n) (E : Mat n n) (a : Vec n)
    (hE : E *ᵥ F.b=a) (C : F.Candidate) :
    (fun r => F.demandGain (r • E) C.val-r^2*dotProduct a (F.supplyResponse C.val *ᵥ a))
      =O[𝓝 (0 : ℝ)] (fun r : ℝ => r^3) := by
  simpa only [F.demandGain_scaled E a hE,F.supplyResponse_quadratic] using
    smallInverseEnergy_cubic_remainder (F.supplyT C.val) (C.val.transpose*E*C.val)
      (C.val.transpose *ᵥ a) (F.supplyT_posDef hn C)

theorem demandGain_separated_near (hn : 0<n) (E : Mat n n) (a : Vec n)
    (hE : E *ᵥ F.b=a) (C1 C0 : F.Candidate)
    (hneq : dotProduct a (F.supplyResponse C1.val *ᵥ a)≠
      dotProduct a (F.supplyResponse C0.val *ᵥ a)) :
    ∀ᶠ r : ℝ in 𝓝 0,r≠0 → F.demandGain (r • E) C1.val≠F.demandGain (r • E) C0.val := by
  have hh := smallInverseEnergy_separation (F.supplyT C1.val) (F.supplyT C0.val)
    (C1.val.transpose*E*C1.val) (C0.val.transpose*E*C0.val)
    (C1.val.transpose *ᵥ a) (C0.val.transpose *ᵥ a)
    (F.supplyT_posDef hn C1) (F.supplyT_posDef hn C0)
    (by simpa only [F.supplyResponse_quadratic] using hneq)
  simpa only [F.demandGain_scaled E a hE] using hh

theorem demandGain_separation_positive (hn : 0<n) (E : Mat n n) (a : Vec n)
    (hE : E *ᵥ F.b=a) (C1 C0 : F.Candidate)
    (hneq : dotProduct a (F.supplyResponse C1.val *ᵥ a)≠
      dotProduct a (F.supplyResponse C0.val *ᵥ a)) (U : Set ℝ) (hU : U∈𝓝 0) :
    ∃r : ℝ,r∈U ∧ 0<r ∧ F.demandGain (r • E) C1.val≠F.demandGain (r • E) C0.val := by
  obtain ⟨l,u,hu,hs⟩ := mem_nhds_iff_exists_Ioo_subset.mp
    (inter_mem hU (F.demandGain_separated_near hn E a hE C1 C0 hneq))
  obtain ⟨r,hr,hru⟩ := exists_between hu.2
  have hx := hs ⟨lt_trans hu.1 hr,hru⟩
  exact ⟨r,hx.1,hr,hx.2 hr.ne'⟩

theorem exists_spd_demand_witness (hk : 0<k) (hb : F.b≠0)
    (i j : Fin n) (hij : i≠j) (hgroup : F.parents.group i=F.parents.group j) :
    ∃C : F.Candidate,∃D : Mat n n,D.PosDef ∧
      F.demandGain D C.val≠F.demandGain D F.parentMean := by
  obtain ⟨C,a,_,hquad,hE,hEb⟩ := F.separating_demand_direction hk hb i j hij hgroup 1 (by norm_num)
  have hneq : dotProduct a (F.supplyResponse C.val *ᵥ a)≠
      dotProduct a (F.supplyResponse F.parentMean *ᵥ a) := by
    simpa only [sub_mulVec,dotProduct_sub,sub_ne_zero] using hquad
  obtain ⟨r,_,hr,hd⟩ := F.demandGain_separation_positive (Nat.zero_lt_of_lt i.isLt)
    (interpolationMatrix F.b a 1) a hEb C F.parentMeanCandidate hneq Set.univ Filter.univ_mem
  exact ⟨C,r • interpolationMatrix F.b a 1,hE.smul hr,hd⟩

theorem exists_demand_parent_nonidentification (hk : 0<k) (hb : F.b≠0)
    (i j : Fin n) (hij : i≠j) (hgroup : F.parents.group i=F.parents.group j) :
    ∃D : Mat n n,∃hD : D.PosDef,¬(F.withDemand D hD).ParentIdentified := by
  obtain ⟨C,D,hD,hneq⟩ := F.exists_spd_demand_witness hk hb i j hij hgroup
  refine ⟨D,hD,?_⟩
  intro hp
  let C1 : (F.withDemand D hD).Candidate := ⟨C.val,C.property⟩
  let C0 : (F.withDemand D hD).Candidate := ⟨F.parentMean,F.parentMean_candidate⟩
  have he := (hp C1).trans (hp C0).symm
  have hh : (F.withDemand D hD).coefficient C.val=(F.withDemand D hD).coefficient F.parentMean := he
  rw [F.withDemand_coefficient,F.withDemand_coefficient] at hh
  exact hneq (sub_right_inj.mp hh)

theorem demand_witness_competitive_benchmarks (hk : 0<k) (hb : F.b≠0)
    (i j : Fin n) (hij : i≠j) (hgroup : F.parents.group i=F.parents.group j)
    (s0 c : ℝ) (hs : 0<s0) :
    ∃D : Mat n n,∃hD : D.PosDef,∃C : (F.withDemand D hD).Candidate,
      ((F.withDemand D hD).model C).lossCoefficient≠
        ((F.withDemand D hD).model (F.withDemand D hD).parentMeanCandidate).lossCoefficient ∧
      ((F.withDemand D hD).model C).BenchmarkEquilibrium
        ((F.withDemand D hD).commonUtility c) ((F.withDemand D hD).commonEndowment s0) s0 ∧
      ((F.withDemand D hD).model (F.withDemand D hD).parentMeanCandidate).BenchmarkEquilibrium
        ((F.withDemand D hD).commonUtility c) ((F.withDemand D hD).commonEndowment s0) s0 := by
  obtain ⟨C,D,hD,hneq⟩ := F.exists_spd_demand_witness hk hb i j hij hgroup
  let C1 : (F.withDemand D hD).Candidate := ⟨C.val,C.property⟩
  refine ⟨D,hD,C1,?_,(F.withDemand D hD).every_candidate_equilibrium hs c C1,
    (F.withDemand D hD).every_candidate_equilibrium hs c (F.withDemand D hD).parentMeanCandidate⟩
  rw [(F.withDemand D hD).candidate_lossCoefficient,
    (F.withDemand D hD).candidate_lossCoefficient]
  change (F.withDemand D hD).coefficient C.val≠(F.withDemand D hD).coefficient F.parentMean
  rw [F.withDemand_coefficient,F.withDemand_coefficient]
  exact fun he => hneq (sub_right_inj.mp he)

end CommodityClassification.Equilibrium.BenchmarkFamily
