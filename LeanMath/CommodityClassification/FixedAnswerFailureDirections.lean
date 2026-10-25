module

public import LeanMath.CommodityClassification.LocalNonconstancyWitnesses
public import LeanMath.CommodityClassification.FixedAnswerComplete

/-! The three directional witness cases in the exact-classification appendix. -/
@[expose] public section
noncomputable section
set_option maxHeartbeats 2400000
namespace CommodityClassification.FixedAnswer
open Matrix Filter
open scoped Topology
variable {n k r : ℕ}

theorem Data.zeroLoad_change_direction (a : Data n k r) (U : Set (Mat r k))
    (h : a.Hypotheses U) (hm : a.m₀=0) (hr : a.r_N≠0) :
    ∃ Z : Mat r k,Z.transpose *ᵥ a.r_N≠0 ∧ a.AdmissibleChanges U Z := by
  let j : Fin k := ⟨0,h.relative_dimension_positive⟩
  let u : Vec k := Pi.single j 1
  have hu : u≠0 := by
    intro he
    have hz := congrFun he j
    simp [u] at hz
  obtain ⟨E,hE⟩ := mulVec_surjective_in_matrix a.r_N hr u
  let Z : Mat r k := E.transpose
  have hZ : Z.transpose *ᵥ a.r_N≠0 := by
    simpa only [Z,transpose_transpose,hE] using hu
  have hF0 : a.F a.C₀=0 := (a.F_eq_zero_iff _ (a.K₀_posDef U h)).mpr hm
  have changes (t : ℝ) (ht : t≠0) (htU : t • Z∈U) :
      a.F (a.point (t • Z))≠a.F a.C₀ := by
    rw [hF0]
    intro he
    have hm' := (a.F_eq_zero_iff _ (h.K_posDef _ htU)).mp he
    apply smul_ne_zero ht hZ
    simpa only [a.m_point,hm,zero_add,transpose_smul,smul_mulVec] using hm'
  refine ⟨Z,hZ,?_⟩
  intro V hV
  have hc : Continuous (fun t : ℝ => t • Z) := continuous_id.smul continuous_const
  have hpre : {t : ℝ | t • Z∈U}∈𝓝 0 :=
    hc.continuousAt.preimage_mem_nhds (by simpa only [zero_smul] using h.domain_open.mem_nhds h.origin_mem)
  obtain ⟨l,u,hu,hs⟩ := mem_nhds_iff_exists_Ioo_subset.mp (inter_mem hV hpre)
  obtain ⟨t,ht,htu⟩ := exists_between hu.2
  have hv := hs ⟨lt_trans hu.1 ht,htu⟩
  exact ⟨t,hv.1,hv.2,changes t (ne_of_gt ht) hv.2⟩

theorem Data.firstDerivative_change_direction (a : Data n k r) (U : Set (Mat r k))
    (h : a.Hypotheses U) (hm : a.m₀≠0) (hg : a.r_N-a.A_N *ᵥ a.y₀≠0) :
    ∃ Z : Mat r k,Z *ᵥ a.y₀=a.r_N-a.A_N *ᵥ a.y₀ ∧
      deriv (a.lineF Z) 0≠0 ∧ a.AdmissibleChanges U Z := by
  let g := a.r_N-a.A_N *ᵥ a.y₀
  obtain ⟨Z,hZ⟩ := mulVec_surjective_in_matrix a.y₀ (a.y₀_ne_zero (a.K₀_posDef U h) hm) g
  have hd := a.original_first_derivative U h Z
  have hgq : dotProduct g g≠0 := by simpa using (show g≠0 from hg)
  have hne : 2 * dotProduct (Z *ᵥ a.y₀) (a.r_N-a.A_N *ᵥ a.y₀)≠0 := by
    rw [hZ]
    exact mul_ne_zero (by norm_num) hgq
  refine ⟨Z,hZ,hd.deriv.symm ▸ hne,?_⟩
  exact a.changes_admissibly U h.domain_open h.origin_mem Z
    (changesNearZero_of_first _ _ hd hne)

theorem Data.secondDerivative_change_direction (a : Data n k r) (U : Set (Mat r k))
    (h : a.Hypotheses U) (hm : a.m₀≠0) (hr : a.r_N=a.A_N *ᵥ a.y₀)
    (hB : a.S_NN≠a.A_N*a.K₀⁻¹*a.A_N.transpose) :
    ∃ Z : Mat r k,
      deriv (deriv (a.lineF Z)) 0≠0 ∧ a.AdmissibleChanges U Z := by
  let B := a.S_NN-a.A_N*a.K₀⁻¹*a.A_N.transpose
  have hb : B≠0 := sub_ne_zero.mpr hB
  have hi : (a.K₀⁻¹).transpose=a.K₀⁻¹ := (a.K₀_posDef U h).inv.isHermitian.isSymm
  have hs : B.transpose=B := by
    simp only [B,Data.S_NN,transpose_sub,transpose_mul,transpose_transpose,
      h.L_symmetric,hi,Matrix.mul_assoc]
  have hv : ∃v : Vec r,dotProduct v (B *ᵥ v)≠0 := by
    by_contra hn
    push Not at hn
    exact hb (symmetric_zero_of_quadratic B hs hn)
  obtain ⟨v,hv⟩ := hv
  obtain ⟨Z,hZ⟩ := mulVec_surjective_in_matrix a.y₀ (a.y₀_ne_zero (a.K₀_posDef U h) hm) v
  have hd := a.original_second_derivative U h Z hr
  have hne : -2 * dotProduct (Z *ᵥ a.y₀)
      ((a.S_NN-a.A_N*a.K₀⁻¹*a.A_N.transpose) *ᵥ (Z *ᵥ a.y₀))≠0 := by
    rw [hZ]
    exact mul_ne_zero (by norm_num) hv
  refine ⟨Z,hd.deriv.symm ▸ hne,?_⟩
  exact a.changes_admissibly U h.domain_open h.origin_mem Z
    (changesNearZero_of_second _ _ hd hne)

theorem Data.failure_has_change_direction (a : Data n k r) (U : Set (Mat r k))
    (h : a.Hypotheses U) (hf : ¬a.CongruenceCriterion) :
    ∃ Z : Mat r k,a.AdmissibleChanges U Z := by
  by_cases hm : a.m₀=0
  · have hr : a.r_N≠0 := fun hr => hf (Or.inl ⟨hm,hr⟩)
    obtain ⟨Z,_,hz⟩ := a.zeroLoad_change_direction U h hm hr
    exact ⟨Z,hz⟩
  · by_cases hr : a.r_N=a.A_N *ᵥ a.y₀
    · have hb : a.S_NN≠a.A_N*a.K₀⁻¹*a.A_N.transpose := fun hb => hf (Or.inr ⟨hm,hr,hb⟩)
      obtain ⟨Z,_,hz⟩ := a.secondDerivative_change_direction U h hm hr hb
      exact ⟨Z,hz⟩
    · obtain ⟨Z,_,_,hz⟩ := a.firstDerivative_change_direction U h hm (sub_ne_zero.mpr hr)
      exact ⟨Z,hz⟩

end CommodityClassification.FixedAnswer
