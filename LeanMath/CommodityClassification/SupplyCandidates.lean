module
public import LeanMath.CommodityClassification.SupplyAggregation
@[expose] public section
set_option maxHeartbeats 1800000
namespace CommodityClassification.Supply
open Matrix
open scoped BigOperators Topology
variable {n f k g : ℕ}

theorem sum_report_eq_total (P : InputCoordinates.Partition n g) (q : Vec n) (A : Mat n f)
    (j : Fin f) : (∑ a, P.report q A a j) = totalInputs q A j := by
  simp only [P.report_apply, InputCoordinates.Partition.cell, Finset.sum_filter]
  rw [Finset.sum_comm]
  simp [totalInputs]

theorem total_eq_of_report (P : InputCoordinates.Partition n g) (q : Vec n) (A E : Mat n f)
    (h : P.report q A = P.report q E) : totalInputs q A = totalInputs q E := by
  ext j
  rw [← sum_report_eq_total P, ← sum_report_eq_total P, h]

theorem coordinate_total_eq (e : InputCoordinates.Frame k) (P : InputCoordinates.Partition n g)
    (p q : Vec n) (C E : Mat n k) (h : P.report q C = P.report q E) :
    totalInputs q (e.reconstruct p C) = totalInputs q (e.reconstruct p E) := by
  apply total_eq_of_report P
  rw [P.report_reconstruct, P.report_reconstruct, h]

theorem candidate_total_eq (e : InputCoordinates.Frame k) (P : InputCoordinates.Partition n g)
    (p q : Vec n) (J : Mat g k) (C0 C : Mat n k)
    (h0 : C0 ∈ e.Candidates p q P J) (hC : C ∈ e.Candidates p q P J) :
    totalInputs q (e.reconstruct p C) = totalInputs q (e.reconstruct p C0) :=
  coordinate_total_eq e P p q C C0 (hC.2.trans h0.2.symm)

noncomputable def candidateR (e : InputCoordinates.Frame k) (p q : Vec n) (C0 : Mat n k) : Mat k k :=
  knownR e.w e.V (totalInputs q (e.reconstruct p C0))

theorem candidate_R_eq (e : InputCoordinates.Frame k) (P : InputCoordinates.Partition n g)
    (p q : Vec n) (J : Mat g k) (C0 C : Mat n k)
    (h0 : C0 ∈ e.Candidates p q P J) (hC : C ∈ e.Candidates p q P J) :
    knownR e.w e.V (totalInputs q (e.reconstruct p C)) = candidateR e p q C0 := by
  rw [candidate_total_eq e P p q J C0 C h0 hC]
  rfl

theorem candidate_R_posDef (e : InputCoordinates.Frame k) (p q : Vec n) (C0 : Mat n k)
    (hw : ∀ j,0<e.w j) (hI : ∀ j,0<totalInputs q (e.reconstruct p C0) j) :
    (candidateR e p q C0).PosDef := knownR_posDef e.w e.V _ hw hI e.independent

theorem candidate_residual_posDef (e : InputCoordinates.Frame k) (P : InputCoordinates.Partition n g)
    (p q : Vec n) (J : Mat g k) (C0 C : Mat n k)
    (hp : ∀ i,0<p i) (hq : ∀ i,0<q i) (hw : ∀ j,0<e.w j)
    (hI : ∀ j,0<totalInputs q (e.reconstruct p C0) j)
    (h0 : C0 ∈ e.Candidates p q P J) (hC : C ∈ e.Candidates p q P J) :
    (residual (candidateR e p q C0) p q C).PosDef := by
  have hh := residual_posDef e (e.reconstruct p C) p q
    (goods_nonempty_of_total_pos q _ hI) hp hq hw hC.1 (e.reconstruct_cost p C)
  rw [e.reconstruct_exposure, candidate_R_eq e P p q J C0 C h0 hC] at hh
  exact hh

theorem candidate_substitution_posDef (e : InputCoordinates.Frame k) (P : InputCoordinates.Partition n g)
    (p q : Vec n) (J : Mat g k) (C0 C : Mat n k)
    (hp : ∀ i,0<p i) (hq : ∀ i,0<q i) (hw : ∀ j,0<e.w j)
    (hI : ∀ j,0<totalInputs q (e.reconstruct p C0) j)
    (h0 : C0 ∈ e.Candidates p q P J) (hC : C ∈ e.Candidates p q P J)
    (σ : ℝ) (hσ : 0<σ) : (substitution σ (candidateR e p q C0) p q C).PosDef :=
  (candidate_residual_posDef e P p q J C0 C hp hq hw hI h0 hC).smul hσ

theorem candidate_actual_hessian (e : InputCoordinates.Frame k) (P : InputCoordinates.Partition n g)
    (p q : Vec n) (J : Mat g k) (C0 C : Mat n k)
    (hp : ∀ i,0<p i) (hw : ∀ j,0<e.w j)
    (h0 : C0 ∈ e.Candidates p q P J) (hC : C ∈ e.Candidates p q P J) (σ : ℝ) :
    -(∑ i, q i • (e.V.transpose * Matrix.of (fun j l => CESCost.pricePartial
      (CESCost.pricePartial ((CESCost.ofInputs (e.reconstruct p C) p e.w hC.1 hp hw
        (e.reconstruct_cost p C) i).cost σ) j) l e.w) * e.V)) =
      substitution σ (candidateR e p q C0) p q C := by
  have hh := aggregate_actual_hessian (e.reconstruct p C) p q e.w e.V hC.1 hp hw
    (e.reconstruct_cost p C) σ
  rw [e.reconstruct_exposure,candidate_R_eq e P p q J C0 C h0 hC] at hh
  exact hh

theorem closure_report_eq (e : InputCoordinates.Frame k) (P : InputCoordinates.Partition n g)
    (p q : Vec n) (J : Mat g k) (C : Mat n k) (hC : C∈closure (e.Candidates p q P J)) :
    P.report q C = J := by
  have hcont : Continuous (fun E : Mat n k => P.report q E) := by
    unfold InputCoordinates.Partition.report
    fun_prop
  exact closure_minimal (fun E hE => hE.2) (isClosed_eq hcont continuous_const) hC

theorem closure_R_eq (e : InputCoordinates.Frame k) (P : InputCoordinates.Partition n g)
    (p q : Vec n) (J : Mat g k) (C0 C : Mat n k)
    (h0 : C0 ∈ e.Candidates p q P J) (hC : C∈closure (e.Candidates p q P J)) :
    knownR e.w e.V (totalInputs q (e.reconstruct p C)) = candidateR e p q C0 := by
  rw [coordinate_total_eq e P p q C C0 ((closure_report_eq e P p q J C hC).trans h0.2.symm)]
  rfl

theorem residual_symmetric (R : Mat k k) (p q : Vec n) (C : Mat n k) (hR : R.IsHermitian) :
    (residual R p q C).IsHermitian := by
  have hx : (xi p q).IsHermitian := by
    unfold Matrix.IsHermitian
    ext i j
    simp [xi, Matrix.conjTranspose_apply, Matrix.diagonal_apply]
    split_ifs <;> simp_all
  simpa [residual] using hR.sub (Matrix.isHermitian_conjTranspose_mul_mul C hx)

theorem residual_quad_continuous (R : Mat k k) (p q : Vec n) (z : Vec k) :
    Continuous (fun C : Mat n k => dotProduct z (residual R p q C *ᵥ z)) := by
  unfold residual
  fun_prop

theorem closure_residual_posSemidef (R : Mat k k) (p q : Vec n) (U : Set (Mat n k))
    (hR : R.IsHermitian) (hU : ∀ C∈U,(residual R p q C).PosSemidef)
    (C : Mat n k) (hC : C∈closure U) : (residual R p q C).PosSemidef := by
  apply Matrix.posSemidef_iff_dotProduct_mulVec.mpr
  refine ⟨residual_symmetric R p q C hR,fun z => ?_⟩
  simp only [star_trivial]
  have hs : U ⊆ {E | 0≤dotProduct z (residual R p q E *ᵥ z)} := by
    intro E hE
    simpa using (hU E hE).dotProduct_mulVec_nonneg z
  exact closure_minimal hs (isClosed_le continuous_const (residual_quad_continuous R p q z)) hC

theorem candidate_closure_residual_posSemidef (e : InputCoordinates.Frame k)
    (P : InputCoordinates.Partition n g) (p q : Vec n) (J : Mat g k) (C0 C : Mat n k)
    (hp : ∀ i,0<p i) (hq : ∀ i,0<q i) (hw : ∀ j,0<e.w j)
    (hI : ∀ j,0<totalInputs q (e.reconstruct p C0) j)
    (h0 : C0 ∈ e.Candidates p q P J) (hC : C∈closure (e.Candidates p q P J)) :
    (residual (candidateR e p q C0) p q C).PosSemidef := by
  apply closure_residual_posSemidef _ p q (e.Candidates p q P J)
    (candidate_R_posDef e p q C0 hw hI).isHermitian ?_ C hC
  intro E hE
  exact (candidate_residual_posDef e P p q J C0 E hp hq hw hI h0 hE).posSemidef

theorem candidate_closure_substitution_posSemidef (e : InputCoordinates.Frame k)
    (P : InputCoordinates.Partition n g) (p q : Vec n) (J : Mat g k) (C0 C : Mat n k)
    (hp : ∀ i,0<p i) (hq : ∀ i,0<q i) (hw : ∀ j,0<e.w j)
    (hI : ∀ j,0<totalInputs q (e.reconstruct p C0) j)
    (h0 : C0 ∈ e.Candidates p q P J) (hC : C∈closure (e.Candidates p q P J))
    (σ : ℝ) (hσ : 0≤σ) : (substitution σ (candidateR e p q C0) p q C).PosSemidef :=
  (candidate_closure_residual_posSemidef e P p q J C0 C hp hq hw hI h0 hC).smul hσ

end CommodityClassification.Supply
