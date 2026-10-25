module

public import LeanMath.CommodityClassification.BalancedTwoProductCancellation

/-! Exact policy attributes for separable demand. -/
@[expose] public section
noncomputable section
namespace CommodityClassification.Equilibrium.BenchmarkFamily
open Matrix InputCoordinates
variable {n k h : ℕ} (F : BenchmarkFamily n k h)

theorem separable_elasticity_pos (η : Vec n)
    (hD : F.D=diagonal (fun i => η i*F.q i/F.p i)) (i : Fin n) : 0<η i := by
  have hd : 0<η i*F.q i/F.p i := by simpa only [hD,diagonal_apply_eq] using (F.hD.diag_pos (i:=i))
  exact (mul_pos_iff_of_pos_right (F.hq i)).mp ((div_pos_iff_of_pos_right (F.hp i)).mp hd)

theorem separable_normalized_load (η : Vec n)
    (hD : F.D=diagonal (fun i => η i*F.q i/F.p i)) (i : Fin n) :
    (F.D *ᵥ F.b) i/F.q i=η i*F.b i/F.p i := by
  rw [hD,mulVec_diagonal]
  change (η i*F.q i/F.p i)*F.b i/F.q i=_
  field_simp [(F.hq i).ne',(F.hp i).ne']

theorem separable_adjustedDemand (η : Vec n)
    (hD : F.D=diagonal (fun i => η i*F.q i/F.p i)) :
    Regularity.adjustedDemand F.p F.q F.D F.sigma=
      diagonal (fun i => (η i-F.sigma)*F.q i/F.p i) := by
  ext i j
  by_cases hij : i=j
  · subst j
    simp only [Regularity.adjustedDemand,hD,Supply.xi,Matrix.sub_apply,Matrix.smul_apply,
      diagonal_apply_eq,smul_eq_mul]
    ring
  · simp [Regularity.adjustedDemand,hD,Supply.xi,hij]

theorem separable_column_difference (η : Vec n)
    (hD : F.D=diagonal (fun i => η i*F.q i/F.p i)) (i j : Fin n) (hij : i≠j) :
    (fun a => Regularity.adjustedDemand F.p F.q F.D F.sigma a i/F.q i-
      Regularity.adjustedDemand F.p F.q F.D F.sigma a j/F.q j)=
      twoSupport i j ((η i-F.sigma)/F.p i) ((η j-F.sigma)/F.p j) := by
  rw [F.separable_adjustedDemand η hD]
  ext l
  by_cases hli : l=i
  · subst l
    rw [twoSupport_at_left i j hij]
    simp only [diagonal_apply_eq,diagonal_apply_ne _ hij,zero_div,sub_zero]
    field_simp [(F.hq i).ne',(F.hp i).ne']
  · by_cases hlj : l=j
    · subst l
      rw [twoSupport_at_right i j hij]
      simp only [diagonal_apply_eq,diagonal_apply_ne _ (Ne.symm hij),zero_div,zero_sub]
      field_simp [(F.hq j).ne',(F.hp j).ne']
    · rw [twoSupport_elsewhere i j l hli hlj]
      simp only [diagonal_apply_ne _ hli,diagonal_apply_ne _ hlj,zero_div,sub_self]

theorem separable_attributes_iff (η : Vec n)
    (hD : F.D=diagonal (fun i => η i*F.q i/F.p i)) (i j : Fin n) (hij : i≠j) :
    F.SamePolicyAttributes i j ↔ η i*F.b i/F.p i=η j*F.b j/F.p j ∧
      twoSupport i j ((η i-F.sigma)/F.p i) ((η j-F.sigma)/F.p j)∈
        cancellationSpace (F.parents.Q F.q) F.report := by
  unfold SamePolicyAttributes
  rw [F.separable_normalized_load η hD i,F.separable_normalized_load η hD j,
    F.separable_column_difference η hD i j hij]

theorem separable_rigid_algebra (η : Vec n) (i j : Fin n) :
    (η i*F.b i/F.p i=η j*F.b j/F.p j ∧
      (η i-F.sigma)/F.p i=0 ∧ (η j-F.sigma)/F.p j=0) ↔
      η i=F.sigma ∧ η j=F.sigma ∧ F.b i/F.p i=F.b j/F.p j := by
  constructor
  · rintro ⟨he,hi,hj⟩
    have hi' : η i=F.sigma := sub_eq_zero.mp ((div_eq_zero_iff).mp hi |>.resolve_right (F.hp i).ne')
    have hj' : η j=F.sigma := sub_eq_zero.mp ((div_eq_zero_iff).mp hj |>.resolve_right (F.hp j).ne')
    refine ⟨hi',hj',?_⟩
    rw [hi',hj',mul_div_assoc,mul_div_assoc] at he
    exact mul_left_cancel₀ F.hsigma.ne' he
  · rintro ⟨hi,hj,he⟩
    rw [hi,hj]
    simp only [sub_self,zero_div,and_self,and_true]
    simpa only [mul_div_assoc] using congrArg (fun x => F.sigma*x) he

end CommodityClassification.Equilibrium.BenchmarkFamily
