module

public import LeanMath.CommodityClassification.PrecisionLinearBoxSlice

/-! Group totals and policy load impose at most one additional independent constraint. -/
@[expose] public section
noncomputable section
set_option maxHeartbeats 1400000
namespace CommodityClassification.Precision.Data
open Matrix InputCoordinates
open scoped BigOperators
variable {n g : ℕ} (d : Precision.Data n)

theorem theta_add (c e : Vec n) : d.theta (c+e)=d.theta c+d.theta e := by
  simp only [theta,Pi.add_apply,mul_add,Finset.sum_add_distrib]

theorem theta_smul (c : Vec n) (t : ℝ) : d.theta (t • c)=t*d.theta c := by
  simp only [theta,Pi.smul_apply,smul_eq_mul,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

def classificationConstraints (P : Partition n g) : Vec n →ₗ[ℝ] Vec (g+1) where
  toFun c := Fin.cons (d.theta c) (d.groupTotal P c)
  map_add' c e := by
    ext a
    refine Fin.cases ?_ (fun i => ?_) a
    · simp [d.theta_add]
    · simp [d.groupTotal_add]
  map_smul' t c := by
    ext a
    refine Fin.cases ?_ (fun i => ?_) a
    · simp [d.theta_smul]
    · simp [d.groupTotal_smul]

theorem classificationConstraints_eq_iff (P : Partition n g) (c e : Vec n) :
    d.classificationConstraints P c=d.classificationConstraints P e ↔
      d.theta c=d.theta e ∧ d.groupTotal P c=d.groupTotal P e := by
  constructor
  · intro hh
    exact ⟨congrFun hh 0,funext (fun i => congrFun hh i.succ)⟩
  · rintro ⟨ht,hj⟩
    change (Fin.cons (d.theta c) (d.groupTotal P c) : Vec (g+1))=
      (Fin.cons (d.theta e) (d.groupTotal P e) : Vec (g+1))
    rw [ht,hj]

theorem classificationSlice_eq (P : Partition n g) (c : Vec n) :
    Precision.Box.slice (d.classificationConstraints P) (d.classificationConstraints P c)=
      d.closedFiber P (d.groupTotal P c) ∩ {e | d.theta e=d.theta c} := by
  ext e
  simp only [Precision.Box.slice,closedFiber,Set.mem_ofPred_eq,Set.mem_inter_iff,
    d.classificationConstraints_eq_iff]
  tauto

theorem classification_vertex_count (P : Partition n g) (c e : Vec n)
    (he : e∈(Precision.Box.slice (d.classificationConstraints P)
      (d.classificationConstraints P c)).extremePoints ℝ) :
    (Precision.Box.interiors e).card≤g+1 :=
  Precision.Box.vertex_interior_count _ _ e he

theorem classification_vertex_maximum (P : Partition n g) (c : Vec n)
    (hc : ∀i,|c i|≤1) :
    ∃e,e∈(Precision.Box.slice (d.classificationConstraints P)
      (d.classificationConstraints P c)).extremePoints ℝ ∧
      IsMaxOn d.secondMoment (Precision.Box.slice (d.classificationConstraints P)
        (d.classificationConstraints P c)) e ∧
      (Precision.Box.interiors e).card≤g+1 := by
  let S := Precision.Box.slice (d.classificationConstraints P) (d.classificationConstraints P c)
  have hnon : S.Nonempty := ⟨c,hc,rfl⟩
  obtain ⟨e,he,hm⟩ := (Precision.Box.slice_compact _ _).exists_isMaxOn hnon
    d.secondMoment_continuous.continuousOn
  have hx := d.secondMoment_maximizer_extreme S e he hm
  exact ⟨e,hx,hm,d.classification_vertex_count P c e hx⟩

theorem secondMoment_deficit_bound (c : Vec n) (hc : ∀i,|c i|≤1) :
    1-d.secondMoment c≤∑i∈Precision.Box.interiors c,d.w i := by
  calc
    1-d.secondMoment c=∑i,d.w i*(1-(c i)^2) := by
      simp only [mul_sub,mul_one,Finset.sum_sub_distrib,secondMoment,d.sum_w]
    _≤∑i∈Precision.Box.interiors c,d.w i := by
      rw [Precision.Box.interiors,Finset.sum_filter]
      apply Finset.sum_le_sum
      intro i _
      by_cases hi : |c i|<1
      · rw [ite_eq_left hi]
        nlinarith [d.hw i,sq_nonneg (c i)]
      · rw [ite_eq_right hi]
        have ha : |c i|=1 := le_antisymm (hc i) (le_of_not_gt hi)
        have hs : (c i)^2=1 := by nlinarith [sq_abs (c i)]
        rw [hs,sub_self,mul_zero]

theorem classification_vertex_weight_bound (P : Partition n g) (c : Vec n)
    (hc : ∀i,|c i|≤1) :
    ∃e,e∈(Precision.Box.slice (d.classificationConstraints P)
      (d.classificationConstraints P c)).extremePoints ℝ ∧
      IsMaxOn d.secondMoment (Precision.Box.slice (d.classificationConstraints P)
        (d.classificationConstraints P c)) e ∧
      (Precision.Box.interiors e).card≤g+1 ∧
      1-(∑i∈Precision.Box.interiors e,d.w i)≤d.secondMoment e := by
  obtain ⟨e,he,hm,hr⟩ := d.classification_vertex_maximum P c hc
  have hh := d.secondMoment_deficit_bound e he.1.1
  exact ⟨e,he,hm,hr,by linarith⟩

end CommodityClassification.Precision.Data
