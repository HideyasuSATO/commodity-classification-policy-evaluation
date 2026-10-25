module

public import LeanMath.CommodityClassification.PrecisionReportMean

/-! The exact weighted-variance decomposition and unique second-moment minimum. -/
@[expose] public section
noncomputable section
set_option maxHeartbeats 1000000
namespace CommodityClassification.Precision.Data
open Matrix InputCoordinates
open scoped BigOperators
variable {n g : ℕ} (d : Precision.Data n)

def lowerMoment (P : Partition n g) (J : Vec g) : ℝ := ∑a,(J a)^2/d.groupWeight P a
def residualVariance (P : Partition n g) (c : Vec n) : ℝ :=
  ∑i,d.w i*(c i-d.meanVector P c i)^2

theorem cell_variance_identity (P : Partition n g) (c : Vec n) (a : Fin g) :
    (∑i∈P.cell a,d.w i*(c i-d.groupTotal P c a/d.groupWeight P a)^2)=
      (∑i∈P.cell a,d.w i*(c i)^2)-(d.groupTotal P c a)^2/d.groupWeight P a := by
  let J := d.groupTotal P c a
  let W := d.groupWeight P a
  have hW : W≠0 := (d.groupWeight_pos P a).ne'
  change (∑i∈P.cell a,d.w i*(c i-J/W)^2)=(∑i∈P.cell a,d.w i*(c i)^2)-J^2/W
  calc
    _=(∑i∈P.cell a,d.w i*(c i)^2)-2*(J/W)*(∑i∈P.cell a,d.w i*c i)+
        (J/W)^2*(∑i∈P.cell a,d.w i) := by
      rw [Finset.mul_sum,Finset.mul_sum,←Finset.sum_sub_distrib,←Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro i _;ring
    _=_ := by
      change (∑i∈P.cell a,d.w i*(c i)^2)-2*(J/W)*J+(J/W)^2*W=_
      field_simp [hW]
      ring

theorem residualVariance_identity (P : Partition n g) (c : Vec n) :
    d.residualVariance P c=d.secondMoment c-d.lowerMoment P (d.groupTotal P c) := by
  unfold residualVariance
  rw [←sum_by_partition P]
  have he : (∑a,∑i∈P.cell a,d.w i*(c i-d.meanVector P c i)^2)=
      ∑a,((∑i∈P.cell a,d.w i*(c i)^2)-(d.groupTotal P c a)^2/d.groupWeight P a) := by
    apply Finset.sum_congr rfl
    intro a _
    rw [←d.cell_variance_identity P c a]
    apply Finset.sum_congr rfl
    intro i hi
    simp only [meanVector,(P.mem_cell a i).mp hi]
  rw [he,Finset.sum_sub_distrib,sum_by_partition P]
  rfl

theorem residualVariance_nonneg (P : Partition n g) (c : Vec n) :
    0≤d.residualVariance P c :=
  Finset.sum_nonneg (fun i _ => mul_nonneg (d.hw i).le (sq_nonneg _))

theorem secondMoment_lower (P : Partition n g) (c : Vec n) :
    d.lowerMoment P (d.groupTotal P c)≤d.secondMoment c := by
  have h := d.residualVariance_nonneg P c
  rw [d.residualVariance_identity] at h
  linarith

theorem residualVariance_zero_iff (P : Partition n g) (c : Vec n) :
    d.residualVariance P c=0 ↔ c=d.meanVector P c := by
  constructor
  · intro hz
    funext i
    have hterm := Finset.single_le_sum (s := Finset.univ)
      (fun j _ => mul_nonneg (d.hw j).le (sq_nonneg (c j-d.meanVector P c j))) (Finset.mem_univ i)
    change d.w i*(c i-d.meanVector P c i)^2≤d.residualVariance P c at hterm
    rw [hz] at hterm
    have hs : (c i-d.meanVector P c i)^2=0 := by
      nlinarith [d.hw i,sq_nonneg (c i-d.meanVector P c i)]
    exact sub_eq_zero.mp (sq_eq_zero_iff.mp hs)
  · intro h
    unfold residualVariance
    apply Finset.sum_eq_zero
    intro i _
    rw [congrFun h i]
    simp

theorem meanVector_idempotent (P : Partition n g) (c : Vec n) :
    d.meanVector P (d.meanVector P c)=d.meanVector P c :=
  d.meanVector_same_report P _ _ (d.meanVector_report P c)

theorem meanVector_secondMoment (P : Partition n g) (c : Vec n) :
    d.secondMoment (d.meanVector P c)=d.lowerMoment P (d.groupTotal P c) := by
  have hz := (d.residualVariance_zero_iff P (d.meanVector P c)).mpr
    (d.meanVector_idempotent P c).symm
  rw [d.residualVariance_identity,d.meanVector_report] at hz
  linarith

theorem same_report_minimum (P : Partition n g) (c e : Vec n)
    (h : d.groupTotal P e=d.groupTotal P c) :
    d.secondMoment (d.meanVector P c)≤d.secondMoment e := by
  rw [d.meanVector_secondMoment,←h]
  exact d.secondMoment_lower P e

theorem same_report_minimum_eq_iff (P : Partition n g) (c e : Vec n)
    (h : d.groupTotal P e=d.groupTotal P c) :
    d.secondMoment e=d.lowerMoment P (d.groupTotal P c) ↔ e=d.meanVector P c := by
  have hm := d.meanVector_same_report P e c h
  rw [←h,←hm]
  rw [←d.residualVariance_zero_iff,d.residualVariance_identity]
  exact sub_eq_zero.symm

theorem positive_fiber_minimum (P : Partition n g) (c : Vec n) (hc : d.Admissible c) :
    d.Admissible (d.meanVector P c) ∧
    d.groupTotal P (d.meanVector P c)=d.groupTotal P c ∧
    IsLeast (d.secondMoment '' {e | d.Admissible e ∧ d.groupTotal P e=d.groupTotal P c})
      (d.lowerMoment P (d.groupTotal P c)) := by
  refine ⟨d.meanVector_admissible P c hc,d.meanVector_report P c,?_,?_⟩
  · exact ⟨d.meanVector P c,⟨d.meanVector_admissible P c hc,d.meanVector_report P c⟩,
      d.meanVector_secondMoment P c⟩
  · rintro x ⟨e,he,rfl⟩
    rw [←he.2]
    exact d.secondMoment_lower P e

end CommodityClassification.Precision.Data
