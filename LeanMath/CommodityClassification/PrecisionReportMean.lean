module

public import LeanMath.CommodityClassification.PrecisionConditionalRecovery

/-! Group reports and the strictly positive group-mean candidate in the precision class. -/
@[expose] public section
noncomputable section
set_option maxHeartbeats 1000000
namespace CommodityClassification.Precision.Data
open Matrix InputCoordinates
open scoped BigOperators
variable {n g : ℕ} (d : Precision.Data n)

def groupWeight (P : Partition n g) (a : Fin g) : ℝ := ∑i∈P.cell a,d.w i
def groupTotal (P : Partition n g) (c : Vec n) (a : Fin g) : ℝ := ∑i∈P.cell a,d.w i*c i
def meanVector (P : Partition n g) (c : Vec n) : Vec n :=
  fun i => d.groupTotal P c (P.group i)/d.groupWeight P (P.group i)
def TypeRespecting (P : Partition n g) : Prop := ∃v : Vec g,∀i,d.v i=v (P.group i)

theorem sum_by_partition (P : Partition n g) (f : Vec n) :
    (∑a,∑i∈P.cell a,f i)=∑i,f i := by
  simp only [Partition.cell,Finset.sum_filter]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  simp

theorem groupWeight_pos (P : Partition n g) (a : Fin g) : 0<d.groupWeight P a :=
  Finset.sum_pos (fun i _ => d.hw i) (P.cell_nonempty a)

theorem groupWeight_sales (P : Partition n g) : d.groupWeight P=P.sales d.prices d.w := by
  ext a
  simp [groupWeight,Partition.sales_apply,prices]

theorem groupTotal_report (P : Partition n g) (c : Vec n) (a : Fin g) :
    d.groupTotal P c a=P.report d.w (d.coordinates c) a 0 := by
  rw [Partition.report_apply]
  rfl

theorem coordinates_mean (P : Partition n g) (c : Vec n) :
    d.coordinates (d.meanVector P c)=P.mean d.prices d.w (d.coordinates c) := by
  ext i j;fin_cases j
  simp only [coordinates,meanVector,Partition.mean,prices,groupTotal_report,groupWeight_sales]
  change P.report d.w (d.coordinates c) (P.group i) 0 / P.sales d.prices d.w (P.group i)=
    1 / P.sales d.prices d.w (P.group i)*P.report d.w (d.coordinates c) (P.group i) 0
  ring

theorem meanVector_report (P : Partition n g) (c : Vec n) :
    d.groupTotal P (d.meanVector P c)=d.groupTotal P c := by
  ext a
  rw [d.groupTotal_report,d.coordinates_mean,
    P.mean_report d.prices d.w (fun _ => zero_lt_one) d.hw,←d.groupTotal_report]

theorem meanVector_admissible (P : Partition n g) (c : Vec n) (hc : d.Admissible c) :
    d.Admissible (d.meanVector P c) := by
  let R : Refinement P d.parent := ⟨fun _ => 0,fun _ => rfl⟩
  have h := Supply.Example.frame.mean_candidate d.prices d.w
    (fun _ => zero_lt_one) d.hw R 0 (d.coordinates c) ((d.coordinates_candidate_iff c).mpr hc)
  apply (d.coordinates_candidate_iff _).mp
  rw [d.coordinates_mean]
  exact h.1

theorem meanVector_same_report (P : Partition n g) (c e : Vec n)
    (h : d.groupTotal P c=d.groupTotal P e) : d.meanVector P c=d.meanVector P e := by
  funext i
  change d.groupTotal P c (P.group i)/d.groupWeight P (P.group i)=
    d.groupTotal P e (P.group i)/d.groupWeight P (P.group i)
  rw [h]

theorem theta_from_groups (P : Partition n g) (v : Vec g) (hv : ∀i,d.v i=v (P.group i))
    (c : Vec n) : d.theta c=∑a,v a*d.groupTotal P c a := by
  unfold theta
  rw [←sum_by_partition P (fun i => d.w i*d.v i*c i)]
  apply Finset.sum_congr rfl
  intro a _
  rw [groupTotal,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  rw [hv i,(P.mem_cell a i).mp hi]
  ring

theorem same_report_theta (P : Partition n g) (hP : d.TypeRespecting P) (c e : Vec n)
    (h : d.groupTotal P c=d.groupTotal P e) : d.theta c=d.theta e := by
  obtain ⟨v,hv⟩ := hP
  rw [d.theta_from_groups P v hv,d.theta_from_groups P v hv,h]

theorem meanVector_theta (P : Partition n g) (hP : d.TypeRespecting P) (c : Vec n) :
    d.theta (d.meanVector P c)=d.theta c :=
  d.same_report_theta P hP _ _ (d.meanVector_report P c)

end CommodityClassification.Precision.Data
