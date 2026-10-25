module

public import LeanMath.CommodityClassification.PrecisionCellVariance

/-! Exact finite sign capacity, attainment, bounds and singleton groups. -/
@[expose] public section
noncomputable section
set_option maxHeartbeats 1600000
namespace CommodityClassification.Precision.Data
open InputCoordinates
open scoped BigOperators
variable {n g : ℕ} (d : Precision.Data n)

def signSquaredTotals (P : Partition n g) (a : Fin g) : Set ℝ :=
  (fun s => (d.groupTotal P s a)^2) '' Precision.Box.signs n
def leastSignSquare (P : Partition n g) (a : Fin g) : ℝ := sInf (d.signSquaredTotals P a)
def cellCapacity (P : Partition n g) (a : Fin g) : ℝ :=
  d.groupWeight P a-d.leastSignSquare P a/d.groupWeight P a
def totalCapacity (P : Partition n g) : ℝ := ∑a,d.cellCapacity P a

theorem signSquaredTotals_finite (P : Partition n g) (a : Fin g) :
    (d.signSquaredTotals P a).Finite := Precision.Box.signs_finite.image _

theorem signSquaredTotals_nonempty (P : Partition n g) (a : Fin g) :
    (d.signSquaredTotals P a).Nonempty := Precision.Box.signs_nonempty.image _

theorem leastSignSquare_isLeast (P : Partition n g) (a : Fin g) :
    IsLeast (d.signSquaredTotals P a) (d.leastSignSquare P a) :=
  (d.signSquaredTotals_nonempty P a).isLeast_csInf (d.signSquaredTotals_finite P a)

theorem cellVariance_at_sign (P : Partition n g) (a : Fin g) (s : Vec n)
    (hs : s∈Precision.Box.signs n) :
    d.cellVariance P a s=d.groupWeight P a-(d.groupTotal P s a)^2/d.groupWeight P a := by
  rw [d.cellVariance_formula]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  rcases (Precision.Box.signs_iff s).mp hs i with hi|hi <;> rw [hi] <;> ring

theorem capacity_attained_at_sign (P : Partition n g) (a : Fin g) :
    ∃s∈Precision.Box.signs n,d.cellVariance P a s=d.cellCapacity P a := by
  obtain ⟨s,hs,he⟩ := (d.leastSignSquare_isLeast P a).1
  refine ⟨s,hs,?_⟩
  rw [d.cellVariance_at_sign P a s hs]
  change (d.groupTotal P s a)^2=d.leastSignSquare P a at he
  rw [he]
  rfl

theorem cellVariance_le_capacity (P : Partition n g) (a : Fin g) (c : Vec n)
    (hc : ∀i,|c i|≤1) : d.cellVariance P a c≤d.cellCapacity P a := by
  obtain ⟨s,hs,hv⟩ := d.cellVariance_dominated_by_sign P a c hc
  have hmin := (d.leastSignSquare_isLeast P a).2 ⟨s,hs,rfl⟩
  have hh := div_le_div_of_nonneg_right hmin (d.groupWeight_pos P a).le
  rw [d.cellVariance_at_sign P a s hs] at hv
  unfold cellCapacity
  linarith

theorem capacity_isGreatest (P : Partition n g) (a : Fin g) :
    IsGreatest (d.cellVariance P a '' {c | ∀i,|c i|≤1}) (d.cellCapacity P a) := by
  constructor
  · obtain ⟨s,hs,hv⟩ := d.capacity_attained_at_sign P a
    exact ⟨s,Precision.Box.signs_mem_box s hs,hv⟩
  · rintro x ⟨c,hc,rfl⟩
    exact d.cellVariance_le_capacity P a c hc

theorem cellCapacity_bounds (P : Partition n g) (a : Fin g) :
    0≤d.cellCapacity P a ∧ d.cellCapacity P a≤d.groupWeight P a := by
  obtain ⟨s,hs,hv⟩ := d.capacity_attained_at_sign P a
  constructor
  · rw [←hv]
    exact d.cellVariance_nonneg P a s
  · rw [←hv,d.cellVariance_at_sign P a s hs]
    exact sub_le_self _ (div_nonneg (sq_nonneg _) (d.groupWeight_pos P a).le)

theorem cellVariance_singleton (P : Partition n g) (a : Fin g) (i : Fin n)
    (ha : P.cell a={i}) (c : Vec n) : d.cellVariance P a c=0 := by
  rw [d.cellVariance_formula]
  simp only [groupTotal,groupWeight,ha,Finset.sum_singleton]
  field_simp [(d.hw i).ne']
  ring

theorem cellCapacity_singleton (P : Partition n g) (a : Fin g) (i : Fin n)
    (ha : P.cell a={i}) : d.cellCapacity P a=0 := by
  obtain ⟨s,_,hs⟩ := d.capacity_attained_at_sign P a
  rw [←hs,d.cellVariance_singleton P a i ha]

theorem cell_signs_extend (P : Partition n g) (a : Fin g) (c : Vec n)
    (hc : ∀i∈P.cell a,c i= -1 ∨ c i=1) :
    ∃s∈Precision.Box.signs n,d.groupTotal P s a=d.groupTotal P c a := by
  let s : Vec n := fun i => if i∈P.cell a then c i else 1
  refine ⟨s,(Precision.Box.signs_iff s).mpr ?_,?_⟩
  · intro i
    by_cases hi : i∈P.cell a
    · simpa only [s,ite_eq_left hi] using hc i hi
    · right
      simp only [s,ite_eq_right hi]
  · unfold groupTotal
    apply Finset.sum_congr rfl
    intro i hi
    simp only [s,ite_eq_left hi]

theorem signSquaredTotals_eq_cell_signs (P : Partition n g) (a : Fin g) :
    d.signSquaredTotals P a=(fun c => (d.groupTotal P c a)^2) ''
      {c : Vec n | ∀i∈P.cell a,c i= -1 ∨ c i=1} := by
  ext x
  constructor
  · rintro ⟨s,hs,rfl⟩
    exact ⟨s,fun i _ => (Precision.Box.signs_iff s).mp hs i,rfl⟩
  · rintro ⟨c,hc,rfl⟩
    obtain ⟨s,hs,hj⟩ := d.cell_signs_extend P a c hc
    exact ⟨s,hs,congrArg (fun z : ℝ => z^2) hj⟩

theorem cellCapacity_manuscript (P : Partition n g) (a : Fin g) :
    d.cellCapacity P a=d.groupWeight P a-
      sInf ((fun c => (d.groupTotal P c a)^2) ''
        {c : Vec n | ∀i∈P.cell a,c i= -1 ∨ c i=1})/d.groupWeight P a := by
  rw [←d.signSquaredTotals_eq_cell_signs]
  rfl

end CommodityClassification.Precision.Data
