module

public import LeanMath.CommodityClassification.PrecisionSecondMomentMinimum
public import Mathlib.Analysis.Convex.Extreme

/-! Closed report fibers, actual maximum attainment and extremality of maximizers. -/
@[expose] public section
noncomputable section
set_option maxHeartbeats 1200000
namespace CommodityClassification.Precision.Data
open Matrix InputCoordinates
open scoped BigOperators
variable {n g : ℕ} (d : Precision.Data n)

def closedFiber (P : Partition n g) (J : Vec g) : Set (Vec n) :=
  {c | (∀i,|c i|≤1) ∧ d.groupTotal P c=J}

theorem groupTotal_continuous (P : Partition n g) : Continuous (d.groupTotal P) := by
  unfold groupTotal
  fun_prop

theorem secondMoment_continuous : Continuous d.secondMoment := by
  unfold secondMoment
  fun_prop

theorem closedFiber_compact (P : Partition n g) (J : Vec g) : IsCompact (d.closedFiber P J) := by
  have he : d.closedFiber P J=Set.Icc (fun _ => (-1:ℝ)) (fun _ => (1:ℝ)) ∩
      {c | d.groupTotal P c=J} := by
    ext c
    change ((∀i,|c i|≤1) ∧ d.groupTotal P c=J) ↔
      (((∀i,-1≤c i) ∧ ∀i,c i≤1) ∧ d.groupTotal P c=J)
    simp only [abs_le,forall_and]
  rw [he]
  exact isCompact_Icc.inter_right (isClosed_eq (d.groupTotal_continuous P) continuous_const)

theorem admissible_mem_closedFiber (P : Partition n g) (c : Vec n) (hc : d.Admissible c) :
    c∈d.closedFiber P (d.groupTotal P c) := ⟨fun i => (hc.1 i).le,rfl⟩

theorem closedFiber_nonempty (P : Partition n g) (c : Vec n) (hc : d.Admissible c) :
    (d.closedFiber P (d.groupTotal P c)).Nonempty := ⟨c,d.admissible_mem_closedFiber P c hc⟩

theorem closedFiber_maximum (P : Partition n g) (c : Vec n) (hc : d.Admissible c) :
    ∃e∈d.closedFiber P (d.groupTotal P c),IsMaxOn d.secondMoment (d.closedFiber P (d.groupTotal P c)) e :=
  (d.closedFiber_compact P _).exists_isMaxOn (d.closedFiber_nonempty P c hc)
    d.secondMoment_continuous.continuousOn

theorem closedFiber_secondMoment_bounds (P : Partition n g) (J : Vec g)
    (c : Vec n) (hc : c∈d.closedFiber P J) : d.lowerMoment P J≤d.secondMoment c ∧ d.secondMoment c≤1 := by
  constructor
  · rw [←hc.2]
    exact d.secondMoment_lower P c
  · calc
      d.secondMoment c≤∑i,d.w i := by
        apply Finset.sum_le_sum
        intro i _
        have hsq : (c i)^2≤1 := by
          obtain ⟨hl,hh⟩ := abs_le.mp (hc.1 i)
          nlinarith [mul_nonneg (by linarith : 0≤1-c i) (by linarith : 0≤1+c i)]
        nlinarith [d.hw i]
      _=1 := d.sum_w

theorem secondMoment_zero_iff (c : Vec n) : d.secondMoment c=0 ↔ c=0 := by
  constructor
  · intro hz
    funext i
    have hi := Finset.single_le_sum (s := Finset.univ)
      (fun j _ => mul_nonneg (d.hw j).le (sq_nonneg (c j))) (Finset.mem_univ i)
    change d.w i*(c i)^2≤d.secondMoment c at hi
    rw [hz] at hi
    have hs : (c i)^2=0 := by nlinarith [d.hw i,sq_nonneg (c i)]
    exact sq_eq_zero_iff.mp hs
  · intro hc
    subst c
    simp [secondMoment]

theorem secondMoment_convex_identity (x y : Vec n) (a b : ℝ) (hab : a+b=1) :
    d.secondMoment (a • x+b • y)=a*d.secondMoment x+b*d.secondMoment y-
      a*b*d.secondMoment (x-y) := by
  unfold secondMoment
  simp only [Pi.add_apply,Pi.smul_apply,smul_eq_mul,Pi.sub_apply,
    Finset.mul_sum,←Finset.sum_add_distrib,←Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _
  have hb : b=1-a := by linarith
  rw [hb]
  ring

theorem secondMoment_maximizer_extreme (S : Set (Vec n)) (c : Vec n)
    (hc : c∈S) (hmax : IsMaxOn d.secondMoment S c) : c∈S.extremePoints ℝ := by
  refine ⟨hc,?_⟩
  intro x hx y hy hseg
  obtain ⟨a,b,ha,hb,hab,he⟩ := hseg
  have hq := d.secondMoment_convex_identity x y a b hab
  rw [he] at hq
  have hxq := hmax hx
  have hyq := hmax hy
  have hp : 0<a*b := mul_pos ha hb
  have hsum : a*d.secondMoment x+b*d.secondMoment y≤d.secondMoment c := by
    calc
      _≤a*d.secondMoment c+b*d.secondMoment c :=
        add_le_add (mul_le_mul_of_nonneg_left hxq ha.le) (mul_le_mul_of_nonneg_left hyq hb.le)
      _=d.secondMoment c := by rw [←add_mul,hab,one_mul]
  have hz : d.secondMoment (x-y)=0 := by
    nlinarith [d.secondMoment_nonneg (x-y)]
  have hxy := sub_eq_zero.mp ((d.secondMoment_zero_iff (x-y)).mp hz)
  rw [←hxy,←add_smul,hab,one_smul] at he
  exact he

theorem closedFiber_vertex_maximum (P : Partition n g) (c : Vec n) (hc : d.Admissible c) :
    ∃e, e∈(d.closedFiber P (d.groupTotal P c)).extremePoints ℝ ∧
      IsMaxOn d.secondMoment (d.closedFiber P (d.groupTotal P c)) e := by
  obtain ⟨e,he,hm⟩ := d.closedFiber_maximum P c hc
  exact ⟨e,d.secondMoment_maximizer_extreme _ e he hm,hm⟩

end CommodityClassification.Precision.Data
