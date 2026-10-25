module

public import LeanMath.CommodityClassification.PrecisionPrimitives

/-! Exact equivalence of the structured input box and the positive GE candidate class. -/
@[expose] public section
noncomputable section
set_option maxHeartbeats 1200000
namespace CommodityClassification.Precision.Data
open Matrix InputCoordinates
open scoped BigOperators
variable {n : ℕ} (d : Precision.Data n)

def parent : Partition n 1 where
  group := fun _ => 0
  onto := by intro a;exact ⟨⟨0,d.goods_nonempty⟩,Subsingleton.elim _ _⟩

theorem reconstruct_inputs (c : Vec n) :
    Supply.Example.frame.reconstruct d.prices (d.coordinates c)=d.inputs c := by
  have hw : d.inputs c *ᵥ Supply.Example.frame.w=d.prices := by
    ext i
    simp [inputs,Supply.Example.frame,prices,Matrix.mulVec,dotProduct,Fin.sum_univ_succ]
    ring
  have hv : d.inputs c*Supply.Example.frame.V=d.coordinates c := by
    ext i j;fin_cases j
    change (∑r : Fin 2,d.inputs c i r*Supply.Example.frame.V r 0)=c i
    simp [inputs,Supply.Example.frame,Fin.sum_univ_succ]
    ring
  rw [←hw,←hv]
  exact Supply.Example.frame.reconstruct_original (d.inputs c)

theorem inputs_positive_iff (c : Vec n) : Positive (d.inputs c) ↔ ∀i,|c i|<1 := by
  constructor
  · intro hi i
    have h0 := hi i 0
    have h1 := hi i 1
    norm_num [inputs] at h0 h1
    exact abs_lt.mpr ⟨by linarith,by linarith⟩
  · intro hc i j
    obtain ⟨hlo,hhi⟩ := abs_lt.mp (hc i)
    fin_cases j <;> norm_num [inputs] <;> linarith

theorem parent_report (c : Vec n) :
    d.parent.report d.w (d.coordinates c)=![![∑i,d.w i*c i]] := by
  ext a j;fin_cases a;fin_cases j
  simp [Partition.report,Partition.Q,parent,coordinates,Matrix.mul_apply,Matrix.transpose_apply]

theorem coordinates_candidate_iff (c : Vec n) :
    d.coordinates c∈Supply.Example.frame.Candidates d.prices d.w d.parent 0 ↔ d.Admissible c := by
  constructor
  · intro hc
    have hp : Positive (d.inputs c) := by
      rw [←d.reconstruct_inputs c];exact hc.1
    refine ⟨(d.inputs_positive_iff c).mp hp,?_⟩
    have hh := congrFun (congrFun hc.2 0) 0
    rw [d.parent_report] at hh
    exact hh
  · intro hc
    refine ⟨?_,?_⟩
    · change Positive (Supply.Example.frame.reconstruct d.prices (d.coordinates c))
      rw [d.reconstruct_inputs]
      exact (d.inputs_positive_iff c).mpr hc.1
    · rw [d.parent_report,hc.2]
      ext a j;fin_cases a;fin_cases j;rfl

def family : Equilibrium.BenchmarkFamily n 1 1 where
  frame := Supply.Example.frame
  p := d.prices
  q := d.w
  b := d.policy
  D := d.demand
  sigma := d.sigma
  parents := d.parent
  report := 0
  reference := d.coordinates 0
  reference_mem := (d.coordinates_candidate_iff 0).mpr d.zero_admissible
  hp := fun _ => zero_lt_one
  hq := d.hw
  hw := by intro j;fin_cases j <;> norm_num [Supply.Example.frame]
  ha0 := by intro j;fin_cases j <;> norm_num [Supply.Example.frame]
  hD := d.demand_posDef
  hsigma := d.hsigma

def candidate (c : Vec n) (hc : d.Admissible c) : d.family.Candidate :=
  ⟨d.coordinates c,(d.coordinates_candidate_iff c).mpr hc⟩

theorem candidate_coordinates (C : d.family.Candidate) : d.coordinates (fun i => C.val i 0)=C.val := by
  ext i j;fin_cases j;rfl

theorem candidate_admissible (C : d.family.Candidate) : d.Admissible (fun i => C.val i 0) := by
  apply (d.coordinates_candidate_iff _).mp
  rw [d.candidate_coordinates C]
  exact C.property

theorem balanced_totalInputs (c : Vec n) (hc : d.Admissible c) :
    Supply.totalInputs d.w (d.inputs c)=![1/2,1/2] := by
  ext j;fin_cases j
  · change (∑i,d.w i*((1+c i)/2))=(1/2 : ℝ)
    calc
      _=((∑i,d.w i)+(∑i,d.w i*c i))/2 := by
        rw [←Finset.sum_add_distrib,Finset.sum_div]
        apply Finset.sum_congr rfl
        intro i _;ring
      _=_ := by rw [d.sum_w,hc.2];ring
  · change (∑i,d.w i*((1-c i)/2))=(1/2 : ℝ)
    calc
      _=((∑i,d.w i)-(∑i,d.w i*c i))/2 := by
        rw [←Finset.sum_sub_distrib,Finset.sum_div]
        apply Finset.sum_congr rfl
        intro i _;ring
      _=_ := by rw [d.sum_w,hc.2];ring

theorem fixed_R : d.family.fixedR=![![1]] := by
  change Supply.knownR Supply.Example.frame.w Supply.Example.frame.V
    (Supply.totalInputs d.w (Supply.Example.frame.reconstruct d.prices (d.coordinates 0)))=_
  rw [d.reconstruct_inputs,d.balanced_totalInputs 0 d.zero_admissible]
  ext i j;fin_cases i;fin_cases j
  change (∑r : Fin 2,(∑s : Fin 2,Supply.Example.frame.V s 0 *
    (diagonal (fun k : Fin 2 => ![1/2,1/2] k / Supply.Example.frame.w k)) s r)*
      Supply.Example.frame.V r 0)=1
  norm_num [Supply.Example.frame,Matrix.diagonal,Fin.sum_univ_succ]

end CommodityClassification.Precision.Data
