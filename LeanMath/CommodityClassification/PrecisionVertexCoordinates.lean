module

public import LeanMath.CommodityClassification.PrecisionClosedMaximum
public import LeanMath.CommodityClassification.WeightedExchangeSpanning

/-! A closed-fiber vertex has at most one strictly interior input coordinate per cell. -/
@[expose] public section
noncomputable section
set_option maxHeartbeats 1400000
namespace CommodityClassification.Precision.Data
open Matrix InputCoordinates
open scoped BigOperators
variable {n g : ℕ} (d : Precision.Data n)

theorem groupTotal_mulVec (P : Partition n g) (c : Vec n) :
    d.groupTotal P c=(P.Q d.w).transpose *ᵥ c := by
  ext a
  simp [groupTotal,Partition.cell,Partition.Q,Matrix.mulVec,dotProduct,
    Matrix.transpose_apply,Finset.sum_filter,ite_mul]

theorem groupTotal_add (P : Partition n g) (c e : Vec n) :
    d.groupTotal P (c+e)=d.groupTotal P c+d.groupTotal P e := by
  simp only [d.groupTotal_mulVec,Matrix.mulVec_add]

theorem groupTotal_sub (P : Partition n g) (c e : Vec n) :
    d.groupTotal P (c-e)=d.groupTotal P c-d.groupTotal P e := by
  simp only [d.groupTotal_mulVec,Matrix.mulVec_sub]

theorem groupTotal_smul (P : Partition n g) (c : Vec n) (t : ℝ) :
    d.groupTotal P (t • c)=t • d.groupTotal P c := by
  simp only [d.groupTotal_mulVec,Matrix.mulVec_smul]

theorem interior_exchange (P : Partition n g) (J : Vec g) (c : Vec n)
    (hc : c∈d.closedFiber P J) (i j : Fin n) (hne : i≠j)
    (hg : P.group i=P.group j) (hi : |c i|<1) (hj : |c j|<1) :
    ∃u : Vec n,u≠0 ∧ c+u∈d.closedFiber P J ∧ c-u∈d.closedFiber P J := by
  let t : ℝ := min ((1-|c i|)*d.w i) ((1-|c j|)*d.w j)/2
  have hi0 : 0<(1-|c i|)*d.w i := mul_pos (by linarith) (d.hw i)
  have hj0 : 0<(1-|c j|)*d.w j := mul_pos (by linarith) (d.hw j)
  have ht : 0<t := div_pos (lt_min hi0 hj0) (by norm_num)
  have hti : t/d.w i≤1-|c i| := by
    apply (div_le_iff₀ (d.hw i)).mpr
    have h := min_le_left ((1-|c i|)*d.w i) ((1-|c j|)*d.w j)
    dsimp [t]
    linarith
  have htj : t/d.w j≤1-|c j| := by
    apply (div_le_iff₀ (d.hw j)).mpr
    have h := min_le_right ((1-|c i|)*d.w i) ((1-|c j|)*d.w j)
    dsimp [t]
    linarith
  let u : Vec n := t • weightedExchange d.w i j
  have hui : u i=t/d.w i := by
    simp [u,weightedExchange,hne,div_eq_mul_inv]
  have huj : u j=-(t/d.w j) := by
    simp [u,weightedExchange,Ne.symm hne,div_eq_mul_inv]
  have hu0 : u≠0 := by
    intro hz
    have hpos : 0<u i := hui ▸ div_pos ht (d.hw i)
    rw [hz] at hpos
    exact (lt_irrefl 0) hpos
  have hbox : ∀l,|c l|+|u l|≤1 := by
    intro l
    by_cases hli : l=i
    · subst l
      rw [hui,abs_of_pos (div_pos ht (d.hw i))]
      linarith
    by_cases hlj : l=j
    · subst l
      rw [huj,abs_neg,abs_of_pos (div_pos ht (d.hw j))]
      linarith
    have hz : u l=0 := by
      simp [u,weightedExchange,hli,hlj]
    rw [hz,abs_zero,add_zero]
    exact hc.1 l
  have hreport : d.groupTotal P u=0 := by
    rw [d.groupTotal_mulVec]
    change (P.Q d.w).transpose *ᵥ (t • weightedExchange d.w i j)=0
    rw [Matrix.mulVec_smul,P.weighted_exchange_hidden d.w d.hw i j hg,smul_zero]
  refine ⟨u,hu0,⟨?_,?_⟩,⟨?_,?_⟩⟩
  · intro l
    exact (abs_add_le (c l) (u l)).trans (hbox l)
  · rw [d.groupTotal_add,hreport,add_zero]
    exact hc.2
  · intro l
    calc
      |(c-u) l|=|c l+(-u l)| := rfl
      _≤|c l|+|-u l| := abs_add_le _ _
      _=|c l|+|u l| := by rw [abs_neg]
      _≤1 := hbox l
  · rw [d.groupTotal_sub,hreport,sub_zero]
    exact hc.2

theorem vertex_interior_unique (P : Partition n g) (J : Vec g) (c : Vec n)
    (hc : c∈(d.closedFiber P J).extremePoints ℝ) (i j : Fin n)
    (hg : P.group i=P.group j) (hi : |c i|<1) (hj : |c j|<1) : i=j := by
  by_contra hne
  obtain ⟨u,hu,hplus,hminus⟩ := d.interior_exchange P J c hc.1 i j hne hg hi hj
  have he := hc.2 hplus hminus (mem_openSegment_add_sub (𝕜 := ℝ) c u)
  apply hu
  funext l
  have hh := congrFun he l
  change c l+u l=c l at hh
  change u l=0
  linarith

theorem vertex_interior_card (P : Partition n g) (J : Vec g) (c : Vec n)
    (hc : c∈(d.closedFiber P J).extremePoints ℝ) (a : Fin g) :
    ((P.cell a).filter (fun i => |c i|<1)).card≤1 := by
  apply Finset.card_le_one.mpr
  intro i hi j hj
  obtain ⟨hgi,hi⟩ := Finset.mem_filter.mp hi
  obtain ⟨hgj,hj⟩ := Finset.mem_filter.mp hj
  exact d.vertex_interior_unique P J c hc i j
    (((P.mem_cell a i).mp hgi).trans ((P.mem_cell a j).mp hgj).symm) hi hj

theorem closedFiber_maximum_sparse (P : Partition n g) (c : Vec n) (hc : d.Admissible c) :
    ∃e, e∈(d.closedFiber P (d.groupTotal P c)).extremePoints ℝ ∧
      IsMaxOn d.secondMoment (d.closedFiber P (d.groupTotal P c)) e ∧
      ∀a,((P.cell a).filter (fun i => |e i|<1)).card≤1 := by
  obtain ⟨e,he,hm⟩ := d.closedFiber_vertex_maximum P c hc
  exact ⟨e,he,hm,d.vertex_interior_card P _ e he⟩

end CommodityClassification.Precision.Data
