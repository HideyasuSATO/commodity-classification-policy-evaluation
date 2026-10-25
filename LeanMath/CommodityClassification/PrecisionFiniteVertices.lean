module

public import LeanMath.CommodityClassification.PrecisionFiberClosure

/-! Explicit finite candidate enumeration for the closed-fiber second-moment maximum. -/
@[expose] public section
noncomputable section
set_option maxHeartbeats 1600000
namespace CommodityClassification.Precision.Data
open Matrix InputCoordinates
open scoped BigOperators
variable {n g : ℕ} (d : Precision.Data n)

def boundaryCode (x : ℝ) : Fin 3 := if x=-1 then 0 else if x=1 then 1 else 2
def vertexCode (c : Vec n) : Fin n → Fin 3 := fun i => boundaryCode (c i)
def codeBoundary (s : Fin 3) : ℝ := if s=0 then -1 else 1

def decodeVertex (P : Partition n g) (J : Vec g) (s : Fin n → Fin 3) : Vec n :=
  fun i => if s i=0 then -1 else if s i=1 then 1 else
    (J (P.group i)-(∑j∈(P.cell (P.group i)).erase i,d.w j*codeBoundary (s j)))/d.w i

def finiteSearch (P : Partition n g) (J : Vec g) : Set (Vec n) :=
  Set.range (d.decodeVertex P J) ∩ d.closedFiber P J

theorem boundaryCode_zero (x : ℝ) : boundaryCode x=0 ↔ x=-1 := by
  by_cases h : x=-1 <;> by_cases h1 : x=1 <;> norm_num [boundaryCode,h,h1]

theorem boundaryCode_one (x : ℝ) : boundaryCode x=1 ↔ x=1 := by
  by_cases h : x=-1
  · subst x;norm_num [boundaryCode]
  · simp [boundaryCode,h]

theorem boundaryCode_two (x : ℝ) : boundaryCode x=2 ↔ x≠-1 ∧ x≠1 := by
  by_cases h0 : x=-1 <;> by_cases h1 : x=1 <;> norm_num [boundaryCode,h0,h1]

theorem codeBoundary_of_boundary (x : ℝ) (hx : x=-1 ∨ x=1) :
    codeBoundary (boundaryCode x)=x := by
  rcases hx with rfl|rfl <;> norm_num [codeBoundary,boundaryCode]

theorem interior_of_not_boundary (x : ℝ) (hx : |x|≤1) (hm : x≠-1) (hp : x≠1) : |x|<1 := by
  obtain ⟨hlo,hhi⟩ := abs_le.mp hx
  exact abs_lt.mpr ⟨lt_of_le_of_ne hlo (Ne.symm hm),lt_of_le_of_ne hhi hp⟩

theorem vertex_other_boundary (P : Partition n g) (J : Vec g) (c : Vec n)
    (hc : c∈(d.closedFiber P J).extremePoints ℝ) (i j : Fin n)
    (hi : |c i|<1) (hji : j≠i) (hg : P.group i=P.group j) : c j=-1 ∨ c j=1 := by
  by_contra h
  push Not at h
  have hj := interior_of_not_boundary (c j) (hc.1.1 j) h.1 h.2
  exact hji (d.vertex_interior_unique P J c hc i j hg hi hj).symm

theorem decodeVertex_code (P : Partition n g) (J : Vec g) (c : Vec n)
    (hc : c∈(d.closedFiber P J).extremePoints ℝ) : d.decodeVertex P J (vertexCode c)=c := by
  ext i
  by_cases hm : c i=-1
  · have hcode : vertexCode c i=0 := (boundaryCode_zero (c i)).mpr hm
    simp only [decodeVertex,hcode,ite_true,hm]
  by_cases hp : c i=1
  · have hcode : vertexCode c i=1 := (boundaryCode_one (c i)).mpr hp
    simp only [decodeVertex,hcode,show (1:Fin 3)≠0 by decide,ite_false,ite_true,hp]
  have hi := interior_of_not_boundary (c i) (hc.1.1 i) hm hp
  have he : (∑j∈(P.cell (P.group i)).erase i,d.w j*codeBoundary (vertexCode c j))=
      ∑j∈(P.cell (P.group i)).erase i,d.w j*c j := by
    apply Finset.sum_congr rfl
    intro j hj
    obtain ⟨hji,hjg⟩ := Finset.mem_erase.mp hj
    have hbound := d.vertex_other_boundary P J c hc i j hi hji
      ((P.mem_cell (P.group i) j).mp hjg).symm
    rw [vertexCode,codeBoundary_of_boundary (c j) hbound]
  have hsum := Finset.sum_erase_add (P.cell (P.group i)) (fun j => d.w j*c j)
    ((P.mem_cell (P.group i) i).mpr rfl)
  have hJ : d.groupTotal P c (P.group i)=J (P.group i) := congrFun hc.1.2 _
  change (∑j∈(P.cell (P.group i)).erase i,d.w j*c j)+d.w i*c i=d.groupTotal P c (P.group i) at hsum
  rw [hJ] at hsum
  have hcode : vertexCode c i=2 := (boundaryCode_two (c i)).mpr ⟨hm,hp⟩
  simp only [decodeVertex,hcode,show (2:Fin 3)≠0 by decide,show (2:Fin 3)≠1 by decide,ite_false]
  rw [he]
  apply (div_eq_iff (d.hw i).ne').mpr
  linarith

theorem vertexCode_injective (P : Partition n g) (J : Vec g) :
    Set.InjOn vertexCode ((d.closedFiber P J).extremePoints ℝ) := by
  intro c hc e he hcode
  calc
    c=d.decodeVertex P J (vertexCode c) := (d.decodeVertex_code P J c hc).symm
    _=d.decodeVertex P J (vertexCode e) := by rw [hcode]
    _=e := d.decodeVertex_code P J e he

theorem closedFiber_vertices_finite (P : Partition n g) (J : Vec g) :
    ((d.closedFiber P J).extremePoints ℝ).Finite :=
  Set.Finite.of_injOn (t := Set.univ) (fun _ _ => Set.mem_univ _)
    (d.vertexCode_injective P J) (Set.toFinite _)

theorem finiteSearch_finite (P : Partition n g) (J : Vec g) : (d.finiteSearch P J).Finite :=
  (Set.finite_range (d.decodeVertex P J)).subset Set.inter_subset_left

theorem vertex_mem_finiteSearch (P : Partition n g) (J : Vec g) (c : Vec n)
    (hc : c∈(d.closedFiber P J).extremePoints ℝ) : c∈d.finiteSearch P J :=
  ⟨⟨vertexCode c,d.decodeVertex_code P J c hc⟩,hc.1⟩

theorem finiteSearch_global_maximum (P : Partition n g) (c : Vec n) (hc : d.Admissible c) :
    ∃e∈d.finiteSearch P (d.groupTotal P c),
      IsMaxOn d.secondMoment (d.closedFiber P (d.groupTotal P c)) e ∧
      IsGreatest (d.secondMoment '' d.finiteSearch P (d.groupTotal P c)) (d.secondMoment e) := by
  obtain ⟨e,he,hm⟩ := d.closedFiber_vertex_maximum P c hc
  have hs := d.vertex_mem_finiteSearch P _ e he
  refine ⟨e,hs,hm,⟨e,hs,rfl⟩,?_⟩
  rintro x ⟨a,ha,rfl⟩
  exact hm ha.2

end CommodityClassification.Precision.Data
