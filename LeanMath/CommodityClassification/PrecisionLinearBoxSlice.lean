module

public import LeanMath.CommodityClassification.PrecisionZeroInformationWidth
public import Mathlib.LinearAlgebra.Dimension.Constructions

/-! Extreme points of a box cut by arbitrary finite linear observations. -/
@[expose] public section
noncomputable section
set_option maxHeartbeats 1400000
namespace CommodityClassification.Precision.Box
open InputCoordinates Filter
open scoped Topology
variable {n r : ℕ}

def slice (L : Vec n →ₗ[ℝ] Vec r) (j : Vec r) : Set (Vec n) :=
  {c | (∀i,|c i|≤1) ∧ L c=j}

def interiors (c : Vec n) : Finset (Fin n) := Finset.univ.filter (fun i => |c i|<1)

theorem mem_interiors (c : Vec n) (i : Fin n) : i∈interiors c ↔ |c i|<1 := by
  simp [interiors]

theorem slice_compact (L : Vec n →ₗ[ℝ] Vec r) (j : Vec r) : IsCompact (slice L j) := by
  have he : slice L j=Set.Icc (fun _ => (-1:ℝ)) (fun _ => (1:ℝ)) ∩ {c | L c=j} := by
    ext c
    change ((∀i,|c i|≤1) ∧ L c=j) ↔ (((∀i,-1≤c i) ∧ ∀i,c i≤1) ∧ L c=j)
    simp only [abs_le,forall_and]
  rw [he]
  exact isCompact_Icc.inter_right (isClosed_eq L.continuous_of_finiteDimensional continuous_const)

theorem supported_small_perturbation (c u : Vec n) (hc : ∀i,|c i|≤1)
    (hs : ∀i,i∉interiors c → u i=0) :
    ∃t : ℝ,0<t ∧ (∀i,|c i+t*u i|≤1) ∧ ∀i,|c i-t*u i|≤1 := by
  have hev : ∀ᶠ t : ℝ in 𝓝 0,∀i,|c i+t*u i|≤1 := by
    apply Filter.eventually_all.mpr
    intro i
    by_cases hi : i∈interiors c
    · have hlt : |c i+(0:ℝ)*u i|<1 := by simpa using (mem_interiors c i).mp hi
      have hcont : ContinuousAt (fun t : ℝ => |c i+t*u i|) 0 := by fun_prop
      exact (hcont.eventually_lt continuousAt_const hlt).mono (fun _ hh => hh.le)
    · have hu := hs i hi
      exact Filter.Eventually.of_forall (fun _ => by simpa only [hu,mul_zero,add_zero] using hc i)
  obtain ⟨δ,hδ,hnear⟩ := Metric.eventually_nhds_iff.mp hev
  refine ⟨δ/2,by positivity,?_,?_⟩
  · apply hnear
    rw [Real.dist_eq,sub_zero,abs_of_pos (by positivity : 0<δ/2)]
    linarith
  · have hneg : dist (-(δ/2)) (0:ℝ)<δ := by
      rw [Real.dist_eq,sub_zero,abs_neg,abs_of_pos (by positivity : 0<δ/2)]
      linarith
    simpa only [neg_mul,sub_eq_add_neg] using hnear hneg

theorem vertex_supported_kernel_zero (L : Vec n →ₗ[ℝ] Vec r) (j : Vec r) (c : Vec n)
    (hc : c∈(slice L j).extremePoints ℝ) (u : Vec n)
    (hs : ∀i,i∉interiors c → u i=0) (hu : L u=0) : u=0 := by
  obtain ⟨t,ht,hplus,hminus⟩ := supported_small_perturbation c u hc.1.1 hs
  have hp : c+t • u∈slice L j := by
    refine ⟨hplus,?_⟩
    rw [map_add,map_smul,hu,smul_zero,add_zero]
    exact hc.1.2
  have hm : c-t • u∈slice L j := by
    refine ⟨hminus,?_⟩
    rw [map_sub,map_smul,hu,smul_zero,sub_zero]
    exact hc.1.2
  have he := hc.2 hp hm (mem_openSegment_add_sub (𝕜 := ℝ) c (t • u))
  funext i
  have hi := congrFun he i
  change c i+t*u i=c i at hi
  change u i=0
  exact (mul_eq_zero.mp (by linarith : t*u i=0)).resolve_left ht.ne'

def supportedExtension (S : Finset (Fin n)) : (S → ℝ) →ₗ[ℝ] Vec n where
  toFun u i := if hi : i∈S then u ⟨i,hi⟩ else 0
  map_add' u v := by ext i; by_cases hi : i∈S <;> simp [hi]
  map_smul' t u := by ext i; by_cases hi : i∈S <;> simp [hi]

theorem supportedExtension_apply (S : Finset (Fin n)) (u : S → ℝ) (i : S) :
    supportedExtension S u i=u i := by simp [supportedExtension,i.property]

theorem supportedExtension_outside (S : Finset (Fin n)) (u : S → ℝ) (i : Fin n) (hi : i∉S) :
    supportedExtension S u i=0 := by simp [supportedExtension,hi]

theorem vertex_restricted_injective (L : Vec n →ₗ[ℝ] Vec r) (j : Vec r) (c : Vec n)
    (hc : c∈(slice L j).extremePoints ℝ) :
    Function.Injective (L.comp (supportedExtension (interiors c))) := by
  apply (LinearMap.ker_eq_bot).mp
  apply LinearMap.ker_eq_bot'.mpr
  intro u hu
  have hz := vertex_supported_kernel_zero L j c hc (supportedExtension (interiors c) u)
    (supportedExtension_outside (interiors c) u) hu
  funext i
  have hi := congrFun hz i
  simpa only [supportedExtension_apply,Pi.zero_apply] using hi

theorem vertex_interior_rank (L : Vec n →ₗ[ℝ] Vec r) (j : Vec r) (c : Vec n)
    (hc : c∈(slice L j).extremePoints ℝ) :
    (interiors c).card≤Module.finrank ℝ (LinearMap.range L) := by
  let F := L.rangeRestrict.comp (supportedExtension (interiors c))
  have hf : Function.Injective F := by
    intro u v huv
    apply vertex_restricted_injective L j c hc
    exact congrArg Subtype.val huv
  have hh := LinearMap.finrank_le_finrank_of_injective hf
  simpa only [Module.finrank_fintype_fun_eq_card,Fintype.card_coe] using hh

theorem vertex_interior_count (L : Vec n →ₗ[ℝ] Vec r) (j : Vec r) (c : Vec n)
    (hc : c∈(slice L j).extremePoints ℝ) : (interiors c).card≤r := by
  have hh := (vertex_interior_rank L j c hc).trans (LinearMap.range L).finrank_le
  simpa only [Module.finrank_fintype_fun_eq_card,Fintype.card_fin] using hh

end CommodityClassification.Precision.Box
