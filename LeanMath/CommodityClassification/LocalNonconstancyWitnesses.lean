module

public import LeanMath.CommodityClassification.FixedAnswerOriginalDerivatives
public import LeanMath.CommodityClassification.AllAnswerVariation

/-! Nonzero actual first/second derivatives give changes in every neighborhood. -/
@[expose] public section
noncomputable section
namespace CommodityClassification.FixedAnswer
open Matrix Filter
open scoped Topology
variable {n k r : ℕ}

def ChangesNearZero (f : ℝ → ℝ) : Prop :=
  ∀V : Set ℝ,V∈𝓝 0 → ∃t∈V,f t≠f 0

theorem changesNearZero_of_first (f : ℝ → ℝ) (d : ℝ)
    (hd : HasDerivAt f d 0) (hne : d≠0) : ChangesNearZero f := by
  intro V hV
  by_contra hno
  push Not at hno
  have he : f =ᶠ[𝓝 0] (fun _ => f 0) := by
    filter_upwards [hV] with t ht
    exact hno t ht
  have hz : HasDerivAt f 0 0 := (hasDerivAt_const 0 (f 0)).congr_of_eventuallyEq he
  exact hne (hd.unique hz)

theorem changesNearZero_of_second (f : ℝ → ℝ) (d : ℝ)
    (hd : HasDerivAt (deriv f) d 0) (hne : d≠0) : ChangesNearZero f := by
  intro V hV
  by_contra hno
  push Not at hno
  have he : f =ᶠ[𝓝 0] (fun _ => f 0) := by
    filter_upwards [hV] with t ht
    exact hno t ht
  have he' : deriv f =ᶠ[𝓝 0] (fun _ => (0:ℝ)) := by
    filter_upwards [he.deriv] with t ht
    simpa only [deriv_const] using ht
  have hz : HasDerivAt (deriv f) 0 0 :=
    (hasDerivAt_const 0 (0:ℝ)).congr_of_eventuallyEq he'
  exact hne (hd.unique hz)

def Data.AdmissibleChanges (a : Data n k r) (U : Set (Mat r k)) (Z : Mat r k) : Prop :=
  ∀V : Set ℝ,V∈𝓝 0 → ∃t∈V,t • Z∈U ∧ a.F (a.point (t • Z))≠a.F a.C₀

theorem Data.changes_admissibly (a : Data n k r) (U : Set (Mat r k))
    (hU : IsOpen U) (h0 : (0:Mat r k)∈U) (Z : Mat r k)
    (hchange : ChangesNearZero (a.lineF Z)) : a.AdmissibleChanges U Z := by
  intro V hV
  have hc : Continuous (fun t : ℝ => t • Z) := continuous_id.smul continuous_const
  have hpre : {t : ℝ | t • Z∈U}∈𝓝 0 :=
    hc.continuousAt.preimage_mem_nhds (by simpa only [zero_smul] using hU.mem_nhds h0)
  obtain ⟨t,ht,hh⟩ := hchange (V∩{t | t • Z∈U}) (inter_mem hV hpre)
  refine ⟨t,ht.1,ht.2,?_⟩
  simpa only [Data.lineF,zero_smul,Data.point,Matrix.mul_zero,add_zero] using hh

theorem Data.admissibleChanges_nonzero (a : Data n k r) (U : Set (Mat r k))
    (Z : Mat r k) (hc : a.AdmissibleChanges U Z) (V : Set ℝ) (hV : V∈𝓝 0) :
    ∃t∈V,t≠0 ∧ t • Z∈U ∧ a.F (a.point (t • Z))≠a.F a.C₀ := by
  obtain ⟨t,ht,hU,hF⟩ := hc V hV
  refine ⟨t,ht,?_,hU,hF⟩
  intro ht0
  apply hF
  simp only [ht0,zero_smul,Data.point,Matrix.mul_zero,add_zero]

end CommodityClassification.FixedAnswer
