module

public import LeanMath.CommodityClassification.RobustMarginNeighborhood

/-! Production substitution is an independent unknown parameter; all other primitives stay fixed. -/
@[expose] public section
noncomputable section
namespace CommodityClassification.Precision.Data
open Matrix InputCoordinates Information
variable {n : ℕ} (d : Precision.Data n)

def withSigma (s : ℝ) (hs : 0<s) : Precision.Data n := {d with sigma:=s,hsigma:=hs}

def sigmaWelfare (s : ℝ) (c : Vec n) : ℝ :=
  1-d.lossScale*(d.theta c)^2/d.denominator s (d.secondMoment c) ((d.theta c)^2)

def sigmaDomain (l u : ℝ) : Set (Vec n×ℝ) := {x | d.Admissible x.1 ∧ x.2∈Set.Icc l u}
def sigmaValues (l u : ℝ) (c : Vec n) : Set ℝ := (fun s => d.sigmaWelfare s c) '' Set.Icc l u

theorem withSigma_admissible (s : ℝ) (hs : 0<s) (c : Vec n) :
    (d.withSigma s hs).Admissible c ↔ d.Admissible c := Iff.rfl

theorem withSigma_welfare (s : ℝ) (hs : 0<s) (c : Vec n) :
    (d.withSigma s hs).normalizedWelfare c=d.sigmaWelfare s c := rfl

theorem withSigma_actual_coefficient (s : ℝ) (hs : 0<s) (c : Vec n) (hc : d.Admissible c) :
    ((d.withSigma s hs).family.model ((d.withSigma s hs).candidate c hc)).lossCoefficient/d.nu=
      d.sigmaWelfare s c := (d.withSigma s hs).actual_normalized_coefficient c hc

theorem sigmaWelfare_bounds (s : ℝ) (hs : 0<s) (c : Vec n) (hc : d.Admissible c) :
    0≤d.sigmaWelfare s c ∧ d.sigmaWelfare s c≤1 :=
  (d.withSigma s hs).normalizedWelfare_bounds c hc

theorem sigmaDomain_nonempty (l u : ℝ) (hlu : l≤u) : (d.sigmaDomain l u).Nonempty :=
  ⟨(0,l),d.zero_admissible,le_rfl,hlu⟩

theorem sigmaDomain_bounded (l u : ℝ) (hl : 0<l) :
    BoundedValues (d.sigmaDomain l u) (fun x => d.sigmaWelfare x.2 x.1) := by
  constructor
  · refine ⟨1,?_⟩
    rintro z ⟨x,hx,rfl⟩
    exact (d.sigmaWelfare_bounds x.2 (hl.trans_le hx.2.1) x.1 hx.1).2
  · refine ⟨0,?_⟩
    rintro z ⟨x,hx,rfl⟩
    exact (d.sigmaWelfare_bounds x.2 (hl.trans_le hx.2.1) x.1 hx.1).1

theorem sigmaWelfare_moment_sufficient (s : ℝ) (c e : Vec n)
    (hO : d.momentReport c=d.momentReport e) : d.sigmaWelfare s c=d.sigmaWelfare s e := by
  have ht : d.theta c=d.theta e := congrArg Prod.fst hO
  have hq : d.secondMoment c=d.secondMoment e := congrArg Prod.snd hO
  simp only [sigmaWelfare,ht,hq]

end CommodityClassification.Precision.Data
