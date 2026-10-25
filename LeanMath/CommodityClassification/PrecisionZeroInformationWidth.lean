module

public import LeanMath.CommodityClassification.PrecisionObservationWidth

/-! Exact zero widths for sufficient moment information and product input reports. -/
@[expose] public section
noncomputable section
namespace CommodityClassification.Precision.Data
open Matrix InputCoordinates
variable {n : ℕ} (d : Precision.Data n) {A : Type*}

theorem observation_values_singleton (O : Vec n → A) (c : Vec n) (hc : d.Admissible c)
    (hs : ∀e,d.Admissible e → O e=O c → d.normalizedWelfare e=d.normalizedWelfare c) :
    d.observationValues O (O c)={d.normalizedWelfare c} := by
  ext x
  constructor
  · rintro ⟨e,he,rfl⟩
    exact hs e he.1 he.2
  · intro hx
    have hx' : x=d.normalizedWelfare c := hx
    subst x
    exact ⟨c,⟨hc,rfl⟩,rfl⟩

theorem observation_width_zero_iff (O : Vec n → A) (c : Vec n) (hc : d.Admissible c) :
    d.observationAnswerWidth O (O c)=0 ↔
      ∀e,d.Admissible e → O e=O c → d.normalizedWelfare e=d.normalizedWelfare c := by
  constructor
  · intro hz e he hO
    have hh := d.observation_pair_gap_le_width O c e hc he hO
    rw [hz] at hh
    exact (sub_eq_zero.mp (abs_eq_zero.mp (le_antisymm hh (abs_nonneg _)))).symm
  · intro hs
    unfold observationAnswerWidth
    rw [d.observation_values_singleton O c hc hs]
    simp

theorem observationExAnte_zero_iff (O : Vec n → A) :
    d.observationExAnteWidth O=0 ↔
      ∀c e,d.Admissible c → d.Admissible e → O e=O c → d.normalizedWelfare e=d.normalizedWelfare c := by
  constructor
  · intro hz c e hc he hO
    have hh := (d.observationExAnteWidth_le_iff O 0).mp hz.le c hc
    exact (d.observation_width_zero_iff O c hc).mp
      (le_antisymm hh (d.observationAnswerWidth_bounds O c hc).1) e he hO
  · intro hs
    apply le_antisymm _ (d.observationExAnteWidth_bounds O).1
    apply (d.observationExAnteWidth_le_iff O 0).mpr
    intro c hc
    exact ((d.observation_width_zero_iff O c hc).mpr (fun e he hO => hs c e hc he hO)).le

theorem momentReport_answer_zero (c : Vec n) (hc : d.Admissible c) :
    d.observationAnswerWidth d.momentReport (d.momentReport c)=0 :=
  (d.observation_width_zero_iff _ c hc).mpr (fun e _ hO => d.momentReport_sufficient e c hO)

theorem momentReport_exAnte_zero : d.observationExAnteWidth d.momentReport=0 :=
  (d.observationExAnte_zero_iff _).mpr (fun c e _ _ hO => d.momentReport_sufficient e c hO)

theorem productInputs_injective : Function.Injective d.inputs := by
  intro c e hce
  funext i
  have hh := congrFun (congrFun hce i) 0
  change (1+c i)/2=(1+e i)/2 at hh
  linarith

theorem productInputs_answer_zero (c : Vec n) (hc : d.Admissible c) :
    d.observationAnswerWidth d.inputs (d.inputs c)=0 :=
  (d.observation_width_zero_iff _ c hc).mpr (fun _ _ hO => congrArg d.normalizedWelfare (d.productInputs_injective hO))

theorem productInputs_exAnte_zero : d.observationExAnteWidth d.inputs=0 :=
  (d.observationExAnte_zero_iff _).mpr (fun _ _ _ _ hO => congrArg d.normalizedWelfare (d.productInputs_injective hO))

end CommodityClassification.Precision.Data
