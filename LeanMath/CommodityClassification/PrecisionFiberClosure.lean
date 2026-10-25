module

public import LeanMath.CommodityClassification.PrecisionEndpointPath

/-! The actual positive-fiber closure and sharp second-moment endpoints. -/
@[expose] public section
noncomputable section
set_option maxHeartbeats 1400000
namespace CommodityClassification.Precision.Data
open Matrix InputCoordinates Filter
open scoped BigOperators Topology
variable {n g : ℕ} (d : Precision.Data n)

def positiveFiber (P : Partition n g) (J : Vec g) : Set (Vec n) :=
  {c | d.Admissible c ∧ d.groupTotal P c=J}

theorem endpointPath_tendsto (P : Partition n g) (c e : Vec n) :
    Tendsto (d.endpointPath P c e) (𝓝[<] (1:ℝ)) (𝓝 e) := by
  have h := (d.endpointPath_continuous P c e).continuousAt.tendsto.mono_left
    (nhdsWithin_le_nhds (a := (1:ℝ)) (s := Set.Iio 1))
  simpa only [d.endpointPath_one] using h

theorem closedFiber_subset_closure_positive (P : Partition n g) (c : Vec n)
    (hc : d.Admissible c) :
    d.closedFiber P (d.groupTotal P c)⊆closure (d.positiveFiber P (d.groupTotal P c)) := by
  intro e he
  apply mem_closure_of_tendsto (d.endpointPath_tendsto P c e)
  have h0 : ∀ᶠt : ℝ in 𝓝[<] (1:ℝ),0≤t :=
    (eventually_ge_nhds (by norm_num : (0:ℝ)<1)).filter_mono nhdsWithin_le_nhds
  filter_upwards [h0,self_mem_nhdsWithin] with t ht ht1
  exact ⟨d.endpointPath_admissible P c e hc he t ht ht1,d.endpointPath_report P c e he.2 t⟩

theorem closure_positiveFiber (P : Partition n g) (c : Vec n) (hc : d.Admissible c) :
    closure (d.positiveFiber P (d.groupTotal P c))=d.closedFiber P (d.groupTotal P c) := by
  apply Set.Subset.antisymm
  · apply closure_minimal _ (d.closedFiber_compact P _).isClosed
    intro e he
    exact ⟨fun i => (he.1.1 i).le,he.2⟩
  · exact d.closedFiber_subset_closure_positive P c hc

theorem positiveFiber_secondMoment_isLUB (P : Partition n g) (c e : Vec n)
    (hc : d.Admissible c) (he : e∈d.closedFiber P (d.groupTotal P c))
    (hm : IsMaxOn d.secondMoment (d.closedFiber P (d.groupTotal P c)) e) :
    IsLUB (d.secondMoment '' d.positiveFiber P (d.groupTotal P c)) (d.secondMoment e) := by
  constructor
  · rintro x ⟨a,ha,rfl⟩
    exact hm ⟨fun i => (ha.1.1 i).le,ha.2⟩
  · intro b hb
    have hec := d.closedFiber_subset_closure_positive P c hc he
    have hmem := mem_closure_image d.secondMoment_continuous.continuousAt hec
    have hsub : d.secondMoment '' d.positiveFiber P (d.groupTotal P c)⊆Set.Iic b := hb
    exact (closure_minimal hsub isClosed_Iic) hmem

theorem positiveFiber_secondMoment_isLeast (P : Partition n g) (c : Vec n) (hc : d.Admissible c) :
    IsLeast (d.secondMoment '' d.positiveFiber P (d.groupTotal P c))
      (d.lowerMoment P (d.groupTotal P c)) := (d.positive_fiber_minimum P c hc).2.2

theorem endpointPath_attains_intermediate (P : Partition n g) (c e : Vec n)
    (hc : d.Admissible c) (he : e∈d.closedFiber P (d.groupTotal P c)) (q : ℝ)
    (hlo : d.lowerMoment P (d.groupTotal P c)≤q) (hhi : q<d.secondMoment e) :
    ∃t : ℝ,0≤t ∧ t<1 ∧ d.endpointPath P c e t∈d.positiveFiber P (d.groupTotal P c) ∧
      d.secondMoment (d.endpointPath P c e t)=q := by
  let Q0 := d.lowerMoment P (d.groupTotal P c)
  let delta := d.secondMoment e-Q0
  have hd : 0<delta := by dsimp [delta,Q0];linarith
  have hx : 0≤(q-Q0)/delta := div_nonneg (by dsimp [Q0];linarith) hd.le
  have hx1 : (q-Q0)/delta<1 := (div_lt_one hd).mpr (by dsimp [delta,Q0];linarith)
  let t := Real.sqrt ((q-Q0)/delta)
  have ht : 0≤t := Real.sqrt_nonneg _
  have ht2 : t^2=(q-Q0)/delta := Real.sq_sqrt hx
  have ht1 : t<1 := by nlinarith
  refine ⟨t,ht,ht1,⟨d.endpointPath_admissible P c e hc he t ht ht1,
    d.endpointPath_report P c e he.2 t⟩,?_⟩
  rw [d.endpointPath_secondMoment P c e he.2 t]
  change Q0+t^2*delta=q
  rw [ht2,div_mul_cancel₀ _ hd.ne']
  ring

theorem positiveFiber_moment_interval (P : Partition n g) (c e : Vec n)
    (hc : d.Admissible c) (he : e∈d.closedFiber P (d.groupTotal P c)) :
    Set.Ico (d.lowerMoment P (d.groupTotal P c)) (d.secondMoment e)⊆
      d.secondMoment '' d.positiveFiber P (d.groupTotal P c) := by
  intro q hq
  obtain ⟨t,_,_,ht,heq⟩ := d.endpointPath_attains_intermediate P c e hc he q hq.1 hq.2
  exact ⟨d.endpointPath P c e t,ht,heq⟩

end CommodityClassification.Precision.Data
