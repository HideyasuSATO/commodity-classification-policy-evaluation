module

public import LeanMath.CommodityClassification.ReportKernelCoordinates

/-! Positive economic candidate fibers and the geometric assumptions of B.1.
The final assembly explicitly takes symmetry and K-positivity as additional hypotheses. -/
@[expose] public section
namespace CommodityClassification.InputCoordinates
open Matrix Filter
open scoped Topology
variable {n k g h r : ℕ}

def Frame.Candidates (e : Frame k) (p q : Vec n) (P0 : Partition n h)
    (J0 : Mat h k) : Set (Mat n k) :=
  {C | C ∈ e.PositiveDomain p ∧ P0.report q C = J0}

def Frame.FixedFiber (e : Frame k) (p q : Vec n) (P0 : Partition n h)
    (J0 : Mat h k) (P : Partition n g) (C0 : Mat n k) : Set (Mat n k) :=
  {C | C ∈ e.Candidates p q P0 J0 ∧ P.report q C = P.report q C0}

def Frame.FiberDomain (e : Frame k) (p : Vec n) {Q : Mat n g}
    (H : HiddenBasis Q r) (C0 : Mat n k) : Set (Mat r k) :=
  {Z | C0 + H.N * Z ∈ e.PositiveDomain p}

theorem Frame.mean_candidate (e : Frame k) (p q : Vec n)
    (hp : ∀ i, 0 < p i) (hq : ∀ i, 0 < q i)
    {P : Partition n g} {P0 : Partition n h} (R : Refinement P P0)
    (J0 : Mat h k) (C : Mat n k) (hC : C ∈ e.Candidates p q P0 J0) :
    P.mean p q C ∈ e.Candidates p q P0 J0 ∧
      P.report q (P.mean p q C) = P.report q C := by
  refine ⟨⟨?_, (R.mean_parent p q hp hq C).trans hC.2⟩, P.mean_report p q hp hq C⟩
  change Positive (e.reconstruct p (P.mean p q C))
  rw [P.reconstruct_mean e p q hp hq C]
  exact P.mean_positive p q hp hq _ hC.1

theorem Frame.fiberDomain_open (e : Frame k) (p : Vec n) {Q : Mat n g}
    (H : HiddenBasis Q r) (C0 : Mat n k) : IsOpen (e.FiberDomain p H C0) := by
  exact (e.positiveDomain_open p).preimage
    (continuous_const.add (continuous_const.matrix_mul continuous_id))

theorem Frame.fiberDomain_zero (e : Frame k) (p : Vec n) {Q : Mat n g}
    (H : HiddenBasis Q r) (C0 : Mat n k) (hC : C0 ∈ e.PositiveDomain p) :
    (0 : Mat r k) ∈ e.FiberDomain p H C0 := by
  simpa only [Frame.FiberDomain, Set.mem_ofPred_eq, Matrix.mul_zero, add_zero] using hC

theorem Frame.fixedFiber_eq_image (e : Frame k) (p q : Vec n)
    {P : Partition n g} {P0 : Partition n h} (R : Refinement P P0)
    (J0 : Mat h k) (C0 : Mat n k) (hC0 : C0 ∈ e.Candidates p q P0 J0)
    (H : HiddenBasis (P.Q q) r) :
    e.FixedFiber p q P0 J0 P C0 =
      (fun Z => C0 + H.N * Z) '' e.FiberDomain p H C0 := by
  ext C
  constructor
  · rintro ⟨hC, hr⟩
    obtain ⟨Z, hZ⟩ := (H.fiber_exists_iff C0 C).mp hr
    refine ⟨Z, ?_, hZ.symm⟩
    change C0 + H.N * Z ∈ e.PositiveDomain p
    rw [← hZ]
    exact hC.1
  · rintro ⟨Z, hZ, rfl⟩
    have hr : P.report q (C0 + H.N*Z) = P.report q C0 := H.report_point C0 Z
    exact ⟨⟨hZ, (R.report_preserved q _ _ hr).trans hC0.2⟩, hr⟩

theorem Frame.fixedFiber_unique (e : Frame k) (p q : Vec n)
    {P : Partition n g} {P0 : Partition n h} (R : Refinement P P0)
    (J0 : Mat h k) (C0 : Mat n k) (hC0 : C0 ∈ e.Candidates p q P0 J0)
    (H : HiddenBasis (P.Q q) r) (C : Mat n k) :
    C ∈ e.FixedFiber p q P0 J0 P C0 ↔
      ∃! Z, Z ∈ e.FiberDomain p H C0 ∧ C = C0 + H.N * Z := by
  constructor
  · intro hc
    obtain ⟨Z, hZ, hu⟩ := (H.fiber_iff C0 C).mp hc.2
    refine ⟨Z, ⟨?_, hZ⟩, fun W hw => hu W hw.2⟩
    change C0 + H.N*Z ∈ e.PositiveDomain p
    rw [← hZ]
    exact hc.1.1
  · rintro ⟨Z, hZ, _⟩
    rw [e.fixedFiber_eq_image p q R J0 C0 hC0 H]
    exact ⟨Z, hZ.1, hZ.2.symm⟩

theorem Frame.small_perturbations (e : Frame k) (p q : Vec n)
    {P : Partition n g} {P0 : Partition n h} (R : Refinement P P0)
    (J0 : Mat h k) (C0 : Mat n k) (hC0 : C0 ∈ e.Candidates p q P0 J0)
    (H : HiddenBasis (P.Q q) r) :
    ∀ᶠ Z : Mat r k in 𝓝 0, C0 + H.N * Z ∈ e.FixedFiber p q P0 J0 P C0 := by
  have hu := (e.fiberDomain_open p H C0).mem_nhds (e.fiberDomain_zero p H C0 hC0.1)
  filter_upwards [hu] with Z hZ
  rw [e.fixedFiber_eq_image p q R J0 C0 hC0 H]
  exact ⟨Z, hZ, rfl⟩

theorem Frame.positive_fiber_inputs (e : Frame k) (p q : Vec n)
    (P : Partition n g) (H : HiddenBasis (P.Q q) r) (C0 : Mat n k)
    (Z : Mat r k) (hZ : Z ∈ e.FiberDomain p H C0) :
    Positive (e.reconstruct p (C0 + H.N * Z)) ∧
    e.reconstruct p (C0 + H.N * Z) *ᵥ e.w = p ∧
    P.report q (e.reconstruct p (C0 + H.N * Z)) =
      P.report q (e.reconstruct p C0) := by
  refine ⟨hZ, e.reconstruct_cost p _, ?_⟩
  apply (P.report_equiv e p q _ _ (e.reconstruct_cost p _) (e.reconstruct_cost p _)).mpr
  rw [e.reconstruct_exposure, e.reconstruct_exposure]
  exact H.report_point C0 Z

theorem Frame.fixedFiber_zeroDim (e : Frame k) (p q : Vec n)
    {P : Partition n g} {P0 : Partition n h} (R : Refinement P P0)
    (J0 : Mat h k) (C0 : Mat n k) (hC0 : C0 ∈ e.Candidates p q P0 J0)
    (H : HiddenBasis (P.Q q) 0) :
    e.FixedFiber p q P0 J0 P C0 = {C0} := by
  rw [e.fixedFiber_eq_image p q R J0 C0 hC0 H]
  ext C
  constructor
  · rintro ⟨Z, _, hZ⟩
    simpa only [H.zeroDim_point, Set.mem_singleton_iff] using hZ.symm
  · intro hc
    have he : C = C0 := Set.mem_singleton_iff.mp hc
    subst C
    exact ⟨0, e.fiberDomain_zero p H C0 hC0.1, H.zeroDim_point C0 0⟩

/-- Construction of the basis and open domain for each realized answer. -/
theorem Frame.exists_open_fiber (e : Frame k) (p q : Vec n)
    {P : Partition n g} {P0 : Partition n h} (R : Refinement P P0)
    (J0 : Mat h k) (C0 : Mat n k) (hC0 : C0 ∈ e.Candidates p q P0 J0) :
    ∃ r, ∃ H : HiddenBasis (P.Q q) r,
      IsOpen (e.FiberDomain p H C0) ∧ (0 : Mat r k) ∈ e.FiberDomain p H C0 ∧
      e.FixedFiber p q P0 J0 P C0 =
        (fun Z => C0 + H.N * Z) '' e.FiberDomain p H C0 := by
  obtain ⟨r, ⟨H⟩⟩ := exists_hiddenBasis (P.Q q)
  exact ⟨r, H, e.fiberDomain_open p H C0, e.fiberDomain_zero p H C0 hC0.1,
    e.fixedFiber_eq_image p q R J0 C0 hC0 H⟩

theorem Frame.singleton_fixedFiber (e : Frame k) (p q : Vec n) (hq : ∀ i, 0 < q i)
    (P0 : Partition n h) (R : Refinement (Partition.singleton n) P0)
    (J0 : Mat h k) (C0 : Mat n k) (hC0 : C0 ∈ e.Candidates p q P0 J0) :
    e.FixedFiber p q P0 J0 (Partition.singleton n) C0 = {C0} := by
  obtain ⟨H⟩ := Partition.singleton_hiddenBasis q hq
  exact e.fixedFiber_zeroDim p q R J0 C0 hC0 H

def b1Data {Q : Mat n g} (H : HiddenBasis Q r) (C0 : Mat n k)
    (base : Mat k k) (L : Mat n n) (d : Vec n) :
    CommodityClassification.FixedAnswer.Data n k r :=
  {base := base, L := L, d := d, C₀ := C0, N := H.N}

/-- The geometric fiber conditions, with explicit symmetry and SPD assumptions. -/
theorem Frame.b1_geometric_assembly (e : Frame k) (p : Vec n) {Q : Mat n g}
    (H : HiddenBasis Q r) (C0 : Mat n k) (hC0 : C0 ∈ e.PositiveDomain p)
    (base : Mat k k) (L : Mat n n) (d : Vec n)
    (hk : 0 < k) (hb : base.transpose = base) (hL : L.transpose = L)
    (hK : ∀ Z ∈ e.FiberDomain p H C0,
      ((b1Data H C0 base L d).K ((b1Data H C0 base L d).point Z)).PosDef) :
    (b1Data H C0 base L d).Hypotheses (e.FiberDomain p H C0) := by
  exact ⟨hk, hb, hL, H.independent, e.fiberDomain_open p H C0,
    e.fiberDomain_zero p H C0 hC0, hK⟩

end CommodityClassification.InputCoordinates
