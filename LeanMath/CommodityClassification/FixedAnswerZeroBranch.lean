module

public import LeanMath.CommodityClassification.FixedAnswer

/-!
# Fixed-answer congruence: zero-load branch




-/

public section

namespace CommodityClassification.FixedAnswer

open Matrix
open scoped BigOperators Topology

variable {n k r : ℕ}

/-- The load depends affinely on the hidden coordinates. -/
theorem Data.m_point (a : Data n k r) (Z : Mat r k) :
    a.m (a.point Z) = a.m₀ + Z.transpose *ᵥ a.r_N := by
  simp only [Data.m, Data.point, Data.m₀, Data.r_N, transpose_add,
    transpose_mul, add_mulVec, mulVec_mulVec]

/-- Strict positive definiteness rules out a nonzero vector of zero inverse energy. -/
theorem invQuadratic_eq_zero_iff (M : Mat k k) (hM : M.PosDef) (x : Vec k) :
    dotProduct x (M⁻¹ *ᵥ x) = 0 ↔ x = 0 := by
  constructor
  · intro hzero
    by_contra hx
    have hpos : 0 < dotProduct x (M⁻¹ *ᵥ x) := by
      simpa using hM.inv.dotProduct_mulVec_pos hx
    exact (ne_of_gt hpos) hzero
  · rintro rfl
    simp

/-- The preceding matrix fact, specialized to the manuscript's F and m. -/
theorem Data.F_eq_zero_iff (a : Data n k r) (C : Mat n k)
    (hK : (a.K C).PosDef) : a.F C = 0 ↔ a.m C = 0 :=
  invQuadratic_eq_zero_iff (a.K C) hK (a.m C)

/-- A neighborhood of the zero matrix tests every component of a vector.
The row dimension may be zero; a positive column dimension is essential. -/
theorem vector_eq_zero_of_transpose_mulVec_on_open
    (hk : 0 < k) (U : Set (Mat r k)) (hU : IsOpen U)
    (h0 : (0 : Mat r k) ∈ U) (v : Vec r)
    (hv : ∀ Z ∈ U, Z.transpose *ᵥ v = 0) : v = 0 := by
  classical
  ext i
  let j : Fin k := ⟨0, hk⟩
  let E : Mat r k := fun row _ => if row = i then 1 else 0
  have hcont : Continuous (fun t : ℝ => t • E) :=
    continuous_pi fun row => continuous_pi fun col =>
      continuous_id.mul continuous_const
  have hpre : IsOpen {t : ℝ | t • E ∈ U} := hU.preimage hcont
  have hmem : (0 : ℝ) ∈ {t : ℝ | t • E ∈ U} := by simpa using h0
  obtain ⟨l, u, hlu, hsub⟩ :=
    mem_nhds_iff_exists_Ioo_subset.mp (hpre.mem_nhds hmem)
  obtain ⟨t, ht, htu⟩ := exists_between hlu.2
  have htU : t • E ∈ U := hsub ⟨lt_trans hlu.1 ht, htu⟩
  have hcoord := congrFun (hv (t • E) htU) j
  change (∑ row : Fin r, (t * (if row = i then 1 else 0)) * v row) = 0 at hcoord
  have hmul : t * v i = 0 := by
    simpa [mul_ite, ite_mul] using hcoord
  exact (mul_eq_zero.mp hmul).resolve_left (ne_of_gt ht)

/-- B1.ZERO_BRANCH, with exactly the previously declared hypotheses. -/
theorem zeroLoad_constantOn_iff (a : Data n k r) (U : Set (Mat r k))
    (h : a.Hypotheses U) (hm₀ : a.m₀ = 0) :
    a.ConstantOn U ↔ a.r_N = 0 := by
  have hbase : a.F a.C₀ = 0 := by
    change dotProduct a.m₀ ((a.K₀)⁻¹ *ᵥ a.m₀) = 0
    simp [hm₀]
  constructor
  · intro hconstant
    apply vector_eq_zero_of_transpose_mulVec_on_open
      h.relative_dimension_positive U h.domain_open h.origin_mem a.r_N
    intro Z hZ
    have hF : a.F (a.point Z) = 0 := (hconstant Z hZ).trans hbase
    have hm : a.m (a.point Z) = 0 :=
      (a.F_eq_zero_iff (a.point Z) (h.K_posDef Z hZ)).mp hF
    simpa only [Data.m_point, hm₀, zero_add] using hm
  · intro hr Z _hZ
    have hm : a.m (a.point Z) = 0 := by
      simp only [Data.m_point, hm₀, hr, mulVec_zero, add_zero]
    rw [hbase]
    simp [Data.F, hm]

/-- Explicit specialization showing that zero hidden dimension is retained. -/
theorem zeroLoad_noHiddenDirections (a : Data n k 0) (U : Set (Mat 0 k))
    (h : a.Hypotheses U) (hm₀ : a.m₀ = 0) : a.ConstantOn U := by
  apply (zeroLoad_constantOn_iff a U h hm₀).mpr
  ext i
  exact Fin.elim0 i

end CommodityClassification.FixedAnswer
