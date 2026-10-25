module

public import Mathlib.LinearAlgebra.Matrix.PosDef
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.Topology.Instances.Matrix
public import Mathlib.Topology.Algebra.Ring.Real

/-!
# Fixed-answer congruence: definitions

Lemma B.1 is proved in FixedAnswerComplete.







-/

@[expose] public section

namespace CommodityClassification.FixedAnswer

open Matrix

/-- All coefficient spaces are finite-dimensional spaces over the reals. -/
abbrev Mat (rows cols : ℕ) := Matrix (Fin rows) (Fin cols) ℝ

abbrev Vec (dim : ℕ) := Fin dim → ℝ

/-- Fixed data at ONE answer. No positivity or conclusion is built into this data. -/
structure Data (n k r : ℕ) where
  base : Mat k k
  L : Mat n n
  d : Vec n
  C₀ : Mat n k
  N : Mat n r

variable {n k r : ℕ}

namespace Data

/-- Vary only Z, keeping the answer and all the data fixed. -/
def point (a : Data n k r) (Z : Mat r k) : Mat n k := a.C₀ + a.N * Z

def K (a : Data n k r) (C : Mat n k) : Mat k k :=
  a.base + C.transpose * a.L * C

def m (a : Data n k r) (C : Mat n k) : Vec k := C.transpose *ᵥ a.d

/-- Matrix inverse is total in Lean; substantive statements below restrict K to PosDef. -/
noncomputable def F (a : Data n k r) (C : Mat n k) : ℝ :=
  dotProduct (a.m C) ((a.K C)⁻¹ *ᵥ a.m C)

def K₀ (a : Data n k r) : Mat k k := a.K a.C₀
def m₀ (a : Data n k r) : Vec k := a.m a.C₀
noncomputable def y₀ (a : Data n k r) : Vec k := (a.K₀)⁻¹ *ᵥ a.m₀
def A_N (a : Data n k r) : Mat r k := a.N.transpose * a.L * a.C₀
def S_NN (a : Data n k r) : Mat r r := a.N.transpose * a.L * a.N
def r_N (a : Data n k r) : Vec r := a.N.transpose *ᵥ a.d

/-- An open neighborhood in the full hidden-coordinate matrix space. -/
structure Hypotheses (a : Data n k r) (U : Set (Mat r k)) : Prop where
  relative_dimension_positive : 0 < k
  base_symmetric : a.base.transpose = a.base
  L_symmetric : a.L.transpose = a.L
  directions_independent : Function.Injective (fun z : Vec r => a.N *ᵥ z)
  domain_open : IsOpen U
  origin_mem : (0 : Mat r k) ∈ U
  K_posDef : ∀ Z ∈ U, (a.K (a.point Z)).PosDef

/-- Equality to the value at C₀; 0 ∈ U is separately required in Hypotheses. -/
def ConstantOn (a : Data n k r) (U : Set (Mat r k)) : Prop :=
  ∀ Z ∈ U, a.F (a.point Z) = a.F a.C₀

/-- The disjunction of the zero-load and nonzero-load branches. -/
def CongruenceCriterion (a : Data n k r) : Prop :=
  (a.m₀ = 0 ∧ a.r_N = 0) ∨
    (a.m₀ ≠ 0 ∧ a.r_N = a.A_N *ᵥ a.y₀ ∧
      a.S_NN = a.A_N * (a.K₀)⁻¹ * a.A_N.transpose)

/-- Maximal algebraic domain for the global extension; economic admissibility is a subset. -/
def AdmissibleCoordinates (a : Data n k r) : Set (Mat r k) :=
  {Z | (a.K (a.point Z)).PosDef}

end Data

/-- Local equivalence in Lemma B.1. -/
def LemmaB1LocalStatement (a : Data n k r) (U : Set (Mat r k)) : Prop :=
  a.Hypotheses U → (a.ConstantOn U ↔ a.CongruenceCriterion)

/-- Global extension in Lemma B.1. -/
def LemmaB1GlobalStatement (a : Data n k r) (U : Set (Mat r k)) : Prop :=
  a.Hypotheses U → a.CongruenceCriterion →
    a.ConstantOn a.AdmissibleCoordinates

/-- Universal closure for general n, positive k, and possibly zero hidden dimension r. -/
def LemmaB1Statement : Prop :=
  ∀ (n k r : ℕ) (a : Data n k r) (U : Set (Mat r k)),
    LemmaB1LocalStatement a U ∧ LemmaB1GlobalStatement a U

end CommodityClassification.FixedAnswer
