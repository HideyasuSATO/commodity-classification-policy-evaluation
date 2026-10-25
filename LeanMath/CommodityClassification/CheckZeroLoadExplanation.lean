module
import LeanMath.CommodityClassification.ZeroLoadExplanation
open CommodityClassification.FixedAnswer

example {n k r : ℕ} (a : Data n k r) (U : Set (Mat r k))
    (h : a.Hypotheses U) (hm : a.m₀ = 0) (nu : ℝ) :
    (∀ Z ∈ U, nu - a.F (a.point Z) = nu) ↔ a.r_N = 0 :=
  zeroLoad_coefficient_eq_iff a U h hm nu

example {n k : ℕ} (a : Data n k 0) (U : Set (Mat 0 k))
    (h : a.Hypotheses U) (hm : a.m₀ = 0) (nu : ℝ) :
    ∀ Z ∈ U, nu - a.F (a.point Z) = nu :=
  (zeroLoad_coefficient_eq_iff a U h hm nu).mpr (Subsingleton.elim _ _)

#print axioms zeroLoad_coefficient_eq_iff
#print axioms zeroLoad_coefficient_eq_global
