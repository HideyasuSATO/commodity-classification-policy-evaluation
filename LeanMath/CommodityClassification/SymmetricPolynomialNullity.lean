module

public import LeanMath.CommodityClassification.MultivariatePolynomialNullity
public import Mathlib.MeasureTheory.Measure.Haar.Unique

/-! Null polynomial zero sets in the actual symmetric-matrix space. -/
@[expose] public section
noncomputable section
namespace CommodityClassification.Genericity
open Matrix FixedAnswer MeasureTheory MeasureTheory.Measure
open scoped Topology
variable {n : ℕ}

local instance (a b : ℕ) : NormedAddCommGroup (Mat a b) :=
  inferInstanceAs (NormedAddCommGroup (Fin a → Fin b → ℝ))
local instance (a b : ℕ) : NormedSpace ℝ (Mat a b) :=
  inferInstanceAs (NormedSpace ℝ (Fin a → Fin b → ℝ))

theorem symmetric_polynomial_zero_null (P : MvPolynomial (SymmetricEntry n) ℝ) (hP : P≠0)
    (μ : Measure (SymmetricDemand n)) [IsAddHaarMeasure μ] :
    μ {D : SymmetricDemand n | MvPolynomial.eval (symmetricCoordinates D) P=0}=0 := by
  let e : SymmetricDemand n ≃ₗ[ℝ] (SymmetricEntry n → ℝ) := symmetricCoordinates
  have hc : Continuous e := symmetricCoordinates_continuous
  have hci : Continuous e.symm := symmetricCoordinates_inverse_continuous
  let _ : IsAddHaarMeasure (Measure.map e μ) := e.toAddEquiv.isAddHaarMeasure_map μ hc hci
  have ha : Measure.map e μ ≪ (volume : Measure (SymmetricEntry n → ℝ)) :=
    absolutelyContinuous_isAddHaarMeasure _ _
  have hz : Measure.map e μ {x : SymmetricEntry n → ℝ | MvPolynomial.eval x P=0}=0 :=
    ha (polynomial_zero_null P hP)
  rw [Measure.map_apply hc.measurable
    (isClosed_eq P.continuous_eval continuous_const).measurableSet] at hz
  exact hz

theorem symmetric_polynomial_empty_interior (P : MvPolynomial (SymmetricEntry n) ℝ) (hP : P≠0)
    (μ : Measure (SymmetricDemand n)) [IsAddHaarMeasure μ] :
    interior {D : SymmetricDemand n | MvPolynomial.eval (symmetricCoordinates D) P=0}=∅ :=
  interior_eq_empty_of_null (symmetric_polynomial_zero_null P hP μ)

theorem symmetric_polynomial_open_dense (P : MvPolynomial (SymmetricEntry n) ℝ) (hP : P≠0)
    (μ : Measure (SymmetricDemand n)) [IsAddHaarMeasure μ] :
    IsOpen {D : SymmetricDemand n | MvPolynomial.eval (symmetricCoordinates D) P≠0} ∧
      Dense {D : SymmetricDemand n | MvPolynomial.eval (symmetricCoordinates D) P≠0} :=
  ⟨(symmetric_polynomial_zero_closed P).isOpen_compl,
    interior_eq_empty_iff_dense_compl.mp (symmetric_polynomial_empty_interior P hP μ)⟩

theorem symmetric_polynomial_ae_nonzero (P : MvPolynomial (SymmetricEntry n) ℝ) (hP : P≠0)
    (μ : Measure (SymmetricDemand n)) [IsAddHaarMeasure μ] :
    ∀ᵐD ∂μ,MvPolynomial.eval (symmetricCoordinates D) P≠0 :=
  compl_mem_ae_iff.mpr (symmetric_polynomial_zero_null P hP μ)

end CommodityClassification.Genericity
