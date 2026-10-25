module
import LeanMath.CommodityClassification.EconomicReportFibers
import LeanMath.CommodityClassification.CheckB1Complete
import LeanMath.CommodityClassification.CheckOriginalDerivatives
import LeanMath.CommodityClassification.CheckZeroLoadExplanation
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum

/-! Integration and axiom audit, with a concrete admissible example.
The preceding theorems apply in general finite dimensions. -/
open CommodityClassification.InputCoordinates Matrix
open scoped BigOperators
namespace CommodityClassification.InputCoordinates.Audit

noncomputable def twoFactorFrame : Frame 1 where
  w := ![1,1]
  a0 := ![1/2,1/2]
  V := ![![1],![-1]]
  normalized := by norm_num [dotProduct, Fin.sum_univ_succ]
  annihilates := by
    ext i
    fin_cases i
    norm_num [Matrix.mulVec, Matrix.transpose_apply, dotProduct, Fin.sum_univ_succ]
    change (1 : ℝ) * (1/2) + (-1) * (1/2) = 0
    norm_num
  independent := by
    intro x y hh
    ext j
    fin_cases j
    have hc := congrFun hh 0
    simpa [Matrix.mulVec, dotProduct, Fin.sum_univ_succ] using hc

example : (twoFactorFrame.PositiveDomain (fun _ : Fin 3 => (1 : ℝ))).Nonempty := by
  apply Frame.positiveDomain_nonempty
  · intro i; norm_num
  · intro j; fin_cases j <;> norm_num [twoFactorFrame]

example (Q : Mat 0 0) : ∃ r, Nonempty (HiddenBasis Q r) := exists_hiddenBasis Q

example {n k g : ℕ} (e : Frame k) (p : Vec n) (Q : Mat n g)
    (H : HiddenBasis Q 0) (C0 : Mat n k) (hC : C0 ∈ e.PositiveDomain p) :
    IsOpen (e.FiberDomain p H C0) ∧ (0 : Mat 0 k) ∈ e.FiberDomain p H C0 :=
  ⟨e.fiberDomain_open p H C0, e.fiberDomain_zero p H C0 hC⟩

end CommodityClassification.InputCoordinates.Audit
set_option pp.universes false

#check @CommodityClassification.InputCoordinates.Frame.B_mulVec
#print axioms CommodityClassification.InputCoordinates.Frame.B_mulVec

#check @CommodityClassification.InputCoordinates.Frame.a0_dot_V
#print axioms CommodityClassification.InputCoordinates.Frame.a0_dot_V

#check @CommodityClassification.InputCoordinates.Frame.B_isUnit
#print axioms CommodityClassification.InputCoordinates.Frame.B_isUnit

#check @CommodityClassification.InputCoordinates.Frame.spans_kernel
#print axioms CommodityClassification.InputCoordinates.Frame.spans_kernel

#check @CommodityClassification.InputCoordinates.Frame.mul_B
#print axioms CommodityClassification.InputCoordinates.Frame.mul_B

#check @CommodityClassification.InputCoordinates.Frame.reconstruct_mul_B
#print axioms CommodityClassification.InputCoordinates.Frame.reconstruct_mul_B

#check @CommodityClassification.InputCoordinates.Frame.reconstruct_cost
#print axioms CommodityClassification.InputCoordinates.Frame.reconstruct_cost

#check @CommodityClassification.InputCoordinates.Frame.reconstruct_exposure
#print axioms CommodityClassification.InputCoordinates.Frame.reconstruct_exposure

#check @CommodityClassification.InputCoordinates.Frame.reconstruct_original
#print axioms CommodityClassification.InputCoordinates.Frame.reconstruct_original

#check @CommodityClassification.InputCoordinates.Frame.coordinates_unique
#print axioms CommodityClassification.InputCoordinates.Frame.coordinates_unique

#check @CommodityClassification.InputCoordinates.Frame.reconstruct_continuous
#print axioms CommodityClassification.InputCoordinates.Frame.reconstruct_continuous

#check @CommodityClassification.InputCoordinates.Frame.positiveDomain_open
#print axioms CommodityClassification.InputCoordinates.Frame.positiveDomain_open

#check @CommodityClassification.InputCoordinates.Frame.reconstruct_combination
#print axioms CommodityClassification.InputCoordinates.Frame.reconstruct_combination

#check @CommodityClassification.InputCoordinates.Frame.positiveDomain_convex
#print axioms CommodityClassification.InputCoordinates.Frame.positiveDomain_convex

#check @CommodityClassification.InputCoordinates.Frame.exposure_continuous
#print axioms CommodityClassification.InputCoordinates.Frame.exposure_continuous

#check @CommodityClassification.InputCoordinates.Frame.positiveDomain_nonempty
#print axioms CommodityClassification.InputCoordinates.Frame.positiveDomain_nonempty

#check @CommodityClassification.InputCoordinates.Partition.mem_cell
#print axioms CommodityClassification.InputCoordinates.Partition.mem_cell

#check @CommodityClassification.InputCoordinates.Partition.cell_nonempty
#print axioms CommodityClassification.InputCoordinates.Partition.cell_nonempty

#check @CommodityClassification.InputCoordinates.Partition.report_apply
#print axioms CommodityClassification.InputCoordinates.Partition.report_apply

#check @CommodityClassification.InputCoordinates.Partition.sales_apply
#print axioms CommodityClassification.InputCoordinates.Partition.sales_apply

#check @CommodityClassification.InputCoordinates.Partition.report_mul
#print axioms CommodityClassification.InputCoordinates.Partition.report_mul

#check @CommodityClassification.InputCoordinates.Partition.report_cost
#print axioms CommodityClassification.InputCoordinates.Partition.report_cost

#check @CommodityClassification.InputCoordinates.Partition.report_equiv
#print axioms CommodityClassification.InputCoordinates.Partition.report_equiv

#check @CommodityClassification.InputCoordinates.Partition.report_reconstruct
#print axioms CommodityClassification.InputCoordinates.Partition.report_reconstruct

#check @CommodityClassification.InputCoordinates.Partition.sales_pos
#print axioms CommodityClassification.InputCoordinates.Partition.sales_pos

#check @CommodityClassification.InputCoordinates.Partition.report_positive
#print axioms CommodityClassification.InputCoordinates.Partition.report_positive

#check @CommodityClassification.InputCoordinates.Partition.mean_positive
#print axioms CommodityClassification.InputCoordinates.Partition.mean_positive

#check @CommodityClassification.InputCoordinates.Partition.mean_report
#print axioms CommodityClassification.InputCoordinates.Partition.mean_report

#check @CommodityClassification.InputCoordinates.Partition.mean_cost
#print axioms CommodityClassification.InputCoordinates.Partition.mean_cost

#check @CommodityClassification.InputCoordinates.Partition.mean_exposure
#print axioms CommodityClassification.InputCoordinates.Partition.mean_exposure

#check @CommodityClassification.InputCoordinates.Partition.reconstruct_mean
#print axioms CommodityClassification.InputCoordinates.Partition.reconstruct_mean

#check @CommodityClassification.InputCoordinates.Refinement.Q_factor
#print axioms CommodityClassification.InputCoordinates.Refinement.Q_factor

#check @CommodityClassification.InputCoordinates.Refinement.report_factor
#print axioms CommodityClassification.InputCoordinates.Refinement.report_factor

#check @CommodityClassification.InputCoordinates.Refinement.report_preserved
#print axioms CommodityClassification.InputCoordinates.Refinement.report_preserved

#check @CommodityClassification.InputCoordinates.Refinement.mean_parent
#print axioms CommodityClassification.InputCoordinates.Refinement.mean_parent

#check @CommodityClassification.InputCoordinates.exists_hiddenBasis
#print axioms CommodityClassification.InputCoordinates.exists_hiddenBasis

#check @CommodityClassification.InputCoordinates.HiddenBasis.annihilates
#print axioms CommodityClassification.InputCoordinates.HiddenBasis.annihilates

#check @CommodityClassification.InputCoordinates.HiddenBasis.mul_injective
#print axioms CommodityClassification.InputCoordinates.HiddenBasis.mul_injective

#check @CommodityClassification.InputCoordinates.HiddenBasis.report_point
#print axioms CommodityClassification.InputCoordinates.HiddenBasis.report_point

#check @CommodityClassification.InputCoordinates.HiddenBasis.fiber_iff
#print axioms CommodityClassification.InputCoordinates.HiddenBasis.fiber_iff

#check @CommodityClassification.InputCoordinates.HiddenBasis.fiber_exists_iff
#print axioms CommodityClassification.InputCoordinates.HiddenBasis.fiber_exists_iff

#check @CommodityClassification.InputCoordinates.HiddenBasis.zeroDim_point
#print axioms CommodityClassification.InputCoordinates.HiddenBasis.zeroDim_point

#check @CommodityClassification.InputCoordinates.Partition.singleton_kernel
#print axioms CommodityClassification.InputCoordinates.Partition.singleton_kernel

#check @CommodityClassification.InputCoordinates.Partition.singleton_hiddenBasis
#print axioms CommodityClassification.InputCoordinates.Partition.singleton_hiddenBasis

#check @CommodityClassification.InputCoordinates.Frame.mean_candidate
#print axioms CommodityClassification.InputCoordinates.Frame.mean_candidate

#check @CommodityClassification.InputCoordinates.Frame.fiberDomain_open
#print axioms CommodityClassification.InputCoordinates.Frame.fiberDomain_open

#check @CommodityClassification.InputCoordinates.Frame.fiberDomain_zero
#print axioms CommodityClassification.InputCoordinates.Frame.fiberDomain_zero

#check @CommodityClassification.InputCoordinates.Frame.fixedFiber_eq_image
#print axioms CommodityClassification.InputCoordinates.Frame.fixedFiber_eq_image

#check @CommodityClassification.InputCoordinates.Frame.fixedFiber_unique
#print axioms CommodityClassification.InputCoordinates.Frame.fixedFiber_unique

#check @CommodityClassification.InputCoordinates.Frame.small_perturbations
#print axioms CommodityClassification.InputCoordinates.Frame.small_perturbations

#check @CommodityClassification.InputCoordinates.Frame.positive_fiber_inputs
#print axioms CommodityClassification.InputCoordinates.Frame.positive_fiber_inputs

#check @CommodityClassification.InputCoordinates.Frame.fixedFiber_zeroDim
#print axioms CommodityClassification.InputCoordinates.Frame.fixedFiber_zeroDim

#check @CommodityClassification.InputCoordinates.Frame.exists_open_fiber
#print axioms CommodityClassification.InputCoordinates.Frame.exists_open_fiber

#check @CommodityClassification.InputCoordinates.Frame.singleton_fixedFiber
#print axioms CommodityClassification.InputCoordinates.Frame.singleton_fixedFiber

#check @CommodityClassification.InputCoordinates.Frame.b1_geometric_assembly
#print axioms CommodityClassification.InputCoordinates.Frame.b1_geometric_assembly

#print axioms CommodityClassification.InputCoordinates.Audit.twoFactorFrame
