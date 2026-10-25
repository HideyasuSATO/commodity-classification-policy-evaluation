module

public import LeanMath.CommodityClassification.SeparableFourIdentification
public import Mathlib.Analysis.InnerProductSpace.LinearMap
public import Mathlib.Analysis.InnerProductSpace.PiL2

/-! Exact primitives of the fixed-answer cancellation example. -/
@[expose] public section
noncomputable section
set_option maxHeartbeats 2400000
namespace CommodityClassification.FixedCancellation
open Matrix InputCoordinates
open ResourceCancellation (e visible coordinates inputs parent fine)

def loadingMatrix : Matrix (Fin 3) (Fin 3) ℝ :=
  (1/10 : ℝ) • (vecMulVec ResourceCancellation.hidden visible+vecMulVec visible ResourceCancellation.hidden)+
    (3/2500 : ℝ) • vecMulVec ResourceCancellation.hidden ResourceCancellation.hidden
def demand : Matrix (Fin 3) (Fin 3) ℝ := 1+loadingMatrix
def demandLoad : Vec 3 := e+(1/10 : ℝ) • visible+(3/2500 : ℝ) • ResourceCancellation.hidden
def policy : Vec 3 := demand⁻¹ *ᵥ demandLoad

theorem demand_entries : demand=!![3003/2500,-3/2500,-1/5;
    -3/2500,2003/2500,1/5;-1/5,1/5,1] := by
  ext i j
  change (if i=j then (1 : ℝ) else 0)+
    ((1/10 : ℝ)*(ResourceCancellation.hidden i*visible j+visible i*ResourceCancellation.hidden j)+
      (3/2500 : ℝ)*(ResourceCancellation.hidden i*ResourceCancellation.hidden j))=_
  fin_cases i <;> fin_cases j <;>
    norm_num [demand,loadingMatrix,ResourceCancellation.hidden,ResourceCancellation.visible,
      vecMulVec,Matrix.one_apply]

theorem demand_symmetric : demand.transpose=demand := by
  rw [demand_entries]
  ext i j; fin_cases i <;> fin_cases j <;> norm_num [transpose_apply]

theorem demand_quadratic (x : Vec 3) : dotProduct x (demand *ᵥ x)=
    (x 0)^2+(3/5 : ℝ)*(x 1)^2+(3/5 : ℝ)*(x 2)^2+
      (3/2500 : ℝ)*(x 0-x 1)^2+(1/5 : ℝ)*(x 0-x 2)^2+(1/5 : ℝ)*(x 1+x 2)^2 := by
  rw [demand_entries]
  simp [dotProduct,Matrix.mulVec,Fin.sum_univ_succ]
  ring

theorem demand_posDef : demand.PosDef := by
  apply Matrix.PosDef.of_dotProduct_mulVec_pos
  · simpa only [Matrix.IsHermitian,conjTranspose_eq_transpose_of_trivial] using demand_symmetric
  · intro x hx
    have hsum : 0<(x 0)^2+(x 1)^2+(x 2)^2 := by
      have hn : x 0≠0 ∨ x 1≠0 ∨ x 2≠0 := by
        by_contra he
        push Not at he
        apply hx
        ext i; fin_cases i <;> simp [he]
      rcases hn with h0|h1|h2
      · nlinarith [sq_pos_of_ne_zero h0,sq_nonneg (x 1),sq_nonneg (x 2)]
      · nlinarith [sq_pos_of_ne_zero h1,sq_nonneg (x 0),sq_nonneg (x 2)]
      · nlinarith [sq_pos_of_ne_zero h2,sq_nonneg (x 0),sq_nonneg (x 1)]
    have hp : 0<dotProduct x (demand *ᵥ x) := by
      rw [demand_quadratic]
      nlinarith [sq_nonneg (x 0),sq_nonneg (x 1),sq_nonneg (x 2),
        sq_nonneg (x 0-x 1),sq_nonneg (x 0-x 2),sq_nonneg (x 1+x 2)]
    simpa using hp

theorem demand_policy : demand *ᵥ policy=demandLoad := by
  unfold policy
  rw [Matrix.mulVec_mulVec,Matrix.mul_nonsing_inv _
    ((Matrix.isUnit_iff_isUnit_det _).mp demand_posDef.isUnit),Matrix.one_mulVec]

theorem load_entries : demandLoad=![2753/2500,2747/2500,4/5] := by
  ext i; fin_cases i <;>
    norm_num [demandLoad,ResourceCancellation.e,ResourceCancellation.hidden,ResourceCancellation.visible]

def nE : EuclideanSpace ℝ (Fin 3) := WithLp.toLp 2 ResourceCancellation.hidden
def vE : EuclideanSpace ℝ (Fin 3) := WithLp.toLp 2 visible
def loadingOperator : EuclideanSpace ℝ (Fin 3) →L[ℝ] EuclideanSpace ℝ (Fin 3) :=
  (1/10 : ℝ) • (InnerProductSpace.rankOne ℝ nE vE+InnerProductSpace.rankOne ℝ vE nE)+
    (3/2500 : ℝ) • InnerProductSpace.rankOne ℝ nE nE

theorem euclidean_norms : ‖nE‖^2=2 ∧ ‖vE‖^2=6 := by
  constructor <;> rw [EuclideanSpace.real_norm_sq_eq] <;>
    norm_num [nE,vE,ResourceCancellation.hidden,ResourceCancellation.visible,Fin.sum_univ_succ]

theorem loadingOperator_apply (x : EuclideanSpace ℝ (Fin 3)) (i : Fin 3) :
    loadingOperator x i=(loadingMatrix *ᵥ WithLp.ofLp x) i := by
  simp [loadingOperator,loadingMatrix,InnerProductSpace.rankOne_apply,PiLp.inner_apply,
    nE,vE,Matrix.mulVec,vecMulVec,dotProduct,Fin.sum_univ_succ]
  fin_cases i <;> norm_num [ResourceCancellation.hidden,ResourceCancellation.visible] <;> ring

theorem loading_norm_bound :
    ‖loadingOperator‖≤(1/5 : ℝ)*‖nE‖*‖vE‖+(3/2500 : ℝ)*‖nE‖^2 := by
  have ht := norm_add_le
    ((1/10 : ℝ) • (InnerProductSpace.rankOne ℝ nE vE+InnerProductSpace.rankOne ℝ vE nE))
    ((3/2500 : ℝ) • InnerProductSpace.rankOne ℝ nE nE)
  have hr := norm_add_le (InnerProductSpace.rankOne ℝ nE vE) (InnerProductSpace.rankOne ℝ vE nE)
  norm_num only [norm_smul,Real.norm_eq_abs,abs_of_pos (by norm_num : (0 : ℝ)<1/10),
    abs_of_pos (by norm_num : (0 : ℝ)<3/2500),InnerProductSpace.norm_rankOne] at ht hr
  change ‖loadingOperator‖≤_ at ht
  nlinarith

theorem loading_bound_lt_one :
    (1/5 : ℝ)*‖nE‖*‖vE‖+(3/2500 : ℝ)*‖nE‖^2<1 := by
  obtain ⟨hn,hv⟩ := euclidean_norms
  nlinarith [sq_nonneg (‖nE‖-‖vE‖)]

theorem loading_norm_lt_one : ‖loadingOperator‖<1 :=
  lt_of_le_of_lt loading_norm_bound loading_bound_lt_one

end CommodityClassification.FixedCancellation
