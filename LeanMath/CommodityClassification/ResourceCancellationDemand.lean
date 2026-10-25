module

public import LeanMath.CommodityClassification.QuantityBridgeComplete
public import LeanMath.CommodityClassification.SupplyBoundaryExample

/-! Exact rational demand primitives of the manuscript's resource-cancellation example. -/
@[expose] public section
noncomputable section
set_option maxHeartbeats 2400000
namespace CommodityClassification.ResourceCancellation
open Matrix InputCoordinates

def e : Vec 3 := ![1,1,1]
def hidden : Vec 3 := ![1,-1,0]
def visible : Vec 3 := ![1,1,-2]
def demand : Mat 3 3 := 1+(1/20 : ℝ) • (vecMulVec e hidden+vecMulVec hidden e)+
  (1/10 : ℝ) • vecMulVec visible visible
def policy : Vec 3 := ![19/20,5/4,4/5]

theorem e_pos : ∀i,0<e i := by intro i; fin_cases i <;> norm_num [e]

theorem demand_entries : demand=!![6/5,1/10,-3/20;1/10,1,-1/4;-3/20,-1/4,7/5] := by
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [demand,e,hidden,visible,vecMulVec,Matrix.one_apply]

theorem demand_symmetric : demand.transpose=demand := by
  rw [demand_entries]
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [transpose_apply]

theorem demand_quadratic (x : Vec 3) :
    dotProduct x (demand *ᵥ x)=
      (19/20 : ℝ)*(x 0)^2+(13/20 : ℝ)*(x 1)^2+(x 2)^2+
      (1/10 : ℝ)*(x 0+x 1)^2+(3/20 : ℝ)*(x 0-x 2)^2+(1/4 : ℝ)*(x 1-x 2)^2 := by
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
        ext i
        fin_cases i <;> simp [he]
      rcases hn with h0|h1|h2
      · nlinarith [sq_pos_of_ne_zero h0,sq_nonneg (x 1),sq_nonneg (x 2)]
      · nlinarith [sq_pos_of_ne_zero h1,sq_nonneg (x 0),sq_nonneg (x 2)]
      · nlinarith [sq_pos_of_ne_zero h2,sq_nonneg (x 0),sq_nonneg (x 1)]
    have hp : 0<dotProduct x (demand *ᵥ x) := by
      rw [demand_quadratic]
      nlinarith [sq_nonneg (x 0),sq_nonneg (x 1),sq_nonneg (x 2),
        sq_nonneg (x 0+x 1),sq_nonneg (x 0-x 2),sq_nonneg (x 1-x 2)]
    simpa using hp

theorem xi_identity : Supply.xi e e=1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [Supply.xi,e,Matrix.diagonal,Matrix.one_apply]

theorem adjusted_hidden : (Regularity.adjustedDemand e e demand 1) *ᵥ hidden=(1/10 : ℝ) • e := by
  rw [Regularity.adjustedDemand,xi_identity,demand_entries]
  ext i
  fin_cases i <;> norm_num [hidden,e,Matrix.sub_mulVec,Matrix.mulVec,dotProduct,Fin.sum_univ_succ,Matrix.one_apply]

theorem adjusted_hidden_ne_zero : (Regularity.adjustedDemand e e demand 1) *ᵥ hidden≠0 := by
  rw [adjusted_hidden]
  intro he
  have hh := congrFun he 0
  norm_num [e] at hh

theorem demand_policy : demand *ᵥ policy=![229/200,229/200,133/200] := by
  rw [demand_entries]
  ext i
  fin_cases i <;> norm_num [policy,Matrix.mulVec,dotProduct,Fin.sum_univ_succ]

theorem hidden_policy_zero : dotProduct hidden (demand *ᵥ policy)=0 := by
  rw [demand_policy]
  norm_num [hidden,dotProduct,Fin.sum_univ_succ]

theorem nu_exact : dotProduct policy (demand *ᵥ policy)=3051/1000 := by
  rw [demand_policy]
  norm_num [policy,dotProduct,Fin.sum_univ_succ]

end CommodityClassification.ResourceCancellation
