module

public import LeanMath.CommodityClassification.NestedCovarianceVariance

/-! Exact first- and second-moment algebra with actual nest reports. -/
@[expose] public section
noncomputable section
set_option maxHeartbeats 800000
namespace CommodityClassification.InputCoordinates
open Matrix
open scoped BigOperators
variable {n k : ℕ}

theorem diagonal_conjugate_sum (A : Mat n k) (v : Vec n) :
    A.transpose*diagonal v*A=∑i,v i • vecMulVec (A i) (A i) := by
  ext l m
  rw [Matrix.mul_apply]
  simp only [Matrix.mul_diagonal,Matrix.transpose_apply,Matrix.sum_apply,
    Matrix.smul_apply,smul_eq_mul,Matrix.vecMulVec_apply]
  apply Finset.sum_congr rfl
  intro i _
  ring

end CommodityClassification.InputCoordinates

namespace CommodityClassification.DemandNests.Data
open Matrix InputCoordinates
open scoped BigOperators
variable {n g k : ℕ} (d : DemandNests.Data n g)

def meanAdjustment (DG : Mat g g) (σ : ℝ) : Mat g g :=
  diagonal (fun a => (d.partition.sales d.p d.q a)⁻¹)*
    (DG-σ • diagonal (d.partition.sales d.p d.q))*
      diagonal (fun a => (d.partition.sales d.p d.q a)⁻¹)

def covarianceCorrection (C : Mat n k) (σ : ℝ) : Mat k k :=
  ∑a,(d.eta a-σ) • d.nestCovariance C a

theorem weighted_second_conjugate (C : Mat n k) (γ : Vec g) :
    C.transpose*diagonal (fun i => γ (d.partition.group i)*(d.q i/d.p i))*C=
      ∑a,γ a • d.nestSecondMoment C a := by
  rw [diagonal_conjugate_sum]
  ext l m
  simp only [Matrix.sum_apply,Matrix.smul_apply,smul_eq_mul,Matrix.vecMulVec_apply,
    d.nestSecondMoment_apply]
  calc
    _=∑i,((d.q i/d.p i)*C i l*C i m)*γ (d.partition.group i) := by
      apply Finset.sum_congr rfl
      intro i _
      ring
    _=∑a,(∑i∈d.partition.cell a,(d.q i/d.p i)*C i l*C i m)*γ a :=
      d.sum_nest_multiplier (fun i => (d.q i/d.p i)*C i l*C i m) γ
    _=_ := by simp only [mul_comm]

theorem report_conjugate (C : Mat n k) (B : Mat g g) :
    C.transpose*(d.partition.Q d.q*B*(d.partition.Q d.q).transpose)*C=
      (d.partition.report d.q C).transpose*B*d.partition.report d.q C := by
  simp only [Partition.report,Matrix.transpose_mul,Matrix.transpose_transpose,Matrix.mul_assoc]

theorem weighted_covariance_decomposition (C : Mat n k) (γ : Vec g) :
    (∑a,γ a • d.nestSecondMoment C a)=(∑a,γ a • d.nestCovariance C a)+
      (d.partition.report d.q C).transpose*
        diagonal (fun a => γ a/d.partition.sales d.p d.q a)*d.partition.report d.q C := by
  rw [diagonal_conjugate_sum,←Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro a _
  rw [d.nestCovariance_manuscript,smul_sub,smul_smul]
  have he : γ a*(d.partition.sales d.p d.q a)⁻¹=γ a/d.partition.sales d.p d.q a :=
    (div_eq_mul_inv _ _).symm
  rw [he,sub_add_cancel]

theorem meanAdjustment_eq (DG : Mat g g) (σ : ℝ) :
    d.meanAdjustment DG σ=d.outerAdjustment DG+
      diagonal (fun a => (d.eta a-σ)/d.partition.sales d.p d.q a) := by
  ext a b
  simp only [meanAdjustment,outerAdjustment,Matrix.mul_diagonal,Matrix.diagonal_mul,
    Matrix.sub_apply,Matrix.add_apply,Matrix.smul_apply,smul_eq_mul,Matrix.diagonal_apply]
  by_cases hab : a=b
  · subst b
    simp only [ite_true]
    field_simp [(d.partition.sales_pos d.p d.q d.hp d.hq a).ne']
    ring
  · simp only [hab,ite_false,mul_zero,sub_zero,add_zero]

theorem adjustedDemand_nest_decomposition (DG : Mat g g) (σ : ℝ) :
    Regularity.adjustedDemand d.p d.q (d.demandMatrix DG) σ=
      diagonal (fun i => (d.eta (d.partition.group i)-σ)*(d.q i/d.p i))+
        d.partition.Q d.q*d.outerAdjustment DG*(d.partition.Q d.q).transpose := by
  rw [Regularity.adjustedDemand,demandMatrix,add_sub_right_comm]
  congr 1
  ext i j
  simp only [Supply.xi,Matrix.diagonal_mul_diagonal,Matrix.sub_apply,Matrix.smul_apply,
    smul_eq_mul,Matrix.diagonal_apply]
  by_cases hij : i=j
  · simp only [hij,ite_true]
    ring
  · simp only [hij,ite_false,mul_zero,sub_self]

theorem nest_K_decomposition (DG : Mat g g) (R : Mat k k) (σ : ℝ) (C : Mat n k) :
    Regularity.K d.p d.q (d.demandMatrix DG) R σ C=σ • R+
      (d.partition.report d.q C).transpose*d.meanAdjustment DG σ*d.partition.report d.q C+
        d.covarianceCorrection C σ := by
  rw [Regularity.K,d.adjustedDemand_nest_decomposition,Matrix.mul_add,Matrix.add_mul,
    d.weighted_second_conjugate C (fun a => d.eta a-σ),d.report_conjugate,d.weighted_covariance_decomposition,
    d.meanAdjustment_eq,Matrix.mul_add,Matrix.add_mul]
  unfold covarianceCorrection
  abel

theorem nest_m_decomposition (DG : Mat g g) (β : Vec g) (C : Mat n k) :
    C.transpose *ᵥ (d.demandMatrix DG *ᵥ d.proportionalPolicy β)=
      (d.partition.report d.q C).transpose *ᵥ
        (diagonal (fun a => (d.partition.sales d.p d.q a)⁻¹) *ᵥ (DG *ᵥ β)) := by
  rw [d.demand_policy_matrix,Matrix.mulVec_mulVec]
  simp only [Partition.report,Matrix.transpose_mul,Matrix.transpose_transpose]

theorem covarianceCorrection_matching (C : Mat n k) (σ : ℝ) (hmatch : ∀a,d.eta a=σ) :
    d.covarianceCorrection C σ=0 := by
  simp only [covarianceCorrection,hmatch,sub_self,zero_smul,Finset.sum_const_zero]

end CommodityClassification.DemandNests.Data
