module

public import LeanMath.CommodityClassification.NestedQuadraticImplementation

/-! Exact within-nest exchanges in the actual demand and policy matrices. -/
@[expose] public section
noncomputable section
set_option maxHeartbeats 600000
namespace CommodityClassification.DemandNests.Data
open Matrix InputCoordinates
open scoped BigOperators
variable {n g : ℕ} (d : DemandNests.Data n g)

theorem priceDerivative_exchange (i j : Fin n) (hij : d.partition.group i=d.partition.group j) :
    d.priceDerivative (weightedExchange d.q i j)=0 := by
  rw [d.priceDerivative_matrix,←Matrix.mulVec_mulVec,
    d.partition.weighted_exchange_hidden d.q d.hq i j hij,Matrix.mulVec_zero]

theorem policy_load_ratio (DG : Mat g g) (β : Vec g) (i : Fin n) :
    (d.demandMatrix DG *ᵥ d.proportionalPolicy β) i/d.q i=
      (DG *ᵥ β) (d.partition.group i)/d.partition.sales d.p d.q (d.partition.group i) := by
  rw [d.demand_policy_apply]
  field_simp [(d.hq i).ne']

theorem within_nest_policy_loads (DG : Mat g g) (β : Vec g) (i j : Fin n)
    (hij : d.partition.group i=d.partition.group j) :
    (d.demandMatrix DG *ᵥ d.proportionalPolicy β) i/d.q i=
      (d.demandMatrix DG *ᵥ d.proportionalPolicy β) j/d.q j := by
  rw [d.policy_load_ratio,d.policy_load_ratio,hij]

theorem adjusted_exchange (DG : Mat g g) (σ : ℝ) (i j : Fin n) (hne : i≠j)
    (hij : d.partition.group i=d.partition.group j) :
    Regularity.adjustedDemand d.p d.q (d.demandMatrix DG) σ *ᵥ weightedExchange d.q i j=
      twoSupport i j ((d.eta (d.partition.group i)-σ)/d.p i)
        ((d.eta (d.partition.group i)-σ)/d.p j) := by
  funext l
  simp only [Regularity.adjustedDemand,Matrix.sub_mulVec,Matrix.smul_mulVec,
    Pi.sub_apply,Pi.smul_apply,smul_eq_mul,d.demandMatrix_apply,
    d.priceDerivative_exchange i j hij,Matrix.mulVec_zero,Pi.zero_apply,mul_zero,sub_zero,
    add_zero,Supply.xi,Matrix.mulVec_diagonal]
  by_cases hli : l=i
  · subst l
    simp [weightedExchange,twoSupport,hne]
    field_simp [(d.hq i).ne']
  · by_cases hlj : l=j
    · subst l
      simp [weightedExchange,twoSupport,hli,←hij]
      field_simp [(d.hq j).ne']
      ring
    · simp [weightedExchange,twoSupport,hli,hlj]

end CommodityClassification.DemandNests.Data

namespace CommodityClassification.InputCoordinates
open Matrix
variable {n h k : ℕ}

theorem twoSupport_common_difference_range_iff (P : Partition n h) (p q : Vec n)
    (hp : ∀i,0<p i) (hq : ∀i,0<q i) (i j : Fin n) (hne : i≠j)
    (hgroup : P.group i=P.group j) (δ : ℝ) :
    (∃γ : Vec h,P.Q q *ᵥ γ=twoSupport i j (δ/p i) (δ/p j)) ↔ δ=0 := by
  constructor
  · rintro ⟨γ,hγ⟩
    have hi := congrFun hγ i
    have hj := congrFun hγ j
    rw [P.Q_mulVec_apply,twoSupport_at_left i j hne] at hi
    rw [P.Q_mulVec_apply,twoSupport_at_right i j hne,←hgroup,←neg_div] at hj
    have hi' := (eq_div_iff (hp i).ne').mp hi
    have hj' := (eq_div_iff (hp j).ne').mp hj
    have hm : (q i*p i+q j*p j)*γ (P.group i)=0 := by nlinarith [hi',hj']
    have hz : γ (P.group i)=0 := (mul_eq_zero.mp hm).resolve_left
      (add_pos (mul_pos (hq i) (hp i)) (mul_pos (hq j) (hp j))).ne'
    simpa only [hz,mul_zero,zero_mul] using hi'.symm
  · rintro rfl
    exact ⟨0,by simp [twoSupport]⟩

theorem twoSupport_common_difference_cancellation_iff (P : Partition n h) (p q : Vec n)
    (hp : ∀i,0<p i) (hq : ∀i,0<q i) (J : Mat h k) (i j : Fin n) (hne : i≠j)
    (hgroup : P.group i=P.group j) (δ : ℝ) :
    twoSupport i j (δ/p i) (δ/p j)∈cancellationSpace (P.Q q) J ↔ δ=0 := by
  constructor
  · intro hm
    obtain ⟨γ,hγ,_⟩ := (mem_cancellationSpace_iff _ _ _).mp hm
    exact (twoSupport_common_difference_range_iff P p q hp hq i j hne hgroup δ).mp ⟨γ,hγ⟩
  · rintro rfl
    simpa only [zero_div] using twoSupport_mem_of_zero P q J i j

end CommodityClassification.InputCoordinates
