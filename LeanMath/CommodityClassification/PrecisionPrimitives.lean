module

public import LeanMath.CommodityClassification.CompositePathAgreement

/-! The manuscript's structured precision class, with arbitrary finite sales weights. -/
@[expose] public section
noncomputable section
set_option maxHeartbeats 1200000
namespace CommodityClassification.Precision
open Matrix InputCoordinates
open scoped BigOperators

structure Data (n : ℕ) where
  w : Vec n
  v : Vec n
  hw : ∀i,0<w i
  sum_w : ∑i,w i=1
  type_sign : ∀i,v i= -1 ∨ v i=1
  type_balance : ∑i,w i*v i=0
  eta : ℝ
  alpha : ℝ
  beta : ℝ
  sigma : ℝ
  heta : 0<eta
  halpha : 0≤alpha
  hbeta : 0<beta ∧ beta<1
  hsigma : 0<sigma

namespace Data
variable {n : ℕ} (d : Data n)

def prices (_d : Data n) : Vec n := fun _ => 1
def policy : Vec n := fun i => 1+d.beta*d.v i
def weightedType : Vec n := fun i => d.w i*d.v i
def demand : Mat n n := d.eta • diagonal d.w+d.alpha • vecMulVec d.weightedType d.weightedType
def coordinates (_d : Data n) (c : Vec n) : Mat n 1 := fun i _ => c i
def inputs (_d : Data n) (c : Vec n) : Mat n 2 := fun i j => if j=0 then (1+c i)/2 else (1-c i)/2
def Admissible (c : Vec n) : Prop := (∀i,|c i|<1) ∧ ∑i,d.w i*c i=0
def theta (c : Vec n) : ℝ := ∑i,d.w i*d.v i*c i
def secondMoment (c : Vec n) : ℝ := ∑i,d.w i*(c i)^2
def totalElasticity : ℝ := d.eta+d.alpha
def nu : ℝ := d.eta+d.totalElasticity*d.beta^2
def policyShare : ℝ := d.totalElasticity*d.beta^2/d.nu
def lossScale : ℝ := d.policyShare*d.totalElasticity
def denominator (s Q x : ℝ) : ℝ := s+(d.eta-s)*Q+d.alpha*x

include d in
theorem goods_nonempty : 0<n := by
  by_contra hn
  have hz : n=0 := Nat.eq_zero_of_not_pos hn
  subst n
  have hh := d.sum_w
  simp at hh

theorem type_square (i : Fin n) : (d.v i)^2=1 := by
  rcases d.type_sign i with hi|hi <;> rw [hi] <;> norm_num

theorem type_norm : ∑i,d.w i*(d.v i)^2=1 := by
  simp only [d.type_square,mul_one,d.sum_w]

theorem weightedType_sum : ∑i,d.weightedType i=0 := d.type_balance

theorem demand_posDef : d.demand.PosDef := by
  have hd : (d.eta • diagonal d.w).PosDef :=
    (Matrix.PosDef.diagonal d.hw).smul d.heta
  have hp : (vecMulVec d.weightedType d.weightedType).PosSemidef := by
    simpa only [star_trivial] using Matrix.posSemidef_vecMulVec_self_star d.weightedType
  exact hd.add_posSemidef (hp.smul d.halpha)

theorem zero_admissible : d.Admissible 0 := by
  constructor
  · intro i;simp
  · simp

theorem theta_sq_le_secondMoment (c : Vec n) : (d.theta c)^2≤d.secondMoment c := by
  have hh := Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul (R := ℝ) Finset.univ
    (r := fun i => d.w i*d.v i*c i) (f := d.w) (g := fun i => d.w i*(c i)^2)
    (fun i _ => (d.hw i).le) (fun i _ => mul_nonneg (d.hw i).le (sq_nonneg _))
    (fun i _ => by simp only [mul_pow,d.type_square,mul_one];ring_nf;exact le_rfl)
  simpa only [d.sum_w,one_mul,theta,secondMoment] using hh

theorem secondMoment_nonneg (c : Vec n) : 0≤d.secondMoment c :=
  Finset.sum_nonneg (fun i _ => mul_nonneg (d.hw i).le (sq_nonneg _))

theorem secondMoment_lt_one (c : Vec n) (hc : d.Admissible c) : d.secondMoment c<1 := by
  let : Nonempty (Fin n) := ⟨⟨0,d.goods_nonempty⟩⟩
  rw [←d.sum_w]
  apply Finset.sum_lt_sum_of_nonempty Finset.univ_nonempty
  intro i _
  have hsq : (c i)^2<1 := by
    obtain ⟨hlo,hhi⟩ := abs_lt.mp (hc.1 i)
    have hh := mul_pos (sub_pos.mpr hhi) (show 0<1+c i by linarith)
    nlinarith
  exact mul_lt_of_lt_one_right (d.hw i) hsq

theorem totalElasticity_pos : 0<d.totalElasticity := add_pos_of_pos_of_nonneg d.heta d.halpha

theorem nu_pos : 0<d.nu :=
  add_pos_of_pos_of_nonneg d.heta (mul_nonneg d.totalElasticity_pos.le (sq_nonneg _))

theorem lossScale_pos : 0<d.lossScale := by
  unfold lossScale policyShare
  exact mul_pos (div_pos (mul_pos d.totalElasticity_pos (sq_pos_of_pos d.hbeta.1)) d.nu_pos)
    d.totalElasticity_pos

theorem denominator_lower (s Q x : ℝ) (hQ0 : 0≤Q) (hQ1 : Q≤1) (hx : 0≤x) :
    min d.eta s≤d.denominator s Q x := by
  have h1 : 0≤(d.eta-min d.eta s)*Q := mul_nonneg (sub_nonneg.mpr (min_le_left _ _)) hQ0
  have h2 : 0≤(s-min d.eta s)*(1-Q) := mul_nonneg (sub_nonneg.mpr (min_le_right _ _)) (by linarith)
  have h3 := mul_nonneg d.halpha hx
  unfold denominator
  nlinarith

theorem denominator_positive (c : Vec n) (hc : d.Admissible c) :
    0<d.denominator d.sigma (d.secondMoment c) ((d.theta c)^2) := by
  exact lt_of_lt_of_le (lt_min d.heta d.hsigma)
    (d.denominator_lower _ _ _ (d.secondMoment_nonneg c) (d.secondMoment_lt_one c hc).le (sq_nonneg _))

end Data
end CommodityClassification.Precision
