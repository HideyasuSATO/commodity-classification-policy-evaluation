module

public import LeanMath.CommodityClassification.PrecisionVarianceAllowance

/-! The printed square-completion identity and exact scalar maximum. -/
@[expose] public section
noncomputable section
set_option maxHeartbeats 1800000
namespace CommodityClassification.Precision.Envelope

def factor (a A x : ℝ) : ℝ := a+(A-a)*x
def value (a d A B x : ℝ) : ℝ := B*(d-a)*x*(1-x)/(factor a A x*factor d A x)
def bound (a d A B : ℝ) : ℝ := B*(d-a)/(A*(Real.sqrt a+Real.sqrt d)^2)
def optimizer (a d A : ℝ) : ℝ := Real.sqrt (a*d)/(A+Real.sqrt (a*d))

theorem factor_pos (a A x : ℝ) (ha : 0<a) (hA : 0<A) (hx : x∈Set.Icc (0:ℝ) 1) :
    0<factor a A x := by
  by_cases h1 : x=1
  · simp [factor,h1,hA]
  · have hx1 : x<1 := lt_of_le_of_ne hx.2 h1
    have hp := mul_pos ha (sub_pos.mpr hx1)
    have hn := mul_nonneg hA.le hx.1
    unfold factor
    nlinarith

theorem square_identity (a d A x : ℝ) (ha : 0≤a) (hd : 0≤d) :
    factor a A x*factor d A x-A*(Real.sqrt a+Real.sqrt d)^2*x*(1-x)=
      (Real.sqrt (a*d)-(A+Real.sqrt (a*d))*x)^2 := by
  rw [Real.sqrt_mul ha]
  unfold factor
  ring_nf
  rw [Real.sq_sqrt ha,Real.sq_sqrt hd]
  ring

theorem cap_pos (a d A : ℝ) (ha : 0<a) (hd : 0<d) (hA : 0<A) :
    0<A*(Real.sqrt a+Real.sqrt d)^2 :=
  mul_pos hA (sq_pos_of_pos (add_pos (Real.sqrt_pos.mpr ha) (Real.sqrt_pos.mpr hd)))

theorem value_le_bound (a d A B x : ℝ) (ha : 0<a) (hd : 0<d) (had : a≤d)
    (hA : 0<A) (hB : 0≤B) (hx : x∈Set.Icc (0:ℝ) 1) : value a d A B x≤bound a d A B := by
  have hden := mul_pos (factor_pos a A x ha hA hx) (factor_pos d A x hd hA hx)
  have hcap := cap_pos a d A ha hd hA
  have hs := square_identity a d A x ha.le hd.le
  have hh : A*(Real.sqrt a+Real.sqrt d)^2*x*(1-x)≤factor a A x*factor d A x := by
    nlinarith [sq_nonneg (Real.sqrt (a*d)-(A+Real.sqrt (a*d))*x)]
  have ht := mul_le_mul_of_nonneg_left hh (mul_nonneg hB (sub_nonneg.mpr had))
  rw [value,bound,div_le_div_iff₀ hden hcap]
  nlinarith [ht]

theorem optimizer_mem (a d A : ℝ) (ha : 0<a) (hd : 0<d) (hA : 0<A) :
    optimizer a d A∈Set.Ioo (0:ℝ) 1 := by
  have hs : 0<Real.sqrt (a*d) := Real.sqrt_pos.mpr (mul_pos ha hd)
  have hden : 0<A+Real.sqrt (a*d) := add_pos hA hs
  exact ⟨div_pos hs hden,(div_lt_one hden).mpr (by linarith)⟩

theorem optimizer_root (a d A : ℝ) (ha : 0<a) (hd : 0<d) (hA : 0<A) :
    Real.sqrt (a*d)-(A+Real.sqrt (a*d))*optimizer a d A=0 := by
  have hden : A+Real.sqrt (a*d)≠0 :=
    (add_pos hA (Real.sqrt_pos.mpr (mul_pos ha hd))).ne'
  unfold optimizer
  field_simp [hden]
  ring

theorem value_at_optimizer (a d A B : ℝ) (ha : 0<a) (hd : 0<d) (hA : 0<A) :
    value a d A B (optimizer a d A)=bound a d A B := by
  have hx := optimizer_mem a d A ha hd hA
  have hden := mul_pos (factor_pos a A _ ha hA ⟨hx.1.le,hx.2.le⟩)
    (factor_pos d A _ hd hA ⟨hx.1.le,hx.2.le⟩)
  have hcap := cap_pos a d A ha hd hA
  have hs := square_identity a d A (optimizer a d A) ha.le hd.le
  rw [optimizer_root a d A ha hd hA,zero_pow (by decide : 2≠0)] at hs
  rw [value,bound,div_eq_div_iff hden.ne' hcap.ne']
  have he : factor a A (optimizer a d A)*factor d A (optimizer a d A)=
      A*(Real.sqrt a+Real.sqrt d)^2*optimizer a d A*(1-optimizer a d A) := by linarith
  rw [he]
  ring

theorem bound_scaled (a d A P : ℝ) (ha : 0<a) (hd : 0<d) (hA : 0<A) :
    bound a d A (P*A)=P*(Real.sqrt d-Real.sqrt a)/(Real.sqrt d+Real.sqrt a) := by
  have hs : Real.sqrt a+Real.sqrt d≠0 :=
    (add_pos (Real.sqrt_pos.mpr ha) (Real.sqrt_pos.mpr hd)).ne'
  have hs' : Real.sqrt d+Real.sqrt a≠0 := by simpa only [add_comm] using hs
  unfold bound
  field_simp [hA.ne',hs,hs']
  ring_nf
  rw [Real.sq_sqrt ha.le,Real.sq_sqrt hd.le]
  have ha3 : (Real.sqrt a)^3=a*Real.sqrt a := by rw [pow_succ,Real.sq_sqrt ha.le]
  have hd3 : (Real.sqrt d)^3=d*Real.sqrt d := by rw [pow_succ,Real.sq_sqrt hd.le]
  rw [ha3,hd3]
  ring

theorem value_isGreatest (a d A B : ℝ) (ha : 0<a) (hd : 0<d) (had : a≤d)
    (hA : 0<A) (hB : 0≤B) :
    IsGreatest (value a d A B '' Set.Icc (0:ℝ) 1) (bound a d A B) := by
  have hx := optimizer_mem a d A ha hd hA
  refine ⟨⟨optimizer a d A,⟨hx.1.le,hx.2.le⟩,value_at_optimizer a d A B ha hd hA⟩,?_⟩
  rintro z ⟨x,hx,rfl⟩
  exact value_le_bound a d A B x ha hd had hA hB hx

end CommodityClassification.Precision.Envelope
