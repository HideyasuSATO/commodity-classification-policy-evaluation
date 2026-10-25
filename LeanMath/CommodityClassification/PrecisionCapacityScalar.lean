module

public import LeanMath.CommodityClassification.PrecisionCapacityDispersion

/-! Exact scalar maximum used in the variance-capacity certificate. -/
@[expose] public section
noncomputable section
set_option maxHeartbeats 1600000
namespace CommodityClassification.Precision.Capacity

def factor (a A x : ℝ) : ℝ := a+(A-a)*x
def value (a A x : ℝ) : ℝ := x/(factor a A x)^2
def chi (a A : ℝ) : ℝ := if A≤2*a then 1/A^2 else 1/(4*a*(A-a))
def optimizer (a A : ℝ) : ℝ := if A≤2*a then 1 else a/(A-a)

theorem factor_pos (a A x : ℝ) (ha : 0<a) (hA : a≤A) (hx : 0≤x) :
    0<factor a A x := by
  unfold factor
  exact add_pos_of_pos_of_nonneg ha (mul_nonneg (sub_nonneg.mpr hA) hx)

theorem value_le_endpoint (a A x : ℝ) (ha : 0<a) (hA : a≤A)
    (hsmall : A≤2*a) (hx : x∈Set.Icc (0:ℝ) 1) : value a A x≤1/A^2 := by
  have hAp := ha.trans_le hA
  have hp := factor_pos a A x ha hA hx.1
  have hba : (A-a)^2≤a^2 := by nlinarith
  have hbx : (A-a)^2*x≤(A-a)^2 := mul_le_of_le_one_right (sq_nonneg _) hx.2
  have he : (factor a A x)^2-A^2*x=(1-x)*(a^2-(A-a)^2*x) := by
    unfold factor
    ring
  have hh : 0≤(factor a A x)^2-A^2*x := by
    rw [he]
    exact mul_nonneg (sub_nonneg.mpr hx.2) (by linarith)
  rw [value,div_le_div_iff₀ (sq_pos_of_pos hp) (sq_pos_of_pos hAp)]
  nlinarith

theorem value_le_interior (a A x : ℝ) (ha : 0<a) (hlarge : 2*a<A)
    (hx : 0≤x) : value a A x≤1/(4*a*(A-a)) := by
  have hA : a≤A := by linarith
  have hp := factor_pos a A x ha hA hx
  have hb : 0<4*a*(A-a) := mul_pos (by positivity) (by linarith)
  have he : (factor a A x)^2-4*a*(A-a)*x=(a-(A-a)*x)^2 := by
    unfold factor
    ring
  rw [value,div_le_div_iff₀ (sq_pos_of_pos hp) hb]
  nlinarith [sq_nonneg (a-(A-a)*x)]

theorem value_le_chi (a A x : ℝ) (ha : 0<a) (hA : a≤A)
    (hx : x∈Set.Icc (0:ℝ) 1) : value a A x≤chi a A := by
  unfold chi
  split_ifs with h
  · exact value_le_endpoint a A x ha hA h hx
  · exact value_le_interior a A x ha (lt_of_not_ge h) hx.1

theorem branches_agree (a : ℝ) : 1/(2*a)^2=1/(4*a*(2*a-a)) := by ring

theorem optimizer_mem (a A : ℝ) (ha : 0<a) (_hA : a≤A) :
    optimizer a A∈Set.Icc (0:ℝ) 1 := by
  unfold optimizer
  split_ifs with h
  · exact ⟨by norm_num,le_rfl⟩
  · have hb : 0<A-a := by linarith
    exact ⟨(div_pos ha hb).le,(div_le_one hb).mpr (by linarith)⟩

theorem value_at_optimizer (a A : ℝ) (ha : 0<a) (hA : a≤A) :
    value a A (optimizer a A)=chi a A := by
  have hAp : 0<A := ha.trans_le hA
  unfold optimizer chi
  split_ifs with h
  · simp [value,factor]
  · have hb : A-a≠0 := by linarith
    have hf : factor a A (a/(A-a))=2*a := by
      unfold factor
      field_simp
      ring
    rw [value,hf]
    field_simp
    ring

theorem chi_isGreatest (a A : ℝ) (ha : 0<a) (hA : a≤A) :
    IsGreatest ((fun x => value a A x) '' Set.Icc (0:ℝ) 1) (chi a A) := by
  refine ⟨⟨optimizer a A,optimizer_mem a A ha hA,value_at_optimizer a A ha hA⟩,?_⟩
  rintro y ⟨x,hx,rfl⟩
  exact value_le_chi a A x ha hA hx

theorem chi_pos (a A : ℝ) (ha : 0<a) (hA : a≤A) : 0<chi a A := by
  unfold chi
  split_ifs with h
  · exact div_pos zero_lt_one (sq_pos_of_pos (ha.trans_le hA))
  · exact div_pos zero_lt_one (mul_pos (by positivity) (by linarith))

end CommodityClassification.Precision.Capacity
