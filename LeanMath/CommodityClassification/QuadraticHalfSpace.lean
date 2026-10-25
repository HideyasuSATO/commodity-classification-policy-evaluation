module

public import LeanMath.CommodityClassification.SupplyResponseSeparation

/-! A nonzero real symmetric quadratic form is nonzero somewhere in a policy half-space. -/
@[expose] public section
noncomputable section
namespace CommodityClassification.Genericity
open Matrix FixedAnswer Filter
open scoped Topology
variable {n : ℕ}

theorem quadratic_symmetric_shift_sum (B : Mat n n) (b v : Vec n) (t : ℝ) :
    dotProduct (b+t • v) (B *ᵥ (b+t • v))+
      dotProduct (b-t • v) (B *ᵥ (b-t • v))=
      2*dotProduct b (B *ᵥ b)+2*t^2*dotProduct v (B *ᵥ v) := by
  simp only [mulVec_add,mulVec_sub,mulVec_smul,add_dotProduct,sub_dotProduct,
    dotProduct_add,dotProduct_sub,smul_dotProduct,dotProduct_smul,smul_eq_mul]
  ring

theorem quadratic_zero_of_halfspace (B : Mat n n) (hB : B.transpose=B)
    (b : Vec n) (hb : b≠0)
    (hzero : ∀a : Vec n,0<dotProduct b a → dotProduct a (B *ᵥ a)=0) : B=0 := by
  have hbb : 0<dotProduct b b := by simpa using (dotProduct_self_star_pos_iff.mpr hb)
  have hbB := hzero b hbb
  apply symmetric_zero_of_quadratic B hB
  intro v
  have hp : ∀ᶠ t : ℝ in 𝓝 0,0<dotProduct b (b+t • v) :=
    (isOpen_lt continuous_const
      (show Continuous (fun t : ℝ => dotProduct b (b+t • v)) from by fun_prop)).mem_nhds
        (by simpa using hbb)
  have hm : ∀ᶠ t : ℝ in 𝓝 0,0<dotProduct b (b-t • v) :=
    (isOpen_lt continuous_const
      (show Continuous (fun t : ℝ => dotProduct b (b-t • v)) from by fun_prop)).mem_nhds
        (by simpa using hbb)
  obtain ⟨l,u,hu,hs⟩ := mem_nhds_iff_exists_Ioo_subset.mp (inter_mem hp hm)
  obtain ⟨t,ht,htu⟩ := exists_between hu.2
  have hh := hs ⟨lt_trans hu.1 ht,htu⟩
  have he := quadratic_symmetric_shift_sum B b v t
  rw [hzero _ hh.1,hzero _ hh.2,hbB] at he
  have hcoeff : 2*t^2≠0 := mul_ne_zero (by norm_num) (pow_ne_zero _ ht.ne')
  exact (mul_eq_zero.mp (by linarith : (2*t^2)*dotProduct v (B *ᵥ v)=0)).resolve_left hcoeff

theorem exists_quadratic_nonzero_in_halfspace (B : Mat n n) (hB : B.transpose=B)
    (hB0 : B≠0) (b : Vec n) (hb : b≠0) :
    ∃a : Vec n,0<dotProduct b a ∧ dotProduct a (B *ᵥ a)≠0 := by
  by_contra hn
  push Not at hn
  exact hB0 (quadratic_zero_of_halfspace B hB b hb hn)

end CommodityClassification.Genericity
