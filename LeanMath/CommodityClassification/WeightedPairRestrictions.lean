module

public import LeanMath.CommodityClassification.WeightedExchangeSpanning

/-! Basis-free and pairwise descriptions of the same report restrictions. -/
@[expose] public section
noncomputable section
namespace CommodityClassification.InputCoordinates
open Matrix
open scoped BigOperators
variable {n g r : ℕ}

theorem weighted_exchange_dot (q d : Vec n) (i j : Fin n) :
    dotProduct (weightedExchange q i j) d = d i/q i-d j/q j := by
  simp [weightedExchange,sub_dotProduct,smul_dotProduct,single_dotProduct,
    div_eq_mul_inv,mul_comm]

theorem weighted_exchange_image (q : Vec n) (L : Mat n n) (i j : Fin n) :
    L *ᵥ weightedExchange q i j = (fun a => L a i/q i-L a j/q j) := by
  ext a
  simp [weightedExchange,mulVec_sub,mulVec_smul,div_eq_mul_inv,mul_comm]

theorem matrix_vector_column_sum (V : Mat n r) (z : Vec r) :
    V *ᵥ z = ∑ j, z j • (fun i => V i j) := by
  ext i
  simp [mulVec,dotProduct,mul_comm]

theorem HiddenBasis.annihilator_iff (P : Partition n g) (q : Vec n)
    (H : HiddenBasis (P.Q q) r) (d : Vec n) :
    H.N.transpose *ᵥ d=0 ↔
      ∀ x : Vec n,(P.Q q).transpose *ᵥ x=0 → dotProduct x d=0 := by
  constructor
  · intro hd x hx
    obtain ⟨z,rfl⟩ := (H.spans x).mp hx
    rw [dotProduct_comm,← dotProduct_transpose_mulVec,hd,dotProduct_zero]
  · intro hd
    ext j
    have hx := (H.spans (H.N *ᵥ Pi.single j 1)).mpr ⟨Pi.single j 1,rfl⟩
    have hh := hd _ hx
    rw [mulVec_single_one] at hh
    exact hh

theorem Partition.kernel_annihilator_pair_iff (P : Partition n g) (q d : Vec n)
    (hq : ∀i,0<q i) :
    (∀ x : Vec n,(P.Q q).transpose *ᵥ x=0 → dotProduct x d=0) ↔
      ∀ i j : Fin n,P.group i=P.group j → d i/q i=d j/q j := by
  constructor
  · intro h i j hij
    have hh := h _ (P.weighted_exchange_hidden q hq i j hij)
    rw [weighted_exchange_dot] at hh
    exact sub_eq_zero.mp hh
  · intro h x hx
    rw [P.hidden_exchange_expansion q x hq hx,sum_dotProduct]
    apply Finset.sum_eq_zero
    intro i _
    rw [smul_dotProduct,weighted_exchange_dot,
      h i (P.representative (P.group i)) (P.representative_group _).symm,
      sub_self,smul_zero]

theorem HiddenBasis.annihilator_pair_iff (P : Partition n g) (q d : Vec n)
    (hq : ∀i,0<q i) (H : HiddenBasis (P.Q q) r) :
    H.N.transpose *ᵥ d=0 ↔ ∀ i j : Fin n,P.group i=P.group j → d i/q i=d j/q j :=
  (H.annihilator_iff P q d).trans (P.kernel_annihilator_pair_iff q d hq)

theorem Partition.kernel_image_pair_iff (P : Partition n g) (q : Vec n)
    (hq : ∀i,0<q i) (L : Mat n n) (S : Submodule ℝ (Vec n)) :
    (∀ x : Vec n,(P.Q q).transpose *ᵥ x=0 → L *ᵥ x ∈ S) ↔
      ∀ i j : Fin n,P.group i=P.group j → L *ᵥ weightedExchange q i j ∈ S := by
  constructor
  · exact fun h i j hij => h _ (P.weighted_exchange_hidden q hq i j hij)
  · intro h x hx
    rw [P.hidden_exchange_expansion q x hq hx,mulVec_sum]
    apply S.sum_mem
    intro i _
    rw [mulVec_smul]
    exact S.smul_mem _ (h i (P.representative (P.group i)) (P.representative_group _).symm)

theorem HiddenBasis.image_columns_iff (P : Partition n g) (q : Vec n)
    (H : HiddenBasis (P.Q q) r) (L : Mat n n) (S : Submodule ℝ (Vec n)) :
    (∀ j : Fin r,(fun i => (L*H.N) i j) ∈ S) ↔
      ∀ x : Vec n,(P.Q q).transpose *ᵥ x=0 → L *ᵥ x ∈ S := by
  constructor
  · intro h x hx
    obtain ⟨z,rfl⟩ := (H.spans x).mp hx
    rw [mulVec_mulVec,matrix_vector_column_sum]
    exact S.sum_mem (fun j _ => S.smul_mem _ (h j))
  · intro h j
    have hx := (H.spans (H.N *ᵥ Pi.single j 1)).mpr ⟨Pi.single j 1,rfl⟩
    have hh := h _ hx
    rw [mulVec_mulVec,mulVec_single_one] at hh
    exact hh

theorem HiddenBasis.image_columns_pair_iff (P : Partition n g) (q : Vec n)
    (hq : ∀i,0<q i) (H : HiddenBasis (P.Q q) r) (L : Mat n n)
    (S : Submodule ℝ (Vec n)) :
    (∀ j : Fin r,(fun i => (L*H.N) i j) ∈ S) ↔
      ∀ i j : Fin n,P.group i=P.group j → (fun a => L a i/q i-L a j/q j) ∈ S := by
  rw [H.image_columns_iff P q L S,P.kernel_image_pair_iff q hq L S]
  simp only [weighted_exchange_image]

end CommodityClassification.InputCoordinates
