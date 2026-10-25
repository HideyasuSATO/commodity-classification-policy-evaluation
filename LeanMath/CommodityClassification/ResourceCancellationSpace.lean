module

public import LeanMath.CommodityClassification.ParentKernelFactorization

/-! The observed resource-cancellation space, as a real linear subspace. -/
@[expose] public section
noncomputable section
namespace CommodityClassification.InputCoordinates
open Matrix
variable {n k g r : ℕ}

def cancellationSpace (Q : Mat n g) (J0 : Mat g k) : Submodule ℝ (Vec n) :=
  (LinearMap.ker J0.transpose.mulVecLin).map Q.mulVecLin

theorem mem_cancellationSpace_iff (Q : Mat n g) (J0 : Mat g k) (v : Vec n) :
    v ∈ cancellationSpace Q J0 ↔ ∃ γ : Vec g,Q *ᵥ γ=v ∧ J0.transpose *ᵥ γ=0 := by
  constructor
  · rintro ⟨γ,hγ,hv⟩
    exact ⟨γ,hv,hγ⟩
  · rintro ⟨γ,hv,hγ⟩
    exact ⟨γ,hγ,hv⟩

theorem matrix_columns_cancellation_iff (Q : Mat n g) (J0 : Mat g k) (V : Mat n r) :
    (∀ j : Fin r,(fun i => V i j) ∈ cancellationSpace Q J0) ↔
      ∃ Γ : Mat g r,V=Q*Γ ∧ J0.transpose*Γ=0 := by
  constructor
  · intro hv
    choose γ hγ hzero using fun j => (mem_cancellationSpace_iff Q J0 (fun i => V i j)).mp (hv j)
    refine ⟨(fun a j => γ j a),?_,?_⟩
    · ext i j
      exact (congrFun (hγ j) i).symm
    · ext i j
      exact congrFun (hzero j) i
  · rintro ⟨Γ,hV,hJ⟩ j
    apply (mem_cancellationSpace_iff Q J0 _).mpr
    exact ⟨(fun a => Γ a j),funext (fun i => (congrFun (congrFun hV i) j).symm),
      funext (fun i => congrFun (congrFun hJ i) j)⟩

end CommodityClassification.InputCoordinates
