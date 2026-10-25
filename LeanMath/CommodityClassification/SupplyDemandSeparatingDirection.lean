module

public import LeanMath.CommodityClassification.PositiveDemandInterpolation

/-! Demand directions exposing a supply difference without changing observed supply primitives. -/
@[expose] public section
noncomputable section
namespace CommodityClassification.Equilibrium.BenchmarkFamily
open Matrix InputCoordinates Genericity
variable {n k g : ℕ} (F : BenchmarkFamily n k g)

theorem supply_difference_symmetric (hn : 0<n) (C : F.Candidate) :
    (F.supplyResponse C.val-F.supplyResponse F.parentMean).transpose=
      F.supplyResponse C.val-F.supplyResponse F.parentMean := by
  have hm : (F.supplyResponse F.parentMean).transpose=F.supplyResponse F.parentMean :=
    F.supplyResponse_symmetric hn F.parentMeanCandidate
  rw [transpose_sub,F.supplyResponse_symmetric hn C,hm]

theorem separating_demand_direction (hk : 0<k) (hb : F.b≠0)
    (i j : Fin n) (hij : i≠j) (hgroup : F.parents.group i=F.parents.group j)
    (γ : ℝ) (hγ : 0<γ) :
    ∃C : F.Candidate,∃a : Vec n,
      0<dotProduct F.b a ∧
      dotProduct a ((F.supplyResponse C.val-F.supplyResponse F.parentMean) *ᵥ a)≠0 ∧
      (interpolationMatrix F.b a γ).PosDef ∧ interpolationMatrix F.b a γ *ᵥ F.b=a := by
  obtain ⟨C,hC⟩ := F.same_parent_distinct_supply_responses hk i j hij hgroup
  obtain ⟨a,ha,hq,hE,hEb⟩ := exists_positive_interpolation
    (F.supplyResponse C.val-F.supplyResponse F.parentMean)
    (F.supply_difference_symmetric (Nat.zero_lt_of_lt i.isLt) C) hC F.b hb γ hγ
  exact ⟨C,a,ha,hq,hE,hEb⟩

end CommodityClassification.Equilibrium.BenchmarkFamily
