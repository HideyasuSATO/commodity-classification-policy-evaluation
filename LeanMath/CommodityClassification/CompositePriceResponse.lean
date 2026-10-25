module

public import LeanMath.CommodityClassification.PositivePathSolution

/-! The derivative of the actual original expenditure index along a policy path. -/
@[expose] public section
noncomputable section
set_option maxHeartbeats 1000000
namespace CommodityClassification.Equilibrium.BenchmarkFamily
open Matrix InputCoordinates
variable {n k h g : ℕ} (F : BenchmarkFamily n k h)

theorem composite_index_price_response (P : Partition n g) (β : Vec g)
    (hb : F.b=P.Q F.p *ᵥ β) (C : F.Candidate) (z : Vec k) :
    (F.nestData P (fun _ => F.sigma) (fun _ => F.hsigma)).priceDerivative (F.b+C.val *ᵥ z)=
      β+F.compositeCoordinates P C *ᵥ z := by
  rw [map_add]
  have ht := (F.nestData P (fun _ => F.sigma) (fun _ => F.hsigma)).proportional_price_response β
  change (F.nestData P (fun _ => F.sigma) (fun _ => F.hsigma)).priceDerivative
    (P.Q F.p *ᵥ β)=β at ht
  rw [hb,ht]
  congr 1
  rw [(F.nestData P (fun _ => F.sigma) (fun _ => F.hsigma)).priceDerivative_matrix]
  change (P.inverseSales F.p F.q*(P.Q F.q).transpose) *ᵥ (C.val *ᵥ z)=_
  simp only [compositeCoordinates,Partition.normalizedReport,Partition.report,
    Partition.inverseSales,Matrix.mulVec_mulVec,Matrix.mul_assoc]

theorem composite_index_path_derivative (P : Partition n g) (β : Vec g)
    (hb : F.b=P.Q F.p *ᵥ β) (C : F.Candidate) (u : ℝ → Vec k) (z : Vec k)
    (hu0 : u 0=0) (hu : HasDerivAt u z 0) :
    HasDerivAt
      (fun t => (F.nestData P (fun _ => F.sigma) (fun _ => F.hsigma)).priceMap
        ((F.model C).prices (t,u t))) (β+F.compositeCoordinates P C *ᵥ z) 0 := by
  have hh := (F.model C).consumer_price_path_derivative u z hu0 hu
  have hd : HasFDerivAt
      (F.nestData P (fun _ => F.sigma) (fun _ => F.hsigma)).priceMap
      (F.nestData P (fun _ => F.sigma) (fun _ => F.hsigma)).priceDerivative
      ((F.model C).prices (0,u 0)) := by
    rw [hu0,show ((0 : ℝ),(0 : Vec k))=(0 : PolicyPrice k) from rfl,
      (F.model C).prices_zero]
    exact (F.nestData P (fun _ => F.sigma) (fun _ => F.hsigma)).priceMap_hasFDerivAt
  have hcomp := hd.comp_hasDerivAt (0 : ℝ) hh
  change HasDerivAt _
    ((F.nestData P (fun _ => F.sigma) (fun _ => F.hsigma)).priceDerivative (F.b+C.val *ᵥ z)) 0 at hcomp
  rw [F.composite_index_price_response P β hb C z] at hcomp
  exact hcomp

end CommodityClassification.Equilibrium.BenchmarkFamily
