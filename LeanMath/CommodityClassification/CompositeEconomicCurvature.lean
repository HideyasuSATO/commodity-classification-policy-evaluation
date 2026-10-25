module

public import LeanMath.CommodityClassification.CompositeProjectedCurvature

/-! The printed covariance identity for an actual equilibrium candidate and its frame. -/
@[expose] public section
noncomputable section
set_option maxHeartbeats 1200000
namespace CommodityClassification.Equilibrium.BenchmarkFamily
open Matrix InputCoordinates
open scoped BigOperators
variable {n k h g : ℕ} (F : BenchmarkFamily n k h)

theorem nestProduction_exposure (G : Partition n g) (η : Vec g) (hη : ∀a,0<η a)
    (C : F.Candidate) (a : Fin g) :
    (F.nestProduction G η hη C a).A*F.frame.V=(F.nestData G η hη).nestInputs C.val a := by
  ext i l
  exact congrFun (congrFun (F.frame.reconstruct_exposure F.p C.val)
    ((F.nestData G η hη).product a i)) l

theorem nestProduction_relativeMoment (G : Partition n g) (η : Vec g) (hη : ∀a,0<η a)
    (C : F.Candidate) (a : Fin g) :
    (F.nestProduction G η hη C a).relativeMoment F.frame.V=G.report F.q C.val a := by
  rw [Composite.Data.relativeMoment,F.nestProduction_exposure]
  exact (F.nestData G η hη).nestFirstMoment_eq_report C.val a

theorem nestProduction_relativeCovariance (G : Partition n g) (η : Vec g) (hη : ∀a,0<η a)
    (C : F.Candidate) (a : Fin g) :
    (F.nestProduction G η hη C a).relativeCovariance F.frame.V=
      (F.nestData G η hη).nestCovariance C.val a := by
  rw [Composite.Data.relativeCovariance,F.nestProduction_exposure]
  exact ((F.nestData G η hη).nestCovariance_conjugate C.val a).symm

theorem nestProduction_totalInputs (G : Partition n g) (η : Vec g) (hη : ∀a,0<η a)
    (C : F.Candidate) (a : Fin g) :
    Supply.totalInputs (F.nestProduction G η hη C a).nest.q (F.nestProduction G η hη C a).A=
      G.report F.q (F.model C).A a := by
  funext l
  change (∑j,F.q ((F.nestData G η hη).product a j)*
    (F.model C).A ((F.nestData G η hη).product a j) l)=_
  rw [G.report_apply]
  exact (F.nestData G η hη).sum_restrict a (fun i => F.q i*(F.model C).A i l)

theorem nestProduction_relativeR (G : Partition n g) (η : Vec g) (hη : ∀a,0<η a)
    (C : F.Candidate) (a : Fin g) :
    (F.nestProduction G η hη C a).relativeR F.frame.V=
      Supply.knownR F.frame.w F.frame.V (G.report F.q (F.model C).A a) := by
  rw [Composite.Data.relativeR,F.nestProduction_totalInputs]
  rfl

theorem nested_actual_composite_curvature (G : Partition n g) (η : Vec g) (hη : ∀a,0<η a)
    (C : F.Candidate) (a : Fin g) :
    (-G.sales F.p F.q a) • (F.frame.V.transpose*
      Matrix.of (fun j l => CESCost.pricePartial
        (CESCost.pricePartial (F.nestProduction G η hη C a).compositeCost j) l F.frame.w)*F.frame.V)=
      F.sigma • (Supply.knownR F.frame.w F.frame.V (G.report F.q (F.model C).A a)-
        (G.sales F.p F.q a)⁻¹ • vecMulVec (G.report F.q C.val a) (G.report F.q C.val a))+
      (η a-F.sigma) • (F.nestData G η hη).nestCovariance C.val a := by
  have he := (F.nestProduction G η hη C a).compositeCost_actual_projected_curvature F.frame.V
  rw [F.nestProduction_relativeMoment,F.nestProduction_relativeCovariance,F.nestProduction_relativeR] at he
  have hs : (F.nestProduction G η hη C a).nest.sales=G.sales F.p F.q a :=
    (F.nestData G η hη).nest_sales a
  rw [hs] at he
  exact he

end CommodityClassification.Equilibrium.BenchmarkFamily
