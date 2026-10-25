module
import LeanMath.CommodityClassification.CheckCompositeActualHessian
import LeanMath.CommodityClassification.CompositeEconomicCurvature

set_option pp.universes false

#check @CommodityClassification.Composite.Data.relativeCovariance_moments
#print axioms CommodityClassification.Composite.Data.relativeCovariance_moments

#check @CommodityClassification.Composite.Data.compositeHessian_projected_split
#print axioms CommodityClassification.Composite.Data.compositeHessian_projected_split

#check @CommodityClassification.Composite.Data.compositeHessian_projected_covariance
#print axioms CommodityClassification.Composite.Data.compositeHessian_projected_covariance

#check @CommodityClassification.Composite.Data.compositeCost_actual_projected_curvature
#print axioms CommodityClassification.Composite.Data.compositeCost_actual_projected_curvature

#check @CommodityClassification.Equilibrium.BenchmarkFamily.nestProduction_exposure
#print axioms CommodityClassification.Equilibrium.BenchmarkFamily.nestProduction_exposure

#check @CommodityClassification.Equilibrium.BenchmarkFamily.nestProduction_relativeMoment
#print axioms CommodityClassification.Equilibrium.BenchmarkFamily.nestProduction_relativeMoment

#check @CommodityClassification.Equilibrium.BenchmarkFamily.nestProduction_relativeCovariance
#print axioms CommodityClassification.Equilibrium.BenchmarkFamily.nestProduction_relativeCovariance

#check @CommodityClassification.Equilibrium.BenchmarkFamily.nestProduction_totalInputs
#print axioms CommodityClassification.Equilibrium.BenchmarkFamily.nestProduction_totalInputs

#check @CommodityClassification.Equilibrium.BenchmarkFamily.nestProduction_relativeR
#print axioms CommodityClassification.Equilibrium.BenchmarkFamily.nestProduction_relativeR

#check @CommodityClassification.Equilibrium.BenchmarkFamily.nested_actual_composite_curvature
#print axioms CommodityClassification.Equilibrium.BenchmarkFamily.nested_actual_composite_curvature

#check @CommodityClassification.Composite.Data.relativeMoment
#print axioms CommodityClassification.Composite.Data.relativeMoment
#check @CommodityClassification.Composite.Data.relativeCovariance
#print axioms CommodityClassification.Composite.Data.relativeCovariance
#check @CommodityClassification.Composite.Data.relativeR
#print axioms CommodityClassification.Composite.Data.relativeR
