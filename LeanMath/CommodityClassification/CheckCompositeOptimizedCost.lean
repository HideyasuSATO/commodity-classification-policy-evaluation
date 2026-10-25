module
import LeanMath.CommodityClassification.CheckNestEquilibriumMoments
import LeanMath.CommodityClassification.CompositeCostEconomicConnection

set_option pp.universes false

#check @CommodityClassification.Composite.Data.costs_positive
#print axioms CommodityClassification.Composite.Data.costs_positive

#check @CommodityClassification.Composite.Data.costs_benchmark
#print axioms CommodityClassification.Composite.Data.costs_benchmark

#check @CommodityClassification.Composite.Data.costs_smooth
#print axioms CommodityClassification.Composite.Data.costs_smooth

#check @CommodityClassification.Composite.Data.costDerivative_apply
#print axioms CommodityClassification.Composite.Data.costDerivative_apply

#check @CommodityClassification.Composite.Data.costs_derivative
#print axioms CommodityClassification.Composite.Data.costs_derivative

#check @CommodityClassification.Composite.Data.meanInputs_positive
#print axioms CommodityClassification.Composite.Data.meanInputs_positive

#check @CommodityClassification.Composite.Data.meanInputs_apply
#print axioms CommodityClassification.Composite.Data.meanInputs_apply

#check @CommodityClassification.Composite.Data.meanInputs_calibrated
#print axioms CommodityClassification.Composite.Data.meanInputs_calibrated

#check @CommodityClassification.Composite.Data.meanInputs_total
#print axioms CommodityClassification.Composite.Data.meanInputs_total

#check @CommodityClassification.Composite.Data.compositeCost_positive
#print axioms CommodityClassification.Composite.Data.compositeCost_positive

#check @CommodityClassification.Composite.Data.compositeCost_isLeast
#print axioms CommodityClassification.Composite.Data.compositeCost_isLeast

#check @CommodityClassification.Composite.Data.compositeMix_positive
#print axioms CommodityClassification.Composite.Data.compositeMix_positive

#check @CommodityClassification.Composite.Data.compositeMix_quantity
#print axioms CommodityClassification.Composite.Data.compositeMix_quantity

#check @CommodityClassification.Composite.Data.compositeMix_cost
#print axioms CommodityClassification.Composite.Data.compositeMix_cost

#check @CommodityClassification.Composite.Data.compositeMix_unique
#print axioms CommodityClassification.Composite.Data.compositeMix_unique

#check @CommodityClassification.Composite.Data.compositeCost_benchmark
#print axioms CommodityClassification.Composite.Data.compositeCost_benchmark

#check @CommodityClassification.Composite.Data.compositeMix_benchmark
#print axioms CommodityClassification.Composite.Data.compositeMix_benchmark

#check @CommodityClassification.Composite.Data.compositeCost_smooth
#print axioms CommodityClassification.Composite.Data.compositeCost_smooth

#check @CommodityClassification.Composite.Data.compositeCost_derivative
#print axioms CommodityClassification.Composite.Data.compositeCost_derivative

#check @CommodityClassification.Composite.Data.compositeCost_gradient
#print axioms CommodityClassification.Composite.Data.compositeCost_gradient

#check @CommodityClassification.Equilibrium.BenchmarkFamily.nestProduction_costs
#print axioms CommodityClassification.Equilibrium.BenchmarkFamily.nestProduction_costs

#check @CommodityClassification.Equilibrium.BenchmarkFamily.nestProduction_compositeCost
#print axioms CommodityClassification.Equilibrium.BenchmarkFamily.nestProduction_compositeCost

#check @CommodityClassification.Equilibrium.BenchmarkFamily.nestProduction_actual_minimum
#print axioms CommodityClassification.Equilibrium.BenchmarkFamily.nestProduction_actual_minimum

#check @CommodityClassification.Equilibrium.BenchmarkFamily.nestProduction_meanInputs
#print axioms CommodityClassification.Equilibrium.BenchmarkFamily.nestProduction_meanInputs

#check @CommodityClassification.Composite.Data
#print axioms CommodityClassification.Composite.Data
#check @CommodityClassification.Composite.Data.costData
#print axioms CommodityClassification.Composite.Data.costData
#check @CommodityClassification.Composite.Data.costs
#print axioms CommodityClassification.Composite.Data.costs
#check @CommodityClassification.Composite.Data.compositeCost
#print axioms CommodityClassification.Composite.Data.compositeCost
#check @CommodityClassification.Composite.Data.compositeMix
#print axioms CommodityClassification.Composite.Data.compositeMix
#check @CommodityClassification.Composite.Data.costDerivative
#print axioms CommodityClassification.Composite.Data.costDerivative
#check @CommodityClassification.Composite.Data.meanInputs
#print axioms CommodityClassification.Composite.Data.meanInputs
#check @CommodityClassification.Composite.Data.meanCostData
#print axioms CommodityClassification.Composite.Data.meanCostData
#check @CommodityClassification.Equilibrium.BenchmarkFamily.nestProduction
#print axioms CommodityClassification.Equilibrium.BenchmarkFamily.nestProduction
