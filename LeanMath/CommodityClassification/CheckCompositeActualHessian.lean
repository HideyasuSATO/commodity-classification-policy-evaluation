module
import LeanMath.CommodityClassification.CheckCompositeOptimizedCost
import LeanMath.CommodityClassification.CompositeHessianChainRule

set_option pp.universes false

#check @CommodityClassification.Composite.Data.costs_current_derivative
#print axioms CommodityClassification.Composite.Data.costs_current_derivative

#check @CommodityClassification.Composite.Data.currentCostDerivative_single
#print axioms CommodityClassification.Composite.Data.currentCostDerivative_single

#check @CommodityClassification.Composite.Data.compositeCost_current_derivative
#print axioms CommodityClassification.Composite.Data.compositeCost_current_derivative

#check @CommodityClassification.Composite.Data.compositeCost_current_partial
#print axioms CommodityClassification.Composite.Data.compositeCost_current_partial

#check @CommodityClassification.Composite.Data.composite_partial_derivative
#print axioms CommodityClassification.Composite.Data.composite_partial_derivative

#check @CommodityClassification.Composite.Data.compositeHessianRow_apply
#print axioms CommodityClassification.Composite.Data.compositeHessianRow_apply

#check @CommodityClassification.Composite.Data.compositeCost_actual_hessian
#print axioms CommodityClassification.Composite.Data.compositeCost_actual_hessian

#check @CommodityClassification.Composite.Data.currentCostDerivative
#print axioms CommodityClassification.Composite.Data.currentCostDerivative
#check @CommodityClassification.Composite.Data.compositeHessianRow
#print axioms CommodityClassification.Composite.Data.compositeHessianRow
#check @CommodityClassification.Composite.Data.compositeHessian
#print axioms CommodityClassification.Composite.Data.compositeHessian
