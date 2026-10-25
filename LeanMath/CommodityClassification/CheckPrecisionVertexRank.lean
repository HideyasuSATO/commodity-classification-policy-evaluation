module
import LeanMath.CommodityClassification.CheckPrecisionObservationWidth
import LeanMath.CommodityClassification.PrecisionSalesConcentration

set_option pp.universes false

#check @CommodityClassification.Precision.Box.mem_interiors
#print axioms CommodityClassification.Precision.Box.mem_interiors

#check @CommodityClassification.Precision.Box.slice_compact
#print axioms CommodityClassification.Precision.Box.slice_compact

#check @CommodityClassification.Precision.Box.supported_small_perturbation
#print axioms CommodityClassification.Precision.Box.supported_small_perturbation

#check @CommodityClassification.Precision.Box.vertex_supported_kernel_zero
#print axioms CommodityClassification.Precision.Box.vertex_supported_kernel_zero

#check @CommodityClassification.Precision.Box.supportedExtension_apply
#print axioms CommodityClassification.Precision.Box.supportedExtension_apply

#check @CommodityClassification.Precision.Box.supportedExtension_outside
#print axioms CommodityClassification.Precision.Box.supportedExtension_outside

#check @CommodityClassification.Precision.Box.vertex_restricted_injective
#print axioms CommodityClassification.Precision.Box.vertex_restricted_injective

#check @CommodityClassification.Precision.Box.vertex_interior_rank
#print axioms CommodityClassification.Precision.Box.vertex_interior_rank

#check @CommodityClassification.Precision.Box.vertex_interior_count
#print axioms CommodityClassification.Precision.Box.vertex_interior_count

#check @CommodityClassification.Precision.Data.theta_add
#print axioms CommodityClassification.Precision.Data.theta_add

#check @CommodityClassification.Precision.Data.theta_smul
#print axioms CommodityClassification.Precision.Data.theta_smul

#check @CommodityClassification.Precision.Data.classificationConstraints_eq_iff
#print axioms CommodityClassification.Precision.Data.classificationConstraints_eq_iff

#check @CommodityClassification.Precision.Data.classificationSlice_eq
#print axioms CommodityClassification.Precision.Data.classificationSlice_eq

#check @CommodityClassification.Precision.Data.classification_vertex_count
#print axioms CommodityClassification.Precision.Data.classification_vertex_count

#check @CommodityClassification.Precision.Data.classification_vertex_maximum
#print axioms CommodityClassification.Precision.Data.classification_vertex_maximum

#check @CommodityClassification.Precision.Data.secondMoment_deficit_bound
#print axioms CommodityClassification.Precision.Data.secondMoment_deficit_bound

#check @CommodityClassification.Precision.Data.classification_vertex_weight_bound
#print axioms CommodityClassification.Precision.Data.classification_vertex_weight_bound

#check @CommodityClassification.Precision.Data.salesSums_nonempty
#print axioms CommodityClassification.Precision.Data.salesSums_nonempty

#check @CommodityClassification.Precision.Data.salesSums_finite
#print axioms CommodityClassification.Precision.Data.salesSums_finite

#check @CommodityClassification.Precision.Data.largestSales_isGreatest
#print axioms CommodityClassification.Precision.Data.largestSales_isGreatest

#check @CommodityClassification.Precision.Data.subset_sales_le_largest
#print axioms CommodityClassification.Precision.Data.subset_sales_le_largest

#check @CommodityClassification.Precision.Data.largestSales_bounds
#print axioms CommodityClassification.Precision.Data.largestSales_bounds

#check @CommodityClassification.Precision.Data.largestSales_attained
#print axioms CommodityClassification.Precision.Data.largestSales_attained

#check @CommodityClassification.Precision.Data.largestSales_maximizer_ordered
#print axioms CommodityClassification.Precision.Data.largestSales_maximizer_ordered

#check @CommodityClassification.Precision.Data.largestSales_top_weights
#print axioms CommodityClassification.Precision.Data.largestSales_top_weights

#check @CommodityClassification.Precision.Data.largestSales_monotone
#print axioms CommodityClassification.Precision.Data.largestSales_monotone

#check @CommodityClassification.Precision.Data.largestSales_saturated
#print axioms CommodityClassification.Precision.Data.largestSales_saturated

#check @CommodityClassification.Precision.Data.classification_vertex_concentration
#print axioms CommodityClassification.Precision.Data.classification_vertex_concentration

#check @CommodityClassification.Precision.Box.slice
#print axioms CommodityClassification.Precision.Box.slice
#check @CommodityClassification.Precision.Box.interiors
#print axioms CommodityClassification.Precision.Box.interiors
#check @CommodityClassification.Precision.Box.supportedExtension
#print axioms CommodityClassification.Precision.Box.supportedExtension
#check @CommodityClassification.Precision.Data.classificationConstraints
#print axioms CommodityClassification.Precision.Data.classificationConstraints
#check @CommodityClassification.Precision.Data.salesSums
#print axioms CommodityClassification.Precision.Data.salesSums
#check @CommodityClassification.Precision.Data.largestSales
#print axioms CommodityClassification.Precision.Data.largestSales
#check @CommodityClassification.Precision.Data.coarseSales
#print axioms CommodityClassification.Precision.Data.coarseSales
