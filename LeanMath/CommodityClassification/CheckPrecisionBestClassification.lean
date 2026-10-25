module
import LeanMath.CommodityClassification.CheckPrecisionFiniteError
import LeanMath.CommodityClassification.PrecisionBestClassification

set_option pp.universes false

#check @CommodityClassification.InputCoordinates.Partition.exists_same_cell_pair
#print axioms CommodityClassification.InputCoordinates.Partition.exists_same_cell_pair

#check @CommodityClassification.InputCoordinates.Partition.exists_successor_refinement
#print axioms CommodityClassification.InputCoordinates.Partition.exists_successor_refinement

#check @CommodityClassification.InputCoordinates.Partition.exists_exact_refinement
#print axioms CommodityClassification.InputCoordinates.Partition.exists_exact_refinement

#check @CommodityClassification.Precision.Data.exact_type_refinement_exists
#print axioms CommodityClassification.Precision.Data.exact_type_refinement_exists

#check @CommodityClassification.Precision.Data.exact_type_partition_exists
#print axioms CommodityClassification.Precision.Data.exact_type_partition_exists

#check @CommodityClassification.Precision.Data.classificationWidths_nonempty
#print axioms CommodityClassification.Precision.Data.classificationWidths_nonempty

#check @CommodityClassification.Precision.Data.classificationWidths_bddBelow
#print axioms CommodityClassification.Precision.Data.classificationWidths_bddBelow

#check @CommodityClassification.Precision.Data.bestClassificationWidth_lower
#print axioms CommodityClassification.Precision.Data.bestClassificationWidth_lower

#check @CommodityClassification.Precision.Data.bestClassificationWidth_upper
#print axioms CommodityClassification.Precision.Data.bestClassificationWidth_upper

#check @CommodityClassification.Precision.Data.bestClassificationWidth_error
#print axioms CommodityClassification.Precision.Data.bestClassificationWidth_error

#check @CommodityClassification.Precision.Data.bestClassificationWidth_tendsto
#print axioms CommodityClassification.Precision.Data.bestClassificationWidth_tendsto

#check @CommodityClassification.InputCoordinates.Partition.splitProduct
#print axioms CommodityClassification.InputCoordinates.Partition.splitProduct
#check @CommodityClassification.InputCoordinates.Partition.splitProduct_refinement
#print axioms CommodityClassification.InputCoordinates.Partition.splitProduct_refinement
#check @CommodityClassification.Precision.Data.classificationWidths
#print axioms CommodityClassification.Precision.Data.classificationWidths
#check @CommodityClassification.Precision.Data.bestClassificationWidth
#print axioms CommodityClassification.Precision.Data.bestClassificationWidth
