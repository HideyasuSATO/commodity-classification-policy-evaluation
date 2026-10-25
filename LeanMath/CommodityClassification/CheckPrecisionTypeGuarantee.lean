module
import LeanMath.CommodityClassification.CheckPrecisionScalarEnvelope
import LeanMath.CommodityClassification.PrecisionTypeGuarantee

set_option pp.universes false

#check @CommodityClassification.Precision.Data.type_exists
#print axioms CommodityClassification.Precision.Data.type_exists

#check @CommodityClassification.Precision.Data.typePartition_respecting
#print axioms CommodityClassification.Precision.Data.typePartition_respecting

#check @CommodityClassification.Precision.Data.typePartition_cell_zero
#print axioms CommodityClassification.Precision.Data.typePartition_cell_zero

#check @CommodityClassification.Precision.Data.typePartition_cell_one
#print axioms CommodityClassification.Precision.Data.typePartition_cell_one

#check @CommodityClassification.Precision.Data.typePartition_weights
#print axioms CommodityClassification.Precision.Data.typePartition_weights

#check @CommodityClassification.Precision.Data.typeInputTotal_sum
#print axioms CommodityClassification.Precision.Data.typeInputTotal_sum

#check @CommodityClassification.Precision.Data.typePartition_totals
#print axioms CommodityClassification.Precision.Data.typePartition_totals

#check @CommodityClassification.Precision.Data.typePartition_mean
#print axioms CommodityClassification.Precision.Data.typePartition_mean

#check @CommodityClassification.Precision.Data.typePartition_lowerMoment
#print axioms CommodityClassification.Precision.Data.typePartition_lowerMoment

#check @CommodityClassification.Precision.Data.refinement_typeRespecting
#print axioms CommodityClassification.Precision.Data.refinement_typeRespecting

#check @CommodityClassification.Precision.Data.refinement_groupTotal
#print axioms CommodityClassification.Precision.Data.refinement_groupTotal

#check @CommodityClassification.Precision.Data.refinement_positiveFiber
#print axioms CommodityClassification.Precision.Data.refinement_positiveFiber

#check @CommodityClassification.Precision.Data.refinement_welfareDifferences
#print axioms CommodityClassification.Precision.Data.refinement_welfareDifferences

#check @CommodityClassification.Precision.Data.refinement_answerWidth_le
#print axioms CommodityClassification.Precision.Data.refinement_answerWidth_le

#check @CommodityClassification.Precision.Data.refinement_manuscriptWidth_le
#print axioms CommodityClassification.Precision.Data.refinement_manuscriptWidth_le

#check @CommodityClassification.Precision.Data.feasibleWidths_eq_report_image
#print axioms CommodityClassification.Precision.Data.feasibleWidths_eq_report_image

#check @CommodityClassification.Precision.Data.exAnteWidth_report_formula
#print axioms CommodityClassification.Precision.Data.exAnteWidth_report_formula

#check @CommodityClassification.Precision.Data.typeRespecting_lowerMoment
#print axioms CommodityClassification.Precision.Data.typeRespecting_lowerMoment

#check @CommodityClassification.Precision.Data.typeRespecting_answer_upper
#print axioms CommodityClassification.Precision.Data.typeRespecting_answer_upper

#check @CommodityClassification.Precision.Data.feasibleWidths_nonempty
#print axioms CommodityClassification.Precision.Data.feasibleWidths_nonempty

#check @CommodityClassification.Precision.Data.feasibleWidths_bddAbove
#print axioms CommodityClassification.Precision.Data.feasibleWidths_bddAbove

#check @CommodityClassification.Precision.Data.exAnteWidth_upper
#print axioms CommodityClassification.Precision.Data.exAnteWidth_upper

#check @CommodityClassification.Precision.Data.exAnteWidth_le_iff
#print axioms CommodityClassification.Precision.Data.exAnteWidth_le_iff

#check @CommodityClassification.Precision.Data.typePartition_exAnte_upper
#print axioms CommodityClassification.Precision.Data.typePartition_exAnte_upper

#check @CommodityClassification.Precision.Data.refinement_exAnteWidth_le
#print axioms CommodityClassification.Precision.Data.refinement_exAnteWidth_le

#check @CommodityClassification.Precision.Data.type_refinement_exAnte_upper
#print axioms CommodityClassification.Precision.Data.type_refinement_exAnte_upper

#check @CommodityClassification.Precision.Data.typePartition
#print axioms CommodityClassification.Precision.Data.typePartition
#check @CommodityClassification.Precision.Data.feasibleWidths
#print axioms CommodityClassification.Precision.Data.feasibleWidths
#check @CommodityClassification.Precision.Data.exAnteWidth
#print axioms CommodityClassification.Precision.Data.exAnteWidth
#check @CommodityClassification.Precision.Data.feasibleReports
#print axioms CommodityClassification.Precision.Data.feasibleReports
