module
import LeanMath.CommodityClassification.CheckRankOneWelfareIdentity
import LeanMath.CommodityClassification.NestedMeanExchange

set_option pp.universes false

#check @CommodityClassification.RankOne.outer_conjugate
#print axioms CommodityClassification.RankOne.outer_conjugate

#check @CommodityClassification.RankOne.mean_conjugate_update
#print axioms CommodityClassification.RankOne.mean_conjugate_update

#check @CommodityClassification.InputCoordinates.Partition.exchange_report
#print axioms CommodityClassification.InputCoordinates.Partition.exchange_report

#check @CommodityClassification.InputCoordinates.Partition.mean_twoSupport_zero
#print axioms CommodityClassification.InputCoordinates.Partition.mean_twoSupport_zero

#check @CommodityClassification.DemandNests.Data.exchange_load_zero
#print axioms CommodityClassification.DemandNests.Data.exchange_load_zero

#check @CommodityClassification.DemandNests.Data.mean_exchange_orthogonal
#print axioms CommodityClassification.DemandNests.Data.mean_exchange_orthogonal

#check @CommodityClassification.DemandNests.Data.exchange_adjusted_quadratic
#print axioms CommodityClassification.DemandNests.Data.exchange_adjusted_quadratic

#check @CommodityClassification.DemandNests.Data.exchange_load_preserved
#print axioms CommodityClassification.DemandNests.Data.exchange_load_preserved

#check @CommodityClassification.DemandNests.Data.mean_exchange_K
#print axioms CommodityClassification.DemandNests.Data.mean_exchange_K

