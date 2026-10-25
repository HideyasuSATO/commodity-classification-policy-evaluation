module
import LeanMath.CommodityClassification.CheckSingleParentCancellation
import LeanMath.CommodityClassification.EconomicClassificationWitnesses

set_option pp.universes false

#check @CommodityClassification.FixedAnswer.changesNearZero_of_first
#print axioms CommodityClassification.FixedAnswer.changesNearZero_of_first

#check @CommodityClassification.FixedAnswer.changesNearZero_of_second
#print axioms CommodityClassification.FixedAnswer.changesNearZero_of_second

#check @CommodityClassification.FixedAnswer.Data.changes_admissibly
#print axioms CommodityClassification.FixedAnswer.Data.changes_admissibly

#check @CommodityClassification.FixedAnswer.Data.admissibleChanges_nonzero
#print axioms CommodityClassification.FixedAnswer.Data.admissibleChanges_nonzero

#check @CommodityClassification.FixedAnswer.Data.zeroLoad_change_direction
#print axioms CommodityClassification.FixedAnswer.Data.zeroLoad_change_direction

#check @CommodityClassification.FixedAnswer.Data.firstDerivative_change_direction
#print axioms CommodityClassification.FixedAnswer.Data.firstDerivative_change_direction

#check @CommodityClassification.FixedAnswer.Data.secondDerivative_change_direction
#print axioms CommodityClassification.FixedAnswer.Data.secondDerivative_change_direction

#check @CommodityClassification.FixedAnswer.Data.failure_has_change_direction
#print axioms CommodityClassification.FixedAnswer.Data.failure_has_change_direction

#check @CommodityClassification.Equilibrium.BenchmarkFamily.failed_answer_direction_witness
#print axioms CommodityClassification.Equilibrium.BenchmarkFamily.failed_answer_direction_witness

#check @CommodityClassification.Equilibrium.BenchmarkFamily.pair_failure_direction_witness
#print axioms CommodityClassification.Equilibrium.BenchmarkFamily.pair_failure_direction_witness

#check @CommodityClassification.Equilibrium.BenchmarkFamily.pair_failure_common_benchmark_witness
#print axioms CommodityClassification.Equilibrium.BenchmarkFamily.pair_failure_common_benchmark_witness

#check @CommodityClassification.Equilibrium.BenchmarkFamily.unequal_attributes_common_benchmark_witness
#print axioms CommodityClassification.Equilibrium.BenchmarkFamily.unequal_attributes_common_benchmark_witness

#check @CommodityClassification.FixedAnswer.ChangesNearZero
#check @CommodityClassification.FixedAnswer.Data.AdmissibleChanges
#check @CommodityClassification.Equilibrium.BenchmarkFamily.SameObservationWitness
