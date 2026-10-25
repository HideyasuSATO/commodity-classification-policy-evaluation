module
import LeanMath.CommodityClassification.CheckEquilibriumDerivative
import LeanMath.CommodityClassification.EquilibriumLocalApplication

-- Integrated kernel checks, retaining all prior research checks.
set_option pp.universes false

#check @CommodityClassification.Equilibrium.Model.demandC1_of_open
#print axioms CommodityClassification.Equilibrium.Model.demandC1_of_open

#check @CommodityClassification.Equilibrium.Model.currentPrice_contDiff
#print axioms CommodityClassification.Equilibrium.Model.currentPrice_contDiff

#check @CommodityClassification.Equilibrium.Model.costs_contDiffAt
#print axioms CommodityClassification.Equilibrium.Model.costs_contDiffAt

#check @CommodityClassification.Equilibrium.Model.currentInputs_contDiffAt
#print axioms CommodityClassification.Equilibrium.Model.currentInputs_contDiffAt

#check @CommodityClassification.Equilibrium.Model.prices_contDiffAt
#print axioms CommodityClassification.Equilibrium.Model.prices_contDiffAt

#check @CommodityClassification.Equilibrium.Model.quantities_contDiffAt
#print axioms CommodityClassification.Equilibrium.Model.quantities_contDiffAt

#check @CommodityClassification.Equilibrium.Model.factorDemand_contDiffAt
#print axioms CommodityClassification.Equilibrium.Model.factorDemand_contDiffAt

#check @CommodityClassification.Equilibrium.Model.reduced_contDiffAt
#print axioms CommodityClassification.Equilibrium.Model.reduced_contDiffAt

#check @CommodityClassification.Equilibrium.Model.price_partial_eq
#print axioms CommodityClassification.Equilibrium.Model.price_partial_eq

#check @CommodityClassification.Equilibrium.Model.price_partial_invertible
#print axioms CommodityClassification.Equilibrium.Model.price_partial_invertible

#check @CommodityClassification.Equilibrium.Model.reduced_base
#print axioms CommodityClassification.Equilibrium.Model.reduced_base

#check @CommodityClassification.Equilibrium.Model.localPricePath_base
#print axioms CommodityClassification.Equilibrium.Model.localPricePath_base

#check @CommodityClassification.Equilibrium.Model.localPricePath_contDiffAt
#print axioms CommodityClassification.Equilibrium.Model.localPricePath_contDiffAt

#check @CommodityClassification.Equilibrium.Model.localPricePath_clears
#print axioms CommodityClassification.Equilibrium.Model.localPricePath_clears

#check @CommodityClassification.Equilibrium.Model.localPricePath_unique
#print axioms CommodityClassification.Equilibrium.Model.localPricePath_unique

#check @CommodityClassification.Equilibrium.Model.localPricePath_unique_open
#print axioms CommodityClassification.Equilibrium.Model.localPricePath_unique_open

#check @CommodityClassification.Equilibrium.Model.recoveredNumeraire_base
#print axioms CommodityClassification.Equilibrium.Model.recoveredNumeraire_base

#check @CommodityClassification.Equilibrium.Model.recoveredNumeraire_clears
#print axioms CommodityClassification.Equilibrium.Model.recoveredNumeraire_clears

#check @CommodityClassification.Equilibrium.Model.recoveredNumeraire_unique
#print axioms CommodityClassification.Equilibrium.Model.recoveredNumeraire_unique

#check @CommodityClassification.Equilibrium.Model.full_clearing_iff
#print axioms CommodityClassification.Equilibrium.Model.full_clearing_iff

#check @CommodityClassification.Equilibrium.Model.recoveredNumeraire_contDiffAt
#print axioms CommodityClassification.Equilibrium.Model.recoveredNumeraire_contDiffAt

#check @CommodityClassification.Equilibrium.Model.localNumerairePath_base
#print axioms CommodityClassification.Equilibrium.Model.localNumerairePath_base

#check @CommodityClassification.Equilibrium.Model.localNumerairePath_contDiffAt
#print axioms CommodityClassification.Equilibrium.Model.localNumerairePath_contDiffAt

#check @CommodityClassification.Equilibrium.Model.local_full_clearing
#print axioms CommodityClassification.Equilibrium.Model.local_full_clearing

#check @CommodityClassification.Equilibrium.Model.local_full_uniqueness
#print axioms CommodityClassification.Equilibrium.Model.local_full_uniqueness

#check @CommodityClassification.Equilibrium.Model.positiveState_neighborhood
#print axioms CommodityClassification.Equilibrium.Model.positiveState_neighborhood

#check @CommodityClassification.Equilibrium.Model.local_positive_state
#print axioms CommodityClassification.Equilibrium.Model.local_positive_state

#check @CommodityClassification.Equilibrium.Model.local_common_neighborhood
#print axioms CommodityClassification.Equilibrium.Model.local_common_neighborhood

#check @CommodityClassification.Equilibrium.affineDemand_contDiff
#print axioms CommodityClassification.Equilibrium.affineDemand_contDiff

#check @CommodityClassification.Equilibrium.affineDemand_eq_choice
#print axioms CommodityClassification.Equilibrium.affineDemand_eq_choice

#check @CommodityClassification.Equilibrium.quadraticChoice_foc
#print axioms CommodityClassification.Equilibrium.quadraticChoice_foc

#check @CommodityClassification.Equilibrium.quadratic_form_derivative
#print axioms CommodityClassification.Equilibrium.quadratic_form_derivative

#check @CommodityClassification.Equilibrium.quadraticUtility_derivative
#print axioms CommodityClassification.Equilibrium.quadraticUtility_derivative

#check @CommodityClassification.Equilibrium.quadraticSurplus_derivative
#print axioms CommodityClassification.Equilibrium.quadraticSurplus_derivative

#check @CommodityClassification.Equilibrium.quadraticSurplus_stationary
#print axioms CommodityClassification.Equilibrium.quadraticSurplus_stationary

#check @CommodityClassification.Equilibrium.quadraticSurplus_gap
#print axioms CommodityClassification.Equilibrium.quadraticSurplus_gap

#check @CommodityClassification.Equilibrium.quadraticSurplus_maximum
#print axioms CommodityClassification.Equilibrium.quadraticSurplus_maximum

#check @CommodityClassification.Equilibrium.quadraticSurplus_strict
#print axioms CommodityClassification.Equilibrium.quadraticSurplus_strict

#check @CommodityClassification.Equilibrium.affineDemand_local
#print axioms CommodityClassification.Equilibrium.affineDemand_local

#check @CommodityClassification.Equilibrium.Model.constructed_positive_path
#print axioms CommodityClassification.Equilibrium.Model.constructed_positive_path

#check @CommodityClassification.Equilibrium.Model.constructed_path_derivatives
#print axioms CommodityClassification.Equilibrium.Model.constructed_path_derivatives

#check @CommodityClassification.Equilibrium.Model.economic_local_existence
#print axioms CommodityClassification.Equilibrium.Model.economic_local_existence

#check @CommodityClassification.Equilibrium.Model.ofAffine_demandC1
#print axioms CommodityClassification.Equilibrium.Model.ofAffine_demandC1

#check @CommodityClassification.Equilibrium.Model.quadratic_local_existence
#print axioms CommodityClassification.Equilibrium.Model.quadratic_local_existence

#check @CommodityClassification.Equilibrium.local_utility_optimum
#print axioms CommodityClassification.Equilibrium.local_utility_optimum

#check @CommodityClassification.Equilibrium.Model.factor_price_path_derivative
#print axioms CommodityClassification.Equilibrium.Model.factor_price_path_derivative

#check @CommodityClassification.Equilibrium.Model.consumer_price_path_derivative
#print axioms CommodityClassification.Equilibrium.Model.consumer_price_path_derivative

#check @CommodityClassification.Equilibrium.Model.zero_relative_dimension
#print axioms CommodityClassification.Equilibrium.Model.zero_relative_dimension

#check @CommodityClassification.Equilibrium.Model.local_path_stays_local
#print axioms CommodityClassification.Equilibrium.Model.local_path_stays_local

#check @CommodityClassification.Equilibrium.Model.quadratic_path_local_optimum
#print axioms CommodityClassification.Equilibrium.Model.quadratic_path_local_optimum

#check @CommodityClassification.Equilibrium.Example.model_demandC1
#print axioms CommodityClassification.Equilibrium.Example.model_demandC1

#check @CommodityClassification.Equilibrium.Example.concrete_local_existence
#print axioms CommodityClassification.Equilibrium.Example.concrete_local_existence

#check @CommodityClassification.Equilibrium.Model.DemandC1

#check @CommodityClassification.Equilibrium.Model.endowment

#check @CommodityClassification.Equilibrium.Model.localPricePath

#check @CommodityClassification.Equilibrium.Model.recoveredNumeraire

#check @CommodityClassification.Equilibrium.Model.localNumerairePath

#check @CommodityClassification.Equilibrium.Model.PositiveState

#check @CommodityClassification.Equilibrium.quadraticUtility

#check @CommodityClassification.Equilibrium.quadraticSurplus

#check @CommodityClassification.Equilibrium.quadraticChoice

#check @CommodityClassification.Equilibrium.Model.PositiveLocalPath
