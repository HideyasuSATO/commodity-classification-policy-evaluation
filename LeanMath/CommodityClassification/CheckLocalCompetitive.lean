module
import LeanMath.CommodityClassification.CheckWelfareBridge
import LeanMath.CommodityClassification.LocalCompetitiveExample

set_option pp.universes false

#check @CommodityClassification.Equilibrium.Model.competitive_of_household
#print axioms CommodityClassification.Equilibrium.Model.competitive_of_household

#check @CommodityClassification.Equilibrium.Model.competitive_of_surplus
#print axioms CommodityClassification.Equilibrium.Model.competitive_of_surplus

#check @CommodityClassification.Equilibrium.Model.canonical_competitive_state
#print axioms CommodityClassification.Equilibrium.Model.canonical_competitive_state

#check @CommodityClassification.Equilibrium.Model.quadratic_neighborhood_competitive
#print axioms CommodityClassification.Equilibrium.Model.quadratic_neighborhood_competitive

#check @CommodityClassification.Equilibrium.Model.quadratic_competitive_implementation
#print axioms CommodityClassification.Equilibrium.Model.quadratic_competitive_implementation

#check @CommodityClassification.Equilibrium.BenchmarkFamily.candidate_competitive_implementation
#print axioms CommodityClassification.Equilibrium.BenchmarkFamily.candidate_competitive_implementation

#check @CommodityClassification.Equilibrium.Example.concrete_competitive_implementation
#print axioms CommodityClassification.Equilibrium.Example.concrete_competitive_implementation

#check @CommodityClassification.Equilibrium.Model.CompetitiveState
