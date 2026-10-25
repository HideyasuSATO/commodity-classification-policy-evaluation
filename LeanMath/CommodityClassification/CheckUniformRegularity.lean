module
import LeanMath.CommodityClassification.CheckCESParameterLimit
import LeanMath.CommodityClassification.RegularityBoundaryExample

-- Retains B.1, its original derivative formulas, coordinates, reports, CES derivatives,
-- supply positivity and the CES parameter limit. No subsequent economic claim is asserted.
set_option pp.universes false

#check @CommodityClassification.Regularity.fin_univ_nonempty
#print axioms CommodityClassification.Regularity.fin_univ_nonempty

#check @CommodityClassification.Regularity.minEigen_le
#print axioms CommodityClassification.Regularity.minEigen_le

#check @CommodityClassification.Regularity.minEigen_attained
#print axioms CommodityClassification.Regularity.minEigen_attained

#check @CommodityClassification.Regularity.minEigen_mem_spectrum
#print axioms CommodityClassification.Regularity.minEigen_mem_spectrum

#check @CommodityClassification.Regularity.minEigen_pos
#print axioms CommodityClassification.Regularity.minEigen_pos

#check @CommodityClassification.Regularity.minEigen_isLeast_spectrum
#print axioms CommodityClassification.Regularity.minEigen_isLeast_spectrum

#check @CommodityClassification.Regularity.spectral_lower_bound
#print axioms CommodityClassification.Regularity.spectral_lower_bound

#check @CommodityClassification.Regularity.xi_posDef
#print axioms CommodityClassification.Regularity.xi_posDef

#check @CommodityClassification.Regularity.invRootXi_explicit
#print axioms CommodityClassification.Regularity.invRootXi_explicit

#check @CommodityClassification.Regularity.rootXi_sq
#print axioms CommodityClassification.Regularity.rootXi_sq

#check @CommodityClassification.Regularity.rootXi_invRootXi
#print axioms CommodityClassification.Regularity.rootXi_invRootXi

#check @CommodityClassification.Regularity.invRootXi_rootXi
#print axioms CommodityClassification.Regularity.invRootXi_rootXi

#check @CommodityClassification.Regularity.invRootXi_xi_invRootXi
#print axioms CommodityClassification.Regularity.invRootXi_xi_invRootXi

#check @CommodityClassification.Regularity.invRootXi_posDef
#print axioms CommodityClassification.Regularity.invRootXi_posDef

#check @CommodityClassification.Regularity.normalizedDemand_posDef
#print axioms CommodityClassification.Regularity.normalizedDemand_posDef

#check @CommodityClassification.Regularity.demandLambda_pos
#print axioms CommodityClassification.Regularity.demandLambda_pos

#check @CommodityClassification.Regularity.demandLambda_isLeast_spectrum
#print axioms CommodityClassification.Regularity.demandLambda_isLeast_spectrum

#check @CommodityClassification.Regularity.unnormalizeDemand
#print axioms CommodityClassification.Regularity.unnormalizeDemand

#check @CommodityClassification.Regularity.demand_lower_bound
#print axioms CommodityClassification.Regularity.demand_lower_bound

#check @CommodityClassification.Regularity.K_eq_demand_add_substitution
#print axioms CommodityClassification.Regularity.K_eq_demand_add_substitution

#check @CommodityClassification.Regularity.K_first_gap
#print axioms CommodityClassification.Regularity.K_first_gap

#check @CommodityClassification.Regularity.K_gap_decomposition
#print axioms CommodityClassification.Regularity.K_gap_decomposition

#check @CommodityClassification.Regularity.K_first_lower_bound
#print axioms CommodityClassification.Regularity.K_first_lower_bound

#check @CommodityClassification.Regularity.K_uniform_lower_bound
#print axioms CommodityClassification.Regularity.K_uniform_lower_bound

#check @CommodityClassification.Regularity.posDef_of_positive_lower_bound
#print axioms CommodityClassification.Regularity.posDef_of_positive_lower_bound

#check @CommodityClassification.Regularity.K_posDef
#print axioms CommodityClassification.Regularity.K_posDef

#check @CommodityClassification.Regularity.inverse_identities
#print axioms CommodityClassification.Regularity.inverse_identities

#check @CommodityClassification.Regularity.fixedAnswer_K_eq
#print axioms CommodityClassification.Regularity.fixedAnswer_K_eq

#check @CommodityClassification.Regularity.candidate_closure_lower_bound
#print axioms CommodityClassification.Regularity.candidate_closure_lower_bound

#check @CommodityClassification.Regularity.candidate_closure_certificate
#print axioms CommodityClassification.Regularity.candidate_closure_certificate

#check @CommodityClassification.Regularity.candidate_K_posDef
#print axioms CommodityClassification.Regularity.candidate_K_posDef

#check @CommodityClassification.Regularity.candidate_certificate
#print axioms CommodityClassification.Regularity.candidate_certificate

#check @CommodityClassification.Regularity.fixedAnswer_K_posDef_on
#print axioms CommodityClassification.Regularity.fixedAnswer_K_posDef_on

#check @CommodityClassification.Regularity.BoundaryExample.ones_positive
#print axioms CommodityClassification.Regularity.BoundaryExample.ones_positive

#check @CommodityClassification.Regularity.BoundaryExample.frame_prices_positive
#print axioms CommodityClassification.Regularity.BoundaryExample.frame_prices_positive

#check @CommodityClassification.Regularity.BoundaryExample.total_positive
#print axioms CommodityClassification.Regularity.BoundaryExample.total_positive

#check @CommodityClassification.Regularity.BoundaryExample.boundary_K_eq_R
#print axioms CommodityClassification.Regularity.BoundaryExample.boundary_K_eq_R

#check @CommodityClassification.Regularity.BoundaryExample.boundary_K_value
#print axioms CommodityClassification.Regularity.BoundaryExample.boundary_K_value

#check @CommodityClassification.Regularity.BoundaryExample.boundary_K_posDef
#print axioms CommodityClassification.Regularity.BoundaryExample.boundary_K_posDef

#check @CommodityClassification.Regularity.BoundaryExample.boundary_supply_zero_but_K_regular
#print axioms CommodityClassification.Regularity.BoundaryExample.boundary_supply_zero_but_K_regular

#check @CommodityClassification.Regularity.minEigen

#check @CommodityClassification.Regularity.rootXi

#check @CommodityClassification.Regularity.invRootXi

#check @CommodityClassification.Regularity.normalizedDemand

#check @CommodityClassification.Regularity.demandLambda

#check @CommodityClassification.Regularity.adjustedDemand

#check @CommodityClassification.Regularity.K

#check @CommodityClassification.Regularity.fixedAnswerData
