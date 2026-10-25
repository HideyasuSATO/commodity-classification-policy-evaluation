# Manuscript–Lean correspondence

The correspondence follows the manuscript edition dated 25 October 2026, identified by its source hash in [manuscript_version.json](manuscript_version.json).

The full table contains 508 units: 406 proved results and 102 definitions. Units include named results, unnumbered derivations, equilibrium constructions, examples, and proof subclaims. Exact assumptions and quantifiers appear in the recorded Lean declaration types.

The full table gives printed equation and theorem numbers, section numbers and starting pages, and source line ranges. These locations refer to the paper edition identified above.

## Main results

| Paper location | Result | Lean entry points |
| --- | --- | --- |
| Section 2; Appendix A | CES cost, derivatives, and parameter limit | [GE.COST_DERIVATIVES](../LeanMath/CommodityClassification/CostDerivativeIntegration.lean#L41)<br>[GE.CES_PARAMETER_LIMIT](../LeanMath/CommodityClassification/CESParameterLimit.lean#L69) |
| Section 2; Appendix A | Uniform regularity and local equilibrium | [GE.REGULARITY](../LeanMath/CommodityClassification/CandidateRegularity.lean#L24)<br>[GE.LOCAL_EXISTENCE](../LeanMath/CommodityClassification/EquilibriumLocalExistence.lean#L51) |
| Section 2; Appendix A | Welfare expansion and variational representation | [GE.WELFARE_EXPANSION](../LeanMath/CommodityClassification/WelfareExpansion.lean#L50)<br>[GE.VARIATIONAL](../LeanMath/CommodityClassification/WelfareVariational.lean#L82) |
| Appendix A | Common benchmark and equilibrium implementation | [GE.COMMON_BENCHMARK](../LeanMath/CommodityClassification/CommonBenchmarkEquilibrium.lean#L46) |
| Lemma B.1 | Fixed-answer congruence | [B1.LOCAL](../LeanMath/CommodityClassification/FixedAnswerComplete.lean#L46)<br>[B1.GLOBAL](../LeanMath/CommodityClassification/FixedAnswerComplete.lean#L59) |
| Lemma B.2 | All-answer dichotomy | [B2.DICHOTOMY](../LeanMath/CommodityClassification/AllAnswerDichotomy.lean#L49) |
| Theorem 1; Section 3 | Exact pair rule and coarsest classification | [EXACT.PAIR_RULE](../LeanMath/CommodityClassification/ExactCommodityPairRule.lean#L40)<br>[EXACT.COARSEST](../LeanMath/CommodityClassification/CoarsestCommodityClassification.lean#L63) |
| Section 3; Appendix B | Parent-report exception and failure witnesses | [EXACT.PARENT_TEST](../LeanMath/CommodityClassification/ObservableParentTest.lean#L74)<br>[EXACT.WITNESSES](../LeanMath/CommodityClassification/EconomicClassificationWitnesses.lean#L21) |
| Section 3; Appendix C | Separable demand and generic singleton reports | [SEPARABLE.RULE](../LeanMath/CommodityClassification/SeparableCommodityRule.lean#L12)<br>[GENERIC.SINGLETONS](../LeanMath/CommodityClassification/GenericSingletonClassification.lean#L37) |
| Appendix C | Group quantities and composite-good conditions | [BRIDGE.QUANTITY](../LeanMath/CommodityClassification/QuantityBridgeComplete.lean#L12)<br>[BRIDGE.COMPOSITE](../LeanMath/CommodityClassification/CompositePathAgreement.lean#L52) |
| Corollary 1; Section 4; Appendix D | Demand nests and omitted input covariance | [NEST.RULE](../LeanMath/CommodityClassification/NestedMatchingPairRule.lean#L46)<br>[NEST.COVARIANCE](../LeanMath/CommodityClassification/NestedEquilibriumInformation.lean#L63)<br>[NEST.COMPOSITE_COST](../LeanMath/CommodityClassification/CompositeProjectedCurvature.lean#L71) |
| Section 4.1; Appendix D | Untaxed-nest example | [EX.UNTAXED_NEST](../LeanMath/CommodityClassification/UntaxedNestEquilibrium.lean#L28) |
| Section 5.1; Appendix E | Sharp conditional precision width | [PREC.SHARP_WIDTH](../LeanMath/CommodityClassification/PrecisionManuscriptWidth.lean#L53) |
| Theorem 2; Section 5.2; Appendix E | Lower bound over coarse classifications and limiting boundary | [PREC.ALL_PARTITION_LOWER](../LeanMath/CommodityClassification/PrecisionAllPartitionLower.lean#L65)<br>[PREC.ASYMPTOTIC](../LeanMath/CommodityClassification/PrecisionBestClassification.lean#L46) |
| Section 5.3; Appendix E | Sales concentration and refinement | [PREC.CAPACITY](../LeanMath/CommodityClassification/PrecisionVarianceCapacity.lean#L113)<br>[PREC.LARGE_PRODUCT_RULE](../LeanMath/CommodityClassification/PrecisionTailCapacity.lean#L113) |
| Proposition 1; Appendix F | Stability under perturbations | [ROBUST.WIDTH](../LeanMath/CommodityClassification/RobustStructuredWidth.lean#L68) |
| Appendix F.2 | Unknown supply elasticity | [UNKNOWN.SIGMA_SET](../LeanMath/CommodityClassification/UnknownSigmaConditionalWidth.lean#L63)<br>[UNKNOWN.SIGMA_FLOOR](../LeanMath/CommodityClassification/UnknownSigmaWorstWidth.lean#L12) |
| Section 6 | Information, interval width, and optimal recovery | [INFO.WIDTH_RADIUS](../LeanMath/CommodityClassification/ObservationRecoveryRadius.lean#L68)<br>[INFO.PREDICTION_RISK](../LeanMath/CommodityClassification/PrecisionPredictionRisk.lean#L39) |

## Full correspondence

- [correspondence.csv](correspondence.csv): all units, paper anchors and source lines, status, scope, dependencies, and Lean declarations.
- [claims.json](claims.json): the same claim records in structured form.
- [declarations.json](declarations.json): exact types, file locations, source hashes, and axiom dependencies for all 2,634 declarations.
- [index.html](index.html): a searchable index; open the downloaded file in a browser.

`proved_and_semantically_reviewed` records a proved result checked against the manuscript. `definition_implemented_and_typechecked` records an implemented definition. The dependency field gives the order among correspondence units; Lean imports record the source-level dependencies.

## Scope

The exact classification results use finite product and factor sets, positive benchmark prices and quantities, a symmetric positive-definite demand matrix, and a common positive CES supply elasticity. Policy is fixed before classification. Fixed-answer and all-answer identification have separate statements. The precision-boundary results use the structured two-factor model specified in Section 5. Claim-specific assumptions, degenerate dimensions, and boundary cases are recorded in the full correspondence and exact declaration types.
