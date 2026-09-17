# Article coverage

Source: [the paper](https://arxiv.org/abs/2609.11276).
All numbered theorems, lemmas, and propositions have proved interfaces in this
repository. The proof development also covers the auxiliary estimates,
Appendix A, the old-point perturbation, and the numerical comparison (5.24).
See [Build and verify](README.md#build-and-verify) for the verification
summary and commands.

## Main results and definitions

| Paper | Lean declaration | Meaning |
| --- | --- | --- |
| Theorem 1.1 | [`theorem11_proof`](Formalization/PiMeasureTheorem.lean) | `IrrationalityMeasure Real.pi < 7101862832357 / 10^12`, without extra hypotheses |
| Theorem 1.2 | [`theorem12_proof`](Formalization/LocalOptimality.lean) | Strict local minimum of the actual auxiliary bound at `(1857/5570,1857/2785)` |
| Theorem 1.2, original coordinates | [`theorem12_exponent_coordinates`](Formalization/ExponentCoordinates.lean) | Strict local minimum at `(1857/2785,1857/2785)` after `(A1,A2) -> (A1/2,A2)` |
| Theorem 6.3 | [`theorem63_proof`](Formalization/LocalOptimality.lean) | Nearby distinct real parameters are admissible and have a strictly larger auxiliary bound than the candidate |
| Proposition 6.4 | [`ConstructionRealization.lean`](Formalization/ConstructionRealization.lean) | Actual integer constructions, all rates, and the Hata bound at every nearby rational parameter |

[`Statements.lean`](Formalization/Statements.lean) defines the irrationality
measure as the infimum of eventual rational-approximation exponents, using the
paper's quantifiers. It also defines the four admissibility inequalities and
strict local minimality. The lower-boundedness needed for the real infimum is
proved in `IrrationalityMeasureBounds.lean`. The independent target
`comparator_pi_rational_approximation_bound` checks the eventual approximation
inequality directly.

The public `Challenge.lean` imports only Mathlib and states the two main
results and the direct approximation consequence. Its `paperRealSaddle` and
`paperComplexSaddle` select roots of the explicit stationary cubic by the
conditions `25 < y` and `0 < z.im`. `Solution.lean` proves that these roots,
and hence `paperAuxiliaryBound`, agree near the candidate with the analytic
branches and `parameterAuxiliaryBound` used in the development. This gives
the same strict local minimum without importing implementation proofs into
the trusted statement or assuming any root-existence hypotheses.

The rates in `ParameterRates.lean` are evaluations of the actual logarithmic
phase at proved stationary roots. `ParameterSaving.lean` defines the actual
fractional-part indicator and its weighted integral. `ParameterCost.lean`
defines the cost and auxiliary quotient from these functions. The final main
theorems supply all assumptions of the reusable abstract interfaces.

## Arithmetic and prime saving

| Paper | Principal proof modules |
| --- | --- |
| (1.1)--(2.4), shift, partial fractions, logarithmic term | `Transformation`, `PartialFractionIdentity`, `LaurentIdentification`, `LogarithmicIntegral`, `IntegralDecomposition` |
| Lemma 2.1, complete Laurent valuations | `ScaledLaurent`, `PrincipalLaurent`, `GaussianIntegrality` |
| (2.9)--(2.11), six-factor Gaussian expansion | `ComplexLeibniz`, `ComplexLaurent`, `GaussianExpansion`, `GaussianSignedTerm` |
| Lemma 2.2, finite-field deletion | `FiniteFieldDeletion`, `FiniteFieldLaurent`, `FiniteFieldScaledSeries`, `FiniteFieldTransfer` |
| Lemma 2.3, reduced LCM | `ReducedLcmIntegrality`, `Denominator`, `NormalizedCoefficient` |
| Lemma 2.4, endpoint coefficients | `EndpointFormula`, `EndpointDivisibility` |
| Lemma 2.5, polynomial integral | `PolynomialLaurent`, `PolynomialClearing`, `PolynomialTenClearing`, `PolynomialIntegral` |
| Lemma 2.6, nonlogarithmic pole integral | `PoleArithmetic`, `PoleIntegral` |
| Proposition 2.7, integer linear form | `IntegerLinearForm` |
| Proposition 3.1, five interval families, count, measure | `PrimeSavingCells`, `PrimeSavingIntervals`, `PrimeSavingComponents`, `PrimeSavingMeasure` |
| Lemma 3.2, periodic prime products | `PrimeNumberTheorem`, `PrimeLogIntervals`, `PeriodicPrimeProducts`, `PrimeSavingAsymptotic` |
| (3.14)--(3.16), digamma series and direct tail bounds | `PrimeSavingDigamma`, `PrimeSeriesTail`, `PrimeSavingTail` |
| (3.17)--(3.24), Binet formulas, Bernoulli moments and recurrence | `BinetKernel`, `BinetMoments`, `BinetRemainder`, `DigammaBinet`, `BinetSecondFormula`, `BinetSecondMoments`, `BernoulliCertificate`, `DigammaApproximation`, `PrimeSavingApproximation` |
| (3.25)--(3.30), strict saving and cost enclosures | `PrimeSavingComputation`, `PrimeSavingNumerics`, `DigammaLogApprox`, `DenominatorGrowth` |

Every module name in these tables is relative to `Formalization/`, with suffix
`.lean`. The aggregate `Formalization.lean` imports all 309 proof modules,
including the compatibility port of the required PNT+ dependencies.

## Asymptotics and irrationality measure

| Paper | Principal proof modules |
| --- | --- |
| Lemma 4.1, arbitrary nonnegative span-one power series | `GeneralCoefficientLaw`, `GeneralCoefficientAsymptotic`, `LatticeAperiodicity`, `LatticeFourierInversion`, `LatticeLocalLimit` |
| (4.3)--(4.10), actual extraction and probability law | `CoefficientExtraction`, `CoefficientProbability`, `CoefficientMoments`, `CoefficientCharacteristic`, `CoefficientLocalLimit`, `CoefficientAsymptotic` |
| Proposition 4.2, ordinary coefficient rate | `CoefficientGrowth`, `CoefficientGrowthNumerics`, `IntegerCoefficientGrowth` |
| Proposition 4.3, unique global arc maximum | `PhaseRootCount`, `PhaseCritical`, `SaddlePhaseMaximum` |
| Lemma 4.4, general contour bound and extended-log limsup | `ContourEstimate`, `ContourLogEstimate` |
| Proposition 4.5, actual integral decay | `SmoothContourLift`, `ContourDeformation`, `ComplexDensityModulus`, `IntegralDecay`, `IntegralDecayNumerics` |
| Lemma 5.1 and Remark 5.2, both Hata index-selection cases | `HataSelection`, `HataScale`, `HataBounds`, `HataAssembly`, `HataRateCriterion` |
| (5.15)--(5.23), normalized rates and numerical quotient | `IntegerLinearFormDecay`, `PaperRateNumerics`, `PiMeasureTheorem` |
| (5.24), old value, absolute and relative gain | `OldPointFineLogCertificate`, `OldPointComparisonNumerics` |

The general coefficient theorem constructs the tilted probability laws and
derives their exponential moments from convergence inside the radius. Its
span-one hypothesis uses the subgroup generated by support differences.
The variance is positive and the mean is a natural number, which is the
nonnegative integer mean possible for this support. The output is the literal
coefficient identity with a proved error sequence tending to zero.

The contour proof uses smooth reparametrizations of the square-root lifts.
`OriginalContourAmplitude.lean` proves equality with the paper's original
amplitude integral. The general log estimate uses an extended real logarithm
so a zero integral contributes negative infinity. The actual linear forms
are proved nonzero before their ordinary real logarithms are used.

## Local parameter analysis

| Paper | Principal proof modules |
| --- | --- |
| (6.1)--(6.11), saving integral, normalization, actual rates | `ParameterSaving`, `ParameterSavingSeries`, `ParameterRates`, `ParameterCost`, `RealSaddlePhase` |
| Lemma 6.1, general uniform local polyhedrality | `SavingCellGeometry`, `SavingCellPartition`, `FiniteConewiseLinear`, `LocalPolyhedral`, `SavingMeasurePolyhedral`, `GeneralSavingPolyhedral` |
| Lemma 6.2, general uniform logarithmic variation | `GeneralSavingIntegrability`, `GeneralSavingPeriodBounds`, `SavingRadialModel`, `GeneralSavingLogVariation`, `GeneralSavingPolyhedral` |
| (6.27)--(6.33), old-point partition and strict improvement | `OldPointPartition`, `OldPointLogVariation`, `OldPointAnalytic`, `OldPointImprovement` |
| (6.34)--(6.39), diagonal family and candidate | `DiagonalFamily` |
| (6.40)--(6.46), endpoint catalogue, twelve sectors, exact counts and signs | `EndpointCoincidences`, `EndpointCardinality`, `EndpointSeparation`, `EndpointCountCertificate`, `EndpointSectorCounts`, `EndpointSectorForms`, `SavingMeasureLocalFormula`, `SavingVariationBound` |
| (6.47)--(6.54), persistent saddles, contours, rates and common neighborhood | `ParameterSaddleRoots`, `ParameterCoefficientSaddle`, `ParameterArcMaximum`, `ParameterIntegralBound`, `ParameterNeighborhood` |
| (6.55)--(6.60), uniform Taylor remainder, sensitivity and local minimum | `QuotientRemainder`, `LocalTaylorEstimate`, `LocalLogLowerBound`, `LocalOptimalityNumerics`, `LocalOptimality` |
| (6.61)--(6.68), actual nearby rational constructions | `ConstructionArithmetic`, `ConstructionIntegerLinearForm`, `ConstructionSavingAsymptotic`, `ConstructionAnalyticRates`, `ConstructionIntegerRates`, `ConstructionIntegerDecay`, `ConstructionRealization` |

Generic Lemmas 6.1 and 6.2 allow either sign of nonzero `a + 2*b - c`.
The geometry is proved for positive real triples; the periodic logarithmic
argument uses positive integer triples. The generic model is constructed
from actual floor cells as a finite sum of clipped affine lengths. It has
a finite cover by closed convex polyhedral cones, with a linear formula on
each cone. No local-model hypothesis is left in the final generic lemmas.

At the candidate, the more explicit endpoint proof recovers the printed
twelve-sector table, including boundary directions and one uniform radius.
The main local-minimum theorem applies to all nearby real displacements,
including nonlinear approaches to the candidate.

The old point and the candidate use separate analytic saddle branches, each
proved to solve the same stationary equation on its own neighborhood. The
formalization does not evaluate the candidate's locally chosen branch at the
old point. `OldPointImprovement.lean` proves (1.12) for the actual old-point
branches, along an admissible ray with positive denominator.

## Appendix and source conventions

| Paper | Principal proof modules |
| --- | --- |
| A.1, positive saddle and logarithm remainder | `CoefficientSaddleAlgebra`, `CoefficientLogCertificate`, `ScaledLogApproximation` |
| A.2, elimination and isolating intervals | `SaddleElimination`, `RootIsolation` |
| A.3, transformed derivative and coefficient signs | `PhaseDerivative`, `PhaseSigns`, `ArcTransform`, `PhaseSignPattern` |
| A.4, actual modulus identities and rate enclosure | `SaddleModuli`, `SaddleLogCertificate`, `IntegralDecayNumerics` |
| A.5, old roots, resultants, rates, Machin certificate and sensitivity | `OldPointRoot`, `OldPointSaddles`, `DigammaThirds`, `OldPointSaving`, `ArctanFinite`, `OldPointLogCertificate`, `OldPointRateFormulas`, `OldPointNumerics` |

- The derivative indices in (2.9) are nonnegative, and the power series in
  Section 4 include degree zero, as represented in the Lean statements.
- Decimal prefixes and rounding claims are expressed as strict rational
  intervals. The extra digits in the old-value certificate extend the
  displayed prefix, without treating an ellipsis as an exact real number.

The direct approximation (3.15)--(3.16) has a proved remainder bound. The
paper does not supply a separate decimal value for that finite sum; its
high-precision saving evaluation uses the digamma recurrence instead.

## Reference dependencies

- [Hata (1993), pp. 338--339, Remark 2.1](https://matwbn.icm.edu.pl/ksiazki/aa/aa63/aa6344.pdf):
  the two-case selection proof and its one-number consequence are developed
  in the `Hata*` modules. Ordinary coefficient growth and an error limsup
  suffice; eventual nonvanishing of every paired integer is not assumed.
- [Zeilberger--Zudilin, Part II](https://sites.math.rutgers.edu/~zeilberg/mamarim/mamarimPDF/pimeas.pdf):
  the partial-fraction and contour architecture. The changed parameters,
  arithmetic factors, saving intervals and rates are proved for this paper.
- [Flajolet--Sedgewick, Chapter VIII](https://ac.cs.princeton.edu/home/):
  the positive-coefficient saddle argument is developed through the actual
  tilted laws, Fourier inversion and the lattice Gaussian limit.
- The Almkvist--Zeilberger and Salikhov references describe the historical
  route to this construction. Creative telescoping and the predecessor
  irrationality bound are not assumptions of the present proof.
- [PrimeNumberTheoremAnd](https://github.com/AlexKontorovich/PrimeNumberTheoremAnd),
  commit `a5154676af9aa3095150ee410cdda80555aa0642`: the required analytic
  dependencies are ported under `Formalization/PNT/`. The Chebyshev prime
  number theorem used here is a theorem, not a project axiom.

## Verification boundary

Lean and mathlib are pinned to 4.33.0. The official
[leanprover/comparator](https://github.com/leanprover/comparator) checks the
three named statements in `Challenge.lean` against `Solution.lean`: Theorems
1.1 and 1.2, and the direct rational-approximation consequence. The
`comparator.json` configuration permits only `propext`, `Quot.sound`,
and `Classical.choice`, uses the Lean default kernel, and disables Nanoda.
`Challenge.lean` imports
only Mathlib; all project definitions needed to read the claims appear in it.

The proof modules and the coverage tables above still cover the full article.
Intermediate results are no longer separate Comparator targets. Checking the
main results verifies their proof dependencies; it does not separately certify
every independent article claim. The earlier 260-target checks used a
different interface; their logs are not included in this repository.

The intentional `sorry` placeholders are confined to the challenge statements.
The solution and proof modules contain no placeholders, custom axioms, or
native evaluation. External computations only propose finite witnesses;
their identities and inequalities are checked in the Lean kernel.
The coverage map documents the mathematical reading of the paper; Comparator
checks the Lean statements and their proofs, and does not parse the paper.
