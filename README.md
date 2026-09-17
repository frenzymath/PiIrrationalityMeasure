# Pi irrationality measure formalization

Lean 4.33.0 and mathlib `v4.33.0` formalization of
the [paper](https://arxiv.org/abs/2609.11276).

The two main results are the strict bound
`IrrationalityMeasure Real.pi < 7101862832357 / 10^12` (Theorem 1.1) and
strict local minimality of the actual auxiliary upper-bound function at
`(1857/5570, 1857/2785)` over nearby real parameters (Theorem 1.2).
The full build and all three current Comparator targets passed on
September 15, 2026. Generated logs are not included in this repository.

## Review the statements

[`Challenge.lean`](Challenge.lean) is the single trusted statement file. It
imports only Mathlib and contains all project definitions needed to read the
two main theorems, plus the direct rational-approximation consequence of
Theorem 1.1. Its three `sorry` proofs are intentional Comparator placeholders.
There are no definition holes or additional hypotheses on the main results.

Theorem 1.2 uses the actual fractional-part saving integral, logarithmic phase,
and saddle roots specified by the explicit stationary cubic and their real
or upper-half-plane location. [`Solution.lean`](Solution.lean) proves that
these roots agree near the candidate with the analytic branches used in the
development, then transfers the proved strict local minimum. It does not
import the challenge. Comparator checks the definitions as well as the
theorem statements, including the definitions repeated in the solution.

The complete article proofs remain in the 309 modules under `Formalization/`.
[`ARTICLE_COVERAGE.md`](ARTICLE_COVERAGE.md) maps paper results to proofs and
documents source conventions. Intermediate lemmas are not separate challenge
targets. Checking the main results verifies their proof dependencies; it
does not separately certify every independent article claim. Correspondence
between the paper and the Lean statements still requires mathematical review.

## Build and verify

Lean is pinned in `lean-toolchain`, and dependency revisions are pinned in
`lake-manifest.json`. The recorded September 15, 2026 verification used:

| Component | Version or revision |
| --- | --- |
| Lean | `4.33.0`, `d8b18978322de05a8f3dba51ef03cf5461676c17` |
| mathlib | `v4.33.0`, `db584cd6d46c92f209a44c0f1c829460d327499d` |
| Official `leanprover/comparator` | `3927ad383f208ae977c340a91c48ac9b497d2097` |
| `lean4export` | `15f6055e299ad5b89345e533cc2192f4cc00f659` |

For Comparator checks, install the listed Comparator and
[`lean4export`](https://github.com/leanprover/lean4export) versions and set
`COMPARATOR_BIN` to the path of the Comparator executable.

Build the full proof library and both entry files:

```sh
lake build
```

Check all three targets with the official
[`leanprover/comparator`](https://github.com/leanprover/comparator):

```sh
lake env "$COMPARATOR_BIN" comparator.json
```

The configuration checks `comparator_theorem11`,
`comparator_pi_rational_approximation_bound`, and `comparator_theorem12`.
It permits only `propext`, `Quot.sound`, and `Classical.choice`,
uses the Lean default kernel, and disables Nanoda. The proofs include large
finite certificates, so kernel replay can take tens of minutes with little
output even though the challenge is short.

A successful Comparator run must exit with code 0 and contain both verdicts:

```text
Lean default kernel accepts the solution
Your solution is okay!
```

The recorded run passed statement and definition comparison, the permitted
axiom check, and kernel replay for all three targets. Rerun the commands
above to verify the sources in your checkout after making changes.
