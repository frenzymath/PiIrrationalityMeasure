# Prime Number Theorem Dependency

These files are adapted from the PNT+ project:

- Source: https://github.com/AlexKontorovich/PrimeNumberTheoremAnd
- Commit: `a5154676af9aa3095150ee410cdda80555aa0642`
- Upstream toolchain: Lean 4.32.2
- Local toolchain: Lean 4.33.0
- License: Apache 2.0, included in `LICENSE`

The retained dependency path is the smooth Fourier proof of the
Wiener--Ikehara theorem followed by `WeakPNT`. `Wiener.lean` stops immediately
after `WeakPNT`; later results are outside this dependency. Blueprint
attributes and documentation commands are removed so the proof does not
require the Architect documentation package. Imports point to this local
directory.

The unused bounded-variation declarations `prelim_decay_2`,
`AbsolutelyContinuous`, `prelim_decay_3`, and `decay_alt` are omitted.
The first and third declarations have upstream placeholders. The retained
smooth Fourier estimates have proofs and provide the estimates used by
`WeakPNT`.

Lean 4.33 compatibility changes make two `Circle` norm identities explicit,
expose the function in one Fourier measurability proof, and replace an
expanded almost-everywhere argument by equality of the measures restricted
to `Icc` and `Ioc`.

`../PrimeNumberTheorem.lean` converts the von Mangoldt conclusion into the
Chebyshev form used by the article. Its proof follows the corresponding
argument in upstream `Consequences.lean` and mathlib's bound on `psi-theta`.

`Mathlib/Analysis/SpecialFunctions/Gamma/DigammaSeries.lean` retains the
same commit's proof of `Complex.hasSum_digamma_of_re_pos`. It derives the
series from the Euler limit for Gamma and uniform convergence of the
derivatives of the logarithmic approximants. The later continuation to
the remaining complex domain and unused tail-bound helpers are omitted.
The retained proof builds unchanged on Lean 4.33.0.
`../PrimeSavingDigamma.lean` applies it to the positive real endpoints
in equation (3.14) and identifies the result with `logDeriv Real.Gamma`.
