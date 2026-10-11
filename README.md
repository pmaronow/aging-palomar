# Aging in Spherical Spin Glass Dynamics

This package contains the complete paper and its Lean formalization. The paper
is `manuscript/manuscript.pdf`; its buildable source is
`manuscript/source/main.tex`. The formalization constructs the finite-dimensional
Gaussian spherical model and its positive-semidefinite Cugliandolo--Kurchan
limit, then proves the physical response, entropy and Fisher estimates,
stationary selection, aging bounds and relaxation results.

`submission/claims.json` maps the 100 printed numbered objects to their exact
formal declarations and hypotheses: 84 arguments, 13 mathematical remarks,
one example and two interpretive cautions. The 98 mathematical objects are
covered by the proof development. Chronological slow fluctuation-dissipation
ratio, a matching susceptibility upper bound and an identified aging clock
remain open predictions.

Theorem 11.4 holds for every integer `p >= 3` and `beta > 0`. The cubic product
inequality includes `beta = beta_d`; positive Fisher-cost conclusions require
`beta > beta_d`. The physical response is the actual variational matrix and
terminal L² derivative of the projected nonlinear restart. Its L² Duhamel
representation is proved for bounded continuous deterministic forcing and
bounded continuous adapted random directions. The development separately
constructs affine variational solutions with general predictable L² sources.
The paper does not require a
simultaneous samplewise smooth spatial flow or a general nonlinear
forced-solution derivative on all L²_loc controls.

## Independent statement specification

The root Mathlib-only statement file, `Challenge.lean`,
contains both original theorem statements. The single `comparator.json`
selects both declarations as one Palomar entry:

| Theorem | Scope |
| --- | --- |
| `SphericalAging.PalomarCompleteTheorems.exists_complete_conclusions` | The five principal theorem groups and all-spin Theorem 11.4, with the same CK solution, stationary profile, dimension subsequence, physical density family and Fisher majorant. |
| `SphericalAging.PalomarStationarityCertificate.proposition5_7` | Proposition 5.7 for every CK solution: subsequence compactness for every late translating sequence, and stationarity/FDT for every raw translated cluster on its original sequence, including negative offsets. |

The root `Solution.lean` connects the complete-conclusions proof and retains
the original Proposition 5.7 proof. Both theorem names and mathematical statements
are retained. Each Challenge
target deliberately contains `sorry` because it is a specification to be
compared. The proved Solution and native proof library permit only `propext`,
`Classical.choice` and `Quot.sound`.

## Reproduce the formal checks

Install Lean through Elan, Python 3.11 or later, and Linux bubblewrap. The package pins Lean
`4.35.0-rc2` and Mathlib commit
`065356127b1dc0016f66b7283ce0ce2c4055aa55`; retain the included manifest.
Run from the project root:

```sh
python3 scripts/check_submission.py
lake exe cache get
lake build SphericalAging AbsorptionCutoff BrownianMotion FourPapersCommon \
  KolmogorovExtension4 StochasticCalculus Solution
lake env lean -DautoImplicit=false Audit.lean > ../aging-axiom-audit.log
lake env python3 scripts/run_comparator.py --project "$PWD" \
  --config comparator.json --report ../aging-checks/comparator.json
```

The native build compiles the proof libraries. `Audit.lean` checks imported
project/provider constants, including private declarations, against the three
standard axioms. Comparator checks both selected statements, definitions and
proof dependencies. The helper records checks with Lean, NanoDa and con-ron;
its reports remain outside the repository. Its default configuration is the
project's `comparator.json`. For a broader replay, run
`lake comparator --config comparator.json --paranoid`.

The entry has 1,918 library modules and one root Solution module. Rebuilding,
auditing and comparing the current root entry verifies its 1,919 proof modules
and both advertised theorem targets. The Challenge's 968 lines and 50,568 bytes
meet Palomar's hard limits of 1,000 lines and 100 KiB; its size receives the
standard readability warning above 300 lines or 32 KiB.

## Build the paper

With a TeX installation providing the required packages, BibTeX and `latexmk`,
run:

```sh
latexmk -cd -pdf -interaction=nonstopmode -halt-on-error -no-shell-escape \
  -jobname=manuscript -outdir=.. manuscript/source/main.tex
```

This writes `manuscript/manuscript.pdf`. The bibliography contains 122 cited
works; original-source access limitations identified during review have been
resolved. Relevant passage checks do not imply cover-to-cover reading.

## Provenance and submission

The human authors and responsible maintainer, autonomous GPT-6 agent
contributions, classifications, source relationships and review scope are
recorded in `formalization.yaml`. Agent review and local mechanical checks are
separate from Palomar's own verification and editorial process. One Challenge
file and one configuration selecting both original theorems define one Palomar
submission. For Palomar, make the repository public on GitHub and submit its
immutable commit and single `comparator.json`. The submission form also asks
you to declare your relationship to the formalization.

The current GitHub repository is private, so it is not yet eligible for
Palomar submission. A repository administrator must make it public before
intake. Local structural checks and kernel checks do not complete Palomar's
own verification, editorial review or registration.

Project code and documentation use the root MIT `LICENSE`. Reused stochastic
foundations, OAI adaptations and renewal proofs retain their Apache-2.0 licenses
and exact source/adaptation records in `vendor/PROVENANCE.json`; `NOTICE` records their
attribution. The package includes substantive proof sources and build inputs.
Generated objects, dependency caches and historical working archives are not
submission inputs.
