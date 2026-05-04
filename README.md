# TPTND-Lean

A Lean 4 implementation of a core fragment of **Trustworthy
Probabilistic Typed Natural Deduction (TPTND)**, producing
machine-checked fairness certificates from group-level statistics.

Companion artefact to the OVERLAY 2026 submission *"Fairness
Certificates via a Lean-Backed Probabilistic Typed Deduction"* by
F. A. D'Asaro and G. Primiero.

## Quick start

Requires Lean 4 via [`elan`](https://leanprover-community.github.io/install/)
and `lake`. The pinned toolchain is in `lean-toolchain`.

```bash
lake build                                    # builds the library + 4 binaries
./.lake/build/bin/tptnd_tests                 # 13 acceptance + 7 negative tests
./.lake/build/bin/compas_audit                # numerical comparison vs ProPublica
./.lake/build/bin/compas_from_data            # 12 COMPAS case-study derivations
./.lake/build/bin/hmda_showcase               # 6 HMDA case-study derivations
```

Each binary exits `0` when every derivation passes the kernel and
nonzero otherwise.

## Mapping paper sections to derivations

| Paper section                          | Executable          | Rules used in the derivation             |
|----------------------------------------|---------------------|------------------------------------------|
| §4.1 ProPublica headline (UTrust)      | `compas_from_data`  | `Update` → `IUT` → `EUT` (depth 3)       |
| §4.1 Bayesian belief update            | `compas_from_data`  | `I-P` + `E-P` (depth 2)                  |
| §4.1 Genuine non-finding (Trust)       | `compas_from_data`  | `IT` + `ETex` (depth 2)                  |
| §4.2 HMDA Tree A (reference-rate)      | `hmda_showcase`     | `IT` (depth 2)                           |
| §4.2 HMDA Tree B (temporal pool)       | `hmda_showcase`     | `Update`×2 + `IUT2` (depth 3)            |
| §4.2 HMDA Trees C.1/C.2 (intersect.)   | `hmda_showcase`     | `IUT2` (depth 2)                         |
| §4.2 HMDA Trees D.1/D.2 (year-over-yr) | `hmda_showcase`     | `IUT2` (depth 2)                         |

## Entry point

The kernel exposes one dispatcher:

```lean
def checkDerivation (d : Derivation) : CheckM Unit
```

`CheckM` is `ExceptT String Id` (i.e. `Except String`), so
`checkDerivation d` returns either `.ok ()` — `d` is a valid
certificate — or `.error msg`, where `msg` identifies the failing
premise.

### A successful certificate check

35/100 applicants from group A are denied; the model declares 20 %;
20 % lies outside the score-test acceptance band for the observed
frequency, so the verdict has to be `UTrust`.

```lean
import TPTND
open TPTND

#eval show Except String Unit from Id.run do
  let α    := Output.atom "Denied"
  let t    := Term.atom "applicants"
  let σ    := ({"src_A"} : Finset String)
  let supp := ({"groupA"} : Finset String)
  let n    : Nat := 100
  let f    := clampProb (35 / 100)
  let p    := clampProb (20 / 100)

  let obsCtx : Context := [⟨"applicants", supp, α, .unknown⟩]
  let obsClaim : TermClaim := ⟨.frequency, t, n, α, f, σ⟩
  let dObs := Derivation.node .obs [] ⟨obsCtx, .term obsClaim⟩ false

  let mE  : ContextEntry := ⟨"x", supp, α, .exact p⟩
  let dM  := Derivation.node .identity [] ⟨[mE], .identity mE⟩ false

  let ci      := binomialCI n f p
  let untrust : TrustClaim := .untrust t n α f p ci
  let dIUT    := Derivation.node .iUT [dM, dObs]
                   ⟨[mE] ++ obsCtx, .trust untrust⟩ false

  checkDerivation dIUT
-- Except.ok ()
```

### A failed certificate check

Same shape, but the model now claims 30 % — inside the band, so
`IUT` is no longer the right rule and the kernel rejects:

```lean
#eval show Except String Unit from Id.run do
  let α    := Output.atom "Denied"
  let t    := Term.atom "applicants"
  let σ    := ({"src_A"} : Finset String)
  let supp := ({"groupA"} : Finset String)
  let n    : Nat := 100
  let f    := clampProb (35 / 100)
  let p    := clampProb (30 / 100)        -- inside the CI

  let obsCtx : Context := [⟨"applicants", supp, α, .unknown⟩]
  let obsClaim : TermClaim := ⟨.frequency, t, n, α, f, σ⟩
  let dObs := Derivation.node .obs [] ⟨obsCtx, .term obsClaim⟩ false

  let mE  : ContextEntry := ⟨"x", supp, α, .exact p⟩
  let dM  := Derivation.node .identity [] ⟨[mE], .identity mE⟩ false

  let ci      := binomialCI n f p
  let untrust : TrustClaim := .untrust t n α f p ci
  let dIUT    := Derivation.node .iUT [dM, dObs]
                   ⟨[mE] ++ obsCtx, .trust untrust⟩ false

  checkDerivation dIUT
-- Except.error "IUT: model probability must lie OUTSIDE binomial CI"
```

Same Lean term, rejected because the rule's side condition fails.
To certify this audit you'd write `IT` (Trust) instead of `IUT`.

A `Derivation` tree is built with
`Derivation.node ruleName premises sequent independenceWitness`,
where `ruleName : RuleName` ranges over a closed enumeration
(`.iT`, `.iUT2`, `.update`, `.ePosterior`, `.contraction`, …).
Rule-name typos are compile-time errors.

For the success case the kernel verifies, in order: the observation
leaf's provenance is non-empty; the identity leaf's constraint is
exact; the declared CI matches `binomialCI`; the model probability
lies outside the CI (otherwise `IT` would have been the rule); the
conclusion's term, sample size, output and frequency match the
observation premise; the conclusion context inherits correctly from
the premises. Each check corresponds to one of the `.error` messages
in the failure case.

### Rule constructors

The complete list of `RuleName` constructors:

```
Output / distribution: .outputAtom .outputNeg .outputSum .outputProd
                       .outputArr .base .extend .unknown
Atomic leaves:         .identity .identityStar .obs .experiment .expectation
Sampling / sum:        .sampling .update .iPlus .ePlusL .ePlusR
Product / arrow:       .iProd .eProdL .eProdR .iArr .eArr
Bayesian:              .iPrior .ePosterior
Trust:                 .iT .iUT .iT2 .iUT2 .eT .eUT .eTex
Comparison:            .iEx .iNEx .eEx .eNEx
Structural:            .weakeningD .weakeningS .contraction
```

The dispatcher in `TPTND.lean` is exhaustive over `RuleName`. Adding
a new rule means extending the inductive and writing a new `checkXXX`
function in `TPTND/Rules/`.

## Project layout

```
TPTND.lean                # top-level dispatcher: checkDerivation
TPTND/
  Syntax.lean             # Output, Term, Prob, Constraint, Context
  Judgement.lean          # Claim, Sequent, Derivation, RuleName
  CheckM.lean             # ExceptT String Id monad and helpers
  Arithmetic.lean         # exact-rational ops, sqrt, binomialCI/twoSampleCI
  WellFormedness.lean     # context wf-ness, provenance, contextExtendsBy
  Rules/                  # one file per rule family
    OutputDist.lean
    AtomicLeaves.lean
    SamplingSum.lean
    ProductArrow.lean
    Bayesian.lean
    Trust.lean
    Comparison.lean
    Structural.lean
  Tests.lean              # acceptance tests (8 positive + 7 negative)
  COMPASAudit.lean        # numerical comparison vs ProPublica
  COMPASFromData.lean     # 12 COMPAS derivations
  HMDAShowcase.lean       # 6 HMDA derivations
```

## Data sources

- `compas-scores-two-years.csv` from
  <https://github.com/propublica/compas-analysis>
- `hmda_de_2022.csv`, `hmda_de_2023.csv` from the CFPB HMDA Data Browser
  (<https://ffiec.cfpb.gov/data-browser/>), filtered to Delaware

## Reproducibility

`lake build` followed by the four binaries reproduces every numerical
claim in the paper. The Lean toolchain is pinned in `lean-toolchain`;
the Mathlib dependency in `lake-manifest.json`.
