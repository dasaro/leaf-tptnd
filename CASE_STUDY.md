# Case study: a kernel-checked TPTND certificate of the ProPublica COMPAS audit

This document walks through a single TPTND-Lean derivation that produces a
machine-checked certificate of the central claim from ProPublica's 2016
COMPAS audit, alongside the Northpointe rebuttal and a calibration check.

The whole point of running the certificate is this: a TPTND derivation
tree is a sequence of inferential moves, each of which the kernel
verifies against a precise side condition. If any move would let an
auditor draw an unjustified conclusion — by miscounting, by pooling
overlapping samples, by using a confidence interval the data doesn't
support — the kernel rejects the tree. So when the kernel says
"accepted", you have a non-handwavy receipt that the public claim is
arithmetically and structurally consistent with the published data.

Source: [`TPTND/PPDiverse.lean`](TPTND/PPDiverse.lean).
Build & run: `lake build pp_diverse && ./.lake/build/bin/pp_diverse`.

---

## 1. The ProPublica claim, verbatim

From *Machine Bias* (Angwin, Larson, Mattu, Kirchner — ProPublica,
May 23 2016):

> "The formula was particularly likely to falsely flag black defendants
> as future criminals, wrongly labeling them this way at almost twice
> the rate as white defendants."

From the accompanying methodology paper *How We Analyzed the COMPAS
Recidivism Algorithm* (Larson, Mattu, Kirchner, Angwin):

> "Black defendants who did not recidivate over a two-year period were
> nearly twice as likely to be misclassified as higher risk compared to
> their white counterparts (45 percent vs. 23 percent)."

This is the **equal-FPR** (false-positive rate) fairness criterion. The
certificate's headline sub-derivation translates exactly this paragraph
into a TPTND derivation, then asks the kernel: *given the published
counts, is this disparity statistically real, or could it be noise?*

Northpointe (the vendor of COMPAS) replied with a different criterion in
their July 2016 response (*COMPAS Risk Scales: Demonstrating Accuracy
Equity and Predictive Parity*, Dieterich, Mendoza, Brennan):

> "COMPAS achieves equal predictive parity across racial groups."

This is the **equal-PPV** (positive predictive value) criterion: among
defendants the model flagged as high-risk, the rate of actual
recidivism is the same in both racial groups. The certificate's second
sub-derivation translates this rebuttal.

The famous mathematical content of the dispute (Chouldechova 2017;
Kleinberg–Mullainathan–Raghavan 2016) is that *both can be true at
once*, and they are, on this data — TPTND-Lean checks each criterion
separately and produces a structured certificate that reports both
verdicts.

## 2. What the certificate is actually checking

In one sentence per sub-derivation:

| Sub-tree | What the kernel is asked to verify |
| --- | --- |
| **subA** ProPublica FPR | "On the published 6,172-row filter, the false-positive flagging rate for Black non-recidivists differs from that for White non-recidivists by *more* than the score-test confidence interval allows under the equal-rate null. Therefore the equal-FPR claim must be Untrusted." |
| **subA′** Calibration on Black PPV | "On the same filter, the empirical positive predictive value for Black defendants (775/1234) is *outside* the confidence interval centred at the model's calibrated rate of 0.50. Therefore the model's calibration claim, restricted to Black defendants, must be Untrusted." |
| **subB** Northpointe PPV | "On the same filter, the difference between Black PPV (775/1234) and White PPV (272/460) lies inside the score-test CI, which contains zero. Therefore the equal-PPV claim is compatible with the data — Trusted." |
| **subC** Joint audit | "Treating classification (Flagged) and outcome (Recidivated) as independent attributes of the same defendant, the joint frequency equals the product. The kernel checks the multiplication and the syntactic separation of the two output types." |
| **subD** Calibration as a conditional | "The conditional probability P(Recidivated \| Flagged) is *packaged* as a typed conditional that can be applied to other Flagged frequencies via the chain rule, without recomputing." |
| **subE** Prior consolidation | "Two earlier audits (a 2014 estimate of [40 %, 45 %] and a 2016 estimate of [42 %, 50 %] for the Black FPR) are reconciled into the single point estimate 0.43 — and the kernel checks that 0.43 actually lies in the intersection." |

The top-level `WeakeningS` chain bundles these six sub-certificates into
one auditable document. The bundle's *headline conclusion* is subA's
claim — the disparity verdict — but the document also carries the other
sub-trees' conclusions, and any future audit can pick up where this one
left off by composing with one of the trust-interval entries.

## 3. ASCII derivation tree

```text
                                                          WeakeningS  ← root
                                                ┌─────────────┴─────────────┐
                                                │                           │
                                            WeakeningS                   Contraction       (subE)
                                       ┌────────┴────────┐                  │
                                       │                 │                  │
                                  WeakeningS            E→                 Obs
                                  ┌────┴────┐         ┌─┴─┐          (priors loaded as
                                  │         │         │   │           interval entries)
                              WeakeningS   E×L       I→  Obs                              (subD)
                            ┌──────┴──────┐          │
                            │             │         Obs
                       WeakeningS         ET                                              (subB right)
                       ┌────┴────┐         │                                              (subC right)
                       │         │        IT2
                      EUT       E→      ┌──┴──┐
                       │      ┌──┴──┐   Obs   Obs
                      IUT2   I→   Obs
                       │      │
                    Update   EUT                                                           (subA' right)
                       │      │
                      I+    IUT
                       │     │
                      Obs   Identity                                                       (subA + subA' leaves)

  subA  (left spine):  Obs ×8 → I+ ×4 → Update ×2 → IUT2 → EUT
                       (the ProPublica FPR backbone)

  subA' (right of subA, parallel depth):
                       Obs+Identity → IUT → EUT → I→ → E→
                       (the calibration-on-Black-PPV chain)

  subB  Northpointe PPV:                Obs ×2 → IT2 → ET
  subC  Joint independence audit:        Obs ×2 → I× → E×L
  subD  Calibration via I→/E→:           Obs ×2 → I→ → E→
  subE  Prior consolidation:             Obs → Contraction
```

The tree is asymmetric on purpose. ProPublica's FPR pipeline is the
deepest spine because it does the most work — eight raw observation
leaves, four binarisation steps, two pooling steps, the two-sample
test, and the interval extraction. The other sub-trees are shorter
because their narratives are shorter, and they enter the audit by
being weakened-in alongside the FPR backbone.

## 4. ProPublica narrative → derivation node mapping

This is the core of the case study: each sentence the audit makes
in plain English maps to one rule application, and the kernel check on
that rule application is what makes the sentence formally meaningful.

### subA — ProPublica's headline FPR-disparity finding

The audit narrative for this sub-derivation reads, sentence by
sentence:

> *"We start from the published 6,172-row Broward County filter,
> restricted to defendants who did not recidivate within two years."*

The eight `Obs` leaves of subA encode exactly this: each leaf is a raw
empirical claim like *"of 1168 Black-male non-recidivists, 198 were
rated Medium-risk"*. The kernel's check on `Obs` is that the
provenance is non-empty (the leaf cites a real cohort), the sample
size is positive, and the cohort's support entry exists in the typing
context. There is no oracle for the count itself — the leaf is
trusted for the data; the rest of the tree is what the kernel
actually verifies.

> *"The Medium and High risk categories together constitute the
> 'flagged' classification."*

Each `I+` step formalises this binarisation. Its kernel check is
the syntactic disjointness `Medium ⊥_syn High` (the two risk types
share no atomic component, so adding their frequencies cannot
double-count) and that the conclusion's frequency is exactly the sum
of the premise frequencies.

> *"Within each race we pool male and female non-recidivists into a
> single audit cohort."*

Each `Update` step formalises this pooling. Its kernel check is that
the male and female provenances are disjoint (no defendant counted
twice) and that the pooled frequency is the weighted average,
*exactly* in rationals — the kernel rejects any arithmetic
shortcut.

> *"Black non-recidivists were flagged at 42.3 %; White at 22.0 %.
> Could this gap be sampling noise? The score-test 95 % CI for the
> difference is [16.8 %, 23.8 %], which excludes zero."*

This is the `IUT2` step — the formal rendering of ProPublica's
*"nearly twice as likely to be misclassified as higher risk"*
sentence. The kernel computes the score-test CI in exact rationals
and checks that 0 lies outside it. If the CI included zero, the
kernel would reject `IUT2` and demand an `IT2` instead — i.e., the
rule itself enforces the *direction* of the verdict.

> *"From here on, any downstream certificate may assume the gap
> interval as a typing-context fact."*

The final `EUT` step writes the gap interval `¬[16.8 %, 23.8 %]` into
the typing context as a transferable assumption. The kernel checks
that the conclusion's context contains this entry and that no
unrelated entries are smuggled in.

### subA′ — calibration on Black PPV (one-sample IUT)

This sub-derivation makes a *different* claim using a *different* family
of rules, and is included to show how a fixed-rate hypothesis is
checked. The narrative:

> *"The model is calibrated to 0.50 — that's its declared average
> recidivism rate among flagged defendants."*

The `Identity` leaf encodes the model's claim as an exact-typed
context entry `x_model : Recidivated_{0.5}`. The kernel checks
that this leaf's context is a singleton — i.e., the model's claim is
declared standalone, not buried in a larger hypothesis.

> *"Empirically, on the Black flagged sub-cohort, 775 of 1234 actually
> recidivated — that's 62.8 %."*

The `Obs` leaf records the empirical rate.

> *"0.50 lies outside the binomial CI for 775/1234 — therefore the
> calibration claim, restricted to this cohort, is Untrusted."*

This is the `IUT` step: the kernel computes `binomialCI(1234, 0.628,
0.5)` in exact rationals and checks that 0.50 lies *outside* it.

> *"Promote the calibration-gap interval into the typing context, but
> keep the original model-rate entry around for downstream
> reasoning."*

The `EUT` step does both at once.

> *"There is, then, a function from 'model says rate = p' to
> 'recidivism rate = 0.628'. We package this as a typed conditional."*

The `I→` step discharges the `x_model` entry from the context and
returns a derivation whose conclusion type is the arrow
`Recidivated ⇒ Recidivated` — a typed conditional certificate. The
kernel checks that the discharged entry was exact, that the lambda
binder name matches the discharged entry's name, and that the
arrow type is well-formed.

> *"Apply this conditional to a fresh empirical rate, via the chain
> rule."*

The `E→` step applies the conditional to another `Obs` leaf. The
kernel checks that the two premises share term-shape, sample size,
and provenance, and that the conclusion frequency is exactly the
product (chain rule).

### subB — Northpointe's PPV-equality defence

The narrative is shorter:

> *"Among defendants the model flagged, 775 of 1234 Black and 272 of
> 460 White actually recidivated."*

Two `Obs` leaves.

> *"The two-sample 95 % CI for the difference of these two rates is
> [0.0 %, 8.9 %]. It contains zero. Therefore the equal-PPV claim is
> Trusted on this data."*

The `IT2` step is the *symmetric counterpart* of `IUT2`: the kernel
computes the same score-test CI but checks that 0 lies *inside* it.
Same rule family, opposite verdict.

> *"Carry the trusted PPV-equality interval forward."*

The `ET` step adds the interval to the typing context.

### subC — joint attribute audit

The narrative of *"two attributes of the same defendant, treated as
independent"* maps to:

- two `Obs` leaves recording the marginals (one for Flagged, one for
  Recidivated) on a small audit cohort;
- one `I×` step that combines them into a single product-typed
  judgment, with an explicit *independence witness* asserted by the
  auditor (the kernel does not check independence — it only checks
  that the witness is present, putting the assumption on the record);
- one `E×L` step that projects the joint judgment back onto the
  Flagged factor by dividing the joint by the conditioning factor.

### subD — calibration packaged as a conditional

Same shape as subA′'s `I→ / E→` tail, applied to the overall flagged
cohort (Black + White) rather than just the Black sub-cohort. The
narrative is:

> *"P(Recidivated | Flagged) = 1047/1694 ≈ 61.8 %. Package this as a
> conditional certificate that we can apply later."*

The `I→` step packages it; the `E→` step applies it to a fresh
Flagged frequency, checking the chain rule.

### subE — consolidating prior audits

This sub-tree shows how multiple historical audits collapse into a
single point estimate. The narrative:

> *"A 2014 audit placed the Black FPR in [40 %, 45 %]; a 2016 audit
> placed it in [42 %, 50 %]. We are willing to commit to the point
> estimate 0.43 — but only because 0.43 is in the intersection of
> the two prior intervals."*

The `Contraction` step does exactly this collapse, and the kernel
checks the intersection-membership condition (`0.43 ∈ [0.40, 0.45] ∩
[0.42, 0.50]`). If we'd written `0.10` instead, the kernel would
reject — a key adversarial-attack defence.

### Top-level — `WeakeningS` chain

Each of the five `WeakeningS` applications combines one sub-certificate
with the running audit document, retaining the deepest sub-tree's
claim and merging the contexts. The kernel check is the explicit
*independence witness* (the auditor asserts that the two
sub-certificates rest on independent provenance) and the structural
constraint that the merged context contains both premise contexts.

The headline conclusion at the root is therefore subA's frequency
claim about Black non-recidivists, with the FPR-gap interval carried
in the typing context — exactly the formal content of *"the
equal-FPR hypothesis fails on the published data"*. But the
document also carries Northpointe's PPV-equality certificate, the
calibration certificates, the joint-attribute claim, and the
consolidated prior — all in one bundle, all kernel-checked.

## 5. The fairness landscape, in plain English

There is no single "fair" — there are several orthogonal definitions
that data scientists disagree about. This certificate puts three of them
side by side:

* **Equal FPR** (ProPublica) — *"are non-recidivists flagged at the
  same rate across races?"* On this data: **no**, with a kernel-checked
  Untrusted verdict.
* **Equal PPV** (Northpointe) — *"are the model's flagged defendants
  equally likely to actually recidivate, across races?"* On this data:
  **yes**, with a kernel-checked Trusted verdict.
* **Calibration** — *"does the model's quoted risk score equal the
  empirical recidivism rate of those it gives that score?"* On this
  data: **no**, restricted to the Black sub-cohort.

These three verdicts can hold *simultaneously* on the published
COMPAS data because of the impossibility result: when the underlying
group base rates differ, no single algorithm can satisfy more than one
of the three at once. TPTND-Lean does not resolve the dispute. It
makes each side's claim a *separately* checkable certificate, with
the side conditions of the calculus standing in for the auditor's
informal "I checked the arithmetic". Each verdict's certificate can
be inspected, composed, or attacked independently.

## 6. What the kernel is NOT checking

A few things it would be honest to flag:

* **Raw counts at the leaves.** `Obs` trusts the leaf's claim about
  the data. If you write *"1500 Black non-recidivists were flagged"*
  when the CSV says 510, the kernel won't notice — the leaf is the
  ingestion boundary. Defence: use a separate ingest auditor (e.g.
  `compas_audit` against the published CSV).

* **Choice of CI procedure.** The kernel computes one specific kind of
  CI — the score-test (Wilson) interval in exact rationals. If a
  different methodology (Wald, Clopper-Pearson, Bayesian credible
  interval) would have given the opposite verdict on a borderline
  case, the certificate doesn't tell you that. The procedure is
  fixed by the kernel implementation, not by the certificate.

* **Choice of cohort.** Dropping or relabelling whole sub-cohorts
  produces a different but kernel-valid certificate of a different
  audit. The *kernel* never knows what audit you intended; the
  *certificate* is what a reader can hold you to.

These boundaries are honest gaps; each could be closed by a separate
auditor module. The kernel's job is to ensure that, *given* the leaves
and *given* the procedure, every inferential move is sound.

## 7. Reproducing the verdict

```sh
lake build pp_diverse
./.lake/build/bin/pp_diverse
```

The binary prints the kernel verdict and a per-rule justification
table. Every rule application is paired with the audit-report sentence
it formalises and the kernel-checked side condition that gates it.

If any side condition were violated, the kernel would reject. As a
quick sanity check that the kernel really is doing the work, edit
`PPDiverse.lean` to change the IUT2 step's `untrust` to `trust`
(claiming equal-FPR is *Trusted*) and rebuild — the kernel will refuse
the certificate with `IT2: 0 must lie within two-sample CI`, because
the data does not support that verdict.
