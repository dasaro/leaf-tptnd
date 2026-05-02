import TPTND.CheckM
import TPTND.WellFormedness
import TPTND.Arithmetic

namespace TPTND

/-! # Trust Rules (Tables 5–6)

`IT`, `IUT`, `ET`, `EUT`, `ETex`.  Design doc §7.6. -/

-- ============================================================================
-- IT  (trust introduction)
-- ============================================================================

def checkIT (d : Derivation) : CheckM Unit := do
  let ps ← expectPremises d 2 "IT"
  match ps with
  | [pModel, pObs] => do
    let modelEntry ← match getClaim pModel with
      | .identity e => pure e
      | _ => throw "IT: first premise must be an identity claim (model)"
    let modelP ← match modelEntry.constraint with
      | .exact p => pure p
      | _ => throw "IT: model entry must have exact constraint"
    let obs ← expectTermClaim (getClaim pObs) "IT"
    ensure (obs.mode == .frequency) "IT: observation must be frequency mode"
    ensure (modelEntry.output == obs.output)
      "IT: model output must match observed output"
    let ci := binomialCI obs.samples obs.value modelP
    ensure (inConstraint modelP ci)
      "IT: model probability must lie within binomial CI"
    match getClaim d with
    | .trust (.trust t n α f p interval) => do
      ensure (t == obs.term) "IT: trust term mismatch"
      ensure (n == obs.samples) "IT: trust sample size mismatch"
      ensure (α == obs.output) "IT: trust output mismatch"
      ensure (decide (f.val == obs.value.val)) "IT: trust frequency mismatch"
      ensure (decide (p.val == modelP.val)) "IT: trust model prob mismatch"
      ensure (interval == ci) "IT: trust interval mismatch"
    | _ => throw "IT: conclusion must be a trust claim"
  | _ => throw "IT: internal error"

-- ============================================================================
-- IUT  (untrust introduction)
-- ============================================================================

def checkIUT (d : Derivation) : CheckM Unit := do
  let ps ← expectPremises d 2 "IUT"
  match ps with
  | [pModel, pObs] => do
    let modelEntry ← match getClaim pModel with
      | .identity e => pure e
      | _ => throw "IUT: first premise must be an identity claim"
    let modelP ← match modelEntry.constraint with
      | .exact p => pure p
      | _ => throw "IUT: model entry must have exact constraint"
    let obs ← expectTermClaim (getClaim pObs) "IUT"
    ensure (obs.mode == .frequency) "IUT: observation must be frequency mode"
    ensure (modelEntry.output == obs.output) "IUT: output mismatch"
    let ci := binomialCI obs.samples obs.value modelP
    ensure (notInConstraint modelP ci)
      "IUT: model probability must lie OUTSIDE binomial CI"
    match getClaim d with
    | .trust (.untrust t n α f p interval) => do
      ensure (t == obs.term) "IUT: term mismatch"
      ensure (n == obs.samples) "IUT: sample size mismatch"
      ensure (α == obs.output) "IUT: output mismatch"
      ensure (decide (f.val == obs.value.val)) "IUT: frequency mismatch"
      ensure (decide (p.val == modelP.val)) "IUT: model prob mismatch"
      ensure (interval == ci) "IUT: interval mismatch"
    | _ => throw "IUT: conclusion must be an untrust claim"
  | _ => throw "IUT: internal error"

-- ============================================================================
-- IT2  (two-sample trust introduction)
-- ============================================================================
/-- Two-sample Trust: both premises are frequency observations.
    Computes the two-sample score-test CI for the difference f − g.
    If 0 ∈ CI → the groups are statistically indistinguishable → Trust.
    The `model` field in the TrustClaim stores the right-hand rate (g). -/

def checkIT2 (d : Derivation) : CheckM Unit := do
  let ps ← expectPremises d 2 "IT2"
  match ps with
  | [pLeft, pRight] => do
    let tcL ← expectTermClaim (getClaim pLeft) "IT2"
    let tcR ← expectTermClaim (getClaim pRight) "IT2"
    ensure (tcL.mode == .frequency && tcR.mode == .frequency)
      "IT2: both premises must be frequency mode"
    ensure (tcL.output == tcR.output)
      "IT2: both premises must share the same output"
    ensure (Provenance.disjoint tcL.prov tcR.prov)
      "IT2: provenances must be disjoint"
    let ci := twoSampleCI tcL.samples tcR.samples tcL.value tcR.value
    ensure (inConstraint Prob.zero ci)
      "IT2: 0 must lie within two-sample CI (no significant difference)"
    match getClaim d with
    | .trust (.trust t n α f p interval) => do
      ensure (t == tcL.term) "IT2: trust term mismatch"
      ensure (n == tcL.samples) "IT2: trust sample size mismatch"
      ensure (α == tcL.output) "IT2: trust output mismatch"
      ensure (decide (f.val == tcL.value.val)) "IT2: trust frequency mismatch"
      ensure (decide (p.val == tcR.value.val)) "IT2: trust model prob mismatch"
      ensure (interval == ci) "IT2: trust interval mismatch"
    | _ => throw "IT2: conclusion must be a trust claim"
  | _ => throw "IT2: internal error"

-- ============================================================================
-- IUT2  (two-sample untrust introduction)
-- ============================================================================
/-- Two-sample UTrust: both premises are frequency observations.
    If 0 ∉ CI → the groups are significantly different → UTrust. -/

def checkIUT2 (d : Derivation) : CheckM Unit := do
  let ps ← expectPremises d 2 "IUT2"
  match ps with
  | [pLeft, pRight] => do
    let tcL ← expectTermClaim (getClaim pLeft) "IUT2"
    let tcR ← expectTermClaim (getClaim pRight) "IUT2"
    ensure (tcL.mode == .frequency && tcR.mode == .frequency)
      "IUT2: both premises must be frequency mode"
    ensure (tcL.output == tcR.output)
      "IUT2: both premises must share the same output"
    ensure (Provenance.disjoint tcL.prov tcR.prov)
      "IUT2: provenances must be disjoint"
    let ci := twoSampleCI tcL.samples tcR.samples tcL.value tcR.value
    ensure (notInConstraint Prob.zero ci)
      "IUT2: 0 must lie OUTSIDE two-sample CI (significant difference)"
    match getClaim d with
    | .trust (.untrust t n α f p interval) => do
      ensure (t == tcL.term) "IUT2: term mismatch"
      ensure (n == tcL.samples) "IUT2: sample size mismatch"
      ensure (α == tcL.output) "IUT2: output mismatch"
      ensure (decide (f.val == tcL.value.val)) "IUT2: frequency mismatch"
      ensure (decide (p.val == tcR.value.val)) "IUT2: model prob mismatch"
      ensure (interval == ci) "IUT2: interval mismatch"
    | _ => throw "IUT2: conclusion must be an untrust claim"
  | _ => throw "IUT2: internal error"

-- ============================================================================
-- ET  (trust elimination)
-- ============================================================================

def checkET (d : Derivation) : CheckM Unit := do
  let ps ← expectPremises d 1 "ET"
  match ps with
  | [p] => do
    match getClaim p with
    | .trust (.trust t n α f _p interval) => do
      let conc ← expectTermClaim (getClaim d) "ET"
      -- Preserve observed data
      ensure (conc.mode == .frequency) "ET: must preserve frequency mode"
      ensure (conc.term == t) "ET: must preserve observed term"
      ensure (conc.samples == n) "ET: must preserve sample size"
      ensure (conc.output == α) "ET: must preserve output"
      ensure (decide (conc.value.val == f.val)) "ET: must preserve frequency value"
      -- Conclusion context = premise context + interval entry x_u : α_{[ℓ,h]}.
      -- We require: (a) the new interval entry is present, and
      -- (b) the conclusion context extends the premise context only by
      -- entries of that shape (no context laundering).
      let extraOK := fun (e : ContextEntry) =>
        e.output == α && e.constraint == interval
      ensure ((getCtx d).any extraOK)
        "ET: conclusion context must contain x_u : α_{[ℓ,h]}"
      ensure (contextExtendsBy (getCtx p) (getCtx d) extraOK)
        "ET: conclusion context must extend premise context only by the interval entry"
    | _ => throw "ET: premise must be a trust claim"
  | _ => throw "ET: internal error"

-- ============================================================================
-- EUT  (untrust elimination)
-- ============================================================================

def checkEUT (d : Derivation) : CheckM Unit := do
  let ps ← expectPremises d 1 "EUT"
  match ps with
  | [p] => do
    match getClaim p with
    | .trust (.untrust t n α f _p interval) => do
      let conc ← expectTermClaim (getClaim d) "EUT"
      ensure (conc.mode == .frequency) "EUT: must preserve frequency mode"
      ensure (conc.term == t) "EUT: must preserve observed term"
      ensure (conc.samples == n) "EUT: must preserve sample size"
      ensure (conc.output == α) "EUT: must preserve output"
      ensure (decide (conc.value.val == f.val)) "EUT: must preserve frequency value"
      -- Complement interval: [ℓ,h] → ¬[ℓ,h]
      let complementInterval := match interval with
        | .interval lo hi => Constraint.outsideInterval lo hi
        | other           => other
      let extraOK := fun (e : ContextEntry) =>
        e.output == α && e.constraint == complementInterval
      ensure ((getCtx d).any extraOK)
        "EUT: conclusion context must contain x_u : α_{¬[ℓ,h]}"
      ensure (contextExtendsBy (getCtx p) (getCtx d) extraOK)
        "EUT: conclusion context must extend premise context only by the complement-interval entry"
    | _ => throw "EUT: premise must be an untrust claim"
  | _ => throw "EUT: internal error"

-- ============================================================================
-- ETex  (trust exact elimination — re-entry to expected layer)
-- ============================================================================

def checkETex (d : Derivation) : CheckM Unit := do
  let ps ← expectPremises d 1 "ETex"
  match ps with
  | [p] => do
    match getClaim p with
    | .trust (.trust t n α _f modelP _interval) => do
      -- The premise context must contain a non-exact entry for the
      -- observed variable; we check that p lies in SOME constraint in ctx.
      let premCtx := getCtx p
      let obsEntries := premCtx.filter (fun e => e.output == α)
      let pInSomeConstraint := obsEntries.any (fun e =>
        e.constraint.contains modelP)
      ensure pInSomeConstraint
        "ETex: model probability must be consistent with a context constraint"
      -- Conclusion must be a term claim in EXPECTED mode (re-entry)
      let conc ← expectTermClaim (getClaim d) "ETex"
      ensure (conc.mode == .expected)
        "ETex: conclusion must be in expected mode (re-entry)"
      ensure (conc.term == t) "ETex: must preserve term"
      ensure (conc.samples == n) "ETex: must preserve sample size"
      ensure (conc.output == α) "ETex: must preserve output"
      -- Conclusion value = model probability (the trusted exact value)
      ensure (decide (conc.value.val == modelP.val))
        "ETex: conclusion value must equal the trusted model probability"
      -- Context: the non-exact entry replaced by exact  x_u : α_p.
      -- Premise's α-entries that are non-exact are "consumed" (replaced),
      -- and the conclusion may add an exact α_p entry.  Anything else
      -- carries over verbatim — no context laundering.
      let consumed := fun (e : ContextEntry) =>
        e.output == α &&
        (match e.constraint with | .exact _ => false | _ => true)
      let extraOK := fun (e : ContextEntry) =>
        e.output == α && e.constraint == .exact modelP
      ensure ((getCtx d).any extraOK)
        "ETex: conclusion context must contain exact entry x_u : α_p"
      ensure (contextReplacesBy (getCtx p) (getCtx d) consumed extraOK)
        "ETex: conclusion context must replace consumed α-entries with exact x_u : α_p"
    | _ => throw "ETex: premise must be a trust claim"
  | _ => throw "ETex: internal error"

end TPTND
