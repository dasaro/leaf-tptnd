import TPTND.CheckM
import TPTND.WellFormedness
import TPTND.Arithmetic

namespace TPTND

/-! # Comparison Rules (Table 6, second half)

`IEx`, `INEx`, `EEx`, `ENEx`.  Design doc §7.7. -/

-- ============================================================================
-- IEx  (excess introduction)
-- ============================================================================

def checkIEx (d : Derivation) : CheckM Unit := do
  let ps ← expectPremises d 2 "IEx"
  match ps with
  | [p1, p2] => do
    let tc1 ← expectTermClaim (getClaim p1) "IEx"
    let tc2 ← expectTermClaim (getClaim p2) "IEx"
    ensure (tc1.mode == .frequency && tc2.mode == .frequency)
      "IEx: both premises must be frequency mode"
    ensure (tc1.output == tc2.output)
      "IEx: both premises must share the same output"
    ensure (Provenance.disjoint tc1.prov tc2.prov)
      "IEx: provenances must be disjoint"
    let ci := twoSampleCI tc1.samples tc2.samples tc1.value tc2.value
    ensure (notInConstraint Prob.zero ci)
      "IEx: 0 must lie outside the two-sample CI (significant difference)"
    match getClaim d with
    | .comparison (.excess left right diff interval) => do
      ensure (decide (left.value.val == tc1.value.val))
        "IEx: left term claim mismatch"
      ensure (decide (right.value.val == tc2.value.val))
        "IEx: right term claim mismatch"
      match probSub tc1.value tc2.value with
      | some d' =>
        ensure (decide (diff.val == d'.val))
          "IEx: difference must be f - g"
      | none => throw "IEx: f - g is negative (left must exceed right)"
      ensure (interval == ci) "IEx: interval must match computed CI"
    | _ => throw "IEx: conclusion must be an excess comparison claim"
  | _ => throw "IEx: internal error"

-- ============================================================================
-- INEx  (no-excess introduction)
-- ============================================================================

def checkINEx (d : Derivation) : CheckM Unit := do
  let ps ← expectPremises d 2 "INEx"
  match ps with
  | [p1, p2] => do
    let tc1 ← expectTermClaim (getClaim p1) "INEx"
    let tc2 ← expectTermClaim (getClaim p2) "INEx"
    ensure (tc1.mode == .frequency && tc2.mode == .frequency)
      "INEx: both premises must be frequency mode"
    ensure (tc1.output == tc2.output) "INEx: outputs must match"
    ensure (Provenance.disjoint tc1.prov tc2.prov) "INEx: provenances must be disjoint"
    let ci := twoSampleCI tc1.samples tc2.samples tc1.value tc2.value
    ensure (inConstraint Prob.zero ci)
      "INEx: 0 must lie within the two-sample CI (no significant difference)"
    match getClaim d with
    | .comparison (.noExcess _ _ _ interval) =>
      ensure (interval == ci) "INEx: interval must match computed CI"
    | _ => throw "INEx: conclusion must be a noExcess comparison claim"
  | _ => throw "INEx: internal error"

-- ============================================================================
-- EEx  (excess elimination)
-- ============================================================================

def checkEEx (d : Derivation) : CheckM Unit := do
  let ps ← expectPremises d 2 "EEx"
  match ps with
  | [pExcess, pModel] => do
    let exClaim ← expectComparisonClaim (getClaim pExcess) "EEx"
    match exClaim with
    | .excess leftTC _ _ interval => do
      let modelEntry ← match getClaim pModel with
        | .identity e => pure e
        | _ => throw "EEx: second premise must be an identity claim"
      let modelP ← match modelEntry.constraint with
        | .exact p => pure p
        | _ => throw "EEx: model entry must have exact constraint"
      match interval with
      | .interval lo hi => do
        -- p + h ≤ 1
        match probAdd modelP hi with
        | some _ => pure ()
        | none => throw "EEx: p + h exceeds 1"
        -- Conclusion must be a term claim preserving the LEFT side data
        let conc ← expectTermClaim (getClaim d) "EEx"
        ensure (conc.mode == .frequency) "EEx: must preserve frequency mode"
        ensure (conc.term == leftTC.term) "EEx: must preserve left term"
        ensure (conc.samples == leftTC.samples) "EEx: must preserve left sample size"
        ensure (conc.output == leftTC.output) "EEx: must preserve left output"
        ensure (decide (conc.value.val == leftTC.value.val))
          "EEx: must preserve left frequency"
        -- Shifted interval [p+ℓ, p+h] must appear in conclusion context,
        -- and the conclusion context must extend pModel's context only
        -- by entries of that shape (no context laundering).
        let shiftedLo := clampProb (modelP.val + lo.val)
        let shiftedHi := clampProb (modelP.val + hi.val)
        let shiftedConstraint := Constraint.interval shiftedLo shiftedHi
        let extraOK := fun (e : ContextEntry) =>
          e.output == leftTC.output && e.constraint == shiftedConstraint
        ensure ((getCtx d).any extraOK)
          "EEx: conclusion context must contain shifted interval [p+ℓ, p+h]"
        ensure (contextExtendsBy (getCtx pModel) (getCtx d) extraOK)
          "EEx: conclusion context must extend the model premise context only by the shifted-interval entry"
      | _ => throw "EEx: interval must be a proper interval"
    | _ => throw "EEx: first premise must be an excess claim"
  | _ => throw "EEx: internal error"

-- ============================================================================
-- ENEx  (no-excess elimination)
-- ============================================================================

def checkENEx (d : Derivation) : CheckM Unit := do
  let ps ← expectPremises d 2 "ENEx"
  match ps with
  | [pNoExcess, pModel] => do
    let neClaim ← expectComparisonClaim (getClaim pNoExcess) "ENEx"
    match neClaim with
    | .noExcess leftTC _ _ interval => do
      let modelEntry ← match getClaim pModel with
        | .identity e => pure e
        | _ => throw "ENEx: second premise must be an identity claim"
      let modelP ← match modelEntry.constraint with
        | .exact p => pure p
        | _ => throw "ENEx: model entry must have exact constraint"
      match interval with
      | .interval lo hi => do
        match probAdd modelP hi with
        | some _ => pure ()
        | none => throw "ENEx: p + h exceeds 1"
        let conc ← expectTermClaim (getClaim d) "ENEx"
        ensure (conc.mode == .frequency) "ENEx: must preserve frequency mode"
        ensure (conc.term == leftTC.term) "ENEx: must preserve left term"
        ensure (conc.samples == leftTC.samples) "ENEx: must preserve sample size"
        ensure (conc.output == leftTC.output) "ENEx: must preserve output"
        ensure (decide (conc.value.val == leftTC.value.val))
          "ENEx: must preserve left frequency"
        let shiftedLo := clampProb (modelP.val + lo.val)
        let shiftedHi := clampProb (modelP.val + hi.val)
        let shiftedConstraint := Constraint.interval shiftedLo shiftedHi
        let extraOK := fun (e : ContextEntry) =>
          e.output == leftTC.output && e.constraint == shiftedConstraint
        ensure ((getCtx d).any extraOK)
          "ENEx: conclusion context must contain shifted interval [p+ℓ, p+h]"
        ensure (contextExtendsBy (getCtx pModel) (getCtx d) extraOK)
          "ENEx: conclusion context must extend the model premise context only by the shifted-interval entry"
      | _ => throw "ENEx: interval must be a proper interval"
    | _ => throw "ENEx: first premise must be a noExcess claim"
  | _ => throw "ENEx: internal error"

end TPTND
