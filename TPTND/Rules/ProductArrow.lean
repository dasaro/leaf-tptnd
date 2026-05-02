import TPTND.CheckM
import TPTND.WellFormedness
import TPTND.Arithmetic

namespace TPTND

/-! # Product and Arrow Rules (Table 4)

`I×`, `E×L`, `E×R`, `I→`, `E→`.  Design doc §7.4. -/

-- ============================================================================
-- I×  (product introduction)
-- ============================================================================

def checkIProd (d : Derivation) : CheckM Unit := do
  let ps ← expectPremises d 2 "I×"
  match ps with
  | [p1, p2] => do
    ensure d.hasIndependenceWitness
      "I×: explicit independence witness required"
    let tc1 ← expectTermClaim (getClaim p1) "I×"
    let tc2 ← expectTermClaim (getClaim p2) "I×"
    let conc ← expectTermClaim (getClaim d) "I×"
    ensure (tc1.mode == tc2.mode && tc1.mode == conc.mode)
      "I×: all must share the same mode"
    ensure (tc1.samples == tc2.samples && tc1.samples == conc.samples)
      "I×: all must share the same sample size"
    ensure (tc1.prov == tc2.prov && tc1.prov == conc.prov)
      "I×: all must share the same provenance"
    ensure (conc.output == Output.prod tc1.output tc2.output)
      "I×: conclusion output must be product of premise outputs"
    ensure (conc.term == Term.pair tc1.term tc2.term)
      "I×: conclusion term must be ⟨t, u⟩"
    let prod := probMul tc1.value tc2.value
    ensure (decide (conc.value.val == prod.val))
      "I×: conclusion value must be p · q"
    -- Contexts merged
    let merged := mergeContexts [getCtx p1, getCtx p2]
    ensure (contextEqSet (getCtx d) merged)
      "I×: conclusion context must be merge of premise contexts"
  | _ => throw "I×: internal error"

-- ============================================================================
-- E×L  (product elimination left)
-- ============================================================================

def checkEProdL (d : Derivation) : CheckM Unit := do
  let ps ← expectPremises d 2 "E×L"
  match ps with
  | [p1, p2] => do
    let tc1 ← expectTermClaim (getClaim p1) "E×L"   -- (α×β)_r
    let tc2 ← expectTermClaim (getClaim p2) "E×L"   -- snd(v) : β_q
    let conc ← expectTermClaim (getClaim d) "E×L"   -- fst(v) : α_{r/q}
    ensure (tc1.mode == tc2.mode && tc1.mode == conc.mode)
      "E×L: all must share the same mode"
    ensure (tc1.samples == tc2.samples && tc1.samples == conc.samples)
      "E×L: all must share the same sample size"
    ensure (tc1.prov == tc2.prov && tc1.prov == conc.prov)
      "E×L: all must share the same provenance"
    -- tc1 output = α × β, tc2 output = β, conc output = α
    ensure (tc1.output == Output.prod conc.output tc2.output)
      "E×L: first premise must be product of conclusion and second outputs"
    -- 0 < q
    ensure (decide (0 < tc2.value.val))
      "E×L: q must be strictly positive"
    match probDiv tc1.value tc2.value with
    | some quot =>
      ensure (decide (conc.value.val == quot.val))
        "E×L: conclusion value must be r / q"
    | none => throw "E×L: division failed (q = 0 or r/q > 1)"
  | _ => throw "E×L: internal error"

-- ============================================================================
-- E×R  (product elimination right)
-- ============================================================================

def checkEProdR (d : Derivation) : CheckM Unit := do
  let ps ← expectPremises d 2 "E×R"
  match ps with
  | [p1, p2] => do
    let tc1 ← expectTermClaim (getClaim p1) "E×R"   -- (α×β)_r
    let tc2 ← expectTermClaim (getClaim p2) "E×R"   -- fst(v) : α_p
    let conc ← expectTermClaim (getClaim d) "E×R"   -- snd(v) : β_{r/p}
    ensure (tc1.mode == tc2.mode && tc1.mode == conc.mode)
      "E×R: all must share the same mode"
    ensure (tc1.samples == tc2.samples && tc1.samples == conc.samples)
      "E×R: all must share the same sample size"
    ensure (tc1.prov == tc2.prov && tc1.prov == conc.prov)
      "E×R: all must share the same provenance"
    ensure (tc1.output == Output.prod tc2.output conc.output)
      "E×R: first premise must be product of second and conclusion outputs"
    ensure (decide (0 < tc2.value.val))
      "E×R: p must be strictly positive"
    match probDiv tc1.value tc2.value with
    | some quot =>
      ensure (decide (conc.value.val == quot.val))
        "E×R: conclusion value must be r / p"
    | none => throw "E×R: division failed (p = 0 or r/p > 1)"
  | _ => throw "E×R: internal error"

-- ============================================================================
-- I→  (arrow introduction)
-- ============================================================================

def checkIArr (d : Derivation) : CheckM Unit := do
  let ps ← expectPremises d 1 "I→"
  match ps with
  | [p] => do
    let tc ← expectTermClaim (getClaim p) "I→"
    let conc ← expectTermClaim (getClaim d) "I→"
    -- Conclusion term must be [x]t  (lam)
    match conc.term with
    | .lam x body => do
      ensure (body == tc.term)
        "I→: lambda body must match premise term"
      -- Conclusion output must be (α ⇒ β)  where β = premise output
      match conc.output with
      | .arr α β => do
        ensure (β == tc.output) "I→: arrow target must match premise output"
        -- Discharged assumption: exactly one entry x : α_a in premise context
        let discharged := (getCtx p).filter (fun e =>
          e.name == x && e.output == α &&
          match e.constraint with | .exact _ => true | _ => false)
        ensure (discharged.length == 1)
          "I→: must discharge exactly one exact entry for x : α"
        -- Conclusion context = premise context minus the discharged entry
        match discharged with
        | [de] =>
          let expectedCtx := (getCtx p).filter (· != de)
          ensure (contextEqSet (getCtx d) expectedCtx)
            "I→: conclusion context must be premise context minus discharged entry"
        | _ => throw "I→: unreachable"
        ensure (conc.samples == tc.samples) "I→: sample size must be preserved"
        ensure (conc.prov == tc.prov) "I→: provenance must be preserved"
        ensure (conc.mode == tc.mode) "I→: mode must be preserved"
      | _ => throw "I→: conclusion output must be an arrow type"
    | _ => throw "I→: conclusion term must be a lambda"
  | _ => throw "I→: internal error"

-- ============================================================================
-- E→  (arrow elimination)
-- ============================================================================

def checkEArr (d : Derivation) : CheckM Unit := do
  let ps ← expectPremises d 2 "E→"
  match ps with
  | [p1, p2] => do
    let tc1 ← expectTermClaim (getClaim p1) "E→"   -- [x]t : (α ⇒_a β)_q
    let tc2 ← expectTermClaim (getClaim p2) "E→"   -- u : α_r
    let conc ← expectTermClaim (getClaim d) "E→"   -- ([x]t · u) : β_{qr}
    ensure (tc1.mode == tc2.mode && tc1.mode == conc.mode)
      "E→: all must share the same mode"
    ensure (tc1.samples == tc2.samples && tc1.samples == conc.samples)
      "E→: all must share the same sample size"
    ensure (tc1.prov == tc2.prov && tc1.prov == conc.prov)
      "E→: all must share the same provenance"
    match tc1.output with
    | .arr α β => do
      ensure (α == tc2.output)
        "E→: arrow source must match second premise output"
      ensure (β == conc.output)
        "E→: arrow target must match conclusion output"
      -- Conclusion term = app tc1.term tc2.term
      ensure (conc.term == Term.app tc1.term tc2.term)
        "E→: conclusion term must be application"
      let prod := probMul tc1.value tc2.value
      ensure (decide (conc.value.val == prod.val))
        "E→: conclusion value must be q · r"
      -- Contexts merged
      let merged := mergeContexts [getCtx p1, getCtx p2]
      ensure (contextEqSet (getCtx d) merged)
        "E→: conclusion context must be merge of premise contexts"
    | _ => throw "E→: first premise output must be an arrow type"
  | _ => throw "E→: internal error"

end TPTND
