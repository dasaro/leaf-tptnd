import TPTND.CheckM
import TPTND.WellFormedness
import TPTND.Arithmetic
import Mathlib.Data.Finset.Card

namespace TPTND

/-! # Atomic Leaf Rules (Table 2)

`identity`, `identity_star`, `obs`, `experiment`, `expectation`.
Design doc §7.2. -/

private def isAtomicTerm : Term → Bool
  | .atom _ => true
  | _       => false

/-- Find entries in Γ whose name matches the given atomic term name. -/
private def supportEntries (Γ : Context) (t : Term) : List ContextEntry :=
  match t with
  | .atom s => Γ.filter (fun e => e.name == s)
  | _       => []

-- ============================================================================
-- identity  (IDENTITY*₂ in PDF): |Γ| = 1, entry matches conclusion
-- ============================================================================

def checkIdentity (d : Derivation) : CheckM Unit := do
  let _ ← expectPremises d 0 "identity"
  let Γ := getCtx d
  ensure (Γ.length == 1) "identity: context must be a singleton"
  match Γ, getClaim d with
  | [e], .identity e' =>
    ensure (e == e') "identity: context entry must match conclusion entry"
  | _, _ => throw "identity: conclusion must be an identity claim"

-- ============================================================================
-- identity_star (IDENTITY* in PDF): lookup x : αc ∈ Γ
-- ============================================================================

def checkIdentityStar (d : Derivation) : CheckM Unit := do
  let _ ← expectPremises d 0 "identity_star"
  match getClaim d with
  | .identity e =>
    ensure (e ∈ getCtx d)
      "identity_star: entry not found in context"
  | _ => throw "identity_star: conclusion must be an identity claim"

-- ============================================================================
-- obs (OBS* in PDF)
-- ============================================================================

def checkObs (d : Derivation) : CheckM Unit := do
  let _ ← expectPremises d 0 "obs"
  match getClaim d with
  | .term tc => do
    ensure (tc.mode == .frequency) "obs: must be frequency mode"
    ensure tc.prov.Nonempty "obs: provenance must be nonempty"
    ensure (tc.samples > 0) "obs: sample size must be positive"
    ensure (isAtomicTerm tc.term) "obs: term must be atomic"
    -- nf ∈ ℕ: samples * frequency must be a natural number
    let nf := (tc.samples : ℚ) * tc.value.val
    ensure (nf.den == 1 && nf.num ≥ 0)
      "obs: n·f must be a non-negative integer"
    -- Exactly one support entry for term t
    let supp := supportEntries (getCtx d) tc.term
    ensure (supp.length == 1)
      "obs: exactly one support entry required for term"
  | _ => throw "obs: conclusion must be a term claim"

-- ============================================================================
-- experiment (EXPERIMENT in PDF)
-- ============================================================================

def checkExperiment (d : Derivation) : CheckM Unit := do
  let _ ← expectPremises d 0 "experiment"
  match getClaim d with
  | .term tc => do
    ensure (tc.prov.card == 1) "experiment: provenance must be singleton"
    ensure (isAtomicTerm tc.term) "experiment: term must be atomic"
    let supp := supportEntries (getCtx d) tc.term
    ensure (supp.length == 1)
      "experiment: exactly one support entry required for term"
  | _ => throw "experiment: conclusion must be a term claim"

-- ============================================================================
-- expectation (EXPECTATION in PDF)
-- ============================================================================

def checkExpectation (d : Derivation) : CheckM Unit := do
  let _ ← expectPremises d 0 "expectation"
  match getClaim d with
  | .term tc => do
    ensure (tc.mode == .expected) "expectation: must be expected mode"
    ensure (tc.prov.card == 1) "expectation: provenance must be singleton"
    ensure (tc.samples > 0) "expectation: sample size must be positive"
    ensure (isAtomicTerm tc.term) "expectation: term must be atomic"
    -- Exactly one EXACT support entry
    let supp := supportEntries (getCtx d) tc.term
    ensure (supp.length == 1)
      "expectation: exactly one support entry required"
    match supp with
    | [e] =>
      match e.constraint with
      | .exact _ => pure ()
      | _ => throw "expectation: support entry must have exact constraint"
    | _ => throw "expectation: unreachable"
  | _ => throw "expectation: conclusion must be a term claim"

end TPTND
