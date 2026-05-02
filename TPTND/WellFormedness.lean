import TPTND.Syntax
import TPTND.Judgement
import TPTND.Arithmetic

namespace TPTND

/-! # TPTND Well-Formedness Predicates

Entry-level and context-level well-formedness, independence witnesses,
provenance checks, and context merging.
Follows Section 5 of the TPTND Lean Design Document. -/

-- ============================================================================
-- Entry well-formedness
-- ============================================================================

/-- A constraint is well-formed when its endpoints satisfy ℓ ≤ h. -/
def constraintWF (c : Constraint) : Bool :=
  match c with
  | .exact _             => true
  | .interval lo hi      => decide (lo.val ≤ hi.val)
  | .outsideInterval lo hi => decide (lo.val ≤ hi.val)
  | .unknown             => true

/-- An entry is well-formed when its support is nonempty and its
    constraint is well-formed. -/
def entryWF (e : ContextEntry) : Bool :=
  e.support.Nonempty && constraintWF e.constraint

-- ============================================================================
-- Context well-formedness (global admissibility)
-- ============================================================================

/-- Exact mass of an entry: the `val` if the constraint is `.exact`, else 0. -/
private def exactMass (e : ContextEntry) : ℚ :=
  match e.constraint with
  | .exact p => p.val
  | _        => 0

/-- Lower bound contributed by an interval constraint, else 0. -/
private def intervalLower (e : ContextEntry) : ℚ :=
  match e.constraint with
  | .interval lo _ => lo.val
  | _              => 0

/-- Per-variable total: sum of exact masses + interval lower bounds for all
    entries sharing variable name `x`. -/
private def variableMass (Γ : Context) (x : String) : ℚ :=
  Γ.foldl (fun acc e =>
    if e.name == x then acc + exactMass e + intervalLower e else acc) 0

/-- Distinct variable names in a context. -/
private def variableNames (Γ : Context) : List String :=
  Γ.map (·.name) |>.eraseDups

/-- A context is well-formed when every entry is well-formed and, for each
    variable, exact masses plus interval lower bounds do not exceed 1. -/
def contextWF (Γ : Context) : Bool :=
  Γ.all entryWF &&
  (variableNames Γ).all (fun x => decide (variableMass Γ x ≤ 1))

-- ============================================================================
-- Independence witness
-- ============================================================================

/-- Placeholder: the checker delegates independence to the explicit
    `hasIndependenceWitness` flag on the derivation node (design doc §9.4).
    This function always returns `true`; the actual gate is the flag. -/
def independentContexts (_Γ _Δ : Context) : Bool := true

-- ============================================================================
-- Provenance checks
-- ============================================================================

/-- Extract provenance from a term claim inside a derivation's conclusion. -/
private def claimProv (c : Claim) : Option Provenance :=
  match c with
  | .term tc => some tc.prov
  | _        => none

/-- All premises share the same provenance.  Returns `true` when the list is
    empty or when provenance is not applicable to every premise. -/
def sameProvenance (ps : List Derivation) : Bool :=
  let provs := ps.filterMap (fun d => claimProv d.conclusion.claim)
  match provs with
  | []     => true
  | p :: rest => rest.all (· == p)

-- ============================================================================
-- Context merging
-- ============================================================================

/-- Merge a list of contexts by concatenation and deduplication.
    Two entries are considered equal when all four fields match
    (`DecidableEq ContextEntry`).  Order follows the input order with
    later duplicates removed. -/
def mergeContexts (cs : List Context) : Context :=
  (cs.flatten).eraseDups

/-- Check whether two contexts are equal up to ordering (set equality). -/
def contextEqSet (Γ Δ : Context) : Bool :=
  Γ.all (· ∈ Δ) && Δ.all (· ∈ Γ)

/-- Check that conclusion context `Δ` extends premise context `Γ`:
      • every entry of `Γ` appears in `Δ`, and
      • every entry of `Δ` either appears in `Γ` or satisfies `extra`.
    Used by elimination rules to enforce that the conclusion adds only
    the rule-specific new entry, ruling out context laundering. -/
def contextExtendsBy (Γ Δ : Context) (extra : ContextEntry → Bool) : Bool :=
  Γ.all (· ∈ Δ) && Δ.all (fun e => e ∈ Γ || extra e)

/-- Check that conclusion context `Δ` is the result of replacing a
    "consumed" entry in premise context `Γ` with a new entry:
      • every entry of `Γ` either is consumed (matches `consumed`) or
        appears in `Δ`,
      • every entry of `Δ` either appears in `Γ` or matches `extra`.
    Used by `ETex` where a non-exact entry is replaced by an exact one. -/
def contextReplacesBy (Γ Δ : Context)
    (consumed extra : ContextEntry → Bool) : Bool :=
  Γ.all (fun e => consumed e || e ∈ Δ) &&
  Δ.all (fun e => e ∈ Γ || extra e)

end TPTND
