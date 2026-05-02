import TPTND.CheckM
import TPTND.WellFormedness
import TPTND.Arithmetic

namespace TPTND

/-! # Bayesian Rules (Table 5, first half)

`I-P`, `E-P`.  Design doc §7.5. -/

-- ============================================================================
-- I-P  (prior family introduction)
-- ============================================================================

def checkIPrior (d : Derivation) : CheckM Unit := do
  let ps ← expectAtLeastPremises d 1 "I-P"
  let mut aVals : List ℚ := []
  let mut bSum : ℚ := 0
  for pi in ps do
    let ctx := getCtx pi
    ensure (ctx.length == 1) "I-P: each premise must have a singleton context"
    match ctx, getClaim pi with
    | [e], .identity e' => do
      match e.constraint, e'.constraint with
      | .exact a, .exact b => do
        aVals := a.val :: aVals
        bSum := bSum + b.val
      | _, _ => throw "I-P: context and conclusion entries must be exact"
    | _, _ => throw "I-P: premise must be identity claim with singleton context"
  ensure (decide (bSum == 1))
    "I-P: prior weights must sum to 1"
  ensure (aVals.eraseDups.length == aVals.length)
    "I-P: model values aᵢ must be pairwise distinct"
  ensure (getCtx d |>.isEmpty)
    "I-P: conclusion context must be empty"

-- ============================================================================
-- E-P  (posterior computation)
-- ============================================================================

/-- Single-hypothesis weight: aˢ · (1−a)^{n−s} · b -/
private def bayesWeight (a b : ℚ) (s n : Nat) : ℚ :=
  a ^ s * (1 - a) ^ (n - s) * b

/-- Bayesian posterior for hypothesis j:
    aⱼˢ · (1−aⱼ)^{n−s} · bⱼ  /  Σᵢ aᵢˢ · (1−aᵢ)^{n−s} · bᵢ -/
def bayesianPosterior
    (pairs : List (ℚ × ℚ)) (s n : Nat) (j : Nat) : Option ℚ :=
  let weights := pairs.map (fun ⟨a, b⟩ => bayesWeight a b s n)
  let denom := weights.foldl (· + ·) 0
  if denom == 0 then none
  else match weights[j]? with
    | some w => some (w / denom)
    | none   => none

/-- Extract (aᵢ, bᵢ) pairs from the prior-family premise (I-P).
    Expects a distDecl or identity-based encoding of the prior family. -/
private def extractPriorPairs (priorDeriv : Derivation) :
    CheckM (List (ℚ × ℚ)) := do
  -- The prior family was built by I-P: its premises each have
  -- context {x : α_{aᵢ}} and claim identity {y : β_{bᵢ}}.
  let priorPremises := priorDeriv.premises
  let mut pairs : List (ℚ × ℚ) := []
  for pi in priorPremises do
    match (getCtx pi), getClaim pi with
    | [e], .identity e' =>
      match e.constraint, e'.constraint with
      | .exact a, .exact b => pairs := pairs ++ [(a.val, b.val)]
      | _, _ => throw "E-P: prior premise entries must be exact"
    | _, _ => throw "E-P: prior premise must be identity with singleton context"
  pure pairs

def checkEPosterior (d : Derivation) : CheckM Unit := do
  let ps ← expectAtLeastPremises d 2 "E-P"
  match ps with
  | priorDeriv :: rest => do
    -- Extract prior family (aᵢ, bᵢ) pairs
    let pairs ← extractPriorPairs priorDeriv
    ensure (!pairs.isEmpty) "E-P: prior family must be non-empty"
    -- Find the observation premise (a term claim with frequency data)
    let obsDeriv ← match rest with
      | [o] => pure o
      | _   => throw "E-P: expected exactly one observation premise after the prior"
    let obs ← expectTermClaim (getClaim obsDeriv) "E-P"
    ensure (obs.mode == .frequency) "E-P: observation must be frequency mode"
    ensure (obs.samples > 0) "E-P: sample size must be positive"
    -- s = n·f must be a natural number
    let s_rat := (obs.samples : ℚ) * obs.value.val
    ensure (s_rat.den == 1 && s_rat.num ≥ 0)
      "E-P: s = n·f must be a non-negative integer"
    let s := s_rat.num.toNat
    -- The conclusion is an identity claim with exact posterior
    match getClaim d with
    | .identity concEntry => do
      match concEntry.constraint with
      | .exact posterior => do
        -- Find which hypothesis j is being selected: the one whose
        -- aⱼ matches the supporting assumption in the conclusion context.
        -- Look for an exact entry in the conclusion context for the
        -- observed variable.
        let concCtx := getCtx d
        let supportEntry := concCtx.find? (fun e =>
          e.output == obs.output &&
          match e.constraint with | .exact _ => true | _ => false)
        match supportEntry with
        | some se =>
          match se.constraint with
          | .exact aJ => do
            -- Find j such that pairs[j].1 == aJ
            let jOpt := pairs.findIdx? (fun ⟨a, _⟩ => decide (a == aJ.val))
            match jOpt with
            | some j => do
              match bayesianPosterior pairs s obs.samples j with
              | some expectedPost =>
                ensure (decide (posterior.val == expectedPost))
                  "E-P: posterior value does not match Bayesian update formula"
              | none => throw "E-P: Bayesian posterior computation failed (zero denominator)"
            | none => throw "E-P: supporting hypothesis aⱼ not found in prior family"
          | _ => throw "E-P: unreachable"
        | none => throw "E-P: no exact support entry in conclusion context for observed output"
      | _ => throw "E-P: conclusion must have an exact constraint"
    | _ => throw "E-P: conclusion must be an identity claim"
  | _ => throw "E-P: need at least a prior + observation premise"

end TPTND
