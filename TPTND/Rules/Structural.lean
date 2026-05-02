import TPTND.CheckM
import TPTND.WellFormedness
import TPTND.Arithmetic

namespace TPTND

/-! # Structural Rules (Table 7)

`WeakeningD`, `WeakeningS`, `Contraction`.  Design doc §7.8. -/

-- ============================================================================
-- WeakeningD  (distribution weakening)
-- ============================================================================

def checkWeakeningD (d : Derivation) : CheckM Unit := do
  let ps ← expectPremises d 2 "WeakeningD"
  match ps with
  | [pJ, pDelta] => do
    ensure d.hasIndependenceWitness
      "WeakeningD: explicit independence witness required"
    -- First premise: Γ ⊢ J  (any judgement)
    -- Second premise: ⊢ Δ  (distribution well-formedness)
    match getClaim pDelta with
    | .distDecl Δ => do
      -- Conclusion context must be Γ, Δ
      let merged := mergeContexts [getCtx pJ, Δ]
      ensure (contextEqSet (getCtx d) merged)
        "WeakeningD: conclusion context must be merge of Γ and Δ"
      -- Conclusion claim must match first premise claim
      ensure (getClaim d == getClaim pJ)
        "WeakeningD: conclusion claim must match first premise"
    | _ => throw "WeakeningD: second premise must be distDecl"
  | _ => throw "WeakeningD: internal error"

-- ============================================================================
-- WeakeningS  (strengthening weakening)
-- ============================================================================

def checkWeakeningS (d : Derivation) : CheckM Unit := do
  let ps ← expectPremises d 2 "WeakeningS"
  match ps with
  | [pJ, pK] => do
    ensure d.hasIndependenceWitness
      "WeakeningS: explicit independence witness required"
    -- Two distinct judgements
    ensure (getClaim pJ != getClaim pK)
      "WeakeningS: the two premises must have distinct claims"
    -- Conclusion context = Γ, Δ
    let merged := mergeContexts [getCtx pJ, getCtx pK]
    ensure (contextEqSet (getCtx d) merged)
      "WeakeningS: conclusion context must be merge of premise contexts"
    -- Conclusion claim = first premise claim (J, not K)
    ensure (getClaim d == getClaim pJ)
      "WeakeningS: conclusion claim must match first premise"
  | _ => throw "WeakeningS: internal error"

-- ============================================================================
-- Contraction
-- ============================================================================

/-- Does a `Prob` value lie inside a `Constraint`? -/
private def probInConstraint (a : Prob) (c : Constraint) : Bool :=
  c.contains a

def checkContraction (d : Derivation) : CheckM Unit := do
  let ps ← expectPremises d 1 "Contraction"
  match ps with
  | [p] => do
    -- Conclusion: Γ, x : α_a ⊢ J
    -- Premise:  Γ, x : α_{c₁}, ..., x : α_{cₖ} ⊢ J
    -- Claims must match
    ensure (getClaim d == getClaim p)
      "Contraction: conclusion claim must match premise claim"
    -- Find the contracted entry in the conclusion that replaces
    -- multiple entries in the premise.  The contracted entry must
    -- have an exact constraint whose value lies in ∩ cᵢ.
    let premCtx := getCtx p
    let concCtx := getCtx d
    -- Identify entries that are in premCtx but not in concCtx
    -- (these are the contracted entries).  All must share the same
    -- variable name and output, and the contracted exact value
    -- must lie in each of their constraints.
    let removed := premCtx.filter (· ∉ concCtx)
    ensure (removed.length ≥ 2)
      "Contraction: must contract at least two entries"
    -- All removed must share the same name and output
    match removed with
    | e :: rest => do
      ensure (rest.all (fun r => r.name == e.name && r.output == e.output))
        "Contraction: contracted entries must share variable name and output"
      -- Find the replacement entry in concCtx
      let added := concCtx.filter (· ∉ premCtx)
      ensure (added.length == 1)
        "Contraction: exactly one new entry must appear in conclusion"
      match added with
      | [replacement] => do
        ensure (replacement.name == e.name && replacement.output == e.output)
          "Contraction: replacement must have same name and output"
        match replacement.constraint with
        | .exact a => do
          -- Every removed entry must carry genuine information.
          -- A constraint is "trivial" if it is .unknown or .interval [0,1].
          let isTrivial := fun (c : Constraint) => match c with
            | .unknown => true
            | .interval lo hi => decide (lo.val == 0 && hi.val == 1)
            | _ => false
          ensure (removed.any (fun r => !isTrivial r.constraint))
            "Contraction: at least one entry must have an informative (non-trivial) constraint"
          -- a ∈ ∩ cᵢ
          ensure (removed.all (fun r => probInConstraint a r.constraint))
            "Contraction: exact value must lie in intersection of all constraints"
        | _ => throw "Contraction: replacement must have exact constraint"
      | _ => throw "Contraction: unreachable"
    | _ => throw "Contraction: unreachable"
  | _ => throw "Contraction: internal error"

end TPTND
