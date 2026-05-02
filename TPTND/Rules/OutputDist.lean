import TPTND.CheckM
import TPTND.WellFormedness
import TPTND.Arithmetic

namespace TPTND

/-! # Output and Distribution Rules (Table 1)

`output_atom`, `output_neg`, `output_sum`, `output_prod`, `output_arr`,
`base`, `extend`, `unknown`.  Design doc §7.1. -/

-- ============================================================================
-- Output declaration rules
-- ============================================================================

def checkOutputAtom (d : Derivation) : CheckM Unit := do
  let _ ← expectPremises d 0 "output_atom"
  match getClaim d with
  | .outputDecl (.atom _) => pure ()
  | _ => throw "output_atom: conclusion must be outputDecl(atom _)"

def checkOutputNeg (d : Derivation) : CheckM Unit := do
  let ps ← expectPremises d 1 "output_neg"
  match ps with
  | [p] =>
    match getClaim p, getClaim d with
    | .outputDecl α, .outputDecl (.neg β) =>
      ensure (α == β) "output_neg: negated output must match premise"
    | _, _ => throw "output_neg: expected outputDecl in premise and conclusion"
  | _ => throw "output_neg: internal error"

private def checkOutputBinary (d : Derivation) (rule : String)
    (mk : Output → Output → Output) : CheckM Unit := do
  let ps ← expectPremises d 2 rule
  match ps with
  | [p1, p2] =>
    match getClaim p1, getClaim p2, getClaim d with
    | .outputDecl α, .outputDecl β, .outputDecl γ =>
      ensure (γ == mk α β) s!"{rule}: conclusion output mismatch"
    | _, _, _ => throw s!"{rule}: all three claims must be outputDecl"
  | _ => throw s!"{rule}: internal error"

def checkOutputSum  (d : Derivation) : CheckM Unit :=
  checkOutputBinary d "output_sum"  Output.sum
def checkOutputProd (d : Derivation) : CheckM Unit :=
  checkOutputBinary d "output_prod" Output.prod
def checkOutputArr  (d : Derivation) : CheckM Unit :=
  checkOutputBinary d "output_arr"  Output.arr

-- ============================================================================
-- Distribution rules
-- ============================================================================

def checkBase (d : Derivation) : CheckM Unit := do
  let _ ← expectPremises d 0 "base"
  match getClaim d with
  | .distDecl ctx => ensure (ctx.isEmpty) "base: context must be empty"
  | _ => throw "base: conclusion must be distDecl"

def checkExtend (d : Derivation) : CheckM Unit := do
  let ps ← expectPremises d 1 "extend"
  match ps with
  | [p] =>
    match getClaim p, getClaim d with
    | .distDecl Γ, .distDecl Γ' => do
      ensure (Γ'.length == Γ.length + 1)
        "extend: conclusion context must have exactly one more entry"
      ensure (Γ'.take Γ.length == Γ)
        "extend: conclusion must be a proper extension of premise"
      match Γ'.getLast? with
      | some e =>
        match e.constraint with
        | .exact a => do
          let existingMass := Γ.foldl (fun acc entry =>
            if entry.name == e.name then
              match entry.constraint with
              | .exact p => acc + p.val
              | _        => acc
            else acc) (0 : ℚ)
          ensure (decide (existingMass + a.val ≤ 1))
            "extend: total exact mass for variable exceeds 1"
        | _ => throw "extend: new entry must carry an exact constraint"
      | none => throw "extend: empty conclusion context (impossible)"
    | _, _ => throw "extend: premise and conclusion must be distDecl"
  | _ => throw "extend: internal error"

def checkUnknown (d : Derivation) : CheckM Unit := do
  let ps := d.premises
  match getClaim d with
  | .distDecl Γ => do
    ensure (ps.length == Γ.length)
      "unknown: #premises must equal #entries in conclusion context"
    let pairs := ps.zip Γ
    for ⟨pi, ei⟩ in pairs do
      match getClaim pi with
      | .outputDecl α => do
        ensure (ei.output == α)
          "unknown: premise output ≠ entry output"
        ensure (ei.constraint == .unknown)
          "unknown: entry must have unknown constraint"
      | _ => throw "unknown: every premise must be outputDecl"
  | _ => throw "unknown: conclusion must be distDecl"

end TPTND
