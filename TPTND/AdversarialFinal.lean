import TPTND
open TPTND

private def P (n d : Nat) : Prob := clampProb ((n : ℚ) / d)
private def nd (rule : RuleName) (prems : List Derivation)
    (ctx : Context) (claim : Claim) : Derivation :=
  .node rule prems ⟨ctx, claim⟩ false
private def ndW (rule : RuleName) (prems : List Derivation)
    (ctx : Context) (claim : Claim) : Derivation :=
  .node rule prems ⟨ctx, claim⟩ true
private def mkS (s : String) : Finset String := {s}
private def run (name : String) (d : Derivation) (sf : Bool := true) : IO Unit := do
  match checkDerivation d with
  | .ok () => if sf then IO.println s!"  ⚠ EXPLOIT  {name}" else IO.println s!"  ✓ OK       {name}"
  | .error e => if sf then IO.println s!"  ✓ BLOCKED  {name}: {e}" else IO.println s!"  ✗ BUG      {name}: {e}"

def main : IO Unit := do
  IO.println "=== Final edge-case sweep ==="

  -- A: Contraction with outsideInterval [0.3, 0.7] — anything < 0.3 or > 0.7 is valid
  IO.println ""
  let α := Output.atom "X"
  let oi : ContextEntry := ⟨"x", mkS "A", α, .outsideInterval (P 3 10) (P 7 10)⟩
  let uk : ContextEntry := ⟨"x", mkS "B", α, .unknown⟩
  let dPrem := nd .identityStar [] [oi, uk] (.identity oi)
  -- Contract to exact 0.2 — should work (0.2 ∈ ¬[0.3,0.7] AND 0.2 ∈ [0,1])
  let e02 : ContextEntry := ⟨"x", mkS "A", α, .exact (P 2 10)⟩
  let dC := nd .contraction [dPrem] [e02] (.identity oi)
  run "Contraction: outsideInterval + unknown → exact(0.2)" dC (sf := false)
  -- Contract to exact 0.5 — should fail (0.5 ∈ [0.3,0.7], so 0.5 ∉ ¬[0.3,0.7])
  let e05 : ContextEntry := ⟨"x", mkS "A", α, .exact (P 5 10)⟩
  let dC2 := nd .contraction [dPrem] [e05] (.identity oi)
  run "Contraction: outsideInterval + unknown → exact(0.5)" dC2

  -- B: Can we derive f=0 from obs? (n=10, 0 hits → f=0/10=0)
  IO.println ""
  let obsEntry : ContextEntry := ⟨"r", mkS "obs", α, .unknown⟩
  let dObs0 := nd .obs [] [obsEntry] (.term ⟨.frequency, Term.atom "r", 10, α, P 0 10, mkS "σ"⟩)
  run "obs: n=10, f=0/10=0" dObs0 (sf := false)

  -- C: IT with p=0 (degenerate model)
  IO.println ""
  let pZero := P 0 1
  let ci0 := binomialCI 10 (P 0 10) pZero
  let me0 : ContextEntry := ⟨"m", mkS "mdl", α, .exact pZero⟩
  let dM0 := nd .identity [] [me0] (.identity me0)
  let dIT0 := nd .iT [dM0, dObs0] [me0, obsEntry] (.trust (.trust (Term.atom "r") 10 α (P 0 10) pZero ci0))
  run "IT: model=0, obs f=0 (degenerate Trust)" dIT0 (sf := false)

  -- D: Contraction with [0.01,0.99] + [0.01,0.99] → any value in [0.01,0.99]
  IO.println ""
  let narrow1 : ContextEntry := ⟨"x", mkS "A", α, .interval (P 1 100) (P 99 100)⟩
  let narrow2 : ContextEntry := ⟨"x", mkS "B", α, .interval (P 1 100) (P 99 100)⟩
  let dNPrem := nd .identityStar [] [narrow1, narrow2] (.identity narrow1)
  let eForge : ContextEntry := ⟨"x", mkS "A", α, .exact (P 42 100)⟩
  let dNContract := nd .contraction [dNPrem] [eForge] (.identity narrow1)
  run "Contraction: [0.01,0.99] + [0.01,0.99] → exact(0.42)" dNContract (sf := false)
  IO.println "    ↳ This is semantically correct: 0.42 ∈ [0.01, 0.99]"

  -- E: UPDATE with n1=0 or n2=0
  IO.println ""
  -- weightedFreq 0 ... fails. But can we get here?
  -- obs requires n > 0, so UPDATE premises always have n > 0.
  -- Try directly:
  let dObs1 := nd .obs [] [obsEntry] (.term ⟨.frequency, Term.atom "r", 100, α, P 50 100, mkS "σ1"⟩)
  let dObs2 := nd .obs [] [obsEntry] (.term ⟨.frequency, Term.atom "r", 100, α, P 30 100, mkS "σ2"⟩)
  -- UPDATE: (100*0.5 + 100*0.3)/200 = 80/200 = 2/5
  match weightedFreq 100 (P 50 100) 100 (P 30 100) with
  | some wf =>
    let dUp := nd .update [dObs1, dObs2] [obsEntry] (.term ⟨.frequency, Term.atom "r", 200, α, wf, mkS "σ1" ∪ mkS "σ2"⟩)
    run "UPDATE: (100×0.5 + 100×0.3)/200 = 0.4" dUp (sf := false)
  | none => IO.println "  weightedFreq failed??"

  -- F: Context laundering through ET (Audit bug #4 in §3.4 of the paper).
  --    Build a valid IT premise, then attempt ET whose conclusion context
  --    drops the premise's model and observation entries and inserts an
  --    unrelated assumption.  Pre-fix this was silently accepted; the
  --    contextExtendsBy check now rejects it.
  IO.println ""
  let n_F : Nat := 100
  let f_F := P 50 100
  let p_F := P 5 10
  let ci_F := binomialCI n_F f_F p_F
  let modelE : ContextEntry := ⟨"m_F", mkS "model", α, .exact p_F⟩
  let obsE   : ContextEntry := ⟨"u_F", mkS "F", α, .unknown⟩
  let extraE : ContextEntry :=
    ⟨"secret", mkS "elsewhere", α, .exact (P 1 10)⟩
  let dM_F   := nd .identity [] [modelE] (.identity modelE)
  let dObs_F := nd .obs [] [obsE]
    (.term ⟨.frequency, Term.atom "u_F", n_F, α, f_F, mkS "ρ_F"⟩)
  let dIT_F  := nd .iT [dM_F, dObs_F] [modelE, obsE]
    (.trust (.trust (Term.atom "u_F") n_F α f_F p_F ci_F))
  let etConc : TermClaim :=
    ⟨.frequency, Term.atom "u_F", n_F, α, f_F, mkS "ρ_F"⟩
  let intervalE : ContextEntry := ⟨"x_u", mkS "F", α, ci_F⟩
  let dETLaunder := nd .eT [dIT_F] [intervalE, extraE] (.term etConc)
  run "ET context laundering: drop premise ctx + attach unrelated entry" dETLaunder

  IO.println ""
  IO.println "=== Edge-case sweep complete ==="
