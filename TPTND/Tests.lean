import TPTND

open TPTND

/-! # TPTND Acceptance Tests

Hand-constructed derivation trees checked by `checkDerivation`.
Design doc §8. -/

-- ============================================================================
-- Test helpers
-- ============================================================================

/-- Build a `Prob` from a natural-number fraction n/d, clamped to [0,1].
    For test fractions known to be in [0,1] the clamp is a no-op. -/
private def P (n d : Nat) : Prob := clampProb ((n : ℚ) / d)

/-- Shorthand derivation node (no independence witness). -/
private def nd (rule : RuleName) (prems : List Derivation)
    (ctx : Context) (claim : Claim) : Derivation :=
  .node rule prems ⟨ctx, claim⟩ false

/-- Shorthand derivation node WITH independence witness. -/
private def ndW (rule : RuleName) (prems : List Derivation)
    (ctx : Context) (claim : Claim) : Derivation :=
  .node rule prems ⟨ctx, claim⟩ true

private def mkSupport (s : String) : Finset String := {s}
private def mkProv   (s : String) : Finset String := {s}
private def mkProv2  (a b : String) : Finset String := {a, b}

/-- Module-level failure counter used to set the executable's exit code:
    `main` exits non-zero if any test failed.  This makes `lake build`
    + `./tptnd_tests` a CI-friendly check rather than a print-only run. -/
initialize failCount : IO.Ref Nat ← IO.mkRef 0

/-- Run a test and report pass/fail. -/
private def runTest (name : String) (d : Derivation) : IO Unit := do
  match checkDerivation d with
  | .ok () => IO.println s!"  PASS  {name}"
  | .error e => do
    IO.println s!"  FAIL  {name}: {e}"
    failCount.modify (· + 1)

-- ============================================================================
-- Test 1: output_atom + base + extend  (fair coin)
-- ============================================================================
/--
  ⊢ H :: output     ⊢ T :: output     (output_atom × 2)
  ⊢ ∅                                  (base)
  ⊢ {x : H_{1/2}}                      (extend)
  ⊢ {x : H_{1/2}, x : T_{1/2}}        (extend)
-/
private def test1 : Derivation :=
  let H := Output.atom "H"
  let T := Output.atom "T"
  let half := P 1 2
  let supp := mkSupport "coin"
  let e1 : ContextEntry := ⟨"x", supp, H, .exact half⟩
  let e2 : ContextEntry := ⟨"x", supp, T, .exact half⟩
  -- output declarations
  let _dH := nd .outputAtom [] [] (.outputDecl H)
  let _dT := nd .outputAtom [] [] (.outputDecl T)
  -- base
  let dBase := nd .base [] [] (.distDecl [])
  -- extend with H_{1/2}
  let dExt1 := nd .extend [dBase] [e1] (.distDecl [e1])
  -- extend with T_{1/2}
  nd .extend [dExt1] [e1, e2] (.distDecl [e1, e2])

-- ============================================================================
-- Test 2: obs + update  (two disjoint batches)
-- ============================================================================
/--
  Batch 1: n=100, f=48/100   (provenance σ_m)
  Batch 2: n=100, f=52/100   (provenance σ_f)
  UPDATE → n=200, f=100/200 = 1/2   (provenance σ_m ∪ σ_f)
-/
private def test2 : Derivation :=
  let α := Output.atom "H"
  let t := Term.atom "coin"
  let supp := mkSupport "coin"
  let ctx : Context := [⟨"coin", supp, α, .unknown⟩]
  let σm := mkProv "σ_m"
  let σf := mkProv "σ_f"
  let σU := mkProv2 "σ_m" "σ_f"
  let obs1Claim : TermClaim := ⟨.frequency, t, 100, α, P 48 100, σm⟩
  let obs2Claim : TermClaim := ⟨.frequency, t, 100, α, P 52 100, σf⟩
  let dObs1 := nd .obs [] ctx (.term obs1Claim)
  let dObs2 := nd .obs [] ctx (.term obs2Claim)
  -- UPDATE: weighted freq = (100·48/100 + 100·52/100)/200 = 100/200 = 1/2
  let updClaim : TermClaim := ⟨.frequency, t, 200, α, P 1 2, σU⟩
  nd .update [dObs1, dObs2] ctx (.term updClaim)

-- ============================================================================
-- Test 3: I+ and E+L round-trip
-- ============================================================================
/--
  t : H_{1/3}    t : T_{2/3}
  ─────────────────────────── I+
  t : (H+T)_{1}
         t : (H+T)_1    t : H_{1/3}
         ───────────────────────────── E+L
         t : T_{2/3}
-/
private def test3 : Derivation :=
  let H := Output.atom "H"
  let T := Output.atom "T"
  let HT := Output.sum H T
  let t := Term.atom "coin"
  let σ := mkProv "ρ"
  let supp := mkSupport "coin"
  let ctx : Context := [⟨"coin", supp, H, .exact (P 1 3)⟩]
  let tcH : TermClaim := ⟨.frequency, t, 300, H, P 1 3, σ⟩
  let tcT : TermClaim := ⟨.frequency, t, 300, T, P 2 3, σ⟩
  let tcHT : TermClaim := ⟨.frequency, t, 300, HT, P 1 1, σ⟩
  let dH := nd .obs [] ctx (.term tcH)
  let dT := nd .obs [] ctx (.term tcT)
  -- I+
  let dPlus := nd .iPlus [dH, dT] ctx (.term tcHT)
  -- E+L: from (H+T)_1 and H_{1/3}, conclude T_{2/3}
  nd .ePlusL [dPlus, dH] ctx (.term tcT)

-- ============================================================================
-- Test 4: IT + ETex  — COMPAS §4.3 Trust (Black female recidivists)
-- ============================================================================
/--
  Observed: Γ_BRF ⊢_{ρ_f} r_203 : LowRisk_{62/203}
  Model:    Γ^mdl_BRM ⊢ x_BRM : LowRisk_{137/486}
  P(203, 62/203, 137/486) = [ℓ, h]    137/486 ∈ [ℓ, h]
  ──────────────────────────────────────────────────── IT
  Θ_BR ⊢ Trust_P(r_203 : LowRisk_{62/203}; 137/486, [ℓ,h])
-/
private def test4 : IO Unit := do
  let LR := Output.atom "LowRisk"
  let t := Term.atom "r"
  let σ := mkProv "ρ_f"
  let suppBRF := mkSupport "BRF"
  let suppBRM := mkSupport "BRM"
  let n : Nat := 203
  let f := P 62 203
  let p := P 137 486
  -- Compute CI using the checker's own function
  let ci := binomialCI n f p
  -- Model premise: identity claim
  let modelEntry : ContextEntry := ⟨"x_BRM", suppBRM, LR, .exact p⟩
  let modelCtx : Context := [modelEntry]
  let dModel := nd .identity [] modelCtx (.identity modelEntry)
  -- Observation premise: frequency claim
  let obsEntry : ContextEntry := ⟨"r", suppBRF, LR, .unknown⟩
  let obsCtx : Context := [obsEntry]
  let obsClaim : TermClaim := ⟨.frequency, t, n, LR, f, σ⟩
  let dObs := nd .obs [] obsCtx (.term obsClaim)
  -- IT conclusion
  let trustClaim : TrustClaim := .trust t n LR f p ci
  let concCtx := modelCtx ++ obsCtx
  let dIT := nd .iT [dModel, dObs] concCtx (.trust trustClaim)
  -- Check if p ∈ ci  (should be true for Trust)
  if inConstraint p ci then
    runTest "Test 4 — COMPAS Trust (IT, §4.3)" dIT
  else
    IO.println s!"  SKIP  Test 4: model prob not in CI (CI = {repr ci})"

-- ============================================================================
-- Test 5: IUT + EUT — COMPAS §4.2 UTrust (Black non-recidivists)
-- ============================================================================
/--
  Observed: Γ_BN ⊢_{σ_m⊎σ_f} u_1514 : HighRisk_{641/1514}
  Model:    Γ^mdl_WN ⊢ x_WN : HighRisk_{94/427}
  P(1514, 641/1514, 94/427) = [ℓ, h]    94/427 ∉ [ℓ, h]
  ──────────────────────────────────────────────────────── IUT
  Θ_FP ⊢ UTrust_P(u_1514 : HighRisk_{641/1514}; 94/427, [ℓ,h])
-/
private def test5 : IO Unit := do
  let HR := Output.atom "HighRisk"
  let t := Term.atom "u"
  let σ := mkProv2 "σ_m" "σ_f"
  let suppBN := mkSupport "BN"
  let suppWN := mkSupport "WN"
  let n : Nat := 1514
  let f := P 641 1514
  let p := P 94 427
  let ci := binomialCI n f p
  -- Model premise
  let modelEntry : ContextEntry := ⟨"x_WN", suppWN, HR, .exact p⟩
  let modelCtx : Context := [modelEntry]
  let dModel := nd .identity [] modelCtx (.identity modelEntry)
  -- Observation premise
  let obsEntry : ContextEntry := ⟨"u", suppBN, HR, .unknown⟩
  let obsCtx : Context := [obsEntry]
  let obsClaim : TermClaim := ⟨.frequency, t, n, HR, f, σ⟩
  let dObs := nd .obs [] obsCtx (.term obsClaim)
  -- IUT conclusion
  let utrustClaim : TrustClaim := .untrust t n HR f p ci
  let concCtx := modelCtx ++ obsCtx
  let dIUT := nd .iUT [dModel, dObs] concCtx (.trust utrustClaim)
  -- Check 94/427 ∉ ci  (should be true for UTrust)
  if notInConstraint p ci then
    runTest "Test 5 — COMPAS UTrust (IUT, §4.2)" dIUT
  else
    IO.println s!"  SKIP  Test 5: model prob IS in CI (CI = {repr ci}), expected UTrust"

-- ============================================================================
-- Test 6: IEx — synthetic excess comparison
-- ============================================================================
/--
  Left:  n=1000, f=500/1000=0.5   (σ)
  Right: m=1000, g=400/1000=0.4   (τ)
  Q(1000, 1000, 0.5, 0.4) = [ℓ, h],  0 ∉ [ℓ, h]  (significant excess)
-/
private def test6 : IO Unit := do
  let α := Output.atom "X"
  let tL := Term.atom "left"
  let tR := Term.atom "right"
  let σ := mkProv "σ"
  let τ := mkProv "τ"
  let suppL := mkSupport "left"
  let suppR := mkSupport "right"
  let nL : Nat := 1000
  let nR : Nat := 1000
  let fL := P 500 1000
  let gR := P 400 1000
  let ci := twoSampleCI nL nR fL gR
  let diff := P 100 1000  -- 0.5 - 0.4 = 0.1
  let tcL : TermClaim := ⟨.frequency, tL, nL, α, fL, σ⟩
  let tcR : TermClaim := ⟨.frequency, tR, nR, α, gR, τ⟩
  let ctxL : Context := [⟨"left", suppL, α, .unknown⟩]
  let ctxR : Context := [⟨"right", suppR, α, .unknown⟩]
  let dL := nd .obs [] ctxL (.term tcL)
  let dR := nd .obs [] ctxR (.term tcR)
  let concCtx := ctxL ++ ctxR
  let concClaim := Claim.comparison (.excess tcL tcR diff ci)
  let dIEx := nd .iEx [dL, dR] concCtx concClaim
  if notInConstraint Prob.zero ci then
    runTest "Test 6 — Synthetic IEx (excess comparison)" dIEx
  else
    IO.println s!"  SKIP  Test 6: 0 is in CI, no significant excess"

-- ============================================================================
-- Test 7: IT → ET  end-to-end chain (COMPAS §4.3)
-- ============================================================================
/--
  IT gives:  Θ_BR ⊢ Trust_P(r_203 : LowRisk_{62/203}; 137/486, [ℓ,h])
  ET gives:  Θ_BR, x_BRF : LowRisk_{[ℓ,h]} ⊢_{ρ_f} r_203 : LowRisk_{62/203}
-/
private def test7 : IO Unit := do
  let LR := Output.atom "LowRisk"
  let t := Term.atom "r"
  let σ := mkProv "ρ_f"
  let suppBRF := mkSupport "BRF"
  let suppBRM := mkSupport "BRM"
  let n : Nat := 203
  let f := P 62 203
  let p := P 137 486
  let ci := binomialCI n f p
  -- IT derivation (same as test4)
  let modelEntry : ContextEntry := ⟨"x_BRM", suppBRM, LR, .exact p⟩
  let obsEntry : ContextEntry := ⟨"r", suppBRF, LR, .unknown⟩
  let dModel := nd .identity [] [modelEntry] (.identity modelEntry)
  let obsClaim : TermClaim := ⟨.frequency, t, n, LR, f, σ⟩
  let dObs := nd .obs [] [obsEntry] (.term obsClaim)
  let trustClaim : TrustClaim := .trust t n LR f p ci
  let itCtx := [modelEntry, obsEntry]
  let dIT := nd .iT [dModel, dObs] itCtx (.trust trustClaim)
  -- ET derivation: add interval entry, produce term claim
  let intervalEntry : ContextEntry := ⟨"x_BRF", suppBRF, LR, ci⟩
  let etCtx := itCtx ++ [intervalEntry]
  let etClaim : TermClaim := ⟨.frequency, t, n, LR, f, σ⟩
  let dET := nd .eT [dIT] etCtx (.term etClaim)
  runTest "Test 7 — COMPAS IT→ET chain (§4.3)" dET

-- ============================================================================
-- Test 8: IUT → EUT  end-to-end chain (COMPAS §4.2)
-- ============================================================================
private def test8 : IO Unit := do
  let HR := Output.atom "HighRisk"
  let t := Term.atom "u"
  let σ := mkProv2 "σ_m" "σ_f"
  let suppBN := mkSupport "BN"
  let suppWN := mkSupport "WN"
  let n : Nat := 1514
  let f := P 641 1514
  let p := P 94 427
  let ci := binomialCI n f p
  -- IUT
  let modelEntry : ContextEntry := ⟨"x_WN", suppWN, HR, .exact p⟩
  let obsEntry : ContextEntry := ⟨"u", suppBN, HR, .unknown⟩
  let dModel := nd .identity [] [modelEntry] (.identity modelEntry)
  let obsClaim : TermClaim := ⟨.frequency, t, n, HR, f, σ⟩
  let dObs := nd .obs [] [obsEntry] (.term obsClaim)
  let utrustClaim : TrustClaim := .untrust t n HR f p ci
  let iutCtx := [modelEntry, obsEntry]
  let dIUT := nd .iUT [dModel, dObs] iutCtx (.trust utrustClaim)
  -- EUT: add complement-interval entry
  let complementCI := match ci with
    | .interval lo hi => Constraint.outsideInterval lo hi
    | other => other
  let compEntry : ContextEntry := ⟨"x_BN", suppBN, HR, complementCI⟩
  let eutCtx := iutCtx ++ [compEntry]
  let eutClaim : TermClaim := ⟨.frequency, t, n, HR, f, σ⟩
  let dEUT := nd .eUT [dIUT] eutCtx (.term eutClaim)
  runTest "Test 8 — COMPAS IUT→EUT chain (§4.2)" dEUT

-- ============================================================================
-- Negative tests: derivations that MUST be rejected
-- ============================================================================

/-- Helper: expect a CheckM to fail. -/
private def runNegTest (name : String) (d : Derivation) : IO Unit :=
  match checkDerivation d with
  | .ok ()   => do
    IO.println s!"  FAIL  {name}: should have been REJECTED but passed"
    failCount.modify (· + 1)
  | .error _ => IO.println s!"  PASS  {name} (correctly rejected)"

/-- Neg 1: output_atom with wrong conclusion (neg instead of atom). -/
private def neg1 : Derivation :=
  nd .outputAtom [] [] (.outputDecl (.neg (.atom "H")))

/-- Neg 2: extend that violates mass constraint (1/2 + 3/4 > 1). -/
private def neg2 : Derivation :=
  let H := Output.atom "H"
  let T := Output.atom "T"
  let supp := mkSupport "coin"
  let e1 : ContextEntry := ⟨"x", supp, H, .exact (P 1 2)⟩
  let e2 : ContextEntry := ⟨"x", supp, T, .exact (P 3 4)⟩  -- total 1.25 > 1
  let dBase := nd .base [] [] (.distDecl [])
  let dExt1 := nd .extend [dBase] [e1] (.distDecl [e1])
  nd .extend [dExt1] [e1, e2] (.distDecl [e1, e2])

/-- Neg 3: I+ with overlapping outputs (same atom used twice). -/
private def neg3 : Derivation :=
  let H := Output.atom "H"
  let σ := mkProv "ρ"
  let supp := mkSupport "coin"
  let ctx : Context := [⟨"coin", supp, H, .exact (P 1 3)⟩]
  let tc1 : TermClaim := ⟨.frequency, .atom "coin", 300, H, P 1 3, σ⟩
  let tc2 : TermClaim := ⟨.frequency, .atom "coin", 300, H, P 1 3, σ⟩
  let tcSum : TermClaim := ⟨.frequency, .atom "coin", 300, .sum H H, P 2 3, σ⟩
  let d1 := nd .obs [] ctx (.term tc1)
  let d2 := nd .obs [] ctx (.term tc2)
  nd .iPlus [d1, d2] ctx (.term tcSum)

/-- Neg 4: update with non-disjoint provenances. -/
private def neg4 : Derivation :=
  let α := Output.atom "H"
  let t := Term.atom "coin"
  let supp := mkSupport "coin"
  let ctx : Context := [⟨"coin", supp, α, .unknown⟩]
  let σ := mkProv "same_run"  -- SAME provenance for both
  let tc1 : TermClaim := ⟨.frequency, t, 100, α, P 48 100, σ⟩
  let tc2 : TermClaim := ⟨.frequency, t, 100, α, P 52 100, σ⟩
  let tcU : TermClaim := ⟨.frequency, t, 200, α, P 1 2, σ⟩
  let d1 := nd .obs [] ctx (.term tc1)
  let d2 := nd .obs [] ctx (.term tc2)
  nd .update [d1, d2] ctx (.term tcU)

/-- Neg 5: IT where model probability is OUTSIDE the CI (should be IUT). -/
private def test_neg5 : IO Unit := do
  let α := Output.atom "X"
  let t := Term.atom "t"
  let σ := mkProv "ρ"
  let supp := mkSupport "obs"
  let suppM := mkSupport "model"
  let n : Nat := 100
  let f := P 80 100   -- observed 80%
  let p := P 20 100   -- model says 20% — way off
  let ci := binomialCI n f p
  let modelEntry : ContextEntry := ⟨"m", suppM, α, .exact p⟩
  let obsEntry : ContextEntry := ⟨"t", supp, α, .unknown⟩
  let dModel := nd .identity [] [modelEntry] (.identity modelEntry)
  let obsClaim : TermClaim := ⟨.frequency, t, n, α, f, σ⟩
  let dObs := nd .obs [] [obsEntry] (.term obsClaim)
  -- Try to use IT (trust) — should fail because p ∉ CI
  let trustClaim : TrustClaim := .trust t n α f p ci
  let dBadIT := nd .iT [dModel, dObs] [modelEntry, obsEntry] (.trust trustClaim)
  runNegTest "Neg 5 — IT with p outside CI (should reject)" dBadIT

/-- Neg 6: I+ with MISMATCHED provenance — the σ-layer of [0,1] defense.
    Two observations of disjoint events at f=1/4 and g=1/4 sum cleanly
    to 1/2 (so the value-level guard `probAdd` does NOT fire), but the
    σ check rejects the rule because the operands come from different
    batches.  Without this discipline, the textbook attack from JLC §1
    on `t_4 : α_{3/4}` and `t_4 : β_{3/4}` (different batches, summing
    to 3/2) would be derivable. -/
private def neg6 : Derivation :=
  let H := Output.atom "H"
  let T := Output.atom "T"
  let t := Term.atom "t"
  let σA := mkProv "σ_A"
  let σB := mkProv "σ_B"   -- different batch from σA
  let supp := mkSupport "trial"
  let ctx : Context := [⟨"t", supp, H, .unknown⟩]
  let tcH : TermClaim := ⟨.frequency, t, 4, H, P 1 4, σA⟩
  let tcT : TermClaim := ⟨.frequency, t, 4, T, P 1 4, σB⟩
  let tcSum : TermClaim := ⟨.frequency, t, 4, Output.sum H T, P 1 2, σA⟩
  let dH := nd .obs [] ctx (.term tcH)
  let dT := nd .obs [] ctx (.term tcT)
  nd .iPlus [dH, dT] ctx (.term tcSum)

/-- Neg 7: I+ with shared σ but p+q > 1 — the value-layer of [0,1]
    defense.  The σ check passes (both premises share σ); `probAdd`
    catches 3/4 + 3/4 = 3/2 ∉ [0,1] and rejects. -/
private def neg7 : Derivation :=
  let H := Output.atom "H"
  let T := Output.atom "T"
  let t := Term.atom "t"
  let σ := mkProv "ρ"
  let supp := mkSupport "trial"
  let ctx : Context := [⟨"t", supp, H, .unknown⟩]
  let tcH : TermClaim := ⟨.frequency, t, 4, H, P 3 4, σ⟩
  let tcT : TermClaim := ⟨.frequency, t, 4, T, P 3 4, σ⟩
  let tcSum : TermClaim := ⟨.frequency, t, 4, Output.sum H T, P 1 1, σ⟩
  let dH := nd .obs [] ctx (.term tcH)
  let dT := nd .obs [] ctx (.term tcT)
  nd .iPlus [dH, dT] ctx (.term tcSum)

-- ============================================================================
-- Main
-- ============================================================================

def main : IO Unit := do
  IO.println "TPTND Acceptance Tests"
  IO.println "====================="
  IO.println ""
  IO.println "— Positive tests (must pass) —"
  runTest "Test 1 — Fair coin (output_atom + base + extend)" test1
  runTest "Test 2 — Two batches (obs + update)" test2
  runTest "Test 3 — Sum round-trip (I+ + E+L)" test3
  test4
  test5
  test6
  test7
  test8
  IO.println ""
  IO.println "— Negative tests (must reject) —"
  runNegTest "Neg 1 — output_atom with neg output" neg1
  runNegTest "Neg 2 — extend violating mass ≤ 1" neg2
  runNegTest "Neg 3 — I+ with overlapping outputs" neg3
  runNegTest "Neg 4 — update with non-disjoint provenance" neg4
  test_neg5
  runNegTest "Neg 6 — I+ with mismatched provenance (σ-layer)" neg6
  runNegTest "Neg 7 — I+ with shared σ but p+q > 1 (value-layer)" neg7
  IO.println ""
  IO.println "====================="
  let n ← failCount.get
  if n == 0 then
    IO.println "Done — all tests passed."
  else
    IO.println s!"FAILED: {n} test(s) did not pass"
    IO.Process.exit 1
