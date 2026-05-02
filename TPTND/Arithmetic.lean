import TPTND.Syntax
import Mathlib.Tactic.Linarith

namespace TPTND

/-! # TPTND Arithmetic Helpers

Rational arithmetic in [0,1], confidence intervals, and constraint membership.
Follows Section 4 of the TPTND Lean Design Document.

All arithmetic uses exact rational (`ℚ`) computation.  The CI functions use a
rational Newton's-method approximation for square roots (15 iterations). -/

-- ============================================================================
-- Prob arithmetic staying in [0,1]
-- ============================================================================

/-- a + b, fails if the sum exceeds 1. -/
def probAdd (a b : Prob) : Option Prob :=
  if h : a.val + b.val ≤ 1 then
    some ⟨a.val + b.val, add_nonneg a.hlo b.hlo, h⟩
  else none

/-- a − b, fails if the difference is negative. -/
def probSub (a b : Prob) : Option Prob :=
  if h : 0 ≤ a.val - b.val then
    some ⟨a.val - b.val, h, by linarith [a.hhi, b.hlo]⟩
  else none

/-- a · b — always in [0,1]. -/
def probMul (a b : Prob) : Prob :=
  ⟨a.val * b.val,
   mul_nonneg a.hlo b.hlo,
   by nlinarith [a.hhi, b.hhi, a.hlo, b.hlo]⟩

/-- a / b, fails if b = 0 or the quotient exceeds 1. -/
def probDiv (a b : Prob) : Option Prob :=
  if b.val = 0 then none
  else
    let r := a.val / b.val
    if h₁ : 0 ≤ r then
      if h₂ : r ≤ 1 then
        some ⟨r, h₁, h₂⟩
      else none
    else none

-- ============================================================================
-- Weighted frequency combination  (UPDATE rule formula)
-- ============================================================================

/-- (n · f + m · g) / (n + m).  Fails when n + m = 0. -/
def weightedFreq (n : Nat) (f : Prob) (m : Nat) (g : Prob) : Option Prob :=
  if n + m = 0 then none
  else
    let q := ((n : ℚ) * f.val + (m : ℚ) * g.val) / ((n + m : ℕ) : ℚ)
    if h₁ : 0 ≤ q then
      if h₂ : q ≤ 1 then
        some ⟨q, h₁, h₂⟩
      else none
    else none

-- ============================================================================
-- Rational square-root approximation (Newton's method, 15 iterations)
-- ============================================================================

private def ratSqrtAux (x : ℚ) : Nat → ℚ → ℚ
  | 0, y => y
  | n + 1, y =>
    if y = 0 then 0
    else ratSqrtAux x n ((y + x / y) / 2)

/-- Round a non-negative rational to the nearest k/precision.
    Keeps denominators bounded after Newton iteration.  -/
private def roundRat (q : ℚ) (precision : Nat) : ℚ :=
  if precision = 0 then q
  else
    -- round(q * precision) / precision
    -- For non-negative q: round(x) = floor(x + 1/2) = (2·num·prec + den) / (2·den)
    let num := q.num * (precision : ℤ)
    let den := (q.den : ℤ)
    let rounded := (2 * num + den) / (2 * den)
    (rounded : ℚ) / (precision : ℚ)

/-- Rational approximation of √x.  Returns 0 for x ≤ 0.
    Result rounded to 6 decimal places to keep denominators bounded. -/
def ratSqrt (x : ℚ) : ℚ :=
  if x ≤ 0 then 0
  else roundRat (ratSqrtAux x 15 (max x 1)) 1000000

-- ============================================================================
-- Confidence intervals
-- ============================================================================

/-- z-value for a 95 % two-sided CI: 1.96 ≈ 49/25. -/
private def z95 : ℚ := 49 / 25

/-- Clamp a rational to [0,1] and wrap as `Prob`. -/
def clampProb (q : ℚ) : Prob :=
  let c := max 0 (min 1 q)
  ⟨c, le_max_left 0 _, max_le (by norm_num : (0 : ℚ) ≤ 1) (min_le_left 1 q)⟩

/-- Binomial CI  𝒫(n, f, p) = [ℓ, h].
    Score-test (Wald) interval centred at f with variance under p:
      f ± z₉₅ · √(p(1−p)/n)
    Endpoints clamped to [0,1].  Returns `unknown` when n = 0. -/
def binomialCI (n : Nat) (f p : Prob) : Constraint :=
  if n = 0 then .unknown
  else
    let variance := p.val * (1 - p.val) / (n : ℚ)
    let se := ratSqrt variance
    let lo := f.val - z95 * se
    let hi := f.val + z95 * se
    .interval (clampProb lo) (clampProb hi)

/-- Two-sample proportion CI  𝒬(n, m, f, g) = [ℓ, h].
    Score-test (pooled) interval for the difference f − g:
      (f − g) ± z₉₅ · √(p̂(1−p̂)(1/n + 1/m))
    where p̂ = (nf + mg)/(n + m) is the pooled rate under H₀: p₁ = p₂.
    This is consistent with `binomialCI` (both use null-hypothesis variance).
    Endpoints clamped to [0,1].  Returns `unknown` when n = 0 or m = 0. -/
def twoSampleCI (n m : Nat) (f g : Prob) : Constraint :=
  if n = 0 || m = 0 then .unknown
  else
    let nq := (n : ℚ)
    let mq := (m : ℚ)
    let pHat := (nq * f.val + mq * g.val) / (nq + mq)
    let variance := pHat * (1 - pHat) * (1 / nq + 1 / mq)
    let se := ratSqrt variance
    let diff := f.val - g.val
    let lo := diff - z95 * se
    let hi := diff + z95 * se
    .interval (clampProb lo) (clampProb hi)

-- ============================================================================
-- Constraint membership
-- ============================================================================

/-- Does `p` lie inside `c`? -/
def inConstraint (p : Prob) (c : Constraint) : Bool :=
  c.contains p

/-- Does `p` lie outside `c`? -/
def notInConstraint (p : Prob) (c : Constraint) : Bool :=
  !c.contains p

end TPTND
