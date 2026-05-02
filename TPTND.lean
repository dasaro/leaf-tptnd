import TPTND.Syntax
import TPTND.Judgement
import TPTND.Arithmetic
import TPTND.WellFormedness
import TPTND.CheckM
import TPTND.Rules.OutputDist
import TPTND.Rules.AtomicLeaves
import TPTND.Rules.SamplingSum
import TPTND.Rules.ProductArrow
import TPTND.Rules.Bayesian
import TPTND.Rules.Trust
import TPTND.Rules.Comparison
import TPTND.Rules.Structural

namespace TPTND

/-! # Top-level derivation checker

`checkDerivation` dispatches on the rule name to the appropriate family
checker and then recurses into each premise (design doc §6). -/

/-- Dispatch a single node to its rule checker (no recursion).
    Match is exhaustive over `RuleName`; Lean checks coverage. -/
private def checkNode (d : Derivation) : CheckM Unit :=
  match d.ruleName with
  -- Output & distribution (Table 1)
  | .outputAtom => checkOutputAtom d
  | .outputNeg  => checkOutputNeg d
  | .outputSum  => checkOutputSum d
  | .outputProd => checkOutputProd d
  | .outputArr  => checkOutputArr d
  | .base       => checkBase d
  | .extend     => checkExtend d
  | .unknown    => checkUnknown d
  -- Atomic leaves (Table 2)
  | .identity     => checkIdentity d
  | .identityStar => checkIdentityStar d
  | .obs          => checkObs d
  | .experiment   => checkExperiment d
  | .expectation  => checkExpectation d
  -- Sampling & sum (Table 3)
  | .sampling => checkSampling d
  | .update   => checkUpdate d
  | .iPlus    => checkIPlus d
  | .ePlusL   => checkEPlusL d
  | .ePlusR   => checkEPlusR d
  -- Product & arrow (Table 4)
  | .iProd  => checkIProd d
  | .eProdL => checkEProdL d
  | .eProdR => checkEProdR d
  | .iArr   => checkIArr d
  | .eArr   => checkEArr d
  -- Bayesian (Table 5)
  | .iPrior     => checkIPrior d
  | .ePosterior => checkEPosterior d
  -- Trust (Tables 5–6)
  | .iT   => checkIT d
  | .iUT  => checkIUT d
  | .iT2  => checkIT2 d
  | .iUT2 => checkIUT2 d
  | .eT   => checkET d
  | .eUT  => checkEUT d
  | .eTex => checkETex d
  -- Comparison (Table 6)
  | .iEx  => checkIEx d
  | .iNEx => checkINEx d
  | .eEx  => checkEEx d
  | .eNEx => checkENEx d
  -- Structural (Table 7)
  | .weakeningD  => checkWeakeningD d
  | .weakeningS  => checkWeakeningS d
  | .contraction => checkContraction d

/-- Check a full derivation tree: verify the current node's rule and then
    recurse into every premise.  Uses `partial` because `Derivation` is an
    inductive family and the recursion follows the tree structure. -/
partial def checkDerivation (d : Derivation) : CheckM Unit := do
  -- 1. Check this node's rule-specific side conditions
  checkNode d
  -- 2. Recurse into each premise
  for p in d.premises do
    checkDerivation p

end TPTND
