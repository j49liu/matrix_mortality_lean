import LeanWang.UniversalTM0.Semantic
import Mathlib.Computability.Halting

/-!
# Fixed universal Turing-machine source

This file records the computability-theoretic endpoint imported from
`edemaine/lean-wang`.  The upstream theorem identifies the domain of one
fixed Mathlib `TM0` machine on the computable input encoding of a partial-
recursive code with the domain of that code at input zero.
-/

namespace Mortality.SourceMachine.LeanWangTM0

open LeanWang

/-- Halting of the fixed upstream `TM0` machine on its encoded input is not a
computable predicate. -/
theorem fixedTM0Halting_not_computable :
    ¬ComputablePred fun code : Nat.Partrec.Code =>
      (Turing.TM0.eval UniversalTM0Semantic.tm0
        (UniversalTM0Semantic.input code)).Dom := by
  intro computableHalting
  exact ComputablePred.halting_problem 0
    (computableHalting.of_eq UniversalTM0Semantic.tm0_eval_dom_iff)

end Mortality.SourceMachine.LeanWangTM0
