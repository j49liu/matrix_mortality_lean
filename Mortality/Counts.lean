import Mortality.OneCounter.FixedEdges

/-!
# Generator and phase counts

This file makes the numerical calculation in Appendix A executable.
The source instruction counts are obtained from the concrete quotient
table rather than repeated as independent assumptions.
-/

namespace Mortality

set_option maxRecDepth 100000

/-- Physical-letter and private-phase costs for one instruction module. -/
structure ModuleCost where
  letters : Nat
  privatePhases : Nat
  deriving DecidableEq, Repr

def oddHalvingCost : ModuleCost :=
  { letters := 10, privatePhases := 4 }

def ternaryDivisionCost : ModuleCost :=
  { letters := 14, privatePhases := 6 }

def contractionTwoCost : ModuleCost :=
  { letters := 30, privatePhases := 14 }

def contractionThreeCost : ModuleCost :=
  { letters := 32, privatePhases := 15 }

def modTwoTestCost : ModuleCost :=
  { letters := 5, privatePhases := 2 }

def modThreeTestCost : ModuleCost :=
  { letters := 7, privatePhases := 3 }

def cleanupCost : ModuleCost :=
  { letters := 4, privatePhases := 1 }

/-- The number of listed nonsingular letters before duplicate removal. -/
def listedNonsingularGenerators : Nat :=
  let counts := OneCounter.fixedInstructionCounts
  oddHalvingCost.letters * counts.divideTwo +
    ternaryDivisionCost.letters * counts.divideThree +
    contractionTwoCost.letters * counts.contractTwo +
    contractionThreeCost.letters * counts.contractThree +
    modTwoTestCost.letters * counts.testTwo +
    modThreeTestCost.letters * counts.testThree +
    cleanupCost.letters * counts.increment

/-- Program boundaries and all private phases before padding. -/
def genuinePhaseBound : Nat :=
  let counts := OneCounter.fixedInstructionCounts
  SourceMachine.quotientStates.length +
    oddHalvingCost.privatePhases * counts.divideTwo +
    ternaryDivisionCost.privatePhases * counts.divideThree +
    contractionTwoCost.privatePhases * counts.contractTwo +
    contractionThreeCost.privatePhases * counts.contractThree +
    modTwoTestCost.privatePhases * counts.testTwo +
    modThreeTestCost.privatePhases * counts.testThree +
    cleanupCost.privatePhases * counts.increment

/-- The number of unused phases reserved for exact-cardinality padding. -/
def paddingPhaseCount : Nat := listedNonsingularGenerators

/-- The strict lower bound needed for the coding prime. -/
def codingPrimeLowerBound : Nat :=
  6 * (genuinePhaseBound + paddingPhaseCount)

/-- The concrete coding prime, one above the required bound. Its primality
is proved in `Mortality.Prime`. -/
def codingPrime : Nat := 51859

theorem listedNonsingularGenerators_eq :
    listedNonsingularGenerators = 5798 := by
  decide

theorem genuinePhaseBound_eq : genuinePhaseBound = 2845 := by
  decide

theorem codingPrimeLowerBound_eq : codingPrimeLowerBound = 51858 := by
  decide

theorem codingPrime_gt_bound : codingPrimeLowerBound < codingPrime := by
  decide

theorem totalGeneratorCount_eq : listedNonsingularGenerators + 1 = 5799 := by
  decide

end Mortality
