import Mortality.FixedParameters
import Mortality.Compiler.CongruenceModule
import Mortality.Compiler.OddHalvingModule
import Mortality.Compiler.TernaryDivisionModule
import Mortality.Compiler.ContractionModules

/-!
# Concrete phase allocation for the fixed compiler

The paper counts private phases and physical letters by instruction kind.
This file makes the allocation itself executable.  Program boundaries occupy
the first 270 phases, in the order of `SourceMachine.quotientStates`.  The
private phases for edge occurrence `i` form the next contiguous block, after
the blocks for occurrences `0, ..., i - 1`.

The final definitions instantiate the displayed physical alphabet for every
one of the 378 edge occurrences.  Thus the equalities `2845` and `5798` below
check the concrete assembly, rather than only a separate sum of occurrence
counts.
-/

namespace Mortality.Compiler.FixedAllocation

open Mortality
open Mortality.OneCounter
open Mortality.Compiler

set_option maxRecDepth 1000000
set_option maxHeartbeats 8000000

/-- The dense phase number assigned to a quotient-machine boundary state. -/
def boundaryPhase (state : Nat) : Nat :=
  SourceMachine.quotientStates.idxOf state

/-- The private-phase cost of one instruction occurrence. -/
def instructionPrivateCost : Instruction → Nat
  | .increment => cleanupCost.privatePhases
  | .congruenceTest 2 [0] => modTwoTestCost.privatePhases
  | .congruenceTest 3 [0, 1] => modThreeTestCost.privatePhases
  | .divideTwoOdd => oddHalvingCost.privatePhases
  | .divideThreeTwo => ternaryDivisionCost.privatePhases
  | .contractTwo => contractionTwoCost.privatePhases
  | .contractThree => contractionThreeCost.privatePhases
  | .congruenceTest _ _ => 0

/-- The physical-letter cost of one instruction occurrence. -/
def instructionLetterCost : Instruction → Nat
  | .increment => cleanupCost.letters
  | .congruenceTest 2 [0] => modTwoTestCost.letters
  | .congruenceTest 3 [0, 1] => modThreeTestCost.letters
  | .divideTwoOdd => oddHalvingCost.letters
  | .divideThreeTwo => ternaryDivisionCost.letters
  | .contractTwo => contractionTwoCost.letters
  | .contractThree => contractionThreeCost.letters
  | .congruenceTest _ _ => 0

def totalPrivateCost (edges : List (Edge Nat)) : Nat :=
  edges.foldl (fun total edge => total + instructionPrivateCost edge.instruction)
    0

/-- The first private phase assigned to edge occurrence `index`. -/
def privateBase (index : Nat) : Nat :=
  SourceMachine.quotientStates.length +
    totalPrivateCost (fixedProgram.edges.take index)

/-- Offset `offset` inside the private block of edge occurrence `index`. -/
def privatePhase (index offset : Nat) : Nat := privateBase index + offset

/-- Instantiate the physical alphabet for one indexed edge occurrence. -/
def edgeAlphabet (index : Nat) (edge : Edge Nat) : List PhysicalTemplate :=
  let source := boundaryPhase edge.source
  let target := boundaryPhase edge.target
  let privateAt := privatePhase index
  match edge.instruction with
  | .increment =>
      IncrementModule.incrementAlphabet codingPrime source target (privateAt 0)
  | .congruenceTest 2 [0] =>
      CongruenceModule.congruenceAlphabet source target 2 privateAt [0]
  | .congruenceTest 3 [0, 1] =>
      CongruenceModule.congruenceAlphabet source target 3 privateAt [0, 1]
  | .divideTwoOdd =>
      OddHalvingModule.oddHalvingAlphabet source target
        (privateAt 0) (privateAt 1) (privateAt 2) (privateAt 3)
  | .divideThreeTwo =>
      TernaryDivisionModule.ternaryDivisionAlphabet source target
        (privateAt 0) (privateAt 1) (privateAt 2) (privateAt 3)
        (privateAt 4) (privateAt 5)
  | .contractTwo =>
      ContractionModules.twoAlphabet source
        (privateAt 0) (privateAt 1) (privateAt 2) target
        (privateAt 3) (privateAt 4) (privateAt 5) (privateAt 6)
        (privateAt 7) (privateAt 8) (privateAt 9) (privateAt 10)
        (privateAt 11) (privateAt 12) (privateAt 13)
  | .contractThree =>
      ContractionModules.threeAlphabet source
        (privateAt 0) (privateAt 1) target
        (privateAt 2) (privateAt 3) (privateAt 4) (privateAt 5)
        (privateAt 6) (privateAt 7) (privateAt 8) (privateAt 9)
        (privateAt 10) (privateAt 11) (privateAt 12) (privateAt 13)
        (privateAt 14)
  | .congruenceTest _ _ => []

/-- The full listed physical alphabet, before duplicate removal. -/
def listedTemplates : List PhysicalTemplate :=
  fixedProgram.edges.zipIdx.flatMap fun indexed =>
    edgeAlphabet indexed.2 indexed.1

/-- The corresponding listed integer matrices, before duplicate removal. -/
def listedMatrices : List IntMatrix2 :=
  listedTemplates.map (PhysicalTemplate.matrix codingPrime)

/-- Every state used as an edge endpoint is one of the 270 quotient
representatives.  This is checked from the explicit edge list. -/
theorem fixedEndpoints_are_quotientStates :
    fixedProgram.edges.all (fun edge =>
      edge.source ∈ SourceMachine.quotientStates &&
        edge.target ∈ SourceMachine.quotientStates) = true := by
  decide

/-- Boundary phases are exactly the dense interval `0, ..., 269`. -/
theorem boundaryPhases_eq_range :
    SourceMachine.quotientStates.map boundaryPhase =
      List.range SourceMachine.quotientStates.length := by
  decide

/-- The concrete edge list consumes exactly the private-phase budget used in
the manuscript. -/
theorem fixedProgram_private_cost :
    totalPrivateCost fixedProgram.edges =
      genuinePhaseBound - SourceMachine.quotientStates.length := by
  decide

/-- Every allocated private block ends at or before phase 2845. -/
theorem fixedPrivateBlocks_fit :
    fixedProgram.edges.zipIdx.all (fun indexed =>
      privateBase indexed.2 +
          instructionPrivateCost indexed.1.instruction ≤ genuinePhaseBound) =
      true := by
  decide

/-- Every allocated private block starts after the program-boundary phases. -/
theorem fixedPrivateBlocks_after_boundaries :
    fixedProgram.edges.zipIdx.all (fun indexed =>
      SourceMachine.quotientStates.length ≤ privateBase indexed.2) = true := by
  decide

/-- The instantiated alphabet length agrees with each instruction's declared
letter cost. -/
theorem edgeAlphabet_lengths_checked :
    fixedProgram.edges.zipIdx.all (fun indexed =>
      (edgeAlphabet indexed.2 indexed.1).length =
        instructionLetterCost indexed.1.instruction) = true := by
  decide

/-- The actual assembled list contains exactly 5,798 physical templates
before duplicate removal. -/
theorem listedTemplates_length : listedTemplates.length = 5798 := by
  decide

theorem listedMatrices_length : listedMatrices.length = 5798 := by
  simp [listedMatrices, listedTemplates_length]

theorem listedMatrices_nonsingular (matrix : IntMatrix2)
    (matrixMem : matrix ∈ listedMatrices) : matrix.Nonsingular := by
  obtain ⟨letter, _, rfl⟩ := List.mem_map.mp matrixMem
  exact physicalLetter_nonsingular (by have := codingPrime_isPrime.1; omega)

theorem listedMatrices_det_cases (matrix : IntMatrix2)
    (matrixMem : matrix ∈ listedMatrices) :
    matrix.det = codingPrime ∨ matrix.det = -(codingPrime : Int) := by
  obtain ⟨letter, _, rfl⟩ := List.mem_map.mp matrixMem
  exact physicalLetter_det_cases codingPrime letter.sourcePhase
    letter.targetPhase letter.digit letter.preCoefficient letter.postSign
    letter.postCoefficient

/-- The executable allocation reaches exactly the claimed genuine phase
bound. -/
theorem allocatedPhaseCount_eq :
    SourceMachine.quotientStates.length +
        totalPrivateCost fixedProgram.edges = genuinePhaseBound := by
  decide

end Mortality.Compiler.FixedAllocation
