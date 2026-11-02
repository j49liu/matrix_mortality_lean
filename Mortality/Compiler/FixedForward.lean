import Mortality.Compiler.FixedAllocation

/-!
# Forward correctness of the concretely allocated compiler

For every indexed edge occurrence and every successful execution of its
one-counter instruction, this file constructs the literal physical word over
that occurrence's alphabet and proves the claimed boundary-to-boundary
projective action.  The construction is later concatenated along finite
one-counter runs.
-/

namespace Mortality.Compiler.FixedForward

open Mortality
open Mortality.OneCounter
open Mortality.PeriodicCode
open Mortality.Compiler
open Mortality.Compiler.FixedAllocation

set_option maxHeartbeats 2000000
set_option maxRecDepth 100000

/-- The elementary increment word uses only the four displayed increment
letters. -/
private theorem incrementWord_wordOver
    (prime source target privatePhase counter : Nat) :
    WordOver (IncrementModule.incrementAlphabet prime source target privatePhase)
      (IncrementModule.incrementWord prime source target privatePhase counter) := by
  intro letter letterMem
  by_cases counterZero : counter = 0
  · subst counter
    have letterEq : letter = IncrementModule.entryMarker prime source target := by
      simpa [IncrementModule.incrementWord] using letterMem
    subst letter
    simp [IncrementModule.incrementAlphabet]
  · simp [IncrementModule.incrementWord, IncrementModule.incrementTail,
      IncrementModule.incrementAlphabet, counterZero] at letterMem ⊢
    grind

/-- The accepted physical word for one successful indexed edge occurrence. -/
def edgeWord (index : Nat) (edge : Edge Nat) (input output : Nat) :
    List PhysicalTemplate :=
  let source := boundaryPhase edge.source
  let target := boundaryPhase edge.target
  let privateAt := privatePhase index
  match edge.instruction with
  | .increment =>
      IncrementModule.incrementWord codingPrime source target (privateAt 0)
        input
  | .congruenceTest 2 [0] =>
      CongruenceModule.congruenceWord source target 2 input privateAt
  | .congruenceTest 3 [0, 1] =>
      CongruenceModule.congruenceWord source target 3 input privateAt
  | .divideTwoOdd =>
      OddHalvingModule.oddHalvingWord source target
        (privateAt 0) (privateAt 1) (privateAt 2) (privateAt 3) output
  | .divideThreeTwo =>
      TernaryDivisionModule.ternaryDivisionWord source target
        (privateAt 0) (privateAt 1) (privateAt 2) (privateAt 3)
        (privateAt 4) (privateAt 5) output
  | .contractTwo =>
      ContractionModules.twoWord source
        (privateAt 0) (privateAt 1) (privateAt 2) target
        (privateAt 3) (privateAt 4) (privateAt 5) (privateAt 6)
        (privateAt 7) (privateAt 8) (privateAt 9) (privateAt 10)
        (privateAt 11) (privateAt 12) (privateAt 13) (input / 5)
  | .contractThree =>
      ContractionModules.threeWord source
        (privateAt 0) (privateAt 1) target
        (privateAt 2) (privateAt 3) (privateAt 4) (privateAt 5)
        (privateAt 6) (privateAt 7) (privateAt 8) (privateAt 9)
        (privateAt 10) (privateAt 11) (privateAt 12) (privateAt 13)
        (privateAt 14) (input / 5)
  | .congruenceTest _ _ => []

/-- The seven instruction forms that occur in the fixed edge list. -/
inductive SupportedInstruction : Instruction → Prop where
  | increment : SupportedInstruction .increment
  | testTwo : SupportedInstruction (.congruenceTest 2 [0])
  | testThree : SupportedInstruction (.congruenceTest 3 [0, 1])
  | divideTwo : SupportedInstruction .divideTwoOdd
  | divideThree : SupportedInstruction .divideThreeTwo
  | contractTwo : SupportedInstruction .contractTwo
  | contractThree : SupportedInstruction .contractThree

def supportedInstructionBool : Instruction → Bool
  | .increment => true
  | .congruenceTest modulus allowed =>
      (modulus == 2 && allowed == [0]) ||
        (modulus == 3 && allowed == [0, 1])
  | .divideTwoOdd => true
  | .divideThreeTwo => true
  | .contractTwo => true
  | .contractThree => true

theorem supportedInstructionBool_iff (instruction : Instruction) :
    supportedInstructionBool instruction = true ↔
      SupportedInstruction instruction := by
  cases instruction with
  | increment => exact ⟨fun _ => .increment, fun _ => rfl⟩
  | divideTwoOdd => exact ⟨fun _ => .divideTwo, fun _ => rfl⟩
  | divideThreeTwo => exact ⟨fun _ => .divideThree, fun _ => rfl⟩
  | contractTwo => exact ⟨fun _ => .contractTwo, fun _ => rfl⟩
  | contractThree => exact ⟨fun _ => .contractThree, fun _ => rfl⟩
  | congruenceTest modulus allowed =>
      constructor
      · intro checked
        simp [supportedInstructionBool] at checked
        rcases checked with ⟨modulusEq, allowedEq⟩ |
            ⟨modulusEq, allowedEq⟩
        · subst modulus
          subst allowed
          exact .testTwo
        · subst modulus
          subst allowed
          exact .testThree
      · intro supported
        cases supported with
        | testTwo => simp [supportedInstructionBool]
        | testThree => simp [supportedInstructionBool]

theorem fixedProgram_supported_check :
    fixedProgram.edges.all
      (fun edge => supportedInstructionBool edge.instruction) = true := by
  decide

theorem fixedEdge_supported {edge : Edge Nat}
    (edgeMem : edge ∈ fixedProgram.edges) :
    SupportedInstruction edge.instruction := by
  apply (supportedInstructionBool_iff edge.instruction).mp
  exact (List.all_eq_true.mp fixedProgram_supported_check) edge edgeMem

/-- Every edge occurrence in the program has its canonical zero-based index. -/
theorem exists_indexed_edge {edge : Edge Nat}
    (edgeMem : edge ∈ fixedProgram.edges) :
    ∃ index, (edge, index) ∈ fixedProgram.edges.zipIdx := by
  obtain ⟨index, indexBound, edgeEq⟩ := List.mem_iff_getElem.mp edgeMem
  have zippedBound : index < fixedProgram.edges.zipIdx.length := by
    simpa using indexBound
  have indexedMem := List.getElem_mem
    (l := fixedProgram.edges.zipIdx) zippedBound
  rw [List.getElem_zipIdx] at indexedMem
  refine ⟨index, ?_⟩
  simpa [edgeEq] using indexedMem

/-- A successful instruction execution supplies the residue condition needed
by the displayed congruence-test word. -/
private theorem modTwo_allowed {input output : Nat}
    (evaluation :
      Instruction.evaluate (.congruenceTest 2 [0]) input = some output) :
    input % 2 ∈ [0] := by
  simp [Instruction.evaluate] at evaluation ⊢
  exact evaluation.1

private theorem modThree_allowed {input output : Nat}
    (evaluation :
      Instruction.evaluate (.congruenceTest 3 [0, 1]) input = some output) :
    input % 3 ∈ [0, 1] := by
  simp [Instruction.evaluate] at evaluation ⊢
  exact evaluation.1

/-- The accepted edge word belongs to the exact local alphabet. -/
theorem edgeWord_wordOver
    (index : Nat) (edge : Edge Nat) (input output : Nat)
    (supported : SupportedInstruction edge.instruction)
    (evaluation : edge.instruction.evaluate input = some output) :
    WordOver (edgeAlphabet index edge) (edgeWord index edge input output) := by
  generalize instructionEq : edge.instruction = instruction at supported evaluation ⊢
  cases supported with
  | increment =>
      simp only [Instruction.evaluate_increment, Option.some.injEq] at evaluation
      subst output
      simpa [edgeWord, edgeAlphabet, instructionEq] using
        incrementWord_wordOver codingPrime
        (boundaryPhase edge.source) (boundaryPhase edge.target)
        (privatePhase index 0) input
  | testTwo =>
      simpa [edgeWord, edgeAlphabet, instructionEq] using
        CongruenceModule.congruenceWord_wordOver
          (source := boundaryPhase edge.source)
          (target := boundaryPhase edge.target)
          (phase := privatePhase index) (by decide)
          (modTwo_allowed evaluation)
  | testThree =>
      simpa [edgeWord, edgeAlphabet, instructionEq] using
        CongruenceModule.congruenceWord_wordOver
          (source := boundaryPhase edge.source)
          (target := boundaryPhase edge.target)
          (phase := privatePhase index) (by decide)
          (modThree_allowed evaluation)
  | divideTwo =>
      have inputEq :=
        Instruction.evaluate_divideTwoOdd_iff.mp evaluation
      subst input
      simpa [edgeWord, edgeAlphabet, instructionEq] using
        OddHalvingModule.oddHalvingWord_wordOver
          (boundaryPhase edge.source) (boundaryPhase edge.target)
          (privatePhase index 0) (privatePhase index 1)
          (privatePhase index 2) (privatePhase index 3) output
  | divideThree =>
      have inputEq :=
        Instruction.evaluate_divideThreeTwo_iff.mp evaluation
      subst input
      simpa [edgeWord, edgeAlphabet, instructionEq] using
        TernaryDivisionModule.ternaryDivisionWord_wordOver
          (boundaryPhase edge.source) (boundaryPhase edge.target)
          (privatePhase index 0) (privatePhase index 1)
          (privatePhase index 2) (privatePhase index 3)
          (privatePhase index 4) (privatePhase index 5) output
  | contractTwo =>
      obtain ⟨first, inputEq, outputEq⟩ :=
        Instruction.evaluate_contractTwo_iff.mp evaluation
      subst input
      subst output
      have quotientEq : (5 * first + 4) / 5 = first := by omega
      simpa [edgeWord, edgeAlphabet, instructionEq, quotientEq] using
        ContractionModules.twoWord_wordOver
        (boundaryPhase edge.source) (privatePhase index 0)
        (privatePhase index 1) (privatePhase index 2)
        (boundaryPhase edge.target) (privatePhase index 3)
        (privatePhase index 4) (privatePhase index 5)
        (privatePhase index 6) (privatePhase index 7)
        (privatePhase index 8) (privatePhase index 9)
        (privatePhase index 10) (privatePhase index 11)
        (privatePhase index 12) (privatePhase index 13) first
  | contractThree =>
      obtain ⟨first, inputEq, outputEq⟩ :=
        Instruction.evaluate_contractThree_iff.mp evaluation
      subst input
      subst output
      have quotientEq : (5 * first + 4) / 5 = first := by omega
      simpa [edgeWord, edgeAlphabet, instructionEq, quotientEq] using
        ContractionModules.threeWord_wordOver
        (boundaryPhase edge.source) (privatePhase index 0)
        (privatePhase index 1) (boundaryPhase edge.target)
        (privatePhase index 2) (privatePhase index 3)
        (privatePhase index 4) (privatePhase index 5)
        (privatePhase index 6) (privatePhase index 7)
        (privatePhase index 8) (privatePhase index 9)
        (privatePhase index 10) (privatePhase index 11)
        (privatePhase index 12) (privatePhase index 13)
        (privatePhase index 14) first

/-- Exact projective action of a successfully executed indexed edge. -/
theorem edgeWord_correct
    (index : Nat) (edge : Edge Nat) (input output : Nat)
    (supported : SupportedInstruction edge.instruction)
    (evaluation : edge.instruction.evaluate input = some output) :
    SameLine
      (physicalWordAction codingPrime (edgeWord index edge input output)
        (phaseAffine (boundaryPhase edge.source)
          (unaryCode codingPrime input)))
      (phaseAffine (boundaryPhase edge.target)
        (unaryCode codingPrime output)) := by
  generalize instructionEq : edge.instruction = instruction at supported evaluation ⊢
  cases supported with
  | increment =>
      simp only [Instruction.evaluate_increment, Option.some.injEq] at evaluation
      subst output
      simpa [edgeWord, instructionEq] using
        IncrementModule.incrementWord_correct codingPrime
          (boundaryPhase edge.source) (boundaryPhase edge.target)
          (privatePhase index 0) input codingPrime_isPrime.1
  | testTwo =>
      have outputEq := Instruction.evaluate_congruenceTest_eq evaluation
      subst output
      simpa [edgeWord, instructionEq] using
        CongruenceModule.congruenceWord_correct codingPrime
          (boundaryPhase edge.source) (boundaryPhase edge.target) 2 input
          (privatePhase index) codingPrime_isPrime.1
  | testThree =>
      have outputEq := Instruction.evaluate_congruenceTest_eq evaluation
      subst output
      simpa [edgeWord, instructionEq] using
        CongruenceModule.congruenceWord_correct codingPrime
          (boundaryPhase edge.source) (boundaryPhase edge.target) 3 input
          (privatePhase index) codingPrime_isPrime.1
  | divideTwo =>
      have inputEq :=
        Instruction.evaluate_divideTwoOdd_iff.mp evaluation
      subst input
      simpa [edgeWord, instructionEq] using
        OddHalvingModule.oddHalvingWord_correct codingPrime
          (boundaryPhase edge.source) (boundaryPhase edge.target)
          (privatePhase index 0) (privatePhase index 1)
          (privatePhase index 2) (privatePhase index 3) output
          codingPrime_isPrime.1
  | divideThree =>
      have inputEq :=
        Instruction.evaluate_divideThreeTwo_iff.mp evaluation
      subst input
      simpa [edgeWord, instructionEq] using
        TernaryDivisionModule.ternaryDivisionWord_correct codingPrime
          (boundaryPhase edge.source) (boundaryPhase edge.target)
          (privatePhase index 0) (privatePhase index 1)
          (privatePhase index 2) (privatePhase index 3)
          (privatePhase index 4) (privatePhase index 5) output
          codingPrime_isPrime.1
  | contractTwo =>
      obtain ⟨first, inputEq, outputEq⟩ :=
        Instruction.evaluate_contractTwo_iff.mp evaluation
      subst input
      subst output
      have quotientEq : (5 * first + 4) / 5 = first := by omega
      simpa [edgeWord, instructionEq, quotientEq] using
        ContractionModules.twoWord_correct codingPrime
          (boundaryPhase edge.source) (privatePhase index 0)
          (privatePhase index 1) (privatePhase index 2)
          (boundaryPhase edge.target) (privatePhase index 3)
          (privatePhase index 4) (privatePhase index 5)
          (privatePhase index 6) (privatePhase index 7)
          (privatePhase index 8) (privatePhase index 9)
          (privatePhase index 10) (privatePhase index 11)
          (privatePhase index 12) (privatePhase index 13) first
          codingPrime_isPrime.1
  | contractThree =>
      obtain ⟨first, inputEq, outputEq⟩ :=
        Instruction.evaluate_contractThree_iff.mp evaluation
      subst input
      subst output
      have quotientEq : (5 * first + 4) / 5 = first := by omega
      simpa [edgeWord, instructionEq, quotientEq] using
        ContractionModules.threeWord_correct codingPrime
          (boundaryPhase edge.source) (privatePhase index 0)
          (privatePhase index 1) (boundaryPhase edge.target)
          (privatePhase index 2) (privatePhase index 3)
          (privatePhase index 4) (privatePhase index 5)
          (privatePhase index 6) (privatePhase index 7)
          (privatePhase index 8) (privatePhase index 9)
          (privatePhase index 10) (privatePhase index 11)
          (privatePhase index 12) (privatePhase index 13)
          (privatePhase index 14) first codingPrime_isPrime.1

/-- Every state visited by an accepted edge word is local. -/
theorem edgeWord_allStatesLocal
    (index : Nat) (edge : Edge Nat) (input output : Nat)
    (supported : SupportedInstruction edge.instruction)
    (evaluation : edge.instruction.evaluate input = some output) :
    AllStatesLocal codingPrime (edgeWord index edge input output)
      (phaseAffine (boundaryPhase edge.source)
        (unaryCode codingPrime input)) := by
  have action := edgeWord_correct index edge input output supported evaluation
  have inputLocal := IncrementModule.phaseUnaryCode_local codingPrime
    (boundaryPhase edge.source) input codingPrime_isPrime.1
  have outputLocal := IncrementModule.phaseUnaryCode_local codingPrime
    (boundaryPhase edge.target) output codingPrime_isPrime.1
  have outputNonzero := physicalWordAction_nonzero
    (prime := codingPrime) (by have := codingPrime_isPrime.1; omega)
    (edgeWord index edge input output) inputLocal.1
  have finalLocal := LocalAt.of_sameLine outputLocal outputNonzero action
  exact allStatesLocal_of_final_local
    (by have := codingPrime_isPrime.1; omega) _ inputLocal.1 finalLocal

/-- A locally accepted edge word is also a word over the full fixed list. -/
theorem edgeWord_wordOver_listed
    {index : Nat} {edge : Edge Nat} (indexedMem :
      (edge, index) ∈ fixedProgram.edges.zipIdx)
    (input output : Nat)
    (evaluation : edge.instruction.evaluate input = some output) :
    WordOver listedTemplates (edgeWord index edge input output) := by
  apply (edgeWord_wordOver index edge input output
    (fixedEdge_supported
      ((List.mem_zipIdx indexedMem).2.2 ▸ List.getElem_mem
        (List.mem_zipIdx indexedMem).2.1)) evaluation).mono
  intro letter letterMem
  apply List.mem_flatMap.mpr
  exact ⟨(edge, index), indexedMem, letterMem⟩

/-- The guarded projective code of a one-counter configuration. -/
def encodedConfiguration (configuration : Configuration Nat) : Vec2 :=
  phaseAffine (boundaryPhase configuration.state)
    (unaryCode codingPrime configuration.counter)

/-- One concrete program step has a word over the assembled alphabet. -/
theorem fixedStep_compiles {before after : Configuration Nat}
    (step : Step fixedProgram before after) :
    ∃ word, WordOver listedTemplates word ∧
      SameLine
        (physicalWordAction codingPrime word (encodedConfiguration before))
        (encodedConfiguration after) := by
  cases before with
  | mk beforeState beforeCounter =>
      cases after with
      | mk afterState afterCounter =>
          obtain ⟨edge, edgeMem, sourceEq, targetEq, evaluation⟩ := step
          obtain ⟨index, indexedMem⟩ := exists_indexed_edge edgeMem
          change edge.source = beforeState at sourceEq
          change edge.target = afterState at targetEq
          change edge.instruction.evaluate beforeCounter = some afterCounter at evaluation
          subst beforeState
          subst afterState
          refine ⟨edgeWord index edge beforeCounter afterCounter,
            edgeWord_wordOver_listed indexedMem _ _ evaluation, ?_⟩
          simpa [encodedConfiguration] using
            edgeWord_correct index edge beforeCounter afterCounter
              (fixedEdge_supported edgeMem) evaluation

/-- Concatenating the edge words compiles every finite program run. -/
theorem fixedRun_compiles {start finish : Configuration Nat}
    (run : Reaches (Step fixedProgram) start finish) :
    ∃ word, WordOver listedTemplates word ∧
      SameLine
        (physicalWordAction codingPrime word (encodedConfiguration start))
        (encodedConfiguration finish) := by
  induction run with
  | refl =>
      exact ⟨[], wordOver_nil _, SameLine.refl _⟩
  | tail initial lastStep inductionHypothesis =>
      obtain ⟨initialWord, initialOver, initialRun⟩ := inductionHypothesis
      obtain ⟨lastWord, lastOver, lastRun⟩ := fixedStep_compiles lastStep
      exact ⟨initialWord ++ lastWord,
        wordOver_append initialOver lastOver,
        physicalWordAction_append_sameLine codingPrime initialWord lastWord
          initialRun lastRun⟩

/-- Forward half of the fixed compiler, stated with the integer matrix list
used by projective reachability. -/
theorem fixedRun_projectivelyReachable {start finish : Configuration Nat}
    (run : Reaches (Step fixedProgram) start finish) :
    ProjectivelyReachable
      (listedMatrices.map IntMatrix2.cast)
      (encodedConfiguration start) (encodedConfiguration finish) := by
  obtain ⟨word, wordOver, action⟩ := fixedRun_compiles run
  let matrixWord := word.map fun letter =>
    IntMatrix2.cast (letter.matrix codingPrime)
  refine ⟨matrixWord, ?_, ?_⟩
  · intro matrix matrixMem
    obtain ⟨letter, letterMem, rfl⟩ := List.mem_map.mp matrixMem
    apply List.mem_map.mpr
    refine ⟨letter.matrix codingPrime, ?_, rfl⟩
    apply List.mem_map.mpr
    exact ⟨letter, wordOver letter letterMem, rfl⟩
  · simpa [matrixWord, physicalWordAction_eq_product] using action

/-- The concrete source machine's halting predicate implies projective
reachability in the assembled fixed matrix family.  The converse is the
remaining global-compiler obligation. -/
theorem u2Halts_implies_projectivelyReachable (input : Nat) :
    SourceMachine.U2Halts input →
      ProjectivelyReachable
        (listedMatrices.map IntMatrix2.cast)
        (encodedConfiguration zeroHaltConfiguration)
        (encodedConfiguration (inputConfiguration input)) := by
  intro halts
  apply fixedRun_projectivelyReachable
  exact (concreteFixedProgram_reaches_input_iff_u2Halts input).mpr halts

end Mortality.Compiler.FixedForward
