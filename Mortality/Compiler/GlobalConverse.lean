import Mortality.Compiler.GlobalIncrement
import Mortality.Compiler.GlobalCongruence
import Mortality.Compiler.GlobalOddHalving
import Mortality.Compiler.GlobalTernaryDivision
import Mortality.Compiler.GlobalContractions

/-!
# Global converse for the fixed compiler

The instruction-specific parsers expose the first complete compiled edge in
any globally surviving nonempty word.  This file combines the seven cases and
uses strong induction on word length to reconstruct a run of the fixed
one-counter program.
-/

namespace Mortality.Compiler.GlobalConverse

open Mortality
open Mortality.OneCounter
open Mortality.PeriodicCode
open Mortality.Compiler
open Mortality.Compiler.FixedAllocation
open Mortality.Compiler.AllocationProperties

set_option maxRecDepth 100000
set_option maxHeartbeats 3000000

/-- Two affine representatives lie on the same rational line only when their
affine coordinates agree. -/
theorem sameLine_affine_iff {first second : Rat} :
    SameLine (Vec2.affine first) (Vec2.affine second) ↔ first = second := by
  constructor
  · rintro ⟨scalar, scalarNonzero, equality⟩
    have yEquality := congrArg Vec2.y equality
    have scalarEq : scalar = 1 := by
      simpa [Vec2.affine, Vec2.scale] using yEquality.symm
    have xEquality := congrArg Vec2.x equality
    simpa [Vec2.affine, Vec2.scale, scalarEq] using xEquality
  · rintro rfl
    exact SameLine.refl _

/-- A successfully evaluated supported instruction always has a nonempty
physical realization. -/
theorem edgeWord_nonempty
    (index : Nat) (edge : Edge Nat) (input output : Nat)
    (supported : FixedForward.SupportedInstruction edge.instruction)
    (evaluation : edge.instruction.evaluate input = some output) :
    FixedForward.edgeWord index edge input output ≠ [] := by
  generalize instructionEq : edge.instruction = instruction at supported evaluation ⊢
  apply List.ne_nil_of_length_pos
  cases supported with
  | increment =>
      by_cases inputZero : input = 0
      · simp [FixedForward.edgeWord, instructionEq,
          IncrementModule.incrementWord, inputZero]
      · simp [FixedForward.edgeWord, instructionEq,
          IncrementModule.incrementWord, inputZero]
  | testTwo =>
      simp [FixedForward.edgeWord, instructionEq]
  | testThree =>
      simp [FixedForward.edgeWord, instructionEq]
  | divideTwo =>
      simp [FixedForward.edgeWord, instructionEq]
  | divideThree =>
      simp [FixedForward.edgeWord, instructionEq]
  | contractTwo =>
      simp [FixedForward.edgeWord, instructionEq]
  | contractThree =>
      simp [FixedForward.edgeWord, instructionEq]

/-- Uniform first-edge parser obtained by dispatching to the seven checked
instruction parsers. -/
theorem globalEdge_split
    {edge : Edge Nat} {index counter finalState finalCounter : Nat}
    (indexedMem : (edge, index) ∈ fixedProgram.edges.zipIdx)
    (finalStateMem : finalState ∈ SourceMachine.quotientStates)
    {letter : PhysicalTemplate} {tail : List PhysicalTemplate}
    (globalOver : WordOver listedTemplates (letter :: tail))
    (letterLocal : letter ∈ edgeAlphabet index edge)
    (allLocal : AllStatesLocal codingPrime (letter :: tail)
      (phaseAffine (boundaryPhase edge.source)
        (unaryCode codingPrime counter)))
    (completeRun : SameLine
      (physicalWordAction codingPrime (letter :: tail)
        (phaseAffine (boundaryPhase edge.source)
          (unaryCode codingPrime counter)))
      (phaseAffine (boundaryPhase finalState)
        (unaryCode codingPrime finalCounter))) :
    ∃ output suffix,
      edge.instruction.evaluate counter = some output ∧
      letter :: tail =
        FixedForward.edgeWord index edge counter output ++ suffix ∧
      WordOver listedTemplates suffix ∧
      AllStatesLocal codingPrime suffix
        (phaseAffine (boundaryPhase edge.target)
          (unaryCode codingPrime output)) ∧
      SameLine
        (physicalWordAction codingPrime suffix
          (phaseAffine (boundaryPhase edge.target)
            (unaryCode codingPrime output)))
        (phaseAffine (boundaryPhase finalState)
          (unaryCode codingPrime finalCounter)) := by
  have supported :=
    FixedForward.fixedEdge_supported (indexedEdge_mem indexedMem)
  generalize instructionEq : edge.instruction = instruction at supported
  cases supported with
  | increment =>
      obtain ⟨suffix, evaluation, wordEq, suffixOver, suffixLocal,
          suffixRun⟩ :=
        GlobalIncrement.globalIncrement_split indexedMem instructionEq
          finalStateMem globalOver letterLocal allLocal completeRun
      simpa only [instructionEq] using
        (show ∃ output suffix,
            edge.instruction.evaluate counter = some output ∧
            letter :: tail = FixedForward.edgeWord index edge counter output ++
              suffix ∧
            WordOver listedTemplates suffix ∧
            AllStatesLocal codingPrime suffix
              (phaseAffine (boundaryPhase edge.target)
                (unaryCode codingPrime output)) ∧
            SameLine
              (physicalWordAction codingPrime suffix
                (phaseAffine (boundaryPhase edge.target)
                  (unaryCode codingPrime output)))
              (phaseAffine (boundaryPhase finalState)
                (unaryCode codingPrime finalCounter)) from
          ⟨counter + 1, suffix, evaluation, wordEq, suffixOver,
            suffixLocal, suffixRun⟩)
  | testTwo =>
      obtain ⟨suffix, evaluation, wordEq, suffixOver, suffixLocal,
          suffixRun⟩ :=
        GlobalCongruence.globalModTwo_split indexedMem instructionEq
          finalStateMem globalOver letterLocal allLocal completeRun
      simpa only [instructionEq] using
        (show ∃ output suffix,
            edge.instruction.evaluate counter = some output ∧
            letter :: tail = FixedForward.edgeWord index edge counter output ++
              suffix ∧
            WordOver listedTemplates suffix ∧
            AllStatesLocal codingPrime suffix
              (phaseAffine (boundaryPhase edge.target)
                (unaryCode codingPrime output)) ∧
            SameLine
              (physicalWordAction codingPrime suffix
                (phaseAffine (boundaryPhase edge.target)
                  (unaryCode codingPrime output)))
              (phaseAffine (boundaryPhase finalState)
                (unaryCode codingPrime finalCounter)) from
          ⟨counter, suffix, evaluation, wordEq, suffixOver,
            suffixLocal, suffixRun⟩)
  | testThree =>
      obtain ⟨suffix, evaluation, wordEq, suffixOver, suffixLocal,
          suffixRun⟩ :=
        GlobalCongruence.globalModThree_split indexedMem instructionEq
          finalStateMem globalOver letterLocal allLocal completeRun
      simpa only [instructionEq] using
        (show ∃ output suffix,
            edge.instruction.evaluate counter = some output ∧
            letter :: tail = FixedForward.edgeWord index edge counter output ++
              suffix ∧
            WordOver listedTemplates suffix ∧
            AllStatesLocal codingPrime suffix
              (phaseAffine (boundaryPhase edge.target)
                (unaryCode codingPrime output)) ∧
            SameLine
              (physicalWordAction codingPrime suffix
                (phaseAffine (boundaryPhase edge.target)
                  (unaryCode codingPrime output)))
              (phaseAffine (boundaryPhase finalState)
                (unaryCode codingPrime finalCounter)) from
          ⟨counter, suffix, evaluation, wordEq, suffixOver,
            suffixLocal, suffixRun⟩)
  | divideTwo =>
      simpa only [instructionEq] using
        (GlobalOddHalving.globalOddHalving_split indexedMem instructionEq
          finalStateMem globalOver letterLocal allLocal completeRun)
  | divideThree =>
      simpa only [instructionEq] using
        (GlobalTernaryDivision.globalTernaryDivision_split indexedMem
          instructionEq finalStateMem globalOver letterLocal allLocal
          completeRun)
  | contractTwo =>
      simpa only [instructionEq] using
        (GlobalContractions.globalContractTwo_split indexedMem instructionEq
          finalStateMem globalOver letterLocal allLocal completeRun)
  | contractThree =>
      simpa only [instructionEq] using
        (GlobalContractions.globalContractThree_split indexedMem
          instructionEq finalStateMem globalOver letterLocal allLocal
          completeRun)

/-- The guarded boundary encoding is injective on genuine machine states and
natural counters, even projectively. -/
theorem boundaryCode_sameLine_iff
    {firstState secondState firstCounter secondCounter : Nat}
    (firstStateMem : firstState ∈ SourceMachine.quotientStates)
    (secondStateMem : secondState ∈ SourceMachine.quotientStates) :
    SameLine
        (phaseAffine (boundaryPhase firstState)
          (unaryCode codingPrime firstCounter))
        (phaseAffine (boundaryPhase secondState)
          (unaryCode codingPrime secondCounter)) ↔
      firstState = secondState ∧ firstCounter = secondCounter := by
  constructor
  · intro same
    obtain ⟨firstDigit, firstMembership⟩ := unaryCode_inPhaseAt
      (base := codingPrime) (phase := boundaryPhase firstState)
      (counter := firstCounter) codingPrime_isPrime.1
    obtain ⟨secondDigit, secondMembership⟩ := unaryCode_inPhaseAt
      (base := codingPrime) (phase := boundaryPhase secondState)
      (counter := secondCounter) codingPrime_isPrime.1
    have firstBound : boundaryPhase firstState < totalPhaseCount := by
      have denseBound := boundaryPhase_bound firstStateMem
      have boundariesFit : SourceMachine.quotientStates.length ≤
          genuinePhaseBound := by decide
      unfold totalPhaseCount
      omega
    have secondBound : boundaryPhase secondState < totalPhaseCount := by
      have denseBound := boundaryPhase_bound secondStateMem
      have boundariesFit : SourceMachine.quotientStates.length ≤
          genuinePhaseBound := by decide
      unfold totalPhaseCount
      omega
    have phaseEq := (InPhaseAt.unique codingPrime_isPrime
      codingPrime_phase_bound firstBound secondBound firstMembership
      secondMembership same).1
    have stateEq := boundaryPhase_injective_on_quotientStates firstStateMem
      secondStateMem phaseEq
    subst secondState
    have affineSame : SameLine
        (Vec2.affine
          (unaryCode codingPrime firstCounter +
            (phaseShift (boundaryPhase firstState) : Rat)))
        (Vec2.affine
          (unaryCode codingPrime secondCounter +
            (phaseShift (boundaryPhase firstState) : Rat))) := by
      simpa [phaseAffine] using same
    have valueEq := sameLine_affine_iff.mp affineSame
    have codeEq : unaryCode codingPrime firstCounter =
        unaryCode codingPrime secondCounter := by
      grind
    have counterEq := unaryCode_injective codingPrime
      codingPrime_isPrime.1 codeEq
    exact ⟨rfl, counterEq⟩
  · rintro ⟨rfl, rfl⟩
    exact SameLine.refl _

/-- Every globally surviving physical word between two genuine boundary
codes spells a run of the fixed one-counter program. -/
theorem globalWord_implies_fixedRun
    {startState startCounter finishState finishCounter : Nat}
    (startStateMem : startState ∈ SourceMachine.quotientStates)
    (finishStateMem : finishState ∈ SourceMachine.quotientStates)
    {word : List PhysicalTemplate}
    (globalOver : WordOver listedTemplates word)
    (allLocal : AllStatesLocal codingPrime word
      (phaseAffine (boundaryPhase startState)
        (unaryCode codingPrime startCounter)))
    (completeRun : SameLine
      (physicalWordAction codingPrime word
        (phaseAffine (boundaryPhase startState)
          (unaryCode codingPrime startCounter)))
      (phaseAffine (boundaryPhase finishState)
        (unaryCode codingPrime finishCounter))) :
    Reaches (Step fixedProgram)
      { state := startState, counter := startCounter }
      { state := finishState, counter := finishCounter } := by
  induction wordLength : word.length using Nat.strongRecOn generalizing
      word startState startCounter with
  | ind length inductionHypothesis =>
      cases word with
      | nil =>
          have endpointSame : SameLine
              (phaseAffine (boundaryPhase startState)
                (unaryCode codingPrime startCounter))
              (phaseAffine (boundaryPhase finishState)
                (unaryCode codingPrime finishCounter)) := by
            simpa [physicalWordAction] using completeRun
          obtain ⟨stateEq, counterEq⟩ :=
            (boundaryCode_sameLine_iff startStateMem finishStateMem).mp
              endpointSame
          subst finishState
          subst finishCounter
          exact .refl _
      | cons letter tail =>
          have letterGlobal : letter ∈ listedTemplates :=
            globalOver letter (by simp)
          obtain ⟨edge, index, indexedMem, letterLocal, sourceEq⟩ :=
            survivingListedLetter_selects_edge startStateMem letterGlobal
              allLocal.2.start
          subst startState
          obtain ⟨output, suffix, evaluation, wordEq, suffixOver,
              suffixLocal, suffixRun⟩ :=
            globalEdge_split indexedMem finishStateMem globalOver letterLocal
              allLocal completeRun
          have blockNonempty :
              FixedForward.edgeWord index edge startCounter output ≠ [] :=
            edgeWord_nonempty index edge startCounter output
              (FixedForward.fixedEdge_supported (indexedEdge_mem indexedMem))
              evaluation
          have blockPositive : 0 <
              (FixedForward.edgeWord index edge startCounter output).length :=
            List.length_pos_iff.mpr blockNonempty
          have suffixShort : suffix.length < length := by
            have lengthEq := congrArg List.length wordEq
            simp only [List.length_cons, List.length_append] at wordLength lengthEq
            omega
          have endpoints := fixedEdge_endpoints_mem (indexedEdge_mem indexedMem)
          have suffixReaches : Reaches (Step fixedProgram)
              { state := edge.target, counter := output }
              { state := finishState, counter := finishCounter } :=
            inductionHypothesis suffix.length suffixShort
              (startState := edge.target) (startCounter := output)
              endpoints.2 (word := suffix) suffixOver suffixLocal suffixRun rfl
          have firstStep : Step fixedProgram
              { state := edge.source, counter := startCounter }
              { state := edge.target, counter := output } :=
            ⟨edge, indexedEdge_mem indexedMem, rfl, rfl, evaluation⟩
          exact (Reaches.single firstStep).trans suffixReaches

/-- Lift a rational matrix word over the cast fixed alphabet to a word of the
physical templates that generated those matrices. -/
theorem lift_matrix_word
    {matrixWord : List Matrix2}
    (matrixOver : WordOver (listedMatrices.map IntMatrix2.cast) matrixWord) :
    ∃ word,
      WordOver listedTemplates word ∧
      matrixWord = word.map fun letter =>
        IntMatrix2.cast (letter.matrix codingPrime) := by
  induction matrixWord with
  | nil =>
      exact ⟨[], wordOver_nil _, rfl⟩
  | cons matrix matrixTail inductionHypothesis =>
      have matrixMem : matrix ∈ listedMatrices.map IntMatrix2.cast :=
        matrixOver matrix (by simp)
      obtain ⟨integerMatrix, integerMatrixMem, castEq⟩ :=
        List.mem_map.mp matrixMem
      obtain ⟨letter, letterMem, matrixEq⟩ :=
        List.mem_map.mp integerMatrixMem
      have tailOver : WordOver
          (listedMatrices.map IntMatrix2.cast) matrixTail := by
        intro candidate candidateMem
        exact matrixOver candidate (by simp [candidateMem])
      obtain ⟨word, wordOver, tailEq⟩ := inductionHypothesis tailOver
      refine ⟨letter :: word, wordOver_cons letterMem wordOver, ?_⟩
      simp only [List.map_cons, List.cons.injEq]
      exact ⟨castEq.symm.trans
        (congrArg IntMatrix2.cast matrixEq).symm, tailEq⟩

/-- Projective reachability between genuine encoded configurations is exactly
fixed-program reachability in the converse direction. -/
theorem projectivelyReachable_implies_fixedRun
    {start finish : Configuration Nat}
    (startStateMem : start.state ∈ SourceMachine.quotientStates)
    (finishStateMem : finish.state ∈ SourceMachine.quotientStates)
    (reachable : ProjectivelyReachable
      (listedMatrices.map IntMatrix2.cast)
      (FixedForward.encodedConfiguration start)
      (FixedForward.encodedConfiguration finish)) :
    Reaches (Step fixedProgram) start finish := by
  obtain ⟨matrixWord, matrixOver, matrixRun⟩ := reachable
  obtain ⟨word, wordOver, matrixWordEq⟩ := lift_matrix_word matrixOver
  have physicalRun : SameLine
      (physicalWordAction codingPrime word
        (FixedForward.encodedConfiguration start))
      (FixedForward.encodedConfiguration finish) := by
    rw [physicalWordAction_eq_product, ← matrixWordEq]
    exact matrixRun
  have inputNonzero :
      (FixedForward.encodedConfiguration start).Nonzero := by
    exact Vec2.affine_nonzero _
  have finalNonzero :
      (physicalWordAction codingPrime word
        (FixedForward.encodedConfiguration start)).Nonzero :=
    physicalWordAction_nonzero
      (by have := codingPrime_isPrime.1; omega) word inputNonzero
  have finishLocal := IncrementModule.phaseUnaryCode_local codingPrime
    (boundaryPhase finish.state) finish.counter codingPrime_isPrime.1
  have finalLocal : LocalAt codingPrime
      (physicalWordAction codingPrime word
        (FixedForward.encodedConfiguration start)) :=
    LocalAt.of_sameLine finishLocal finalNonzero physicalRun
  have allLocal : AllStatesLocal codingPrime word
      (FixedForward.encodedConfiguration start) :=
    allStatesLocal_of_final_local
      (by have := codingPrime_isPrime.1; omega) word inputNonzero finalLocal
  cases start with
  | mk startState startCounter =>
      cases finish with
      | mk finishState finishCounter =>
          simpa [FixedForward.encodedConfiguration] using
            globalWord_implies_fixedRun startStateMem finishStateMem wordOver
              allLocal physicalRun

/-- Kernel-checked completeness of the fixed projective compiler. -/
theorem projectivelyReachable_iff_u2Halts (input : Nat) :
    ProjectivelyReachable
        (listedMatrices.map IntMatrix2.cast)
        (FixedForward.encodedConfiguration zeroHaltConfiguration)
        (FixedForward.encodedConfiguration (inputConfiguration input)) ↔
      SourceMachine.U2Halts input := by
  constructor
  · intro reachable
    have startMem : zeroHaltConfiguration.state ∈
        SourceMachine.quotientStates := by decide
    have finishMem : (inputConfiguration input).state ∈
        SourceMachine.quotientStates := by
      simpa [inputConfiguration] using
        (show 1 ∈ SourceMachine.quotientStates by decide)
    have run := projectivelyReachable_implies_fixedRun startMem finishMem
      reachable
    exact (concreteFixedProgram_reaches_input_iff_u2Halts input).mp run
  · exact FixedForward.u2Halts_implies_projectivelyReachable input

end Mortality.Compiler.GlobalConverse
