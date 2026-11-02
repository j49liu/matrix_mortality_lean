import Mortality.Compiler.AllocationProperties
import Mortality.Compiler.FixedForward
import Mortality.Compiler.GlobalParserBasics
import Mortality.Compiler.BoundaryParser

/-!
# Lifting odd-halving to the global alphabet

This file repeats only the outer parsing induction of the ten-letter module.
At every private state, the allocation theorem turns membership in the full
5,798-letter alphabet into membership in the selected occurrence's local
alphabet.  The arithmetic classifiers from `OddHalvingModule` then force the
same literal letter as in the module-level converse.
-/

namespace Mortality.Compiler.GlobalOddHalving

open Mortality
open Mortality.OneCounter
open Mortality.PeriodicCode
open Mortality.Compiler
open Mortality.Compiler.UnaryArithmetic
open Mortality.Compiler.PrefixGuessModule
open Mortality.Compiler.OddHalvingArithmetic
open Mortality.Compiler.FixedAllocation
open Mortality.Compiler.AllocationProperties
open Mortality.Compiler.GlobalParserBasics

set_option maxRecDepth 100000
set_option maxHeartbeats 3000000

private theorem oddPrivate_inBlock
    {edge : Edge Nat} {index offset : Nat}
    (instructionEq : edge.instruction = .divideTwoOdd)
    (offsetBound : offset < 4) :
    InPrivateBlock index edge (privatePhase index offset) := by
  simp [InPrivateBlock, privatePhase, instructionEq,
    instructionPrivateCost, oddHalvingCost]
  omega

private theorem oddOccurrence_layout
    {edge : Edge Nat} {index : Nat}
    (indexedMem : (edge, index) ∈ fixedProgram.edges.zipIdx)
    (instructionEq : edge.instruction = .divideTwoOdd) :
    OddHalvingModule.PhaseLayout totalPhaseCount
      (boundaryPhase edge.source) (privatePhase index 0)
      (privatePhase index 1) (privatePhase index 2)
      (privatePhase index 3) := by
  have sourceMem := (fixedEdge_endpoints_mem (indexedEdge_mem indexedMem)).1
  have sourceBound := boundaryPhase_bound sourceMem
  have boundariesFit : SourceMachine.quotientStates.length ≤
      genuinePhaseBound := by decide
  have privateBound : ∀ offset, offset < 4 →
      privatePhase index offset < totalPhaseCount := by
    intro offset offsetBound
    have bounded := privateBlock_bounded indexedMem
      (oddPrivate_inBlock (index := index) instructionEq offsetBound)
    unfold totalPhaseCount
    omega
  have sourcePrivate : ∀ offset, offset < 4 →
      boundaryPhase edge.source ≠ privatePhase index offset := by
    intro offset offsetBound
    exact boundary_ne_private sourceMem indexedMem
      (oddPrivate_inBlock (index := index) instructionEq offsetBound)
  constructor
  · unfold totalPhaseCount
    omega
  · exact privateBound 0 (by omega)
  · exact privateBound 1 (by omega)
  · exact privateBound 2 (by omega)
  · exact privateBound 3 (by omega)
  · exact sourcePrivate 0 (by omega)
  · exact sourcePrivate 1 (by omega)
  · exact sourcePrivate 2 (by omega)
  · exact sourcePrivate 3 (by omega)
  · unfold privatePhase
    omega
  · unfold privatePhase
    omega
  · unfold privatePhase
    omega
  · unfold privatePhase
    omega
  · unfold privatePhase
    omega
  · unfold privatePhase
    omega

private theorem edgeAlphabet_eq_odd
    {edge : Edge Nat} {index : Nat}
    (instructionEq : edge.instruction = .divideTwoOdd) :
    edgeAlphabet index edge =
      OddHalvingModule.oddHalvingAlphabet
        (boundaryPhase edge.source) (boundaryPhase edge.target)
        (privatePhase index 0) (privatePhase index 1)
        (privatePhase index 2) (privatePhase index 3) := by
  simp [edgeAlphabet, instructionEq]

private theorem globalPrivateLetter
    {edge : Edge Nat} {index offset : Nat} {digit : Int} {vector : Vec2}
    {letter : PhysicalTemplate}
    (indexedMem : (edge, index) ∈ fixedProgram.edges.zipIdx)
    (instructionEq : edge.instruction = .divideTwoOdd)
    (offsetBound : offset < 4)
    (membership : InPhaseAt codingPrime (privatePhase index offset) digit
      vector)
    (letterGlobal : letter ∈ listedTemplates)
    (outputLocal : LocalAt codingPrime (letter.act codingPrime vector)) :
    letter ∈ edgeAlphabet index edge :=
  survivingListedLetter_at_private indexedMem
    (oddPrivate_inBlock (index := index) instructionEq offsetBound)
    membership letterGlobal outputLocal

/-- A long surviving ambient word in the selected occurrence's guess phase
must take the local exit before reaching the unary marker. -/
private theorem globalGuessTail_exit
    {edge : Edge Nat} {index counter deleted remaining : Nat}
    (indexedMem : (edge, index) ∈ fixedProgram.edges.zipIdx)
    (instructionEq : edge.instruction = .divideTwoOdd)
    {word : List PhysicalTemplate}
    (globalOver : WordOver listedTemplates word)
    (allLocal : AllStatesLocal codingPrime word
      (phaseAffine (privatePhase index 0)
        (prefixState codingPrime counter deleted)))
    (sumEq : deleted + remaining = counter)
    (longEnough : remaining + 1 ≤ word.length) :
    ∃ loops suffix,
      loops < remaining ∧
      word = PrefixGuessModule.prefixTail (privatePhase index 0)
          (privatePhase index 1) loops ++ suffix ∧
      WordOver listedTemplates suffix ∧
      AllStatesLocal codingPrime suffix
        (phaseAffine (privatePhase index 1)
          (T codingPrime
            (prefixState codingPrime counter (deleted + loops + 1)))) := by
  have layout := oddOccurrence_layout indexedMem instructionEq
  induction remaining generalizing deleted word with
  | zero =>
      cases word with
      | nil => simp at longEnough
      | cons letter tail =>
          have letterGlobal := globalOver letter (by simp)
          have deletedEq : deleted = counter := by omega
          have membership : InPhaseAt codingPrime (privatePhase index 0) 1
              (phaseAffine (privatePhase index 0)
                (prefixState codingPrime counter deleted)) := by
            simpa only [deletedEq] using
              (prefixState_inPhaseAt_marker
                (base := codingPrime) (phase := privatePhase index 0)
                (counter := counter) codingPrime_isPrime.1)
          have letterLocal := globalPrivateLetter indexedMem instructionEq
            (offset := 0) (by omega) membership letterGlobal allLocal.2.start
          have moduleMem : letter ∈ OddHalvingModule.oddHalvingAlphabet
              (boundaryPhase edge.source) (boundaryPhase edge.target)
              (privatePhase index 0) (privatePhase index 1)
              (privatePhase index 2) (privatePhase index 3) := by
            simpa [edgeAlphabet_eq_odd instructionEq] using letterLocal
          have rejected := OddHalvingModule.guess_rejects_marker
            (counter := counter) codingPrime_isPrime codingPrime_phase_bound
            layout moduleMem
          exact False.elim (rejected (by
            simpa only [deletedEq] using allLocal.2.start))
  | succ remaining inductionHypothesis =>
      cases word with
      | nil => simp at longEnough
      | cons letter tail =>
          have letterGlobal := globalOver letter (by simp)
          have tailGlobal : WordOver listedTemplates tail := by
            intro candidate candidateMem
            exact globalOver candidate (by simp [candidateMem])
          have deletedBelow : deleted < counter := by omega
          have membership := prefixState_inPhaseAt_before
            (base := codingPrime) (phase := privatePhase index 0)
            (counter := counter) (deleted := deleted) codingPrime_isPrime.1
            deletedBelow
          have letterLocal := globalPrivateLetter indexedMem instructionEq
            (offset := 0) (by omega) membership letterGlobal allLocal.2.start
          have moduleMem : letter ∈ OddHalvingModule.oddHalvingAlphabet
              (boundaryPhase edge.source) (boundaryPhase edge.target)
              (privatePhase index 0) (privatePhase index 1)
              (privatePhase index 2) (privatePhase index 3) := by
            simpa [edgeAlphabet_eq_odd instructionEq] using letterLocal
          have classified := OddHalvingModule.guess_letter_before_marker
            codingPrime_isPrime codingPrime_phase_bound layout deletedBelow
            moduleMem allLocal.2.start
          rcases classified with letterEq | letterEq
          · subst letter
            have firstStep := PrefixGuessModule.privateLoop_step codingPrime
              (privatePhase index 0) counter deleted codingPrime_isPrime.1
              deletedBelow
            have nextLocal := phasePrefixState_local codingPrime
              (privatePhase index 0) counter (deleted + 1)
              codingPrime_isPrime.1
            have tailLocal : AllStatesLocal codingPrime tail
                (phaseAffine (privatePhase index 0)
                  (prefixState codingPrime counter (deleted + 1))) := by
              apply AllStatesLocal.of_sameLine
                (primePositive := by have := codingPrime_isPrime.1; omega)
                allLocal.2 nextLocal.1 firstStep.symm
            have tailLong : remaining + 1 ≤ tail.length := by
              simpa using longEnough
            obtain ⟨loops, suffix, loopsBound, tailEq, suffixGlobal,
                suffixLocal⟩ :=
              inductionHypothesis tailGlobal tailLocal (by omega) tailLong
            refine ⟨loops + 1, suffix, by omega, ?_, suffixGlobal, ?_⟩
            · rw [tailEq]
              simp [PrefixGuessModule.prefixTail, List.replicate_succ]
            · simpa only [show deleted + 1 + loops + 1 =
                deleted + (loops + 1) + 1 by omega] using suffixLocal
          · subst letter
            have firstStep := PrefixGuessModule.privateExit_step codingPrime
              (privatePhase index 0) (privatePhase index 1) counter deleted
              codingPrime_isPrime.1 deletedBelow
            have exitLocal := phaseTPrefixState_local codingPrime
              (privatePhase index 1) counter (deleted + 1)
              codingPrime_isPrime.1
            have tailLocal : AllStatesLocal codingPrime tail
                (phaseAffine (privatePhase index 1)
                  (T codingPrime
                    (prefixState codingPrime counter (deleted + 1)))) := by
              apply AllStatesLocal.of_sameLine
                (primePositive := by have := codingPrime_isPrime.1; omega)
                allLocal.2 exitLocal.1 firstStep.symm
            exact ⟨0, tail, by omega, by
              simp [PrefixGuessModule.prefixTail], tailGlobal,
              by simpa using tailLocal⟩

/-- From the program boundary, a long ambient survivor chooses a nonempty
prefix and reaches the first automatic private phase. -/
private theorem globalPrefix_choice
    {edge : Edge Nat} {index counter : Nat}
    (indexedMem : (edge, index) ∈ fixedProgram.edges.zipIdx)
    (instructionEq : edge.instruction = .divideTwoOdd)
    (counterPositive : 0 < counter)
    {letter : PhysicalTemplate} {tail : List PhysicalTemplate}
    (globalOver : WordOver listedTemplates (letter :: tail))
    (letterLocal : letter ∈ edgeAlphabet index edge)
    (allLocal : AllStatesLocal codingPrime (letter :: tail)
      (phaseAffine (boundaryPhase edge.source)
        (unaryCode codingPrime counter)))
    (longEnough : counter + 1 ≤ (letter :: tail).length) :
    ∃ first guess suffix,
      0 < guess ∧ first + guess = counter ∧
      letter :: tail = PrefixGuessModule.prefixWord
          (boundaryPhase edge.source) (privatePhase index 0)
          (privatePhase index 1) guess ++ suffix ∧
      WordOver listedTemplates suffix ∧
      AllStatesLocal codingPrime suffix
        (phaseAffine (privatePhase index 1)
          (OddHalvingArithmetic.firstAutomaticState
            codingPrime first guess 0)) := by
  have layout := oddOccurrence_layout indexedMem instructionEq
  have moduleMem : letter ∈ OddHalvingModule.oddHalvingAlphabet
      (boundaryPhase edge.source) (boundaryPhase edge.target)
      (privatePhase index 0) (privatePhase index 1)
      (privatePhase index 2) (privatePhase index 3) := by
    simpa [edgeAlphabet_eq_odd instructionEq] using letterLocal
  cases counter with
  | zero => omega
  | succ previous =>
      have tailGlobal : WordOver listedTemplates tail := by
        intro candidate candidateMem
        exact globalOver candidate (by simp [candidateMem])
      have classified := OddHalvingModule.source_letter_positive
        (counter := previous) codingPrime_isPrime codingPrime_phase_bound
        layout moduleMem allLocal.2.start
      rcases classified with letterEq | letterEq
      · subst letter
        have firstStep := PrefixGuessModule.startContinue_step codingPrime
          (boundaryPhase edge.source) (privatePhase index 0) (previous + 1)
          codingPrime_isPrime.1 (by omega)
        have guessStartLocal := phasePrefixState_local codingPrime
          (privatePhase index 0) (previous + 1) 1 codingPrime_isPrime.1
        have tailLocal : AllStatesLocal codingPrime tail
            (phaseAffine (privatePhase index 0)
              (prefixState codingPrime (previous + 1) 1)) := by
          apply AllStatesLocal.of_sameLine
            (primePositive := by have := codingPrime_isPrime.1; omega)
            allLocal.2 guessStartLocal.1 firstStep.symm
        have tailLong : previous + 1 ≤ tail.length := by
          simpa using longEnough
        obtain ⟨loops, suffix, loopsBound, tailEq, suffixGlobal,
            suffixLocal⟩ :=
          globalGuessTail_exit indexedMem instructionEq tailGlobal tailLocal
            (by omega) tailLong
        have splitEq :
            (previous - (loops + 1)) + (loops + 2) = previous + 1 := by
          omega
        refine ⟨previous - (loops + 1), loops + 2, suffix, by omega,
          splitEq, ?_, suffixGlobal, ?_⟩
        · rw [tailEq]
          simp [PrefixGuessModule.prefixWord,
            PrefixGuessModule.prefixTail]
        · rw [OddHalvingArithmetic.firstAutomaticState_zero codingPrime
            (previous - (loops + 1)) (loops + 2) codingPrime_isPrime.1]
          rw [splitEq]
          simpa only [show 1 + loops + 1 = loops + 2 by omega] using
            suffixLocal
      · subst letter
        have firstStep := PrefixGuessModule.startExit_step codingPrime
          (boundaryPhase edge.source) (privatePhase index 1) (previous + 1)
          codingPrime_isPrime.1 (by omega)
        have exitLocal := phaseTPrefixState_local codingPrime
          (privatePhase index 1) (previous + 1) 1 codingPrime_isPrime.1
        have tailLocal : AllStatesLocal codingPrime tail
            (phaseAffine (privatePhase index 1)
              (T codingPrime (prefixState codingPrime (previous + 1) 1))) := by
          apply AllStatesLocal.of_sameLine
            (primePositive := by have := codingPrime_isPrime.1; omega)
            allLocal.2 exitLocal.1 firstStep.symm
        refine ⟨previous, 1, tail, by omega, by omega, ?_, tailGlobal, ?_⟩
        · simp [PrefixGuessModule.prefixWord]
        · rw [OddHalvingArithmetic.firstAutomaticState_zero codingPrime
            previous 1 codingPrime_isPrime.1]
          simpa using tailLocal

/-- Global-alphabet version of the first automatic marker-one scan. -/
private theorem globalFirstScanTail_unique
    {edge : Edge Nat} {index guess deleted remaining : Nat}
    (indexedMem : (edge, index) ∈ fixedProgram.edges.zipIdx)
    (instructionEq : edge.instruction = .divideTwoOdd)
    {word : List PhysicalTemplate}
    (globalOver : WordOver listedTemplates word)
    (allLocal : AllStatesLocal codingPrime word
      (phaseAffine (privatePhase index 1)
        (firstAutomaticState codingPrime (deleted + remaining) guess
          deleted)))
    (lengthEq : word.length = remaining + 1) :
    word = List.replicate remaining
        (OddHalvingModule.identityZero (privatePhase index 1)) ++
      [OddHalvingModule.identityMarker (privatePhase index 1)
        (privatePhase index 2)] := by
  have layout := oddOccurrence_layout indexedMem instructionEq
  induction remaining generalizing deleted word with
  | zero =>
      cases word with
      | nil => simp at lengthEq
      | cons letter tail =>
          have tailEmpty : tail = [] := by
            apply List.eq_nil_of_length_eq_zero
            simpa using lengthEq
          subst tail
          have letterGlobal := globalOver letter (by simp)
          have membership := firstAutomaticState_inPhaseAt_marker
            (base := codingPrime) (phase := privatePhase index 1)
            (first := deleted) (guess := guess) codingPrime_isPrime.1
          have letterLocal := globalPrivateLetter indexedMem instructionEq
            (offset := 1) (by omega) membership letterGlobal
            (by exact allLocal.2)
          have moduleMem : letter ∈ OddHalvingModule.oddHalvingAlphabet
              (boundaryPhase edge.source) (boundaryPhase edge.target)
              (privatePhase index 0) (privatePhase index 1)
              (privatePhase index 2) (privatePhase index 3) := by
            simpa [edgeAlphabet_eq_odd instructionEq] using letterLocal
          have letterEq := OddHalvingModule.first_letter_at_marker
            (first := deleted) (guess := guess) codingPrime_isPrime
            codingPrime_phase_bound layout.sourceBound layout.guessBound
            layout.firstBound layout.secondBound layout.validatorBound
            layout.sourceFirstDistinct.symm layout.guessFirstDistinct.symm
            layout.firstSecondDistinct layout.firstValidatorDistinct
            moduleMem (by exact allLocal.2)
          subst letter
          simp
  | succ remaining inductionHypothesis =>
      cases word with
      | nil => simp at lengthEq
      | cons letter tail =>
          have letterGlobal := globalOver letter (by simp)
          have tailGlobal : WordOver listedTemplates tail := by
            intro candidate candidateMem
            exact globalOver candidate (by simp [candidateMem])
          have membership := firstAutomaticState_inPhaseAt_before
            (base := codingPrime) (phase := privatePhase index 1)
            (first := deleted + (remaining + 1)) (guess := guess)
            (deleted := deleted) codingPrime_isPrime.1 (by omega)
          have letterLocal := globalPrivateLetter indexedMem instructionEq
            (offset := 1) (by omega) membership letterGlobal allLocal.2.start
          have moduleMem : letter ∈ OddHalvingModule.oddHalvingAlphabet
              (boundaryPhase edge.source) (boundaryPhase edge.target)
              (privatePhase index 0) (privatePhase index 1)
              (privatePhase index 2) (privatePhase index 3) := by
            simpa [edgeAlphabet_eq_odd instructionEq] using letterLocal
          have letterEq := OddHalvingModule.first_letter_before_marker
            (first := deleted + (remaining + 1)) (guess := guess)
            (deleted := deleted) codingPrime_isPrime codingPrime_phase_bound
            layout.sourceBound layout.guessBound layout.firstBound
            layout.secondBound layout.validatorBound
            layout.sourceFirstDistinct.symm layout.guessFirstDistinct.symm
            layout.firstSecondDistinct layout.firstValidatorDistinct
            (by omega) moduleMem allLocal.2.start
          subst letter
          have firstStep := OddHalvingModule.firstZero_step codingPrime
            (privatePhase index 1) (deleted + (remaining + 1)) guess deleted
            codingPrime_isPrime.1 (by omega)
          have canonicalLocal : LocalAt codingPrime
              (phaseAffine (privatePhase index 1)
                (firstAutomaticState codingPrime ((deleted + 1) + remaining)
                  guess (deleted + 1))) :=
            OddHalvingModule.phaseLocal
              (firstAutomaticState_local codingPrime
                ((deleted + 1) + remaining) guess (deleted + 1)
                codingPrime_isPrime.1)
          have tailLocal : AllStatesLocal codingPrime tail
              (phaseAffine (privatePhase index 1)
                (firstAutomaticState codingPrime ((deleted + 1) + remaining)
                  guess (deleted + 1))) := by
            apply AllStatesLocal.of_sameLine
              (primePositive := by have := codingPrime_isPrime.1; omega)
              allLocal.2 canonicalLocal.1
            simpa only [show deleted + (remaining + 1) =
                (deleted + 1) + remaining by omega] using firstStep.symm
          have tailLength : tail.length = remaining + 1 := by
            simpa using lengthEq
          have tailEq := inductionHypothesis tailGlobal tailLocal tailLength
          rw [tailEq]
          simp [List.replicate_succ]

/-- Global-alphabet version of the second automatic marker-one scan. -/
private theorem globalSecondScanTail_unique
    {edge : Edge Nat} {index guess deleted remaining : Nat}
    (indexedMem : (edge, index) ∈ fixedProgram.edges.zipIdx)
    (instructionEq : edge.instruction = .divideTwoOdd)
    (guessPositive : 0 < guess)
    {word : List PhysicalTemplate}
    (globalOver : WordOver listedTemplates word)
    (allLocal : AllStatesLocal codingPrime word
      (phaseAffine (privatePhase index 2)
        (secondAutomaticState codingPrime (deleted + remaining) guess
          deleted)))
    (lengthEq : word.length = remaining + 1) :
    word = List.replicate remaining
        (OddHalvingModule.identityZero (privatePhase index 2)) ++
      [OddHalvingModule.inverseTMarker (privatePhase index 2)
        (privatePhase index 3)] := by
  have layout := oddOccurrence_layout indexedMem instructionEq
  induction remaining generalizing deleted word with
  | zero =>
      cases word with
      | nil => simp at lengthEq
      | cons letter tail =>
          have tailEmpty : tail = [] := by
            apply List.eq_nil_of_length_eq_zero
            simpa using lengthEq
          subst tail
          have letterGlobal := globalOver letter (by simp)
          have membership := secondAutomaticState_inPhaseAt_marker
            (base := codingPrime) (phase := privatePhase index 2)
            (first := deleted) (guess := guess) codingPrime_isPrime.1
            guessPositive
          have letterLocal := globalPrivateLetter indexedMem instructionEq
            (offset := 2) (by omega) membership letterGlobal
            (by exact allLocal.2)
          have moduleMem : letter ∈ OddHalvingModule.oddHalvingAlphabet
              (boundaryPhase edge.source) (boundaryPhase edge.target)
              (privatePhase index 0) (privatePhase index 1)
              (privatePhase index 2) (privatePhase index 3) := by
            simpa [edgeAlphabet_eq_odd instructionEq] using letterLocal
          have letterEq := OddHalvingModule.second_letter_at_marker
            (first := deleted) (guess := guess) codingPrime_isPrime
            codingPrime_phase_bound guessPositive layout.sourceBound
            layout.guessBound layout.firstBound layout.secondBound
            layout.validatorBound layout.sourceSecondDistinct.symm
            layout.guessSecondDistinct.symm layout.firstSecondDistinct.symm
            layout.secondValidatorDistinct moduleMem
            (by exact allLocal.2)
          subst letter
          simp
  | succ remaining inductionHypothesis =>
      cases word with
      | nil => simp at lengthEq
      | cons letter tail =>
          have letterGlobal := globalOver letter (by simp)
          have tailGlobal : WordOver listedTemplates tail := by
            intro candidate candidateMem
            exact globalOver candidate (by simp [candidateMem])
          have membership := secondAutomaticState_inPhaseAt_before
            (base := codingPrime) (phase := privatePhase index 2)
            (first := deleted + (remaining + 1)) (guess := guess)
            (deleted := deleted) codingPrime_isPrime.1 (by omega)
          have letterLocal := globalPrivateLetter indexedMem instructionEq
            (offset := 2) (by omega) membership letterGlobal allLocal.2.start
          have moduleMem : letter ∈ OddHalvingModule.oddHalvingAlphabet
              (boundaryPhase edge.source) (boundaryPhase edge.target)
              (privatePhase index 0) (privatePhase index 1)
              (privatePhase index 2) (privatePhase index 3) := by
            simpa [edgeAlphabet_eq_odd instructionEq] using letterLocal
          have letterEq := OddHalvingModule.second_letter_before_marker
            (first := deleted + (remaining + 1)) (guess := guess)
            (deleted := deleted) codingPrime_isPrime codingPrime_phase_bound
            layout.sourceBound layout.guessBound layout.firstBound
            layout.secondBound layout.validatorBound
            layout.sourceSecondDistinct.symm layout.guessSecondDistinct.symm
            layout.firstSecondDistinct.symm layout.secondValidatorDistinct
            (by omega) moduleMem allLocal.2.start
          subst letter
          have firstStep := OddHalvingModule.secondZero_step codingPrime
            (privatePhase index 2) (deleted + (remaining + 1)) guess deleted
            codingPrime_isPrime.1 (by omega)
          have canonicalLocal : LocalAt codingPrime
              (phaseAffine (privatePhase index 2)
                (secondAutomaticState codingPrime
                  ((deleted + 1) + remaining) guess (deleted + 1))) :=
            OddHalvingModule.phaseLocal
              (secondAutomaticState_local codingPrime
                ((deleted + 1) + remaining) guess (deleted + 1)
                codingPrime_isPrime.1)
          have tailLocal : AllStatesLocal codingPrime tail
              (phaseAffine (privatePhase index 2)
                (secondAutomaticState codingPrime
                  ((deleted + 1) + remaining) guess (deleted + 1))) := by
            apply AllStatesLocal.of_sameLine
              (primePositive := by have := codingPrime_isPrime.1; omega)
              allLocal.2 canonicalLocal.1
            simpa only [show deleted + (remaining + 1) =
                (deleted + 1) + remaining by omega] using firstStep.symm
          have tailLength : tail.length = remaining + 1 := by
            simpa using lengthEq
          have tailEq := inductionHypothesis tailGlobal tailLocal tailLength
          rw [tailEq]
          simp [List.replicate_succ]

/-- Global-alphabet version of the final validator scan. -/
private theorem globalValidatorTail_unique
    {edge : Edge Nat}
    {index first guess deleted remaining : Nat}
    (indexedMem : (edge, index) ∈ fixedProgram.edges.zipIdx)
    (instructionEq : edge.instruction = .divideTwoOdd)
    (guessPositive : 0 < guess)
    {word : List PhysicalTemplate}
    (globalOver : WordOver listedTemplates word)
    (allLocal : AllStatesLocal codingPrime word
      (phaseAffine (privatePhase index 3)
        (validatorState codingPrime first guess deleted)))
    (sumEq : deleted + remaining = validatorLength first guess)
    (lengthEq : word.length = remaining + 1) :
    first = guess - 1 ∧
      word = List.replicate remaining
          (OddHalvingModule.identityZero (privatePhase index 3)) ++
        [OddHalvingModule.validatorMarker (privatePhase index 3)
          (boundaryPhase edge.target)] := by
  have layout := oddOccurrence_layout indexedMem instructionEq
  induction remaining generalizing deleted word with
  | zero =>
      cases word with
      | nil => simp at lengthEq
      | cons letter tail =>
          have tailEmpty : tail = [] := by
            apply List.eq_nil_of_length_eq_zero
            simpa using lengthEq
          subst tail
          have letterGlobal := globalOver letter (by simp)
          have deletedEq : deleted = validatorLength first guess := by omega
          have membership : InPhaseAt codingPrime (privatePhase index 3)
              (validatorMarkerDigit first guess)
              (phaseAffine (privatePhase index 3)
                (validatorState codingPrime first guess deleted)) := by
            simpa only [deletedEq] using
              (validatorState_inPhaseAt_marker
                (base := codingPrime) (phase := privatePhase index 3)
                (first := first) (guess := guess) codingPrime_isPrime.1
                guessPositive)
          have letterLocal := globalPrivateLetter indexedMem instructionEq
            (offset := 3) (by omega) membership letterGlobal
            (by exact allLocal.2)
          have moduleMem : letter ∈ OddHalvingModule.oddHalvingAlphabet
              (boundaryPhase edge.source) (boundaryPhase edge.target)
              (privatePhase index 0) (privatePhase index 1)
              (privatePhase index 2) (privatePhase index 3) := by
            simpa [edgeAlphabet_eq_odd instructionEq] using letterLocal
          have classified := OddHalvingModule.validator_letter_at_marker
            (first := first) (guess := guess) codingPrime_isPrime
            codingPrime_phase_bound guessPositive layout.sourceBound
            layout.guessBound layout.firstBound layout.secondBound
            layout.validatorBound layout.sourceValidatorDistinct.symm
            layout.guessValidatorDistinct.symm
            layout.firstValidatorDistinct.symm
            layout.secondValidatorDistinct.symm moduleMem
            (by subst deleted; exact allLocal.2)
          rcases classified with ⟨accepted, letterEq⟩
          subst letter
          exact ⟨accepted, by simp⟩
  | succ remaining inductionHypothesis =>
      cases word with
      | nil => simp at lengthEq
      | cons letter tail =>
          have letterGlobal := globalOver letter (by simp)
          have tailGlobal : WordOver listedTemplates tail := by
            intro candidate candidateMem
            exact globalOver candidate (by simp [candidateMem])
          have deletedBelow : deleted < validatorLength first guess := by
            omega
          have membership := validatorState_inPhaseAt_before
            (base := codingPrime) (phase := privatePhase index 3)
            (first := first) (guess := guess) (deleted := deleted)
            codingPrime_isPrime.1 guessPositive deletedBelow
          have letterLocal := globalPrivateLetter indexedMem instructionEq
            (offset := 3) (by omega) membership letterGlobal allLocal.2.start
          have moduleMem : letter ∈ OddHalvingModule.oddHalvingAlphabet
              (boundaryPhase edge.source) (boundaryPhase edge.target)
              (privatePhase index 0) (privatePhase index 1)
              (privatePhase index 2) (privatePhase index 3) := by
            simpa [edgeAlphabet_eq_odd instructionEq] using letterLocal
          have letterEq := OddHalvingModule.validator_letter_before_marker
            (first := first) (guess := guess) (deleted := deleted)
            codingPrime_isPrime codingPrime_phase_bound guessPositive
            layout.sourceBound layout.guessBound layout.firstBound
            layout.secondBound layout.validatorBound
            layout.sourceValidatorDistinct.symm
            layout.guessValidatorDistinct.symm
            layout.firstValidatorDistinct.symm
            layout.secondValidatorDistinct.symm deletedBelow moduleMem
            allLocal.2.start
          subst letter
          have firstStep := OddHalvingModule.validatorZero_step codingPrime
            (privatePhase index 3) first guess deleted codingPrime_isPrime.1
            guessPositive deletedBelow
          have canonicalLocal : LocalAt codingPrime
              (phaseAffine (privatePhase index 3)
                (validatorState codingPrime first guess (deleted + 1))) :=
            OddHalvingModule.phaseLocal
              (validatorState_local codingPrime first guess (deleted + 1)
                codingPrime_isPrime.1 guessPositive)
          have tailLocal : AllStatesLocal codingPrime tail
              (phaseAffine (privatePhase index 3)
                (validatorState codingPrime first guess (deleted + 1))) := by
            apply AllStatesLocal.of_sameLine
              (primePositive := by have := codingPrime_isPrime.1; omega)
              allLocal.2 canonicalLocal.1 firstStep.symm
          have tailLength : tail.length = remaining + 1 := by
            simpa using lengthEq
          obtain ⟨accepted, tailEq⟩ := inductionHypothesis tailGlobal
            tailLocal (by omega) tailLength
          rw [tailEq]
          exact ⟨accepted, by simp [List.replicate_succ]⟩

/-- The complete automatic suffix is forced even when the ambient word may
draw from the whole fixed alphabet. -/
private theorem globalAutomaticSuffix_unique
    {edge : Edge Nat} {index first guess : Nat}
    (indexedMem : (edge, index) ∈ fixedProgram.edges.zipIdx)
    (instructionEq : edge.instruction = .divideTwoOdd)
    (guessPositive : 0 < guess)
    {word : List PhysicalTemplate}
    (globalOver : WordOver listedTemplates word)
    (allLocal : AllStatesLocal codingPrime word
      (phaseAffine (privatePhase index 1)
        (firstAutomaticState codingPrime first guess 0)))
    (lengthEq : word.length =
      (first + 1) + (first + 1) + (validatorLength first guess + 1)) :
    first = guess - 1 ∧
      word = OddHalvingModule.firstScanWord (privatePhase index 1)
          (privatePhase index 2) first ++
        OddHalvingModule.secondScanWord (privatePhase index 2)
          (privatePhase index 3) first ++
        OddHalvingModule.validatorWord (privatePhase index 3)
          (boundaryPhase edge.target) first := by
  have firstLengthBound : first + 1 ≤ word.length := by omega
  have firstPartLength : (word.take (first + 1)).length = first + 1 := by
    rw [List.length_take, Nat.min_eq_left firstLengthBound]
  have firstPartLocal : AllStatesLocal codingPrime (word.take (first + 1))
      (phaseAffine (privatePhase index 1)
        (firstAutomaticState codingPrime (0 + first) guess 0)) := by
    simpa using allLocal.take (first + 1)
  have firstPartEq := globalFirstScanTail_unique indexedMem instructionEq
    (deleted := 0) (remaining := first) (guess := guess)
    (globalOver.take (first + 1)) firstPartLocal firstPartLength
  have afterFirstRaw := allLocal.drop (first + 1)
  rw [firstPartEq] at afterFirstRaw
  have firstRun := OddHalvingModule.firstScanWord_correct codingPrime
    (privatePhase index 1) (privatePhase index 2) first guess
    codingPrime_isPrime.1
  have secondStartLocal : LocalAt codingPrime
      (phaseAffine (privatePhase index 2)
        (secondAutomaticState codingPrime first guess 0)) :=
    OddHalvingModule.phaseLocal
      (secondAutomaticState_local codingPrime first guess 0
        codingPrime_isPrime.1)
  have afterFirst : AllStatesLocal codingPrime (word.drop (first + 1))
      (phaseAffine (privatePhase index 2)
        (secondAutomaticState codingPrime first guess 0)) := by
    apply AllStatesLocal.of_sameLine
      (primePositive := by have := codingPrime_isPrime.1; omega)
      afterFirstRaw secondStartLocal.1
    simpa [OddHalvingModule.firstScanWord,
      secondAutomaticState_zero] using firstRun.symm
  have afterFirstLength : (word.drop (first + 1)).length =
      (first + 1) + (validatorLength first guess + 1) := by
    rw [List.length_drop, lengthEq]
    omega
  have secondLengthBound : first + 1 ≤
      (word.drop (first + 1)).length := by omega
  have secondPartLength :
      ((word.drop (first + 1)).take (first + 1)).length = first + 1 := by
    rw [List.length_take, Nat.min_eq_left secondLengthBound]
  have secondPartLocal : AllStatesLocal codingPrime
      ((word.drop (first + 1)).take (first + 1))
      (phaseAffine (privatePhase index 2)
        (secondAutomaticState codingPrime (0 + first) guess 0)) := by
    simpa using afterFirst.take (first + 1)
  have secondPartEq := globalSecondScanTail_unique indexedMem instructionEq
    guessPositive (deleted := 0) (remaining := first)
    ((globalOver.drop (first + 1)).take (first + 1))
    secondPartLocal secondPartLength
  have afterSecondRaw := afterFirst.drop (first + 1)
  rw [secondPartEq] at afterSecondRaw
  have secondRun := OddHalvingModule.secondScanWord_correct codingPrime
    (privatePhase index 2) (privatePhase index 3) first guess
    codingPrime_isPrime.1 guessPositive
  have secondRun' : SameLine
      (physicalWordAction codingPrime
        (OddHalvingModule.secondScanWord (privatePhase index 2)
          (privatePhase index 3) first)
        (phaseAffine (privatePhase index 2)
          (secondAutomaticState codingPrime first guess 0)))
      (phaseAffine (privatePhase index 3)
        (validatorState codingPrime first guess 0)) := by
    simpa [validatorState_zero] using secondRun
  have validatorStartLocal : LocalAt codingPrime
      (phaseAffine (privatePhase index 3)
        (validatorState codingPrime first guess 0)) :=
    OddHalvingModule.phaseLocal
      (validatorState_local codingPrime first guess 0 codingPrime_isPrime.1
        guessPositive)
  have afterSecond : AllStatesLocal codingPrime
      ((word.drop (first + 1)).drop (first + 1))
      (phaseAffine (privatePhase index 3)
        (validatorState codingPrime first guess 0)) := by
    apply AllStatesLocal.of_sameLine
      (primePositive := by have := codingPrime_isPrime.1; omega)
      afterSecondRaw validatorStartLocal.1 secondRun'.symm
  have validatorLengthEq :
      ((word.drop (first + 1)).drop (first + 1)).length =
        validatorLength first guess + 1 := by
    rw [List.length_drop, afterFirstLength]
    omega
  have validatorClassified := globalValidatorTail_unique indexedMem
    instructionEq guessPositive (deleted := 0)
    (remaining := validatorLength first guess)
    ((globalOver.drop (first + 1)).drop (first + 1)) afterSecond
    (by omega) validatorLengthEq
  rcases validatorClassified with ⟨accepted, validatorPartEqRaw⟩
  have validatorPartEq :
      (word.drop (first + 1)).drop (first + 1) =
        OddHalvingModule.validatorWord (privatePhase index 3)
          (boundaryPhase edge.target) first := by
    simpa [OddHalvingModule.validatorWord, validatorLength, accepted] using
      validatorPartEqRaw
  have firstSplit := List.take_append_drop (first + 1) word
  have secondSplit := List.take_append_drop (first + 1)
    (word.drop (first + 1))
  refine ⟨accepted, ?_⟩
  calc
    word = word.take (first + 1) ++ word.drop (first + 1) := firstSplit.symm
    _ = OddHalvingModule.firstScanWord (privatePhase index 1)
          (privatePhase index 2) first ++ word.drop (first + 1) := by
      rw [firstPartEq]
      rfl
    _ = OddHalvingModule.firstScanWord (privatePhase index 1)
          (privatePhase index 2) first ++
        ((word.drop (first + 1)).take (first + 1) ++
          (word.drop (first + 1)).drop (first + 1)) := by
      rw [secondSplit]
    _ = OddHalvingModule.firstScanWord (privatePhase index 1)
          (privatePhase index 2) first ++
        (OddHalvingModule.secondScanWord (privatePhase index 2)
            (privatePhase index 3) first ++
          OddHalvingModule.validatorWord (privatePhase index 3)
            (boundaryPhase edge.target) first) := by
      rw [secondPartEq, validatorPartEq]
      rfl
    _ = OddHalvingModule.firstScanWord (privatePhase index 1)
          (privatePhase index 2) first ++
        OddHalvingModule.secondScanWord (privatePhase index 2)
          (privatePhase index 3) first ++
        OddHalvingModule.validatorWord (privatePhase index 3)
          (boundaryPhase edge.target) first := by
      simp [List.append_assoc]

/-- Global-alphabet odd-halving converse.  A sufficiently long locally
surviving ambient word forces an odd input and the literal accepted module
word as its first complete instruction block. -/
theorem globalOddHalvingWord_forced_prefix
    {edge : Edge Nat} {index counter : Nat}
    (indexedMem : (edge, index) ∈ fixedProgram.edges.zipIdx)
    (instructionEq : edge.instruction = .divideTwoOdd)
    {letter : PhysicalTemplate} {tail : List PhysicalTemplate}
    (globalOver : WordOver listedTemplates (letter :: tail))
    (letterLocal : letter ∈ edgeAlphabet index edge)
    (allLocal : AllStatesLocal codingPrime (letter :: tail)
      (phaseAffine (boundaryPhase edge.source)
        (unaryCode codingPrime counter)))
    (longEnough : 2 * counter + 2 ≤ (letter :: tail).length) :
    ∃ output,
      counter = 2 * output + 1 ∧
      (letter :: tail).take (2 * counter + 2) =
        FixedForward.edgeWord index edge counter output := by
  have layout := oddOccurrence_layout indexedMem instructionEq
  have moduleMem : letter ∈ OddHalvingModule.oddHalvingAlphabet
      (boundaryPhase edge.source) (boundaryPhase edge.target)
      (privatePhase index 0) (privatePhase index 1)
      (privatePhase index 2) (privatePhase index 3) := by
    simpa [edgeAlphabet_eq_odd instructionEq] using letterLocal
  have counterPositive : 0 < counter := by
    cases counter with
    | zero =>
        exact False.elim
          ((OddHalvingModule.source_rejects_zero codingPrime_isPrime
            codingPrime_phase_bound layout moduleMem) allLocal.2.start)
    | succ previous => omega
  have prefixLong : counter + 1 ≤ (letter :: tail).length := by omega
  obtain ⟨first, guess, suffix, guessPositive, splitEq, wordEq,
      suffixGlobal, suffixLocal⟩ :=
    globalPrefix_choice indexedMem instructionEq counterPositive globalOver
      letterLocal allLocal prefixLong
  have prefixLength := PrefixGuessModule.prefixWord_length
    (source := boundaryPhase edge.source)
    (privatePhase := privatePhase index 0)
    (handoff := privatePhase index 1) guessPositive
  have lengthLower : 2 * counter + 2 ≤ guess + suffix.length := by
    rw [wordEq] at longEnough
    simpa [prefixLength] using longEnough
  have validatorBound : validatorLength first guess ≤ guess - 1 :=
    Nat.min_le_right _ _
  have automaticLengthBound :
      (first + 1) + (first + 1) + (validatorLength first guess + 1) ≤
        suffix.length := by
    omega
  let automaticLength :=
    (first + 1) + (first + 1) + (validatorLength first guess + 1)
  have automaticPartLength : (suffix.take automaticLength).length =
      automaticLength := by
    rw [List.length_take, Nat.min_eq_left]
    exact automaticLengthBound
  have automaticClassified := globalAutomaticSuffix_unique indexedMem
    instructionEq guessPositive (word := suffix.take automaticLength)
    (suffixGlobal.take automaticLength)
    (suffixLocal.take automaticLength) automaticPartLength
  rcases automaticClassified with ⟨accepted, automaticPartEq⟩
  have guessEq : guess = first + 1 := by omega
  have counterEq : counter = 2 * first + 1 := by omega
  have automaticLengthEq : automaticLength = 3 * first + 3 := by
    simp [automaticLength, validatorLength, accepted]
    omega
  have prefixWordLength :
      (PrefixGuessModule.prefixWord (boundaryPhase edge.source)
        (privatePhase index 0) (privatePhase index 1) guess).length =
        first + 1 := by
    rw [prefixLength, guessEq]
  refine ⟨first, counterEq, ?_⟩
  rw [wordEq, List.take_append]
  have totalMinusPrefix :
      2 * counter + 2 -
          (PrefixGuessModule.prefixWord (boundaryPhase edge.source)
            (privatePhase index 0) (privatePhase index 1) guess).length =
        automaticLength := by
    rw [prefixWordLength, counterEq, automaticLengthEq]
    omega
  rw [List.take_of_length_le (by omega :
      (PrefixGuessModule.prefixWord (boundaryPhase edge.source)
        (privatePhase index 0) (privatePhase index 1) guess).length ≤
          2 * counter + 2), totalMinusPrefix, automaticPartEq, guessEq]
  simp [FixedForward.edgeWord, instructionEq,
    OddHalvingModule.oddHalvingWord, List.append_assoc]

/-- Endpoint-aware local parser for the nondeterministic prefix choice. -/
private theorem localGuessTail_exit_to_endpoint
    {edge : Edge Nat} {index counter deleted remaining endpointPhase : Nat}
    {endpointDigit : Int} {endpoint : Vec2}
    (indexedMem : (edge, index) ∈ fixedProgram.edges.zipIdx)
    (instructionEq : edge.instruction = .divideTwoOdd)
    (endpointBound : endpointPhase < totalPhaseCount)
    (guessEndpointDistinct : privatePhase index 0 ≠ endpointPhase)
    (endpointMembership : InPhaseAt codingPrime endpointPhase endpointDigit
      endpoint)
    (sumEq : deleted + remaining = counter)
    {word : List PhysicalTemplate}
    (wordOver : WordOver (edgeAlphabet index edge) word)
    (allLocal : AllStatesLocal codingPrime word
      (phaseAffine (privatePhase index 0)
        (prefixState codingPrime counter deleted)))
    (completeRun : SameLine
      (physicalWordAction codingPrime word
        (phaseAffine (privatePhase index 0)
          (prefixState codingPrime counter deleted))) endpoint) :
    ∃ loops suffix,
      loops < remaining ∧
      word = PrefixGuessModule.prefixTail (privatePhase index 0)
          (privatePhase index 1) loops ++ suffix ∧
      WordOver (edgeAlphabet index edge) suffix ∧
      AllStatesLocal codingPrime suffix
        (phaseAffine (privatePhase index 1)
          (T codingPrime
            (prefixState codingPrime counter (deleted + loops + 1)))) ∧
      SameLine
        (physicalWordAction codingPrime suffix
          (phaseAffine (privatePhase index 1)
            (T codingPrime
              (prefixState codingPrime counter (deleted + loops + 1)))))
        endpoint := by
  have layout := oddOccurrence_layout indexedMem instructionEq
  have guessBound := layout.guessBound
  induction remaining generalizing deleted word with
  | zero =>
      have deletedEq : deleted = counter := by omega
      have markerMembership : InPhaseAt codingPrime (privatePhase index 0) 1
          (phaseAffine (privatePhase index 0)
            (prefixState codingPrime counter deleted)) := by
        simpa only [deletedEq] using
          (prefixState_inPhaseAt_marker
            (base := codingPrime) (phase := privatePhase index 0)
            (counter := counter) codingPrime_isPrime.1)
      have wordNonempty : word ≠ [] := by
        intro wordEmpty
        subst word
        have phasesEq := (markerMembership.unique codingPrime_isPrime
          codingPrime_phase_bound guessBound endpointBound endpointMembership
          (by simpa [physicalWordAction] using completeRun)).1
        exact guessEndpointDistinct phasesEq
      cases word with
      | nil => exact False.elim (wordNonempty rfl)
      | cons letter tail =>
          have letterMem := wordOver letter (by simp)
          have moduleMem : letter ∈ OddHalvingModule.oddHalvingAlphabet
              (boundaryPhase edge.source) (boundaryPhase edge.target)
              (privatePhase index 0) (privatePhase index 1)
              (privatePhase index 2) (privatePhase index 3) := by
            simpa [edgeAlphabet_eq_odd instructionEq] using letterMem
          exact False.elim
            ((OddHalvingModule.guess_rejects_marker (counter := counter)
              codingPrime_isPrime codingPrime_phase_bound layout moduleMem)
              (by simpa only [deletedEq] using allLocal.2.start))
  | succ remaining inductionHypothesis =>
      have deletedBelow : deleted < counter := by omega
      have currentMembership := prefixState_inPhaseAt_before
        (base := codingPrime) (phase := privatePhase index 0)
        (counter := counter) (deleted := deleted) codingPrime_isPrime.1
        deletedBelow
      have wordNonempty : word ≠ [] := by
        intro wordEmpty
        subst word
        have phasesEq := (currentMembership.unique codingPrime_isPrime
          codingPrime_phase_bound guessBound endpointBound endpointMembership
          (by simpa [physicalWordAction] using completeRun)).1
        exact guessEndpointDistinct phasesEq
      cases word with
      | nil => exact False.elim (wordNonempty rfl)
      | cons letter tail =>
          have letterMem := wordOver letter (by simp)
          have tailOver : WordOver (edgeAlphabet index edge) tail := by
            intro candidate candidateMem
            exact wordOver candidate (by simp [candidateMem])
          have moduleMem : letter ∈ OddHalvingModule.oddHalvingAlphabet
              (boundaryPhase edge.source) (boundaryPhase edge.target)
              (privatePhase index 0) (privatePhase index 1)
              (privatePhase index 2) (privatePhase index 3) := by
            simpa [edgeAlphabet_eq_odd instructionEq] using letterMem
          rcases OddHalvingModule.guess_letter_before_marker
              codingPrime_isPrime codingPrime_phase_bound layout deletedBelow
              moduleMem allLocal.2.start with letterEq | letterEq
          · subst letter
            have firstStep := PrefixGuessModule.privateLoop_step codingPrime
              (privatePhase index 0) counter deleted codingPrime_isPrime.1
              deletedBelow
            have nextLocal := phasePrefixState_local codingPrime
              (privatePhase index 0) counter (deleted + 1)
              codingPrime_isPrime.1
            have tailLocal : AllStatesLocal codingPrime tail
                (phaseAffine (privatePhase index 0)
                  (prefixState codingPrime counter (deleted + 1))) := by
              apply AllStatesLocal.of_sameLine
                (primePositive := by have := codingPrime_isPrime.1; omega)
                allLocal.2 nextLocal.1 firstStep.symm
            have tailRun := physicalWordAction_tail_sameLine codingPrime
              (PrefixGuessModule.privateLoop (privatePhase index 0)) tail
              firstStep completeRun
            obtain ⟨loops, suffix, loopsBound, tailEq, suffixOver,
                suffixLocal, suffixRun⟩ :=
              inductionHypothesis (deleted := deleted + 1) (by omega)
                tailOver tailLocal tailRun
            refine ⟨loops + 1, suffix, by omega, ?_, suffixOver, ?_, ?_⟩
            · rw [tailEq]
              simp [PrefixGuessModule.prefixTail, List.replicate_succ]
            · simpa only [show deleted + 1 + loops + 1 =
                  deleted + (loops + 1) + 1 by omega] using suffixLocal
            · simpa only [show deleted + 1 + loops + 1 =
                  deleted + (loops + 1) + 1 by omega] using suffixRun
          · subst letter
            have firstStep := PrefixGuessModule.privateExit_step codingPrime
              (privatePhase index 0) (privatePhase index 1) counter deleted
              codingPrime_isPrime.1 deletedBelow
            have nextLocal := phaseTPrefixState_local codingPrime
              (privatePhase index 1) counter (deleted + 1)
              codingPrime_isPrime.1
            have tailLocal : AllStatesLocal codingPrime tail
                (phaseAffine (privatePhase index 1)
                  (T codingPrime
                    (prefixState codingPrime counter (deleted + 1)))) := by
              apply AllStatesLocal.of_sameLine
                (primePositive := by have := codingPrime_isPrime.1; omega)
                allLocal.2 nextLocal.1 firstStep.symm
            have tailRun := physicalWordAction_tail_sameLine codingPrime
              (PrefixGuessModule.privateExit (privatePhase index 0)
                (privatePhase index 1)) tail firstStep completeRun
            exact ⟨0, tail, by omega, by
                simp [PrefixGuessModule.prefixTail],
              tailOver, by simpa using tailLocal, by simpa using tailRun⟩

private theorem localPrefix_choice_to_endpoint
    {edge : Edge Nat} {index counter endpointPhase : Nat}
    {endpointDigit : Int} {endpoint : Vec2}
    (indexedMem : (edge, index) ∈ fixedProgram.edges.zipIdx)
    (instructionEq : edge.instruction = .divideTwoOdd)
    (endpointBound : endpointPhase < totalPhaseCount)
    (guessEndpointDistinct : privatePhase index 0 ≠ endpointPhase)
    (endpointMembership : InPhaseAt codingPrime endpointPhase endpointDigit
      endpoint)
    (counterPositive : 0 < counter)
    {word : List PhysicalTemplate}
    (wordOver : WordOver (edgeAlphabet index edge) word)
    (wordNonempty : word ≠ [])
    (allLocal : AllStatesLocal codingPrime word
      (phaseAffine (boundaryPhase edge.source)
        (unaryCode codingPrime counter)))
    (completeRun : SameLine
      (physicalWordAction codingPrime word
        (phaseAffine (boundaryPhase edge.source)
          (unaryCode codingPrime counter))) endpoint) :
    ∃ first guess suffix,
      0 < guess ∧ first + guess = counter ∧
      word = PrefixGuessModule.prefixWord (boundaryPhase edge.source)
          (privatePhase index 0) (privatePhase index 1) guess ++ suffix ∧
      WordOver (edgeAlphabet index edge) suffix ∧
      AllStatesLocal codingPrime suffix
        (phaseAffine (privatePhase index 1)
          (firstAutomaticState codingPrime first guess 0)) ∧
      SameLine
        (physicalWordAction codingPrime suffix
          (phaseAffine (privatePhase index 1)
            (firstAutomaticState codingPrime first guess 0))) endpoint := by
  have layout := oddOccurrence_layout indexedMem instructionEq
  obtain ⟨previous, counterEq⟩ :=
    Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt counterPositive)
  subst counter
  cases word with
  | nil => exact False.elim (wordNonempty rfl)
  | cons letter tail =>
      have letterMem := wordOver letter (by simp)
      have tailOver : WordOver (edgeAlphabet index edge) tail := by
        intro candidate candidateMem
        exact wordOver candidate (by simp [candidateMem])
      have moduleMem : letter ∈ OddHalvingModule.oddHalvingAlphabet
          (boundaryPhase edge.source) (boundaryPhase edge.target)
          (privatePhase index 0) (privatePhase index 1)
          (privatePhase index 2) (privatePhase index 3) := by
        simpa [edgeAlphabet_eq_odd instructionEq] using letterMem
      rcases OddHalvingModule.source_letter_positive
          (counter := previous) codingPrime_isPrime codingPrime_phase_bound
          layout moduleMem allLocal.2.start with letterEq | letterEq
      · subst letter
        have firstStep := PrefixGuessModule.startContinue_step codingPrime
          (boundaryPhase edge.source) (privatePhase index 0) (previous + 1)
          codingPrime_isPrime.1 (by omega)
        have nextLocal := phasePrefixState_local codingPrime
          (privatePhase index 0) (previous + 1) 1 codingPrime_isPrime.1
        have tailLocal : AllStatesLocal codingPrime tail
            (phaseAffine (privatePhase index 0)
              (prefixState codingPrime (previous + 1) 1)) := by
          apply AllStatesLocal.of_sameLine
            (primePositive := by have := codingPrime_isPrime.1; omega)
            allLocal.2 nextLocal.1 firstStep.symm
        have tailRun := physicalWordAction_tail_sameLine codingPrime
          (PrefixGuessModule.startContinue (boundaryPhase edge.source)
            (privatePhase index 0)) tail firstStep completeRun
        obtain ⟨loops, suffix, loopsBound, tailEq, suffixOver,
            suffixLocal, suffixRun⟩ :=
          localGuessTail_exit_to_endpoint indexedMem instructionEq
            endpointBound guessEndpointDistinct endpointMembership
            (counter := previous + 1) (deleted := 1)
            (remaining := previous) (by omega) tailOver tailLocal tailRun
        have splitEq :
            (previous - (loops + 1)) + (loops + 2) = previous + 1 := by
          omega
        refine ⟨previous - (loops + 1), loops + 2, suffix, by omega,
          splitEq, ?_, suffixOver, ?_, ?_⟩
        · rw [tailEq]
          simp [PrefixGuessModule.prefixWord,
            PrefixGuessModule.prefixTail]
        · rw [firstAutomaticState_zero codingPrime
            (previous - (loops + 1)) (loops + 2) codingPrime_isPrime.1]
          rw [splitEq]
          simpa only [show 1 + loops + 1 = loops + 2 by omega] using
            suffixLocal
        · rw [firstAutomaticState_zero codingPrime
            (previous - (loops + 1)) (loops + 2) codingPrime_isPrime.1]
          rw [splitEq]
          simpa only [show 1 + loops + 1 = loops + 2 by omega] using
            suffixRun
      · subst letter
        have firstStep := PrefixGuessModule.startExit_step codingPrime
          (boundaryPhase edge.source) (privatePhase index 1) (previous + 1)
          codingPrime_isPrime.1 (by omega)
        have nextLocal := phaseTPrefixState_local codingPrime
          (privatePhase index 1) (previous + 1) 1 codingPrime_isPrime.1
        have tailLocal : AllStatesLocal codingPrime tail
            (phaseAffine (privatePhase index 1)
              (T codingPrime (prefixState codingPrime (previous + 1) 1))) := by
          apply AllStatesLocal.of_sameLine
            (primePositive := by have := codingPrime_isPrime.1; omega)
            allLocal.2 nextLocal.1 firstStep.symm
        have tailRun := physicalWordAction_tail_sameLine codingPrime
          (PrefixGuessModule.startExit (boundaryPhase edge.source)
            (privatePhase index 1)) tail firstStep completeRun
        refine ⟨previous, 1, tail, by omega, by omega, by
            simp [PrefixGuessModule.prefixWord],
          tailOver, ?_, ?_⟩
        · rw [firstAutomaticState_zero codingPrime previous 1
            codingPrime_isPrime.1]
          simpa using tailLocal
        · rw [firstAutomaticState_zero codingPrime previous 1
            codingPrime_isPrime.1]
          simpa using tailRun

/-- Endpoint-aware parser for the three deterministic scans following the
prefix choice. -/
private theorem localAutomaticSuffix_to_endpoint
    {edge : Edge Nat} {index first guess endpointPhase : Nat}
    {endpointDigit : Int} {endpoint : Vec2}
    (indexedMem : (edge, index) ∈ fixedProgram.edges.zipIdx)
    (instructionEq : edge.instruction = .divideTwoOdd)
    (endpointBound : endpointPhase < totalPhaseCount)
    (firstEndpointDistinct : privatePhase index 1 ≠ endpointPhase)
    (secondEndpointDistinct : privatePhase index 2 ≠ endpointPhase)
    (validatorEndpointDistinct : privatePhase index 3 ≠ endpointPhase)
    (endpointMembership : InPhaseAt codingPrime endpointPhase endpointDigit
      endpoint)
    (guessPositive : 0 < guess)
    {word : List PhysicalTemplate}
    (wordOver : WordOver (edgeAlphabet index edge) word)
    (allLocal : AllStatesLocal codingPrime word
      (phaseAffine (privatePhase index 1)
        (firstAutomaticState codingPrime first guess 0)))
    (completeRun : SameLine
      (physicalWordAction codingPrime word
        (phaseAffine (privatePhase index 1)
          (firstAutomaticState codingPrime first guess 0))) endpoint) :
    ∃ suffix,
      first = guess - 1 ∧
      word = OddHalvingModule.firstScanWord (privatePhase index 1)
          (privatePhase index 2) first ++
        OddHalvingModule.secondScanWord (privatePhase index 2)
          (privatePhase index 3) first ++
        OddHalvingModule.validatorWord (privatePhase index 3)
          (boundaryPhase edge.target) first ++ suffix ∧
      WordOver (edgeAlphabet index edge) suffix ∧
      AllStatesLocal codingPrime suffix
        (phaseAffine (boundaryPhase edge.target)
          (unaryCode codingPrime first)) ∧
      SameLine
        (physicalWordAction codingPrime suffix
          (phaseAffine (boundaryPhase edge.target)
            (unaryCode codingPrime first))) endpoint := by
  have layout := oddOccurrence_layout indexedMem instructionEq
  have moduleMem : ∀ {letter}, letter ∈ edgeAlphabet index edge →
      letter ∈ OddHalvingModule.oddHalvingAlphabet
        (boundaryPhase edge.source) (boundaryPhase edge.target)
        (privatePhase index 0) (privatePhase index 1)
        (privatePhase index 2) (privatePhase index 3) := by
    intro letter letterMem
    simpa [edgeAlphabet_eq_odd instructionEq] using letterMem
  have firstParsed := forcedScanPrefixToEndpoint
    (Certificate := True) (primeProperty := codingPrime_isPrime)
    (primeBound := codingPrime_phase_bound)
    (alphabet := edgeAlphabet index edge)
    (loopLetter := OddHalvingModule.identityZero (privatePhase index 1))
    (exitLetter := OddHalvingModule.identityMarker (privatePhase index 1)
      (privatePhase index 2))
    (limit := first) (deleted := 0) (remaining := first)
    (state := fun position => phaseAffine (privatePhase index 1)
      (firstAutomaticState codingPrime first guess position))
    (markerDigit := 1)
    (next := phaseAffine (privatePhase index 2)
      (secondAutomaticState codingPrime first guess 0))
    (currentBound := layout.firstBound) (endpointBound := endpointBound)
    (phaseDistinct := firstEndpointDistinct)
    (endpointMembership := endpointMembership)
    (beforeMembership := fun position positionBelow =>
      firstAutomaticState_inPhaseAt_before
        (base := codingPrime) (phase := privatePhase index 1)
        (first := first) (guess := guess) (deleted := position)
        codingPrime_isPrime.1 positionBelow)
    (markerMembership := firstAutomaticState_inPhaseAt_marker
      (base := codingPrime) (phase := privatePhase index 1)
      (first := first) (guess := guess) codingPrime_isPrime.1)
    (stateLocal := fun position _ => OddHalvingModule.phaseLocal
      (firstAutomaticState_local codingPrime first guess position
        codingPrime_isPrime.1))
    (nextLocal := OddHalvingModule.phaseLocal
      (secondAutomaticState_local codingPrime first guess 0
        codingPrime_isPrime.1))
    (forceLoop := fun position positionBelow {letter} letterMem outputLocal =>
      OddHalvingModule.first_letter_before_marker
        (first := first) (guess := guess) (deleted := position)
        codingPrime_isPrime codingPrime_phase_bound layout.sourceBound
        layout.guessBound layout.firstBound layout.secondBound
        layout.validatorBound layout.sourceFirstDistinct.symm
        layout.guessFirstDistinct.symm layout.firstSecondDistinct
        layout.firstValidatorDistinct positionBelow (moduleMem letterMem)
        outputLocal)
    (forceExit := fun {letter} letterMem outputLocal =>
      ⟨True.intro, OddHalvingModule.first_letter_at_marker
        (first := first) (guess := guess) codingPrime_isPrime
        codingPrime_phase_bound layout.sourceBound layout.guessBound
        layout.firstBound layout.secondBound layout.validatorBound
        layout.sourceFirstDistinct.symm layout.guessFirstDistinct.symm
        layout.firstSecondDistinct layout.firstValidatorDistinct
        (moduleMem letterMem) outputLocal⟩)
    (loopStep := fun position positionBelow =>
      OddHalvingModule.firstZero_step codingPrime (privatePhase index 1)
        first guess position codingPrime_isPrime.1 positionBelow)
    (exitStep := fun _ => by
      simpa [secondAutomaticState_zero] using
        (OddHalvingModule.firstMarker_step codingPrime
          (privatePhase index 1) (privatePhase index 2) first guess
          codingPrime_isPrime.1))
    (sumEq := (by omega : 0 + first = first))
    (wordOver := wordOver) (allLocal := allLocal)
    (completeRun := completeRun)
  obtain ⟨afterFirst, _, firstEq, afterFirstOver, afterFirstLocal,
      afterFirstRun⟩ := firstParsed
  have secondParsed := forcedScanPrefixToEndpoint
    (Certificate := True) (primeProperty := codingPrime_isPrime)
    (primeBound := codingPrime_phase_bound)
    (alphabet := edgeAlphabet index edge)
    (loopLetter := OddHalvingModule.identityZero (privatePhase index 2))
    (exitLetter := OddHalvingModule.inverseTMarker (privatePhase index 2)
      (privatePhase index 3))
    (limit := first) (deleted := 0) (remaining := first)
    (state := fun position => phaseAffine (privatePhase index 2)
      (secondAutomaticState codingPrime first guess position))
    (markerDigit := 1)
    (next := phaseAffine (privatePhase index 3)
      (validatorState codingPrime first guess 0))
    (currentBound := layout.secondBound) (endpointBound := endpointBound)
    (phaseDistinct := secondEndpointDistinct)
    (endpointMembership := endpointMembership)
    (beforeMembership := fun position positionBelow =>
      secondAutomaticState_inPhaseAt_before
        (base := codingPrime) (phase := privatePhase index 2)
        (first := first) (guess := guess) (deleted := position)
        codingPrime_isPrime.1 positionBelow)
    (markerMembership := secondAutomaticState_inPhaseAt_marker
      (base := codingPrime) (phase := privatePhase index 2)
      (first := first) (guess := guess) codingPrime_isPrime.1 guessPositive)
    (stateLocal := fun position _ => OddHalvingModule.phaseLocal
      (secondAutomaticState_local codingPrime first guess position
        codingPrime_isPrime.1))
    (nextLocal := OddHalvingModule.phaseLocal
      (validatorState_local codingPrime first guess 0 codingPrime_isPrime.1
        guessPositive))
    (forceLoop := fun position positionBelow {letter} letterMem outputLocal =>
      OddHalvingModule.second_letter_before_marker
        (first := first) (guess := guess) (deleted := position)
        codingPrime_isPrime codingPrime_phase_bound layout.sourceBound
        layout.guessBound layout.firstBound layout.secondBound
        layout.validatorBound layout.sourceSecondDistinct.symm
        layout.guessSecondDistinct.symm layout.firstSecondDistinct.symm
        layout.secondValidatorDistinct positionBelow (moduleMem letterMem)
        outputLocal)
    (forceExit := fun {letter} letterMem outputLocal =>
      ⟨True.intro, OddHalvingModule.second_letter_at_marker
        (first := first) (guess := guess) codingPrime_isPrime
        codingPrime_phase_bound guessPositive layout.sourceBound
        layout.guessBound layout.firstBound layout.secondBound
        layout.validatorBound layout.sourceSecondDistinct.symm
        layout.guessSecondDistinct.symm layout.firstSecondDistinct.symm
        layout.secondValidatorDistinct (moduleMem letterMem) outputLocal⟩)
    (loopStep := fun position positionBelow =>
      OddHalvingModule.secondZero_step codingPrime (privatePhase index 2)
        first guess position codingPrime_isPrime.1 positionBelow)
    (exitStep := fun _ => by
      simpa [validatorState_zero] using
        (OddHalvingModule.secondMarker_step codingPrime
          (privatePhase index 2) (privatePhase index 3) first guess
          codingPrime_isPrime.1 guessPositive))
    (sumEq := (by omega : 0 + first = first))
    (wordOver := afterFirstOver) (allLocal := afterFirstLocal)
    (completeRun := afterFirstRun)
  obtain ⟨afterSecond, _, secondEq, afterSecondOver, afterSecondLocal,
      afterSecondRun⟩ := secondParsed
  have validatorParsed := forcedScanPrefixToEndpoint
    (Certificate := first = guess - 1)
    (primeProperty := codingPrime_isPrime)
    (primeBound := codingPrime_phase_bound)
    (alphabet := edgeAlphabet index edge)
    (loopLetter := OddHalvingModule.identityZero (privatePhase index 3))
    (exitLetter := OddHalvingModule.validatorMarker (privatePhase index 3)
      (boundaryPhase edge.target))
    (limit := validatorLength first guess) (deleted := 0)
    (remaining := validatorLength first guess)
    (state := fun position => phaseAffine (privatePhase index 3)
      (validatorState codingPrime first guess position))
    (markerDigit := validatorMarkerDigit first guess)
    (next := phaseAffine (boundaryPhase edge.target)
      (unaryCode codingPrime first))
    (currentBound := layout.validatorBound) (endpointBound := endpointBound)
    (phaseDistinct := validatorEndpointDistinct)
    (endpointMembership := endpointMembership)
    (beforeMembership := fun position positionBelow =>
      validatorState_inPhaseAt_before
        (base := codingPrime) (phase := privatePhase index 3)
        (first := first) (guess := guess) (deleted := position)
        codingPrime_isPrime.1 guessPositive positionBelow)
    (markerMembership := validatorState_inPhaseAt_marker
      (base := codingPrime) (phase := privatePhase index 3)
      (first := first) (guess := guess) codingPrime_isPrime.1 guessPositive)
    (stateLocal := fun position _ => OddHalvingModule.phaseLocal
      (validatorState_local codingPrime first guess position
        codingPrime_isPrime.1 guessPositive))
    (nextLocal := IncrementModule.phaseUnaryCode_local codingPrime
      (boundaryPhase edge.target) first codingPrime_isPrime.1)
    (forceLoop := fun position positionBelow {letter} letterMem outputLocal =>
      OddHalvingModule.validator_letter_before_marker
        (first := first) (guess := guess) (deleted := position)
        codingPrime_isPrime codingPrime_phase_bound guessPositive
        layout.sourceBound layout.guessBound layout.firstBound
        layout.secondBound layout.validatorBound
        layout.sourceValidatorDistinct.symm
        layout.guessValidatorDistinct.symm
        layout.firstValidatorDistinct.symm
        layout.secondValidatorDistinct.symm positionBelow
        (moduleMem letterMem) outputLocal)
    (forceExit := fun {letter} letterMem outputLocal =>
      OddHalvingModule.validator_letter_at_marker
        (first := first) (guess := guess) codingPrime_isPrime
        codingPrime_phase_bound guessPositive layout.sourceBound
        layout.guessBound layout.firstBound layout.secondBound
        layout.validatorBound layout.sourceValidatorDistinct.symm
        layout.guessValidatorDistinct.symm
        layout.firstValidatorDistinct.symm
        layout.secondValidatorDistinct.symm (moduleMem letterMem) outputLocal)
    (loopStep := fun position positionBelow =>
      OddHalvingModule.validatorZero_step codingPrime (privatePhase index 3)
        first guess position codingPrime_isPrime.1 guessPositive positionBelow)
    (exitStep := fun accepted => by
      have guessEq : guess = first + 1 := by omega
      subst guess
      simpa [validatorLength] using
        (OddHalvingModule.validatorMarker_step codingPrime
          (privatePhase index 3) (boundaryPhase edge.target) first
          codingPrime_isPrime.1))
    (sumEq := (by omega : 0 + validatorLength first guess =
      validatorLength first guess))
    (wordOver := afterSecondOver) (allLocal := afterSecondLocal)
    (completeRun := afterSecondRun)
  obtain ⟨suffix, accepted, validatorEq, suffixOver, suffixLocal,
      suffixRun⟩ := validatorParsed
  refine ⟨suffix, accepted, ?_, suffixOver, suffixLocal, suffixRun⟩
  rw [firstEq, secondEq, validatorEq]
  simp [OddHalvingModule.firstScanWord, OddHalvingModule.secondScanWord,
    OddHalvingModule.validatorWord, validatorLength, accepted,
    List.append_assoc]

private theorem localOddHalvingWord_forced_to_endpoint
    {edge : Edge Nat} {index counter endpointPhase : Nat}
    {endpointDigit : Int} {endpoint : Vec2}
    (indexedMem : (edge, index) ∈ fixedProgram.edges.zipIdx)
    (instructionEq : edge.instruction = .divideTwoOdd)
    (endpointBound : endpointPhase < totalPhaseCount)
    (privateEndpointDistinct : ∀ offset, offset < 4 →
      privatePhase index offset ≠ endpointPhase)
    (endpointMembership : InPhaseAt codingPrime endpointPhase endpointDigit
      endpoint)
    {word : List PhysicalTemplate}
    (wordOver : WordOver (edgeAlphabet index edge) word)
    (wordNonempty : word ≠ [])
    (allLocal : AllStatesLocal codingPrime word
      (phaseAffine (boundaryPhase edge.source)
        (unaryCode codingPrime counter)))
    (completeRun : SameLine
      (physicalWordAction codingPrime word
        (phaseAffine (boundaryPhase edge.source)
          (unaryCode codingPrime counter))) endpoint) :
    ∃ output suffix,
      counter = 2 * output + 1 ∧
      word = FixedForward.edgeWord index edge counter output ++ suffix ∧
      WordOver (edgeAlphabet index edge) suffix ∧
      AllStatesLocal codingPrime suffix
        (phaseAffine (boundaryPhase edge.target)
          (unaryCode codingPrime output)) ∧
      SameLine
        (physicalWordAction codingPrime suffix
          (phaseAffine (boundaryPhase edge.target)
            (unaryCode codingPrime output))) endpoint := by
  have layout := oddOccurrence_layout indexedMem instructionEq
  have counterPositive : 0 < counter := by
    cases counter with
    | zero =>
        cases word with
        | nil => exact False.elim (wordNonempty rfl)
        | cons letter tail =>
            have letterMem := wordOver letter (by simp)
            have moduleMem : letter ∈ OddHalvingModule.oddHalvingAlphabet
                (boundaryPhase edge.source) (boundaryPhase edge.target)
                (privatePhase index 0) (privatePhase index 1)
                (privatePhase index 2) (privatePhase index 3) := by
              simpa [edgeAlphabet_eq_odd instructionEq] using letterMem
            exact False.elim
              ((OddHalvingModule.source_rejects_zero codingPrime_isPrime
                codingPrime_phase_bound layout moduleMem) allLocal.2.start)
    | succ previous => omega
  obtain ⟨first, guess, afterPrefix, guessPositive, splitEq, wordEq,
      afterPrefixOver, afterPrefixLocal, afterPrefixRun⟩ :=
    localPrefix_choice_to_endpoint indexedMem instructionEq endpointBound
      (privateEndpointDistinct 0 (by omega)) endpointMembership
      counterPositive wordOver wordNonempty allLocal completeRun
  obtain ⟨suffix, accepted, automaticEq, suffixOver, suffixLocal,
      suffixRun⟩ :=
    localAutomaticSuffix_to_endpoint indexedMem instructionEq endpointBound
      (privateEndpointDistinct 1 (by omega))
      (privateEndpointDistinct 2 (by omega))
      (privateEndpointDistinct 3 (by omega)) endpointMembership guessPositive
      afterPrefixOver afterPrefixLocal afterPrefixRun
  have counterEq : counter = 2 * first + 1 := by omega
  refine ⟨first, suffix, counterEq, ?_, suffixOver, suffixLocal, suffixRun⟩
  rw [wordEq, automaticEq]
  have guessEq : guess = first + 1 := by omega
  rw [guessEq]
  simp [FixedForward.edgeWord, instructionEq,
    OddHalvingModule.oddHalvingWord, List.append_assoc]

/-- Extract one odd-halving block from an arbitrary globally surviving word
and return the residual word at the halved counter. -/
theorem globalOddHalving_split
    {edge : Edge Nat} {index counter finalState finalCounter : Nat}
    (indexedMem : (edge, index) ∈ fixedProgram.edges.zipIdx)
    (instructionEq : edge.instruction = .divideTwoOdd)
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
          (unaryCode codingPrime finalCounter)) := by
  have localListed : ∀ {candidate},
      candidate ∈ edgeAlphabet index edge → candidate ∈ listedTemplates :=
    fun candidateMem => edgeLetter_listed indexedMem candidateMem
  obtain ⟨finalDigit, finalMembership⟩ := unaryCode_inPhaseAt
    (base := codingPrime) (phase := boundaryPhase finalState)
    (counter := finalCounter) codingPrime_isPrime.1
  rcases split_first_outside localListed globalOver with localOnly |
      ⟨initial, foreign, rest, wordEq, initialOver, foreignGlobal,
        foreignNotLocal, restGlobal⟩
  · have endpointBound : boundaryPhase finalState < totalPhaseCount := by
      have denseBound := boundaryPhase_bound finalStateMem
      have boundariesFit : SourceMachine.quotientStates.length ≤
          genuinePhaseBound := by decide
      unfold totalPhaseCount
      omega
    have privateDistinct : ∀ offset, offset < 4 →
        privatePhase index offset ≠ boundaryPhase finalState := by
      intro offset offsetBound
      exact (boundary_ne_private finalStateMem indexedMem
        (oddPrivate_inBlock (index := index) instructionEq offsetBound)).symm
    obtain ⟨output, suffix, counterEq, wordEq, suffixOver, suffixLocal,
        suffixRun⟩ :=
      localOddHalvingWord_forced_to_endpoint indexedMem instructionEq
        endpointBound privateDistinct finalMembership localOnly (by simp)
        allLocal completeRun
    refine ⟨output, suffix, ?_, wordEq, ?_, suffixLocal, suffixRun⟩
    · simpa [instructionEq] using
        (Instruction.evaluate_divideTwoOdd_iff.mpr counterEq)
    · exact suffixOver.mono (fun _ candidateMem =>
        edgeLetter_listed indexedMem candidateMem)
  · have splitLocal := allLocal.split_append_cons wordEq
    have initialLocal := splitLocal.1
    have foreignTailLocal := splitLocal.2
    have foreignGuard := listedLetter_guard foreignGlobal
    have foreignMembership : InPhaseAt codingPrime foreign.sourcePhase
        foreign.digit
        (physicalWordAction codingPrime initial
          (phaseAffine (boundaryPhase edge.source)
            (unaryCode codingPrime counter))) := by
      apply physicalLetter_input_inPhaseAt codingPrime_isPrime
        foreignGuard.2.2 foreignTailLocal.1
      simpa [PhysicalTemplate.act, PhysicalTemplate.matrix] using
        foreignTailLocal.2.start
    have endpointBound : foreign.sourcePhase < totalPhaseCount := by
      have genuineBound := foreignGuard.1
      unfold totalPhaseCount
      omega
    have privateDistinct : ∀ offset, offset < 4 →
        privatePhase index offset ≠ foreign.sourcePhase := by
      intro offset offsetBound phaseEq
      have membershipAtPrivate : InPhaseAt codingPrime
          (privatePhase index offset) foreign.digit
          (physicalWordAction codingPrime initial
            (phaseAffine (boundaryPhase edge.source)
              (unaryCode codingPrime counter))) := by
        simpa [phaseEq] using foreignMembership
      have localMem := survivingListedLetter_at_private indexedMem
        (oddPrivate_inBlock (index := index) instructionEq offsetBound)
        membershipAtPrivate foreignGlobal foreignTailLocal.2.start
      exact foreignNotLocal localMem
    have initialNonempty : initial ≠ [] := by
      intro initialEmpty
      subst initial
      simp only [List.nil_append, List.cons.injEq] at wordEq
      exact foreignNotLocal (wordEq.1 ▸ letterLocal)
    obtain ⟨output, localSuffix, counterEq, initialEq, localSuffixOver,
        localSuffixLocal, localSuffixRun⟩ :=
      localOddHalvingWord_forced_to_endpoint indexedMem instructionEq
        endpointBound privateDistinct foreignMembership initialOver
        initialNonempty initialLocal (SameLine.refl _)
    have localSuffixGlobal : WordOver listedTemplates localSuffix :=
      localSuffixOver.mono (fun _ candidateMem =>
        edgeLetter_listed indexedMem candidateMem)
    have residualGlobal : WordOver listedTemplates
        (localSuffix ++ foreign :: rest) :=
      wordOver_append localSuffixGlobal (wordOver_cons foreignGlobal restGlobal)
    have targetNonzero :
        (phaseAffine (boundaryPhase edge.target)
          (unaryCode codingPrime output)).Nonzero := Vec2.affine_nonzero _
    have afterLocalSuffixNonzero := physicalWordAction_nonzero
      (prime := codingPrime) (by have := codingPrime_isPrime.1; omega)
      localSuffix targetNonzero
    have foreignTailCanonical : AllStatesLocal codingPrime (foreign :: rest)
        (physicalWordAction codingPrime localSuffix
          (phaseAffine (boundaryPhase edge.target)
            (unaryCode codingPrime output))) := by
      apply AllStatesLocal.of_sameLine
        (primePositive := by have := codingPrime_isPrime.1; omega)
        foreignTailLocal afterLocalSuffixNonzero localSuffixRun
    have residualLocal : AllStatesLocal codingPrime
        (localSuffix ++ foreign :: rest)
        (phaseAffine (boundaryPhase edge.target)
          (unaryCode codingPrime output)) :=
      localSuffixLocal.append foreignTailCanonical
    have residualRunRaw : SameLine
        (physicalWordAction codingPrime (foreign :: rest)
          (physicalWordAction codingPrime initial
            (phaseAffine (boundaryPhase edge.source)
              (unaryCode codingPrime counter))))
        (phaseAffine (boundaryPhase finalState)
          (unaryCode codingPrime finalCounter)) := by
      rw [wordEq, physicalWordAction_append] at completeRun
      exact completeRun
    have afterSuffixRun : SameLine
        (physicalWordAction codingPrime (foreign :: rest)
          (physicalWordAction codingPrime localSuffix
            (phaseAffine (boundaryPhase edge.target)
              (unaryCode codingPrime output))))
        (physicalWordAction codingPrime (foreign :: rest)
          (physicalWordAction codingPrime initial
            (phaseAffine (boundaryPhase edge.source)
              (unaryCode codingPrime counter)))) :=
      physicalWordAction_preserves_sameLine codingPrime (foreign :: rest)
        localSuffixRun
    have residualRun : SameLine
        (physicalWordAction codingPrime (localSuffix ++ foreign :: rest)
          (phaseAffine (boundaryPhase edge.target)
            (unaryCode codingPrime output)))
        (phaseAffine (boundaryPhase finalState)
          (unaryCode codingPrime finalCounter)) := by
      rw [physicalWordAction_append]
      exact afterSuffixRun.trans residualRunRaw
    refine ⟨output, localSuffix ++ foreign :: rest,
      (by simpa [instructionEq] using
        (Instruction.evaluate_divideTwoOdd_iff.mpr counterEq)), ?_,
      residualGlobal, residualLocal, residualRun⟩
    rw [wordEq, initialEq, List.append_assoc]

end Mortality.Compiler.GlobalOddHalving
