import Mortality.Compiler.AllocationProperties
import Mortality.Compiler.FixedForward
import Mortality.Compiler.GlobalParserBasics

/-!
# Lifting the increment converse to the global alphabet

This is the first instruction-level use of private-block ownership.  Even
though an ambient word may use any of the 5,798 templates, once its first
letter chooses an increment occurrence, every locally surviving private
scan letter is forced back into that occurrence's four-letter alphabet.
-/

namespace Mortality.Compiler.GlobalIncrement

open Mortality
open Mortality.OneCounter
open Mortality.PeriodicCode
open Mortality.Compiler
open Mortality.Compiler.FixedAllocation
open Mortality.Compiler.AllocationProperties
open Mortality.Compiler.GlobalParserBasics
open Mortality.Compiler.UnaryArithmetic

set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

theorem incrementPrivate_inBlock
    {edge : Edge Nat} {index : Nat}
    (instructionEq : edge.instruction = .increment) :
    InPrivateBlock index edge (privatePhase index 0) := by
  simp [InPrivateBlock, privatePhase, instructionEq,
    instructionPrivateCost, cleanupCost]

private theorem incrementOccurrence_bounds
    {edge : Edge Nat} {index : Nat}
    (indexedMem : (edge, index) ∈ fixedProgram.edges.zipIdx)
    (instructionEq : edge.instruction = .increment) :
    boundaryPhase edge.source < totalPhaseCount ∧
      privatePhase index 0 < totalPhaseCount ∧
      boundaryPhase edge.source ≠ privatePhase index 0 := by
  have sourceMem := (fixedEdge_endpoints_mem (indexedEdge_mem indexedMem)).1
  have sourceBound := boundaryPhase_bound sourceMem
  have boundariesFit : SourceMachine.quotientStates.length ≤
      genuinePhaseBound := by decide
  have privateIn := incrementPrivate_inBlock (index := index) instructionEq
  have privateBound := privateBlock_bounded indexedMem privateIn
  have distinct := boundary_ne_private sourceMem indexedMem privateIn
  unfold totalPhaseCount
  exact ⟨by omega, by omega, distinct⟩

private theorem edgeAlphabet_eq_increment
    {edge : Edge Nat} {index : Nat}
    (instructionEq : edge.instruction = .increment) :
    edgeAlphabet index edge =
      IncrementModule.incrementAlphabet codingPrime
        (boundaryPhase edge.source) (boundaryPhase edge.target)
        (privatePhase index 0) := by
  simp [edgeAlphabet, instructionEq]

/-- A sufficiently long ambient tail starting inside an increment-private
phase uses only that occurrence's alphabet for the complete remaining scan. -/
theorem globalIncrementTail_wordOver
    {edge : Edge Nat} {index deleted remaining : Nat}
    (indexedMem : (edge, index) ∈ fixedProgram.edges.zipIdx)
    (instructionEq : edge.instruction = .increment)
    {word : List PhysicalTemplate}
    (globalOver : WordOver listedTemplates word)
    (allLocal : AllStatesLocal codingPrime word
      (phaseAffine (privatePhase index 0)
        (incrementState codingPrime
          (deleted + remaining) deleted)))
    (longEnough : remaining + 1 ≤ word.length) :
    WordOver (edgeAlphabet index edge) (word.take (remaining + 1)) := by
  have bounds := incrementOccurrence_bounds indexedMem instructionEq
  have privateIn := incrementPrivate_inBlock (index := index) instructionEq
  induction remaining generalizing deleted word with
  | zero =>
      cases word with
      | nil => simp at longEnough
      | cons letter tail =>
          have letterGlobal := globalOver letter (by simp)
          have actualMembership :=
            IncrementModule.incrementState_inPhaseAt_marker
              (base := codingPrime) (phase := privatePhase index 0)
              (counter := deleted) codingPrime_isPrime.1
          have letterLocal := survivingListedLetter_at_private indexedMem
            privateIn actualMembership letterGlobal allLocal.2.start
          simpa using
            (wordOver_cons letterLocal (wordOver_nil (edgeAlphabet index edge)))
  | succ remaining inductionHypothesis =>
      cases word with
      | nil => simp at longEnough
      | cons letter tail =>
          have letterGlobal := globalOver letter (by simp)
          have tailGlobal : WordOver listedTemplates tail := by
            intro candidate candidateMem
            exact globalOver candidate (by simp [candidateMem])
          have actualMembership :=
            IncrementModule.incrementState_inPhaseAt_before
              (base := codingPrime) (phase := privatePhase index 0)
              (counter := deleted + (remaining + 1)) (deleted := deleted)
              codingPrime_isPrime.1 (by omega)
          have letterLocal := survivingListedLetter_at_private indexedMem
            privateIn actualMembership letterGlobal allLocal.2.start
          have localAlphabetMem : letter ∈
              IncrementModule.incrementAlphabet codingPrime
                (boundaryPhase edge.source) (boundaryPhase edge.target)
                (privatePhase index 0) := by
            simpa [edgeAlphabet_eq_increment instructionEq] using letterLocal
          have letterEq := IncrementModule.private_letter_before_marker
            codingPrime_isPrime codingPrime_phase_bound bounds.1 bounds.2.1
            bounds.2.2 (by omega) localAlphabetMem allLocal.2.start
          subst letter
          have firstStep := IncrementModule.loopZero_step codingPrime
            (privatePhase index 0) (deleted + (remaining + 1)) deleted
            codingPrime_isPrime.1 (by omega)
          have canonicalLocal := IncrementModule.phaseIncrementState_local
            codingPrime (privatePhase index 0) ((deleted + 1) + remaining)
            (deleted + 1) codingPrime_isPrime.1
          have tailLocal : AllStatesLocal codingPrime tail
              (phaseAffine (privatePhase index 0)
                (incrementState codingPrime
                  ((deleted + 1) + remaining) (deleted + 1))) := by
            apply AllStatesLocal.of_sameLine
              (primePositive := by have := codingPrime_isPrime.1; omega)
              allLocal.2 canonicalLocal.1
            simpa only [show deleted + (remaining + 1) =
                (deleted + 1) + remaining by omega] using firstStep.symm
          have tailLong : remaining + 1 ≤ tail.length := by
            simpa using longEnough
          have tailOver := inductionHypothesis (deleted := deleted + 1)
            tailGlobal tailLocal tailLong
          simpa using (wordOver_cons letterLocal tailOver)

/-- Global-alphabet increment converse.  Once the first letter has selected
this occurrence, the complete `counter + 1`-letter prefix is the literal
accepted increment word. -/
theorem globalIncrementWord_forced_prefix
    {edge : Edge Nat} {index counter : Nat}
    (indexedMem : (edge, index) ∈ fixedProgram.edges.zipIdx)
    (instructionEq : edge.instruction = .increment)
    {letter : PhysicalTemplate} {tail : List PhysicalTemplate}
    (globalOver : WordOver listedTemplates (letter :: tail))
    (letterLocal : letter ∈ edgeAlphabet index edge)
    (allLocal : AllStatesLocal codingPrime (letter :: tail)
      (phaseAffine (boundaryPhase edge.source)
        (unaryCode codingPrime counter)))
    (longEnough : counter + 1 ≤ (letter :: tail).length) :
    (letter :: tail).take (counter + 1) =
      FixedForward.edgeWord index edge counter (counter + 1) := by
  have bounds := incrementOccurrence_bounds indexedMem instructionEq
  have localAlphabetMem : letter ∈
      IncrementModule.incrementAlphabet codingPrime
        (boundaryPhase edge.source) (boundaryPhase edge.target)
        (privatePhase index 0) := by
    simpa [edgeAlphabet_eq_increment instructionEq] using letterLocal
  cases counter with
  | zero =>
      have letterEq := IncrementModule.first_letter_at_zero
        codingPrime_isPrime codingPrime_phase_bound bounds.1 bounds.2.1
        bounds.2.2 localAlphabetMem allLocal.2.start
      subst letter
      simp [FixedForward.edgeWord, instructionEq,
        IncrementModule.incrementWord]
  | succ previous =>
      have letterEq := IncrementModule.first_letter_at_positive
        (counter := previous) codingPrime_isPrime codingPrime_phase_bound
        bounds.1 bounds.2.1 bounds.2.2 localAlphabetMem allLocal.2.start
      subst letter
      have firstStep := IncrementModule.entryZero_step codingPrime
        (boundaryPhase edge.source) (privatePhase index 0) (previous + 1)
        codingPrime_isPrime.1 (by omega)
      have canonicalLocal := IncrementModule.phaseIncrementState_local
        codingPrime (privatePhase index 0) (1 + previous) 1
        codingPrime_isPrime.1
      have tailLocal : AllStatesLocal codingPrime tail
          (phaseAffine (privatePhase index 0)
            (incrementState codingPrime (1 + previous) 1)) := by
        apply AllStatesLocal.of_sameLine
          (primePositive := by have := codingPrime_isPrime.1; omega)
          allLocal.2 canonicalLocal.1
        simpa only [show previous + 1 = 1 + previous by omega] using
          firstStep.symm
      have tailGlobal : WordOver listedTemplates tail := by
        intro candidate candidateMem
        exact globalOver candidate (by simp [candidateMem])
      have tailLong : previous + 1 ≤ tail.length := by
        simpa using longEnough
      have tailOver := globalIncrementTail_wordOver indexedMem instructionEq
        (deleted := 1) (remaining := previous) tailGlobal tailLocal tailLong
      have prefixOver : WordOver (edgeAlphabet index edge)
          ((IncrementModule.entryZero codingPrime (boundaryPhase edge.source)
              (privatePhase index 0) :: tail).take (previous + 2)) := by
        simpa using (wordOver_cons letterLocal tailOver)
      have prefixLocal := allLocal.take (previous + 2)
      have prefixLength :
          ((IncrementModule.entryZero codingPrime (boundaryPhase edge.source)
            (privatePhase index 0) :: tail).take (previous + 2)).length =
            previous + 2 := by
        rw [List.length_take, Nat.min_eq_left longEnough]
      have exactWord := IncrementModule.incrementWord_surviving_unique
        codingPrime_isPrime codingPrime_phase_bound bounds.1 bounds.2.1
        bounds.2.2
        (by simpa [edgeAlphabet_eq_increment instructionEq] using prefixOver)
        prefixLocal prefixLength
      simpa [FixedForward.edgeWord, instructionEq] using exactWord

/-- Endpoint-aware parser for the private part of one local increment word.
Unlike the fixed-clock converse, it returns every unconsumed local letter
after the marker exit. -/
private theorem incrementTail_forced_to_endpoint
    {edge : Edge Nat} {index deleted remaining endpointPhase : Nat}
    {endpointDigit : Int} {endpoint : Vec2}
    (indexedMem : (edge, index) ∈ fixedProgram.edges.zipIdx)
    (instructionEq : edge.instruction = .increment)
    (endpointBound : endpointPhase < totalPhaseCount)
    (privateEndpointDistinct : privatePhase index 0 ≠ endpointPhase)
    (endpointMembership : InPhaseAt codingPrime endpointPhase endpointDigit
      endpoint)
    {word : List PhysicalTemplate}
    (wordOver : WordOver (edgeAlphabet index edge) word)
    (allLocal : AllStatesLocal codingPrime word
      (phaseAffine (privatePhase index 0)
        (incrementState codingPrime (deleted + remaining) deleted)))
    (completeRun : SameLine
      (physicalWordAction codingPrime word
        (phaseAffine (privatePhase index 0)
          (incrementState codingPrime (deleted + remaining) deleted)))
      endpoint) :
    ∃ suffix,
      word = IncrementModule.incrementTail (privatePhase index 0)
          (boundaryPhase edge.target) remaining ++ suffix ∧
      WordOver (edgeAlphabet index edge) suffix ∧
      AllStatesLocal codingPrime suffix
        (phaseAffine (boundaryPhase edge.target)
          (unaryCode codingPrime (deleted + remaining + 1))) ∧
      SameLine
        (physicalWordAction codingPrime suffix
          (phaseAffine (boundaryPhase edge.target)
            (unaryCode codingPrime (deleted + remaining + 1)))) endpoint := by
  have bounds := incrementOccurrence_bounds indexedMem instructionEq
  induction remaining generalizing deleted word with
  | zero =>
      have actualMembership :=
        IncrementModule.incrementState_inPhaseAt_marker
          (base := codingPrime) (phase := privatePhase index 0)
          (counter := deleted) codingPrime_isPrime.1
      have wordNonempty : word ≠ [] := by
        intro wordEmpty
        subst word
        have phasesEq := (actualMembership.unique codingPrime_isPrime
          codingPrime_phase_bound bounds.2.1 endpointBound endpointMembership
          (by simpa [physicalWordAction] using completeRun)).1
        exact privateEndpointDistinct phasesEq
      cases word with
      | nil => exact False.elim (wordNonempty rfl)
      | cons letter tail =>
          have letterMem := wordOver letter (by simp)
          have tailOver : WordOver (edgeAlphabet index edge) tail := by
            intro candidate candidateMem
            exact wordOver candidate (by simp [candidateMem])
          have moduleMem : letter ∈ IncrementModule.incrementAlphabet
              codingPrime (boundaryPhase edge.source)
              (boundaryPhase edge.target) (privatePhase index 0) := by
            simpa [edgeAlphabet_eq_increment instructionEq] using letterMem
          have classified := IncrementModule.private_letter_at_marker
            (counter := deleted) codingPrime_isPrime codingPrime_phase_bound
            bounds.1 bounds.2.1 bounds.2.2 moduleMem allLocal.2.start
          subst letter
          have firstStep := IncrementModule.exitMarker_step codingPrime
            (privatePhase index 0) (boundaryPhase edge.target) deleted
            codingPrime_isPrime.1
          have targetLocal := IncrementModule.phaseUnaryCode_local codingPrime
            (boundaryPhase edge.target) (deleted + 1) codingPrime_isPrime.1
          have tailLocal : AllStatesLocal codingPrime tail
              (phaseAffine (boundaryPhase edge.target)
                (unaryCode codingPrime (deleted + 1))) := by
            apply AllStatesLocal.of_sameLine
              (primePositive := by have := codingPrime_isPrime.1; omega)
              allLocal.2 targetLocal.1 firstStep.symm
          have tailRun := physicalWordAction_tail_sameLine codingPrime
            (IncrementModule.exitMarker (privatePhase index 0)
              (boundaryPhase edge.target)) tail firstStep completeRun
          exact ⟨tail, by simp [IncrementModule.incrementTail], tailOver,
            by simpa using tailLocal, by simpa using tailRun⟩
  | succ remaining inductionHypothesis =>
      have actualMembership :=
        IncrementModule.incrementState_inPhaseAt_before
          (base := codingPrime) (phase := privatePhase index 0)
          (counter := deleted + (remaining + 1)) (deleted := deleted)
          codingPrime_isPrime.1 (by omega)
      have wordNonempty : word ≠ [] := by
        intro wordEmpty
        subst word
        have phasesEq := (actualMembership.unique codingPrime_isPrime
          codingPrime_phase_bound bounds.2.1 endpointBound endpointMembership
          (by simpa [physicalWordAction] using completeRun)).1
        exact privateEndpointDistinct phasesEq
      cases word with
      | nil => exact False.elim (wordNonempty rfl)
      | cons letter tail =>
          have letterMem := wordOver letter (by simp)
          have tailOver : WordOver (edgeAlphabet index edge) tail := by
            intro candidate candidateMem
            exact wordOver candidate (by simp [candidateMem])
          have moduleMem : letter ∈ IncrementModule.incrementAlphabet
              codingPrime (boundaryPhase edge.source)
              (boundaryPhase edge.target) (privatePhase index 0) := by
            simpa [edgeAlphabet_eq_increment instructionEq] using letterMem
          have letterEq := IncrementModule.private_letter_before_marker
            codingPrime_isPrime codingPrime_phase_bound bounds.1 bounds.2.1
            bounds.2.2 (by omega) moduleMem allLocal.2.start
          subst letter
          have firstStep := IncrementModule.loopZero_step codingPrime
            (privatePhase index 0) (deleted + (remaining + 1)) deleted
            codingPrime_isPrime.1 (by omega)
          have canonicalLocal := IncrementModule.phaseIncrementState_local
            codingPrime (privatePhase index 0) ((deleted + 1) + remaining)
            (deleted + 1) codingPrime_isPrime.1
          have tailLocal : AllStatesLocal codingPrime tail
              (phaseAffine (privatePhase index 0)
                (incrementState codingPrime ((deleted + 1) + remaining)
                  (deleted + 1))) := by
            apply AllStatesLocal.of_sameLine
              (primePositive := by have := codingPrime_isPrime.1; omega)
              allLocal.2 canonicalLocal.1
            simpa only [show deleted + (remaining + 1) =
                (deleted + 1) + remaining by omega] using firstStep.symm
          have tailRun : SameLine
              (physicalWordAction codingPrime tail
                (phaseAffine (privatePhase index 0)
                  (incrementState codingPrime ((deleted + 1) + remaining)
                    (deleted + 1)))) endpoint := by
            apply physicalWordAction_tail_sameLine codingPrime
              (IncrementModule.loopZero (privatePhase index 0)) tail
              (completeRun := completeRun)
            simpa only [show deleted + (remaining + 1) =
                (deleted + 1) + remaining by omega] using firstStep
          obtain ⟨suffix, tailEq, suffixOver, suffixLocal, suffixRun⟩ :=
            inductionHypothesis (deleted := deleted + 1) tailOver tailLocal
              tailRun
          refine ⟨suffix, ?_, suffixOver, ?_, ?_⟩
          · rw [tailEq]
            simp [IncrementModule.incrementTail, List.replicate_succ]
          · simpa only [show deleted + (remaining + 1) + 1 =
                deleted + 1 + remaining + 1 by omega] using suffixLocal
          · simpa only [show deleted + (remaining + 1) + 1 =
                deleted + 1 + remaining + 1 by omega] using suffixRun

private theorem localIncrementWord_forced_to_endpoint
    {edge : Edge Nat} {index counter endpointPhase : Nat}
    {endpointDigit : Int} {endpoint : Vec2}
    (indexedMem : (edge, index) ∈ fixedProgram.edges.zipIdx)
    (instructionEq : edge.instruction = .increment)
    (endpointBound : endpointPhase < totalPhaseCount)
    (privateEndpointDistinct : privatePhase index 0 ≠ endpointPhase)
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
    ∃ suffix,
      word = FixedForward.edgeWord index edge counter (counter + 1) ++
          suffix ∧
      WordOver (edgeAlphabet index edge) suffix ∧
      AllStatesLocal codingPrime suffix
        (phaseAffine (boundaryPhase edge.target)
          (unaryCode codingPrime (counter + 1))) ∧
      SameLine
        (physicalWordAction codingPrime suffix
          (phaseAffine (boundaryPhase edge.target)
            (unaryCode codingPrime (counter + 1))) ) endpoint := by
  have bounds := incrementOccurrence_bounds indexedMem instructionEq
  cases counter with
  | zero =>
      cases word with
      | nil => exact False.elim (wordNonempty rfl)
      | cons letter tail =>
          have letterMem := wordOver letter (by simp)
          have tailOver : WordOver (edgeAlphabet index edge) tail := by
            intro candidate candidateMem
            exact wordOver candidate (by simp [candidateMem])
          have moduleMem : letter ∈ IncrementModule.incrementAlphabet
              codingPrime (boundaryPhase edge.source)
              (boundaryPhase edge.target) (privatePhase index 0) := by
            simpa [edgeAlphabet_eq_increment instructionEq] using letterMem
          have letterEq := IncrementModule.first_letter_at_zero
            codingPrime_isPrime codingPrime_phase_bound bounds.1 bounds.2.1
            bounds.2.2 moduleMem allLocal.2.start
          subst letter
          have firstStep := IncrementModule.entryMarker_step codingPrime
            (boundaryPhase edge.source) (boundaryPhase edge.target)
            codingPrime_isPrime.1
          have targetLocal := IncrementModule.phaseUnaryCode_local codingPrime
            (boundaryPhase edge.target) 1 codingPrime_isPrime.1
          have tailLocal : AllStatesLocal codingPrime tail
              (phaseAffine (boundaryPhase edge.target)
                (unaryCode codingPrime 1)) := by
            apply AllStatesLocal.of_sameLine
              (primePositive := by have := codingPrime_isPrime.1; omega)
              allLocal.2 targetLocal.1 firstStep.symm
          have tailRun := physicalWordAction_tail_sameLine codingPrime
            (IncrementModule.entryMarker codingPrime
              (boundaryPhase edge.source) (boundaryPhase edge.target)) tail
            firstStep completeRun
          exact ⟨tail, by
              simp [FixedForward.edgeWord, instructionEq,
                IncrementModule.incrementWord],
            tailOver, by simpa using tailLocal, by simpa using tailRun⟩
  | succ previous =>
      cases word with
      | nil => exact False.elim (wordNonempty rfl)
      | cons letter tail =>
          have letterMem := wordOver letter (by simp)
          have tailOver : WordOver (edgeAlphabet index edge) tail := by
            intro candidate candidateMem
            exact wordOver candidate (by simp [candidateMem])
          have moduleMem : letter ∈ IncrementModule.incrementAlphabet
              codingPrime (boundaryPhase edge.source)
              (boundaryPhase edge.target) (privatePhase index 0) := by
            simpa [edgeAlphabet_eq_increment instructionEq] using letterMem
          have letterEq := IncrementModule.first_letter_at_positive
            (counter := previous) codingPrime_isPrime codingPrime_phase_bound
            bounds.1 bounds.2.1 bounds.2.2 moduleMem allLocal.2.start
          subst letter
          have firstStep := IncrementModule.entryZero_step codingPrime
            (boundaryPhase edge.source) (privatePhase index 0) (previous + 1)
            codingPrime_isPrime.1 (by omega)
          have canonicalLocal := IncrementModule.phaseIncrementState_local
            codingPrime (privatePhase index 0) (previous + 1) 1
            codingPrime_isPrime.1
          have tailLocal : AllStatesLocal codingPrime tail
              (phaseAffine (privatePhase index 0)
                (incrementState codingPrime (previous + 1) 1)) := by
            apply AllStatesLocal.of_sameLine
              (primePositive := by have := codingPrime_isPrime.1; omega)
              allLocal.2 canonicalLocal.1 firstStep.symm
          have tailRun := physicalWordAction_tail_sameLine codingPrime
            (IncrementModule.entryZero codingPrime
              (boundaryPhase edge.source) (privatePhase index 0)) tail
            firstStep completeRun
          have tailLocal' : AllStatesLocal codingPrime tail
              (phaseAffine (privatePhase index 0)
                (incrementState codingPrime (1 + previous) 1)) := by
            simpa only [show previous + 1 = 1 + previous by omega] using
              tailLocal
          have tailRun' : SameLine
              (physicalWordAction codingPrime tail
                (phaseAffine (privatePhase index 0)
                  (incrementState codingPrime (1 + previous) 1))) endpoint := by
            simpa only [show previous + 1 = 1 + previous by omega] using
              tailRun
          obtain ⟨suffix, tailEq, suffixOver, suffixLocal, suffixRun⟩ :=
            incrementTail_forced_to_endpoint indexedMem instructionEq
              endpointBound privateEndpointDistinct endpointMembership
              (deleted := 1) (remaining := previous) tailOver tailLocal'
              tailRun'
          refine ⟨suffix, ?_, suffixOver, ?_, ?_⟩
          · rw [tailEq]
            simp [FixedForward.edgeWord, instructionEq,
              IncrementModule.incrementWord]
          · simpa only [show 1 + previous + 1 = previous + 2 by omega]
              using suffixLocal
          · simpa only [show 1 + previous + 1 = previous + 2 by omega]
              using suffixRun

/-- Extract one increment block from the front of an arbitrary globally
surviving word and return the untouched suffix at the target boundary.  This
also handles the fixed program's cleanup self-loop. -/
theorem globalIncrement_split
    {edge : Edge Nat} {index counter finalState finalCounter : Nat}
    (indexedMem : (edge, index) ∈ fixedProgram.edges.zipIdx)
    (instructionEq : edge.instruction = .increment)
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
    ∃ suffix,
      edge.instruction.evaluate counter = some (counter + 1) ∧
      letter :: tail =
        FixedForward.edgeWord index edge counter (counter + 1) ++ suffix ∧
      WordOver listedTemplates suffix ∧
      AllStatesLocal codingPrime suffix
        (phaseAffine (boundaryPhase edge.target)
          (unaryCode codingPrime (counter + 1))) ∧
      SameLine
        (physicalWordAction codingPrime suffix
          (phaseAffine (boundaryPhase edge.target)
            (unaryCode codingPrime (counter + 1))))
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
    have privateDistinct : privatePhase index 0 ≠
        boundaryPhase finalState :=
      (boundary_ne_private finalStateMem indexedMem
        (incrementPrivate_inBlock (index := index) instructionEq)).symm
    obtain ⟨suffix, wordEq, suffixOver, suffixLocal, suffixRun⟩ :=
      localIncrementWord_forced_to_endpoint indexedMem instructionEq
        endpointBound privateDistinct finalMembership localOnly (by simp)
        allLocal completeRun
    refine ⟨suffix, by simp [instructionEq], wordEq, ?_, suffixLocal,
      suffixRun⟩
    exact suffixOver.mono (fun _ candidateMem =>
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
    have privateDistinct : privatePhase index 0 ≠ foreign.sourcePhase := by
      intro phaseEq
      have membershipAtPrivate : InPhaseAt codingPrime
          (privatePhase index 0) foreign.digit
          (physicalWordAction codingPrime initial
            (phaseAffine (boundaryPhase edge.source)
              (unaryCode codingPrime counter))) := by
        simpa [phaseEq] using foreignMembership
      have localMem := survivingListedLetter_at_private indexedMem
        (incrementPrivate_inBlock (index := index) instructionEq)
        membershipAtPrivate foreignGlobal foreignTailLocal.2.start
      exact foreignNotLocal localMem
    have initialNonempty : initial ≠ [] := by
      intro initialEmpty
      subst initial
      simp only [List.nil_append, List.cons.injEq] at wordEq
      exact foreignNotLocal (wordEq.1 ▸ letterLocal)
    obtain ⟨localSuffix, initialEq, localSuffixOver, localSuffixLocal,
        localSuffixRun⟩ :=
      localIncrementWord_forced_to_endpoint indexedMem instructionEq
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
          (unaryCode codingPrime (counter + 1))).Nonzero :=
      Vec2.affine_nonzero _
    have afterLocalSuffixNonzero := physicalWordAction_nonzero
      (prime := codingPrime) (by have := codingPrime_isPrime.1; omega)
      localSuffix targetNonzero
    have foreignTailCanonical : AllStatesLocal codingPrime (foreign :: rest)
        (physicalWordAction codingPrime localSuffix
          (phaseAffine (boundaryPhase edge.target)
            (unaryCode codingPrime (counter + 1)))) := by
      apply AllStatesLocal.of_sameLine
        (primePositive := by have := codingPrime_isPrime.1; omega)
        foreignTailLocal afterLocalSuffixNonzero localSuffixRun
    have residualLocal : AllStatesLocal codingPrime
        (localSuffix ++ foreign :: rest)
        (phaseAffine (boundaryPhase edge.target)
          (unaryCode codingPrime (counter + 1))) :=
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
              (unaryCode codingPrime (counter + 1)))))
        (physicalWordAction codingPrime (foreign :: rest)
          (physicalWordAction codingPrime initial
            (phaseAffine (boundaryPhase edge.source)
              (unaryCode codingPrime counter)))) :=
      physicalWordAction_preserves_sameLine codingPrime (foreign :: rest)
        localSuffixRun
    have residualRun : SameLine
        (physicalWordAction codingPrime (localSuffix ++ foreign :: rest)
          (phaseAffine (boundaryPhase edge.target)
            (unaryCode codingPrime (counter + 1))) )
        (phaseAffine (boundaryPhase finalState)
          (unaryCode codingPrime finalCounter)) := by
      rw [physicalWordAction_append]
      exact afterSuffixRun.trans residualRunRaw
    refine ⟨localSuffix ++ foreign :: rest, by simp [instructionEq], ?_,
      residualGlobal, residualLocal, residualRun⟩
    rw [wordEq, initialEq, List.append_assoc]

end Mortality.Compiler.GlobalIncrement
