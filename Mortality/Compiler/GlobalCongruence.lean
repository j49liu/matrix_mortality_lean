import Mortality.Compiler.AllocationProperties
import Mortality.Compiler.FixedForward
import Mortality.Compiler.GlobalParserBasics

/-!
# Lifting congruence-test converses to the global alphabet

The residue-cycle phases of an indexed test occurrence lie in its private
block.  Consequently, after the boundary entry has selected that occurrence,
every globally available letter that preserves locality belongs to the same
finite congruence alphabet.  The module-level converse can then be applied to
the complete scan prefix.
-/

namespace Mortality.Compiler.GlobalCongruence

open Mortality
open Mortality.OneCounter
open Mortality.PeriodicCode
open Mortality.Compiler
open Mortality.Compiler.FixedAllocation
open Mortality.Compiler.AllocationProperties
open Mortality.Compiler.GlobalParserBasics

set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

private theorem congruencePrivate_inBlock
    {edge : Edge Nat} {index modulus offset : Nat}
    (costEq : instructionPrivateCost edge.instruction = modulus)
    (offsetBound : offset < modulus) :
    InPrivateBlock index edge (privatePhase index offset) := by
  unfold InPrivateBlock privatePhase
  omega

private theorem congruenceOccurrence_bounds
    {edge : Edge Nat} {index modulus : Nat}
    (indexedMem : (edge, index) ∈ fixedProgram.edges.zipIdx)
    (costEq : instructionPrivateCost edge.instruction = modulus) :
    boundaryPhase edge.source < totalPhaseCount ∧
      (∀ offset, offset < modulus →
        privatePhase index offset < totalPhaseCount) ∧
      (∀ offset, offset < modulus →
        boundaryPhase edge.source ≠ privatePhase index offset) := by
  have sourceMem := (fixedEdge_endpoints_mem (indexedEdge_mem indexedMem)).1
  have sourceBound := boundaryPhase_bound sourceMem
  have boundariesFit : SourceMachine.quotientStates.length ≤
      genuinePhaseBound := by decide
  refine ⟨by unfold totalPhaseCount; omega, ?_, ?_⟩
  · intro offset offsetBound
    have privateIn := congruencePrivate_inBlock (index := index)
      costEq offsetBound
    have privateBound := privateBlock_bounded indexedMem privateIn
    unfold totalPhaseCount
    omega
  · intro offset offsetBound
    exact boundary_ne_private sourceMem indexedMem
      (congruencePrivate_inBlock (index := index) costEq offsetBound)

private theorem congruencePrivate_injective
    {index : Nat} {first second : Nat}
    (phaseEq : privatePhase index first = privatePhase index second) :
    first = second := by
  unfold privatePhase at phaseEq
  omega

/-- A sufficiently long ambient tail starting in a congruence-test private
phase uses only that occurrence's alphabet for the remaining scan. -/
theorem globalCongruenceTail_wordOver
    {edge : Edge Nat} {index modulus deleted remaining : Nat}
    {allowed : List Nat}
    (indexedMem : (edge, index) ∈ fixedProgram.edges.zipIdx)
    (alphabetEq : edgeAlphabet index edge =
      CongruenceModule.congruenceAlphabet
        (boundaryPhase edge.source) (boundaryPhase edge.target) modulus
        (privatePhase index) allowed)
    (costEq : instructionPrivateCost edge.instruction = modulus)
    (modulusPositive : 0 < modulus)
    (allowedBound : ∀ residue ∈ allowed, residue < modulus)
    {word : List PhysicalTemplate}
    (globalOver : WordOver listedTemplates word)
    (allLocal : AllStatesLocal codingPrime word
      (phaseAffine (privatePhase index (deleted % modulus))
        (periodicCode (codingPrime : Rat)
          (CongruenceModule.scanStateDigits
            (deleted + remaining) deleted))))
    (longEnough : remaining + 1 ≤ word.length) :
    WordOver (edgeAlphabet index edge) (word.take (remaining + 1)) := by
  induction remaining generalizing deleted word with
  | zero =>
      cases word with
      | nil => simp at longEnough
      | cons letter tail =>
          have letterGlobal := globalOver letter (by simp)
          have offsetBound := Nat.mod_lt deleted modulusPositive
          have privateIn := congruencePrivate_inBlock (index := index)
            costEq offsetBound
          have actualMembership :=
            CongruenceModule.scanState_inPhaseAt_marker
              (base := codingPrime)
              (phase := privatePhase index (deleted % modulus))
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
          have offsetBound := Nat.mod_lt deleted modulusPositive
          have privateIn := congruencePrivate_inBlock (index := index)
            costEq offsetBound
          have actualMembership :=
            CongruenceModule.scanState_inPhaseAt_before
              (base := codingPrime)
              (phase := privatePhase index (deleted % modulus))
              (counter := deleted + (remaining + 1)) (deleted := deleted)
              codingPrime_isPrime.1 (by omega)
          have letterLocal := survivingListedLetter_at_private indexedMem
            privateIn actualMembership letterGlobal allLocal.2.start
          have moduleMem : letter ∈
              CongruenceModule.congruenceAlphabet
                (boundaryPhase edge.source) (boundaryPhase edge.target)
                modulus (privatePhase index) allowed := by
            simpa [alphabetEq] using letterLocal
          have bounds := congruenceOccurrence_bounds indexedMem costEq
          have letterEq := CongruenceModule.private_letter_before_marker
            codingPrime_isPrime codingPrime_phase_bound modulusPositive
            bounds.1 bounds.2.1 allowedBound
            bounds.2.2 (by
              intro first second _ _ phaseEq
              exact congruencePrivate_injective phaseEq)
            (by omega) moduleMem allLocal.2.start
          subst letter
          have firstStep := CongruenceModule.zeroRotationStep codingPrime
            modulus (deleted + (remaining + 1)) deleted (privatePhase index)
            codingPrime_isPrime.1 (by omega)
          have canonicalLocal := CongruenceModule.phaseScanState_local
            codingPrime (privatePhase index ((deleted + 1) % modulus))
            ((deleted + 1) + remaining) (deleted + 1)
            codingPrime_isPrime.1
          have tailLocal : AllStatesLocal codingPrime tail
              (phaseAffine (privatePhase index ((deleted + 1) % modulus))
                (periodicCode (codingPrime : Rat)
                  (CongruenceModule.scanStateDigits
                    ((deleted + 1) + remaining) (deleted + 1)))) := by
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

/-- Global-alphabet converse for either fixed congruence-test occurrence.
The assumptions expose only its modulus, allowed residues, alphabet, and
private-phase cost, so the two concrete tests share one proof. -/
theorem globalCongruenceWord_forced_prefix
    {edge : Edge Nat} {index modulus counter : Nat} {allowed : List Nat}
    (indexedMem : (edge, index) ∈ fixedProgram.edges.zipIdx)
    (alphabetEq : edgeAlphabet index edge =
      CongruenceModule.congruenceAlphabet
        (boundaryPhase edge.source) (boundaryPhase edge.target) modulus
        (privatePhase index) allowed)
    (costEq : instructionPrivateCost edge.instruction = modulus)
    (modulusPositive : 0 < modulus)
    (allowedBound : ∀ residue ∈ allowed, residue < modulus)
    {letter : PhysicalTemplate} {tail : List PhysicalTemplate}
    (globalOver : WordOver listedTemplates (letter :: tail))
    (letterLocal : letter ∈ edgeAlphabet index edge)
    (allLocal : AllStatesLocal codingPrime (letter :: tail)
      (phaseAffine (boundaryPhase edge.source)
        (unaryCode codingPrime counter)))
    (longEnough : counter + 1 ≤ (letter :: tail).length) :
    counter % modulus ∈ allowed ∧
      (letter :: tail).take (counter + 1) =
        CongruenceModule.congruenceWord
          (boundaryPhase edge.source) (boundaryPhase edge.target)
          modulus counter (privatePhase index) := by
  have bounds := congruenceOccurrence_bounds indexedMem costEq
  have moduleMem : letter ∈
      CongruenceModule.congruenceAlphabet
        (boundaryPhase edge.source) (boundaryPhase edge.target) modulus
        (privatePhase index) allowed := by
    simpa [alphabetEq] using letterLocal
  cases counter with
  | zero =>
      have classified := CongruenceModule.source_letter_zero
        codingPrime_isPrime codingPrime_phase_bound bounds.1 bounds.2.1
        allowedBound bounds.2.2 moduleMem (by simpa using allLocal.2.start)
      rcases classified with ⟨zeroAllowed, letterEq⟩
      subst letter
      exact ⟨zeroAllowed, by
        simp [CongruenceModule.congruenceWord]⟩
  | succ previous =>
      have letterEq := CongruenceModule.source_letter_positive
        (counter := previous) codingPrime_isPrime codingPrime_phase_bound
        bounds.1 bounds.2.1 allowedBound bounds.2.2 moduleMem
        allLocal.2.start
      subst letter
      have firstStep := CongruenceModule.entryZeroStep codingPrime
        (boundaryPhase edge.source) modulus (previous + 1)
        (privatePhase index) codingPrime_isPrime.1 (by omega)
      have canonicalLocal := CongruenceModule.phaseScanState_local codingPrime
        (privatePhase index (1 % modulus)) (1 + previous) 1
        codingPrime_isPrime.1
      have tailLocal : AllStatesLocal codingPrime tail
          (phaseAffine (privatePhase index (1 % modulus))
            (periodicCode (codingPrime : Rat)
              (CongruenceModule.scanStateDigits (1 + previous) 1))) := by
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
      have tailOver := globalCongruenceTail_wordOver indexedMem alphabetEq
        costEq modulusPositive allowedBound (deleted := 1)
        (remaining := previous)
        tailGlobal tailLocal tailLong
      have prefixOver : WordOver
          (CongruenceModule.congruenceAlphabet
            (boundaryPhase edge.source) (boundaryPhase edge.target) modulus
            (privatePhase index) allowed)
          ((CongruenceModule.entryZero (boundaryPhase edge.source) modulus
              (privatePhase index) :: tail).take (previous + 2)) := by
        have combined := wordOver_cons letterLocal tailOver
        simpa [alphabetEq] using combined
      have prefixLocal := allLocal.take (previous + 2)
      have prefixLength :
          ((CongruenceModule.entryZero (boundaryPhase edge.source) modulus
            (privatePhase index) :: tail).take (previous + 2)).length =
            previous + 2 := by
        rw [List.length_take, Nat.min_eq_left longEnough]
      exact CongruenceModule.congruenceWord_surviving_unique
        codingPrime_isPrime codingPrime_phase_bound modulusPositive bounds.1
        bounds.2.1 allowedBound bounds.2.2 (by
          intro first second _ _ phaseEq
          exact congruencePrivate_injective phaseEq)
        prefixOver prefixLocal prefixLength

/-- Specialization to the fixed binary test. -/
theorem globalModTwoWord_forced_prefix
    {edge : Edge Nat} {index counter : Nat}
    (indexedMem : (edge, index) ∈ fixedProgram.edges.zipIdx)
    (instructionEq : edge.instruction = .congruenceTest 2 [0])
    {letter : PhysicalTemplate} {tail : List PhysicalTemplate}
    (globalOver : WordOver listedTemplates (letter :: tail))
    (letterLocal : letter ∈ edgeAlphabet index edge)
    (allLocal : AllStatesLocal codingPrime (letter :: tail)
      (phaseAffine (boundaryPhase edge.source)
        (unaryCode codingPrime counter)))
    (longEnough : counter + 1 ≤ (letter :: tail).length) :
    counter % 2 ∈ [0] ∧
      (letter :: tail).take (counter + 1) =
        FixedForward.edgeWord index edge counter counter := by
  have alphabetEq : edgeAlphabet index edge =
      CongruenceModule.congruenceAlphabet
        (boundaryPhase edge.source) (boundaryPhase edge.target) 2
        (privatePhase index) [0] := by
    simp [edgeAlphabet, instructionEq]
  have costEq : instructionPrivateCost edge.instruction = 2 := by
    simp [instructionEq, instructionPrivateCost, modTwoTestCost]
  have classified := globalCongruenceWord_forced_prefix indexedMem alphabetEq
    costEq (by decide) (by simp) globalOver letterLocal allLocal longEnough
  simpa [FixedForward.edgeWord, instructionEq] using classified

/-- Specialization to the fixed ternary test. -/
theorem globalModThreeWord_forced_prefix
    {edge : Edge Nat} {index counter : Nat}
    (indexedMem : (edge, index) ∈ fixedProgram.edges.zipIdx)
    (instructionEq : edge.instruction = .congruenceTest 3 [0, 1])
    {letter : PhysicalTemplate} {tail : List PhysicalTemplate}
    (globalOver : WordOver listedTemplates (letter :: tail))
    (letterLocal : letter ∈ edgeAlphabet index edge)
    (allLocal : AllStatesLocal codingPrime (letter :: tail)
      (phaseAffine (boundaryPhase edge.source)
        (unaryCode codingPrime counter)))
    (longEnough : counter + 1 ≤ (letter :: tail).length) :
    counter % 3 ∈ [0, 1] ∧
      (letter :: tail).take (counter + 1) =
        FixedForward.edgeWord index edge counter counter := by
  have alphabetEq : edgeAlphabet index edge =
      CongruenceModule.congruenceAlphabet
        (boundaryPhase edge.source) (boundaryPhase edge.target) 3
        (privatePhase index) [0, 1] := by
    simp [edgeAlphabet, instructionEq]
  have costEq : instructionPrivateCost edge.instruction = 3 := by
    simp [instructionEq, instructionPrivateCost, modThreeTestCost]
  have classified := globalCongruenceWord_forced_prefix indexedMem alphabetEq
    costEq (by decide) (by decide) globalOver letterLocal allLocal
    longEnough
  simpa [FixedForward.edgeWord, instructionEq] using classified

/-- Endpoint-aware parser for the private residue-cycle tail. -/
private theorem congruenceTail_forced_to_endpoint
    {edge : Edge Nat} {index modulus deleted remaining endpointPhase : Nat}
    {allowed : List Nat} {endpointDigit : Int} {endpoint : Vec2}
    (indexedMem : (edge, index) ∈ fixedProgram.edges.zipIdx)
    (alphabetEq : edgeAlphabet index edge =
      CongruenceModule.congruenceAlphabet
        (boundaryPhase edge.source) (boundaryPhase edge.target) modulus
        (privatePhase index) allowed)
    (costEq : instructionPrivateCost edge.instruction = modulus)
    (modulusPositive : 0 < modulus)
    (allowedBound : ∀ residue ∈ allowed, residue < modulus)
    (endpointBound : endpointPhase < totalPhaseCount)
    (privateEndpointDistinct : ∀ offset, offset < modulus →
      privatePhase index offset ≠ endpointPhase)
    (endpointMembership : InPhaseAt codingPrime endpointPhase endpointDigit
      endpoint)
    {word : List PhysicalTemplate}
    (wordOver : WordOver (edgeAlphabet index edge) word)
    (allLocal : AllStatesLocal codingPrime word
      (phaseAffine (privatePhase index (deleted % modulus))
        (periodicCode (codingPrime : Rat)
          (CongruenceModule.scanStateDigits
            (deleted + remaining) deleted))))
    (completeRun : SameLine
      (physicalWordAction codingPrime word
        (phaseAffine (privatePhase index (deleted % modulus))
          (periodicCode (codingPrime : Rat)
            (CongruenceModule.scanStateDigits
              (deleted + remaining) deleted)))) endpoint) :
    (deleted + remaining) % modulus ∈ allowed ∧
      ∃ suffix,
        word = CongruenceModule.scanTail (boundaryPhase edge.target)
            modulus deleted remaining (privatePhase index) ++ suffix ∧
        WordOver (edgeAlphabet index edge) suffix ∧
        AllStatesLocal codingPrime suffix
          (phaseAffine (boundaryPhase edge.target)
            (unaryCode codingPrime (deleted + remaining))) ∧
        SameLine
          (physicalWordAction codingPrime suffix
            (phaseAffine (boundaryPhase edge.target)
              (unaryCode codingPrime (deleted + remaining)))) endpoint := by
  have bounds := congruenceOccurrence_bounds indexedMem costEq
  have phaseInjective : ∀ {first second}, first < modulus →
      second < modulus → privatePhase index first = privatePhase index second →
      first = second := by
    intro first second _ _ phaseEq
    exact congruencePrivate_injective phaseEq
  induction remaining generalizing deleted word with
  | zero =>
      have offsetBound := Nat.mod_lt deleted modulusPositive
      have actualMembership := CongruenceModule.scanState_inPhaseAt_marker
        (base := codingPrime)
        (phase := privatePhase index (deleted % modulus))
        (counter := deleted) codingPrime_isPrime.1
      have wordNonempty : word ≠ [] := by
        intro wordEmpty
        subst word
        have phasesEq := (actualMembership.unique codingPrime_isPrime
          codingPrime_phase_bound (bounds.2.1 _ offsetBound) endpointBound
          endpointMembership (by
            simpa [physicalWordAction] using completeRun)).1
        exact privateEndpointDistinct _ offsetBound phasesEq
      cases word with
      | nil => exact False.elim (wordNonempty rfl)
      | cons letter tail =>
          have letterMem := wordOver letter (by simp)
          have tailOver : WordOver (edgeAlphabet index edge) tail := by
            intro candidate candidateMem
            exact wordOver candidate (by simp [candidateMem])
          have moduleMem : letter ∈
              CongruenceModule.congruenceAlphabet
                (boundaryPhase edge.source) (boundaryPhase edge.target)
                modulus (privatePhase index) allowed := by
            simpa [alphabetEq] using letterMem
          obtain ⟨residueAllowed, letterEq⟩ :=
            CongruenceModule.private_letter_at_marker
              (counter := deleted) codingPrime_isPrime
              codingPrime_phase_bound modulusPositive bounds.1 bounds.2.1
              allowedBound bounds.2.2 phaseInjective moduleMem
              (by simpa using allLocal.2.start)
          subst letter
          have firstStep := CongruenceModule.markerExitStep codingPrime
            (boundaryPhase edge.target) modulus deleted (privatePhase index)
            codingPrime_isPrime.1
          have targetLocal := IncrementModule.phaseUnaryCode_local codingPrime
            (boundaryPhase edge.target) deleted codingPrime_isPrime.1
          have tailLocal : AllStatesLocal codingPrime tail
              (phaseAffine (boundaryPhase edge.target)
                (unaryCode codingPrime deleted)) := by
            apply AllStatesLocal.of_sameLine
              (primePositive := by have := codingPrime_isPrime.1; omega)
              allLocal.2 targetLocal.1 firstStep.symm
          have tailRun := physicalWordAction_tail_sameLine codingPrime
            (CongruenceModule.exitMarker (boundaryPhase edge.target)
              (deleted % modulus) (privatePhase index)) tail firstStep
            completeRun
          exact ⟨by simpa using residueAllowed, tail, by
              simp [CongruenceModule.scanTail],
            tailOver, by simpa using tailLocal, by simpa using tailRun⟩
  | succ remaining inductionHypothesis =>
      have offsetBound := Nat.mod_lt deleted modulusPositive
      have actualMembership := CongruenceModule.scanState_inPhaseAt_before
        (base := codingPrime)
        (phase := privatePhase index (deleted % modulus))
        (counter := deleted + (remaining + 1)) (deleted := deleted)
        codingPrime_isPrime.1 (by omega)
      have wordNonempty : word ≠ [] := by
        intro wordEmpty
        subst word
        have phasesEq := (actualMembership.unique codingPrime_isPrime
          codingPrime_phase_bound (bounds.2.1 _ offsetBound) endpointBound
          endpointMembership (by
            simpa [physicalWordAction] using completeRun)).1
        exact privateEndpointDistinct _ offsetBound phasesEq
      cases word with
      | nil => exact False.elim (wordNonempty rfl)
      | cons letter tail =>
          have letterMem := wordOver letter (by simp)
          have tailOver : WordOver (edgeAlphabet index edge) tail := by
            intro candidate candidateMem
            exact wordOver candidate (by simp [candidateMem])
          have moduleMem : letter ∈
              CongruenceModule.congruenceAlphabet
                (boundaryPhase edge.source) (boundaryPhase edge.target)
                modulus (privatePhase index) allowed := by
            simpa [alphabetEq] using letterMem
          have letterEq := CongruenceModule.private_letter_before_marker
            (counter := deleted + (remaining + 1)) (deleted := deleted)
            codingPrime_isPrime codingPrime_phase_bound modulusPositive
            bounds.1 bounds.2.1 allowedBound bounds.2.2 phaseInjective
            (by omega) moduleMem allLocal.2.start
          subst letter
          have firstStep := CongruenceModule.zeroRotationStep codingPrime
            modulus (deleted + (remaining + 1)) deleted (privatePhase index)
            codingPrime_isPrime.1 (by omega)
          have canonicalLocal := CongruenceModule.phaseScanState_local
            codingPrime (privatePhase index ((deleted + 1) % modulus))
            ((deleted + 1) + remaining) (deleted + 1)
            codingPrime_isPrime.1
          have tailLocal : AllStatesLocal codingPrime tail
              (phaseAffine (privatePhase index ((deleted + 1) % modulus))
                (periodicCode (codingPrime : Rat)
                  (CongruenceModule.scanStateDigits
                    ((deleted + 1) + remaining) (deleted + 1)))) := by
            apply AllStatesLocal.of_sameLine
              (primePositive := by have := codingPrime_isPrime.1; omega)
              allLocal.2 canonicalLocal.1
            simpa only [show deleted + (remaining + 1) =
                (deleted + 1) + remaining by omega] using firstStep.symm
          have tailRun : SameLine
              (physicalWordAction codingPrime tail
                (phaseAffine (privatePhase index ((deleted + 1) % modulus))
                  (periodicCode (codingPrime : Rat)
                    (CongruenceModule.scanStateDigits
                      ((deleted + 1) + remaining) (deleted + 1)))))
              endpoint := by
            apply physicalWordAction_tail_sameLine codingPrime
              (CongruenceModule.loopZero modulus (deleted % modulus)
                (privatePhase index)) tail (completeRun := completeRun)
            simpa only [show deleted + (remaining + 1) =
                (deleted + 1) + remaining by omega] using firstStep
          obtain ⟨residueAllowed, suffix, tailEq, suffixOver, suffixLocal,
              suffixRun⟩ :=
            inductionHypothesis (deleted := deleted + 1) tailOver tailLocal
              tailRun
          refine ⟨by simpa only [show deleted + (remaining + 1) =
              deleted + 1 + remaining by omega] using residueAllowed,
            suffix, ?_, suffixOver, ?_, ?_⟩
          · rw [tailEq]
            simp [CongruenceModule.scanTail]
          · simpa only [show deleted + (remaining + 1) =
                deleted + 1 + remaining by omega] using suffixLocal
          · simpa only [show deleted + (remaining + 1) =
                deleted + 1 + remaining by omega] using suffixRun

private theorem localCongruenceWord_forced_to_endpoint
    {edge : Edge Nat} {index modulus counter endpointPhase : Nat}
    {allowed : List Nat} {endpointDigit : Int} {endpoint : Vec2}
    (indexedMem : (edge, index) ∈ fixedProgram.edges.zipIdx)
    (alphabetEq : edgeAlphabet index edge =
      CongruenceModule.congruenceAlphabet
        (boundaryPhase edge.source) (boundaryPhase edge.target) modulus
        (privatePhase index) allowed)
    (costEq : instructionPrivateCost edge.instruction = modulus)
    (modulusPositive : 0 < modulus)
    (allowedBound : ∀ residue ∈ allowed, residue < modulus)
    (endpointBound : endpointPhase < totalPhaseCount)
    (privateEndpointDistinct : ∀ offset, offset < modulus →
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
    counter % modulus ∈ allowed ∧
      ∃ suffix,
        word = CongruenceModule.congruenceWord
            (boundaryPhase edge.source) (boundaryPhase edge.target)
            modulus counter (privatePhase index) ++ suffix ∧
        WordOver (edgeAlphabet index edge) suffix ∧
        AllStatesLocal codingPrime suffix
          (phaseAffine (boundaryPhase edge.target)
            (unaryCode codingPrime counter)) ∧
        SameLine
          (physicalWordAction codingPrime suffix
            (phaseAffine (boundaryPhase edge.target)
              (unaryCode codingPrime counter))) endpoint := by
  have bounds := congruenceOccurrence_bounds indexedMem costEq
  cases counter with
  | zero =>
      cases word with
      | nil => exact False.elim (wordNonempty rfl)
      | cons letter tail =>
          have letterMem := wordOver letter (by simp)
          have tailOver : WordOver (edgeAlphabet index edge) tail := by
            intro candidate candidateMem
            exact wordOver candidate (by simp [candidateMem])
          have moduleMem : letter ∈
              CongruenceModule.congruenceAlphabet
                (boundaryPhase edge.source) (boundaryPhase edge.target)
                modulus (privatePhase index) allowed := by
            simpa [alphabetEq] using letterMem
          obtain ⟨zeroAllowed, letterEq⟩ :=
            CongruenceModule.source_letter_zero codingPrime_isPrime
              codingPrime_phase_bound bounds.1 bounds.2.1 allowedBound
              bounds.2.2 moduleMem (by simpa using allLocal.2.start)
          subst letter
          have firstStep := CongruenceModule.directMarkerStep codingPrime
            (boundaryPhase edge.source) (boundaryPhase edge.target)
            codingPrime_isPrime.1
          have targetLocal := IncrementModule.phaseUnaryCode_local codingPrime
            (boundaryPhase edge.target) 0 codingPrime_isPrime.1
          have tailLocal : AllStatesLocal codingPrime tail
              (phaseAffine (boundaryPhase edge.target)
                (unaryCode codingPrime 0)) := by
            apply AllStatesLocal.of_sameLine
              (primePositive := by have := codingPrime_isPrime.1; omega)
              allLocal.2 targetLocal.1 firstStep.symm
          have tailRun := physicalWordAction_tail_sameLine codingPrime
            (CongruenceModule.directMarker (boundaryPhase edge.source)
              (boundaryPhase edge.target)) tail firstStep completeRun
          exact ⟨zeroAllowed, tail, by
              simp [CongruenceModule.congruenceWord],
            tailOver, by simpa using tailLocal, by simpa using tailRun⟩
  | succ previous =>
      cases word with
      | nil => exact False.elim (wordNonempty rfl)
      | cons letter tail =>
          have letterMem := wordOver letter (by simp)
          have tailOver : WordOver (edgeAlphabet index edge) tail := by
            intro candidate candidateMem
            exact wordOver candidate (by simp [candidateMem])
          have moduleMem : letter ∈
              CongruenceModule.congruenceAlphabet
                (boundaryPhase edge.source) (boundaryPhase edge.target)
                modulus (privatePhase index) allowed := by
            simpa [alphabetEq] using letterMem
          have letterEq := CongruenceModule.source_letter_positive
            (counter := previous) codingPrime_isPrime codingPrime_phase_bound
            bounds.1 bounds.2.1 allowedBound bounds.2.2 moduleMem
            allLocal.2.start
          subst letter
          have firstStep := CongruenceModule.entryZeroStep codingPrime
            (boundaryPhase edge.source) modulus (previous + 1)
            (privatePhase index) codingPrime_isPrime.1 (by omega)
          have canonicalLocal := CongruenceModule.phaseScanState_local
            codingPrime (privatePhase index (1 % modulus))
            (previous + 1) 1 codingPrime_isPrime.1
          have tailLocal : AllStatesLocal codingPrime tail
              (phaseAffine (privatePhase index (1 % modulus))
                (periodicCode (codingPrime : Rat)
                  (CongruenceModule.scanStateDigits (previous + 1) 1))) := by
            apply AllStatesLocal.of_sameLine
              (primePositive := by have := codingPrime_isPrime.1; omega)
              allLocal.2 canonicalLocal.1 firstStep.symm
          have tailRun := physicalWordAction_tail_sameLine codingPrime
            (CongruenceModule.entryZero (boundaryPhase edge.source) modulus
              (privatePhase index)) tail firstStep completeRun
          obtain ⟨residueAllowed, suffix, tailEq, suffixOver, suffixLocal,
              suffixRun⟩ :=
            congruenceTail_forced_to_endpoint indexedMem alphabetEq costEq
              modulusPositive allowedBound endpointBound
              privateEndpointDistinct endpointMembership (deleted := 1)
              (remaining := previous) tailOver (by
                simpa only [show previous + 1 = 1 + previous by omega] using
                  tailLocal) (by
                simpa only [show previous + 1 = 1 + previous by omega] using
                  tailRun)
          refine ⟨by simpa only [show previous + 1 = 1 + previous by omega]
              using residueAllowed, suffix, ?_, suffixOver, ?_, ?_⟩
          · rw [tailEq]
            simp [CongruenceModule.congruenceWord]
          · simpa only [show 1 + previous = previous + 1 by omega] using
              suffixLocal
          · simpa only [show 1 + previous = previous + 1 by omega] using
              suffixRun

private theorem globalCongruence_split
    {edge : Edge Nat} {index modulus counter finalState finalCounter : Nat}
    {allowed : List Nat}
    (indexedMem : (edge, index) ∈ fixedProgram.edges.zipIdx)
    (alphabetEq : edgeAlphabet index edge =
      CongruenceModule.congruenceAlphabet
        (boundaryPhase edge.source) (boundaryPhase edge.target) modulus
        (privatePhase index) allowed)
    (costEq : instructionPrivateCost edge.instruction = modulus)
    (modulusPositive : 0 < modulus)
    (allowedBound : ∀ residue ∈ allowed, residue < modulus)
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
    counter % modulus ∈ allowed ∧
      ∃ suffix,
        letter :: tail = CongruenceModule.congruenceWord
            (boundaryPhase edge.source) (boundaryPhase edge.target)
            modulus counter (privatePhase index) ++ suffix ∧
        WordOver listedTemplates suffix ∧
        AllStatesLocal codingPrime suffix
          (phaseAffine (boundaryPhase edge.target)
            (unaryCode codingPrime counter)) ∧
        SameLine
          (physicalWordAction codingPrime suffix
            (phaseAffine (boundaryPhase edge.target)
              (unaryCode codingPrime counter)))
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
    have privateDistinct : ∀ offset, offset < modulus →
        privatePhase index offset ≠ boundaryPhase finalState := by
      intro offset offsetBound
      exact (boundary_ne_private finalStateMem indexedMem
        (congruencePrivate_inBlock (index := index) costEq offsetBound)).symm
    obtain ⟨residueAllowed, suffix, wordEq, suffixOver, suffixLocal,
        suffixRun⟩ :=
      localCongruenceWord_forced_to_endpoint indexedMem alphabetEq costEq
        modulusPositive allowedBound endpointBound privateDistinct
        finalMembership localOnly (by simp) allLocal completeRun
    refine ⟨residueAllowed, suffix, wordEq, ?_, suffixLocal, suffixRun⟩
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
    have privateDistinct : ∀ offset, offset < modulus →
        privatePhase index offset ≠ foreign.sourcePhase := by
      intro offset offsetBound phaseEq
      have membershipAtPrivate : InPhaseAt codingPrime
          (privatePhase index offset) foreign.digit
          (physicalWordAction codingPrime initial
            (phaseAffine (boundaryPhase edge.source)
              (unaryCode codingPrime counter))) := by
        simpa [phaseEq] using foreignMembership
      have localMem := survivingListedLetter_at_private indexedMem
        (congruencePrivate_inBlock (index := index) costEq offsetBound)
        membershipAtPrivate foreignGlobal foreignTailLocal.2.start
      exact foreignNotLocal localMem
    have initialNonempty : initial ≠ [] := by
      intro initialEmpty
      subst initial
      simp only [List.nil_append, List.cons.injEq] at wordEq
      exact foreignNotLocal (wordEq.1 ▸ letterLocal)
    obtain ⟨residueAllowed, localSuffix, initialEq, localSuffixOver,
        localSuffixLocal, localSuffixRun⟩ :=
      localCongruenceWord_forced_to_endpoint indexedMem alphabetEq costEq
        modulusPositive allowedBound endpointBound privateDistinct
        foreignMembership initialOver initialNonempty initialLocal
        (SameLine.refl _)
    have localSuffixGlobal : WordOver listedTemplates localSuffix :=
      localSuffixOver.mono (fun _ candidateMem =>
        edgeLetter_listed indexedMem candidateMem)
    have residualGlobal : WordOver listedTemplates
        (localSuffix ++ foreign :: rest) :=
      wordOver_append localSuffixGlobal (wordOver_cons foreignGlobal restGlobal)
    have targetNonzero :
        (phaseAffine (boundaryPhase edge.target)
          (unaryCode codingPrime counter)).Nonzero := Vec2.affine_nonzero _
    have afterLocalSuffixNonzero := physicalWordAction_nonzero
      (prime := codingPrime) (by have := codingPrime_isPrime.1; omega)
      localSuffix targetNonzero
    have foreignTailCanonical : AllStatesLocal codingPrime (foreign :: rest)
        (physicalWordAction codingPrime localSuffix
          (phaseAffine (boundaryPhase edge.target)
            (unaryCode codingPrime counter))) := by
      apply AllStatesLocal.of_sameLine
        (primePositive := by have := codingPrime_isPrime.1; omega)
        foreignTailLocal afterLocalSuffixNonzero localSuffixRun
    have residualLocal : AllStatesLocal codingPrime
        (localSuffix ++ foreign :: rest)
        (phaseAffine (boundaryPhase edge.target)
          (unaryCode codingPrime counter)) :=
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
              (unaryCode codingPrime counter))))
        (physicalWordAction codingPrime (foreign :: rest)
          (physicalWordAction codingPrime initial
            (phaseAffine (boundaryPhase edge.source)
              (unaryCode codingPrime counter)))) :=
      physicalWordAction_preserves_sameLine codingPrime (foreign :: rest)
        localSuffixRun
    have residualRun : SameLine
        (physicalWordAction codingPrime (localSuffix ++ foreign :: rest)
          (phaseAffine (boundaryPhase edge.target)
            (unaryCode codingPrime counter)))
        (phaseAffine (boundaryPhase finalState)
          (unaryCode codingPrime finalCounter)) := by
      rw [physicalWordAction_append]
      exact afterSuffixRun.trans residualRunRaw
    refine ⟨residueAllowed, localSuffix ++ foreign :: rest, ?_,
      residualGlobal, residualLocal, residualRun⟩
    rw [wordEq, initialEq, List.append_assoc]

/-- Segmentation theorem for the fixed binary congruence test. -/
theorem globalModTwo_split
    {edge : Edge Nat} {index counter finalState finalCounter : Nat}
    (indexedMem : (edge, index) ∈ fixedProgram.edges.zipIdx)
    (instructionEq : edge.instruction = .congruenceTest 2 [0])
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
      edge.instruction.evaluate counter = some counter ∧
      letter :: tail = FixedForward.edgeWord index edge counter counter ++
        suffix ∧
      WordOver listedTemplates suffix ∧
      AllStatesLocal codingPrime suffix
        (phaseAffine (boundaryPhase edge.target)
          (unaryCode codingPrime counter)) ∧
      SameLine
        (physicalWordAction codingPrime suffix
          (phaseAffine (boundaryPhase edge.target)
            (unaryCode codingPrime counter)))
        (phaseAffine (boundaryPhase finalState)
          (unaryCode codingPrime finalCounter)) := by
  have alphabetEq : edgeAlphabet index edge =
      CongruenceModule.congruenceAlphabet
        (boundaryPhase edge.source) (boundaryPhase edge.target) 2
        (privatePhase index) [0] := by
    simp [edgeAlphabet, instructionEq]
  have costEq : instructionPrivateCost edge.instruction = 2 := by
    simp [instructionEq, instructionPrivateCost, modTwoTestCost]
  obtain ⟨allowed, suffix, wordEq, suffixOver, suffixLocal, suffixRun⟩ :=
    globalCongruence_split indexedMem alphabetEq costEq (by decide)
      (by decide) finalStateMem globalOver letterLocal allLocal completeRun
  refine ⟨suffix, ?_, ?_, suffixOver, suffixLocal, suffixRun⟩
  · simp [Instruction.evaluate, instructionEq] at allowed ⊢
    exact allowed
  · simpa [FixedForward.edgeWord, instructionEq] using wordEq

/-- Segmentation theorem for the fixed ternary congruence test. -/
theorem globalModThree_split
    {edge : Edge Nat} {index counter finalState finalCounter : Nat}
    (indexedMem : (edge, index) ∈ fixedProgram.edges.zipIdx)
    (instructionEq : edge.instruction = .congruenceTest 3 [0, 1])
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
      edge.instruction.evaluate counter = some counter ∧
      letter :: tail = FixedForward.edgeWord index edge counter counter ++
        suffix ∧
      WordOver listedTemplates suffix ∧
      AllStatesLocal codingPrime suffix
        (phaseAffine (boundaryPhase edge.target)
          (unaryCode codingPrime counter)) ∧
      SameLine
        (physicalWordAction codingPrime suffix
          (phaseAffine (boundaryPhase edge.target)
            (unaryCode codingPrime counter)))
        (phaseAffine (boundaryPhase finalState)
          (unaryCode codingPrime finalCounter)) := by
  have alphabetEq : edgeAlphabet index edge =
      CongruenceModule.congruenceAlphabet
        (boundaryPhase edge.source) (boundaryPhase edge.target) 3
        (privatePhase index) [0, 1] := by
    simp [edgeAlphabet, instructionEq]
  have costEq : instructionPrivateCost edge.instruction = 3 := by
    simp [instructionEq, instructionPrivateCost, modThreeTestCost]
  obtain ⟨allowed, suffix, wordEq, suffixOver, suffixLocal, suffixRun⟩ :=
    globalCongruence_split indexedMem alphabetEq costEq (by decide)
      (by decide) finalStateMem globalOver letterLocal allLocal completeRun
  refine ⟨suffix, ?_, ?_, suffixOver, suffixLocal, suffixRun⟩
  · have allowedBool : [0, 1].contains (counter % 3) = true := by
      simpa using allowed
    rw [instructionEq]
    change (if 3 = 0 then none
      else if [0, 1].contains (counter % 3) then some counter else none) =
        some counter
    rw [if_neg (by decide), if_pos allowedBool]
  · simpa [FixedForward.edgeWord, instructionEq] using wordEq

end Mortality.Compiler.GlobalCongruence
