import Mortality.Compiler.GlobalParserBasics
import Mortality.Compiler.FixedForward

/-!
# Global parsing of ternary division

The word is split at the first template outside the selected fourteen-letter
occurrence.  The preceding local prefix ends either at the final program
boundary or at the guarded input of that first foreign template.  Private
block ownership makes every such endpoint distinct from the six active
private phases, so the module's nonempty endpoint parser applies.  No local
suffix can continue from a non-self-loop target boundary.
-/

namespace Mortality.Compiler.GlobalTernaryDivision

open Mortality
open Mortality.OneCounter
open Mortality.PeriodicCode
open Mortality.Compiler
open Mortality.Compiler.FixedAllocation
open Mortality.Compiler.AllocationProperties
open Mortality.Compiler.GlobalParserBasics

set_option maxRecDepth 100000
set_option maxHeartbeats 3000000

private theorem ternaryPrivate_inBlock
    {edge : Edge Nat} {index offset : Nat}
    (instructionEq : edge.instruction = .divideThreeTwo)
    (offsetBound : offset < 6) :
    InPrivateBlock index edge (privatePhase index offset) := by
  simp [InPrivateBlock, privatePhase, instructionEq,
    instructionPrivateCost, ternaryDivisionCost]
  omega

private theorem ternaryOccurrence_layout
    {edge : Edge Nat} {index : Nat}
    (indexedMem : (edge, index) ∈ fixedProgram.edges.zipIdx)
    (instructionEq : edge.instruction = .divideThreeTwo) :
    TernaryDivisionModule.PhaseLayout totalPhaseCount
      (boundaryPhase edge.source) (privatePhase index 0)
      (privatePhase index 1) (privatePhase index 2)
      (privatePhase index 3) (privatePhase index 4)
      (privatePhase index 5) := by
  have sourceMem := (fixedEdge_endpoints_mem (indexedEdge_mem indexedMem)).1
  have sourceBound := boundaryPhase_bound sourceMem
  have boundariesFit : SourceMachine.quotientStates.length ≤
      genuinePhaseBound := by decide
  have privateBound : ∀ offset, offset < 6 →
      privatePhase index offset < totalPhaseCount := by
    intro offset offsetBound
    have bounded := privateBlock_bounded indexedMem
      (ternaryPrivate_inBlock (index := index) instructionEq offsetBound)
    unfold totalPhaseCount
    omega
  have sourcePrivate : ∀ offset, offset < 6 →
      boundaryPhase edge.source ≠ privatePhase index offset := by
    intro offset offsetBound
    exact boundary_ne_private sourceMem indexedMem
      (ternaryPrivate_inBlock (index := index) instructionEq offsetBound)
  refine
    { front :=
        { core :=
            { sourceBound := by unfold totalPhaseCount; omega
              guessBound := privateBound 0 (by omega)
              firstBound := privateBound 1 (by omega)
              secondBound := privateBound 2 (by omega)
              validatorBound := privateBound 3 (by omega)
              sourceGuessDistinct := sourcePrivate 0 (by omega)
              sourceFirstDistinct := sourcePrivate 1 (by omega)
              sourceSecondDistinct := sourcePrivate 2 (by omega)
              sourceValidatorDistinct := sourcePrivate 3 (by omega)
              guessFirstDistinct := by unfold privatePhase; omega
              guessSecondDistinct := by unfold privatePhase; omega
              guessValidatorDistinct := by unfold privatePhase; omega
              firstSecondDistinct := by unfold privatePhase; omega
              firstValidatorDistinct := by unfold privatePhase; omega
              secondValidatorDistinct := by unfold privatePhase; omega }
          validatorBound := privateBound 4 (by omega)
          sourceValidatorDistinct := sourcePrivate 4 (by omega)
          guessValidatorDistinct := by unfold privatePhase; omega
          firstValidatorDistinct := by unfold privatePhase; omega
          secondValidatorDistinct := by unfold privatePhase; omega
          thirdValidatorDistinct := by unfold privatePhase; omega }
      handoffBound := privateBound 5 (by omega)
      sourceHandoffDistinct := sourcePrivate 5 (by omega)
      guessHandoffDistinct := by unfold privatePhase; omega
      firstHandoffDistinct := by unfold privatePhase; omega
      secondHandoffDistinct := by unfold privatePhase; omega
      thirdHandoffDistinct := by unfold privatePhase; omega
      validatorHandoffDistinct := by unfold privatePhase; omega }

private theorem edgeAlphabet_eq_ternary
    {edge : Edge Nat} {index : Nat}
    (instructionEq : edge.instruction = .divideThreeTwo) :
    edgeAlphabet index edge =
      TernaryDivisionModule.ternaryDivisionAlphabet
        (boundaryPhase edge.source) (boundaryPhase edge.target)
        (privatePhase index 0) (privatePhase index 1)
        (privatePhase index 2) (privatePhase index 3)
        (privatePhase index 4) (privatePhase index 5) := by
  simp [edgeAlphabet, instructionEq]

private theorem ternary_notIncrement
    {edge : Edge Nat}
    (instructionEq : edge.instruction = .divideThreeTwo) :
    edge.instruction ≠ .increment := by
  simp [instructionEq]

/-- A foreign surviving letter cannot advertise any private phase of the
selected ternary-division occurrence. -/
private theorem foreignEndpoint_ne_private
    {edge : Edge Nat} {index offset : Nat}
    (indexedMem : (edge, index) ∈ fixedProgram.edges.zipIdx)
    (instructionEq : edge.instruction = .divideThreeTwo)
    (offsetBound : offset < 6)
    {foreign : PhysicalTemplate} {vector : Vec2}
    (foreignGlobal : foreign ∈ listedTemplates)
    (foreignNotLocal : foreign ∉ edgeAlphabet index edge)
    (membership : InPhaseAt codingPrime foreign.sourcePhase foreign.digit
      vector)
    (outputLocal : LocalAt codingPrime
      (foreign.act codingPrime vector)) :
    privatePhase index offset ≠ foreign.sourcePhase := by
  intro phaseEq
  have privateMembership : InPhaseAt codingPrime (privatePhase index offset)
      foreign.digit vector := by
    simpa [phaseEq] using membership
  have localMem := survivingListedLetter_at_private indexedMem
    (ternaryPrivate_inBlock (index := index) instructionEq offsetBound)
    privateMembership foreignGlobal outputLocal
  exact foreignNotLocal localMem

/-- A nonempty local ternary-division path to a guarded endpoint outside its
private phases is exactly one accepted instruction word. -/
private theorem localTernaryWord_unique
    {edge : Edge Nat} {index counter endpointPhase : Nat}
    {endpointDigit : Int} {endpoint : Vec2}
    (indexedMem : (edge, index) ∈ fixedProgram.edges.zipIdx)
    (instructionEq : edge.instruction = .divideThreeTwo)
    (endpointBound : endpointPhase < totalPhaseCount)
    (privateDistinct : ∀ offset, offset < 6 →
      privatePhase index offset ≠ endpointPhase)
    (endpointMembership : InPhaseAt codingPrime endpointPhase endpointDigit
      endpoint)
    {word : List PhysicalTemplate}
    (wordOver : WordOver (edgeAlphabet index edge) word)
    (wordNonempty : word ≠ [])
    (completeRun : SameLine
      (physicalWordAction codingPrime word
        (phaseAffine (boundaryPhase edge.source)
          (unaryCode codingPrime counter))) endpoint) :
    ∃ output,
      edge.instruction.evaluate counter = some output ∧
      word = FixedForward.edgeWord index edge counter output := by
  have layout := ternaryOccurrence_layout indexedMem instructionEq
  have counterPositive : 0 < counter := by
    have inputLocal := IncrementModule.phaseUnaryCode_local codingPrime
      (boundaryPhase edge.source) counter codingPrime_isPrime.1
    have outputNonzero := physicalWordAction_nonzero
      (prime := codingPrime) (by have := codingPrime_isPrime.1; omega)
      word inputLocal.1
    have finalLocal := LocalAt.of_sameLine endpointMembership.local
      outputNonzero completeRun
    have allLocal := allStatesLocal_of_final_local
      (by have := codingPrime_isPrime.1; omega) word inputLocal.1 finalLocal
    cases counter with
    | zero =>
        cases word with
        | nil => exact False.elim (wordNonempty rfl)
        | cons letter tail =>
            have letterMem := wordOver letter (by simp)
            have moduleMem : letter ∈
                TernaryDivisionModule.ternaryDivisionAlphabet
                  (boundaryPhase edge.source) (boundaryPhase edge.target)
                  (privatePhase index 0) (privatePhase index 1)
                  (privatePhase index 2) (privatePhase index 3)
                  (privatePhase index 4) (privatePhase index 5) := by
              simpa [edgeAlphabet_eq_ternary instructionEq] using letterMem
            exact False.elim
              ((TernaryDivisionModule.source_rejects_zero
                codingPrime_isPrime codingPrime_phase_bound layout moduleMem)
                allLocal.2.start)
    | succ previous => omega
  have moduleOver : WordOver
      (TernaryDivisionModule.ternaryDivisionAlphabet
        (boundaryPhase edge.source) (boundaryPhase edge.target)
        (privatePhase index 0) (privatePhase index 1)
        (privatePhase index 2) (privatePhase index 3)
        (privatePhase index 4) (privatePhase index 5)) word := by
    simpa [edgeAlphabet_eq_ternary instructionEq] using wordOver
  obtain ⟨output, suffix, counterEq, wordEq, suffixOver, suffixLocal,
      _suffixRun⟩ :=
    TernaryDivisionModule.ternaryDivisionWord_forced_prefix_to_endpoint_of_nonempty
      codingPrime_isPrime codingPrime_phase_bound layout endpointBound
      (privateDistinct 0 (by omega)) (privateDistinct 1 (by omega))
      (privateDistinct 2 (by omega)) (privateDistinct 3 (by omega))
      (privateDistinct 4 (by omega)) (privateDistinct 5 (by omega))
      endpointMembership counterPositive moduleOver wordNonempty completeRun
  have suffixLocalOver : WordOver (edgeAlphabet index edge) suffix := by
    simpa [edgeAlphabet_eq_ternary instructionEq] using suffixOver
  have suffixEmpty := localWord_from_target_empty indexedMem
    (ternary_notIncrement instructionEq) suffixLocalOver suffixLocal
  subst suffix
  refine ⟨output, ?_, ?_⟩
  · simpa [instructionEq] using
      (Instruction.evaluate_divideThreeTwo_iff.mpr counterEq)
  · simpa [FixedForward.edgeWord, instructionEq] using wordEq

/-- Parse the selected ternary-division occurrence at the front of an
arbitrary globally surviving word, returning the untouched global suffix at
the target boundary. -/
theorem globalTernaryDivision_split
    {edge : Edge Nat} {index counter finalState finalCounter : Nat}
    (indexedMem : (edge, index) ∈ fixedProgram.edges.zipIdx)
    (instructionEq : edge.instruction = .divideThreeTwo)
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
  · have wordNonempty : (letter :: tail) ≠ [] := by simp
    have endpointBound : boundaryPhase finalState < totalPhaseCount := by
      have denseBound := boundaryPhase_bound finalStateMem
      have boundariesFit : SourceMachine.quotientStates.length ≤
          genuinePhaseBound := by decide
      unfold totalPhaseCount
      omega
    have privateDistinct : ∀ offset, offset < 6 →
        privatePhase index offset ≠ boundaryPhase finalState := by
      intro offset offsetBound
      exact (boundary_ne_private finalStateMem indexedMem
        (ternaryPrivate_inBlock (index := index) instructionEq offsetBound)).symm
    obtain ⟨output, evaluation, exactWord⟩ := localTernaryWord_unique
      indexedMem instructionEq endpointBound privateDistinct finalMembership
      localOnly wordNonempty completeRun
    have canonicalRun := FixedForward.edgeWord_correct index edge counter
      output (FixedForward.fixedEdge_supported (indexedEdge_mem indexedMem))
      evaluation
    have targetLocal := IncrementModule.phaseUnaryCode_local codingPrime
      (boundaryPhase edge.target) output codingPrime_isPrime.1
    have completeRun' := completeRun
    rw [exactWord] at completeRun'
    refine ⟨output, [], evaluation, ?_, wordOver_nil _, targetLocal, ?_⟩
    · simp [exactWord]
    · simpa [physicalWordAction] using
        canonicalRun.symm.trans completeRun'
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
    have privateDistinct : ∀ offset, offset < 6 →
        privatePhase index offset ≠ foreign.sourcePhase := by
      intro offset offsetBound
      exact foreignEndpoint_ne_private indexedMem instructionEq offsetBound
        foreignGlobal foreignNotLocal foreignMembership
        foreignTailLocal.2.start
    have initialNonempty : initial ≠ [] := by
      intro initialEmpty
      subst initial
      simp only [List.nil_append, List.cons.injEq] at wordEq
      exact foreignNotLocal (wordEq.1 ▸ letterLocal)
    obtain ⟨output, evaluation, initialEq⟩ := localTernaryWord_unique
      indexedMem instructionEq endpointBound privateDistinct foreignMembership
      initialOver initialNonempty (SameLine.refl _)
    have canonicalRun := FixedForward.edgeWord_correct index edge counter
      output (FixedForward.fixedEdge_supported (indexedEdge_mem indexedMem))
      evaluation
    have targetCodeNonzero :
        (phaseAffine (boundaryPhase edge.target)
          (unaryCode codingPrime output)).Nonzero := Vec2.affine_nonzero _
    have boundarySame : SameLine
        (phaseAffine (boundaryPhase edge.target)
          (unaryCode codingPrime output))
        (physicalWordAction codingPrime initial
          (phaseAffine (boundaryPhase edge.source)
            (unaryCode codingPrime counter))) := by
      rw [initialEq]
      exact canonicalRun.symm
    have residualLocal : AllStatesLocal codingPrime (foreign :: rest)
        (phaseAffine (boundaryPhase edge.target)
          (unaryCode codingPrime output)) := by
      apply AllStatesLocal.of_sameLine
        (primePositive := by have := codingPrime_isPrime.1; omega)
        foreignTailLocal targetCodeNonzero
      exact boundarySame
    have residualRunRaw : SameLine
        (physicalWordAction codingPrime (foreign :: rest)
          (physicalWordAction codingPrime initial
            (phaseAffine (boundaryPhase edge.source)
              (unaryCode codingPrime counter))))
        (phaseAffine (boundaryPhase finalState)
          (unaryCode codingPrime finalCounter)) := by
      rw [wordEq, physicalWordAction_append] at completeRun
      exact completeRun
    have residualRun : SameLine
        (physicalWordAction codingPrime (foreign :: rest)
          (phaseAffine (boundaryPhase edge.target)
            (unaryCode codingPrime output)))
        (phaseAffine (boundaryPhase finalState)
          (unaryCode codingPrime finalCounter)) :=
      (physicalWordAction_preserves_sameLine codingPrime (foreign :: rest)
        boundarySame).trans
        residualRunRaw
    refine ⟨output, foreign :: rest, evaluation, ?_, ?_, residualLocal,
      residualRun⟩
    · rw [wordEq, initialEq]
    · exact wordOver_cons foreignGlobal restGlobal

end Mortality.Compiler.GlobalTernaryDivision
