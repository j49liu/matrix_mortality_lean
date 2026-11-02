import Mortality.Compiler.GlobalParserBasics
import Mortality.Compiler.FixedForward
import Mortality.Compiler.ContractionModulesConverse

/-!
# Global parsing of the two contraction instructions

For each concrete contraction occurrence, this file instantiates the
validated-front and projection layouts inside its private phase block.  A
first-foreign-letter split then reduces an arbitrary word over all 5,798
templates to the endpoint-aware contraction converses.  The result extracts
one exact contraction block and returns the untouched global suffix at the
instruction target.
-/

namespace Mortality.Compiler.GlobalContractions

open Mortality
open Mortality.OneCounter
open Mortality.PeriodicCode
open Mortality.Compiler
open Mortality.Compiler.FixedAllocation
open Mortality.Compiler.AllocationProperties
open Mortality.Compiler.GlobalParserBasics
open Mortality.Compiler.ValidatedFivefoldFrontModule
open Mortality.Compiler.ContractionModules

set_option maxRecDepth 100000
set_option maxHeartbeats 3000000

private theorem twoPrivate_inBlock
    {edge : Edge Nat} {index offset : Nat}
    (instructionEq : edge.instruction = .contractTwo)
    (offsetBound : offset < 14) :
    InPrivateBlock index edge (privatePhase index offset) := by
  simp [InPrivateBlock, privatePhase, instructionEq,
    instructionPrivateCost, contractionTwoCost]
  omega

private theorem threePrivate_inBlock
    {edge : Edge Nat} {index offset : Nat}
    (instructionEq : edge.instruction = .contractThree)
    (offsetBound : offset < 15) :
    InPrivateBlock index edge (privatePhase index offset) := by
  simp [InPrivateBlock, privatePhase, instructionEq,
    instructionPrivateCost, contractionThreeCost]
  omega

private theorem edgeAlphabet_eq_two
    {edge : Edge Nat} {index : Nat}
    (instructionEq : edge.instruction = .contractTwo) :
    edgeAlphabet index edge =
      twoAlphabet (boundaryPhase edge.source)
        (privatePhase index 0) (privatePhase index 1)
        (privatePhase index 2) (boundaryPhase edge.target)
        (privatePhase index 3) (privatePhase index 4)
        (privatePhase index 5) (privatePhase index 6)
        (privatePhase index 7) (privatePhase index 8)
        (privatePhase index 9) (privatePhase index 10)
        (privatePhase index 11) (privatePhase index 12)
        (privatePhase index 13) := by
  simp [edgeAlphabet, instructionEq]

private theorem edgeAlphabet_eq_three
    {edge : Edge Nat} {index : Nat}
    (instructionEq : edge.instruction = .contractThree) :
    edgeAlphabet index edge =
      threeAlphabet (boundaryPhase edge.source)
        (privatePhase index 0) (privatePhase index 1)
        (boundaryPhase edge.target) (privatePhase index 2)
        (privatePhase index 3) (privatePhase index 4)
        (privatePhase index 5) (privatePhase index 6)
        (privatePhase index 7) (privatePhase index 8)
        (privatePhase index 9) (privatePhase index 10)
        (privatePhase index 11) (privatePhase index 12)
        (privatePhase index 13) (privatePhase index 14) := by
  simp [edgeAlphabet, instructionEq]

private theorem contraction_notIncrement
    {edge : Edge Nat} {instruction : Instruction}
    (instructionEq : edge.instruction = instruction)
    (instructionNe : instruction ≠ .increment) :
    edge.instruction ≠ .increment := by
  simpa [instructionEq] using instructionNe

private theorem twoFrontLayout
    {edge : Edge Nat} {index : Nat}
    (indexedMem : (edge, index) ∈ fixedProgram.edges.zipIdx)
    (instructionEq : edge.instruction = .contractTwo) :
    FivefoldFrontModule.PhaseLayout totalPhaseCount
      (boundaryPhase edge.source) (privatePhase index 3)
      (privatePhase index 4) (privatePhase index 5)
      (privatePhase index 6) (privatePhase index 7)
      (privatePhase index 8) (privatePhase index 9) := by
  have sourceMem := (fixedEdge_endpoints_mem (indexedEdge_mem indexedMem)).1
  have sourceBound := boundaryPhase_bound sourceMem
  have boundariesFit : SourceMachine.quotientStates.length ≤
      genuinePhaseBound := by decide
  have privateBound : ∀ offset, offset < 14 →
      privatePhase index offset < totalPhaseCount := by
    intro offset offsetBound
    have bounded := privateBlock_bounded indexedMem
      (twoPrivate_inBlock (index := index) instructionEq offsetBound)
    unfold totalPhaseCount
    omega
  have sourcePrivate : ∀ offset, offset < 14 →
      boundaryPhase edge.source ≠ privatePhase index offset := by
    intro offset offsetBound
    exact boundary_ne_private sourceMem indexedMem
      (twoPrivate_inBlock (index := index) instructionEq offsetBound)
  refine
    { sourceBound := by unfold totalPhaseCount; omega
      guessBound := privateBound 3 (by omega)
      firstBound := privateBound 4 (by omega)
      secondBound := privateBound 5 (by omega)
      thirdBound := privateBound 6 (by omega)
      fourthBound := privateBound 7 (by omega)
      fifthBound := privateBound 8 (by omega)
      markerTwoBound := privateBound 9 (by omega)
      distinct := ?_ }
  have s3 := sourcePrivate 3 (by omega)
  have s4 := sourcePrivate 4 (by omega)
  have s5 := sourcePrivate 5 (by omega)
  have s6 := sourcePrivate 6 (by omega)
  have s7 := sourcePrivate 7 (by omega)
  have s8 := sourcePrivate 8 (by omega)
  have s9 := sourcePrivate 9 (by omega)
  simp [List.nodup_cons, privatePhase] at s3 s4 s5 s6 s7 s8 s9 ⊢
  exact ⟨s3, s4, s5, s6, s7, s8, s9⟩

private theorem threeFrontLayout
    {edge : Edge Nat} {index : Nat}
    (indexedMem : (edge, index) ∈ fixedProgram.edges.zipIdx)
    (instructionEq : edge.instruction = .contractThree) :
    FivefoldFrontModule.PhaseLayout totalPhaseCount
      (boundaryPhase edge.source) (privatePhase index 2)
      (privatePhase index 3) (privatePhase index 4)
      (privatePhase index 5) (privatePhase index 6)
      (privatePhase index 7) (privatePhase index 8) := by
  have sourceMem := (fixedEdge_endpoints_mem (indexedEdge_mem indexedMem)).1
  have sourceBound := boundaryPhase_bound sourceMem
  have boundariesFit : SourceMachine.quotientStates.length ≤
      genuinePhaseBound := by decide
  have privateBound : ∀ offset, offset < 15 →
      privatePhase index offset < totalPhaseCount := by
    intro offset offsetBound
    have bounded := privateBlock_bounded indexedMem
      (threePrivate_inBlock (index := index) instructionEq offsetBound)
    unfold totalPhaseCount
    omega
  have sourcePrivate : ∀ offset, offset < 15 →
      boundaryPhase edge.source ≠ privatePhase index offset := by
    intro offset offsetBound
    exact boundary_ne_private sourceMem indexedMem
      (threePrivate_inBlock (index := index) instructionEq offsetBound)
  refine
    { sourceBound := by unfold totalPhaseCount; omega
      guessBound := privateBound 2 (by omega)
      firstBound := privateBound 3 (by omega)
      secondBound := privateBound 4 (by omega)
      thirdBound := privateBound 5 (by omega)
      fourthBound := privateBound 6 (by omega)
      fifthBound := privateBound 7 (by omega)
      markerTwoBound := privateBound 8 (by omega)
      distinct := ?_ }
  have s2 := sourcePrivate 2 (by omega)
  have s3 := sourcePrivate 3 (by omega)
  have s4 := sourcePrivate 4 (by omega)
  have s5 := sourcePrivate 5 (by omega)
  have s6 := sourcePrivate 6 (by omega)
  have s7 := sourcePrivate 7 (by omega)
  have s8 := sourcePrivate 8 (by omega)
  simp [List.nodup_cons, privatePhase] at s2 s3 s4 s5 s6 s7 s8 ⊢
  exact ⟨s2, s3, s4, s5, s6, s7, s8⟩

private theorem twoProjectionLayout
    {edge : Edge Nat} {index : Nat}
    (indexedMem : (edge, index) ∈ fixedProgram.edges.zipIdx)
    (instructionEq : edge.instruction = .contractTwo) :
    TwoProjectionModule.PhaseLayout totalPhaseCount
      (privatePhase index 2) (privatePhase index 10)
      (privatePhase index 11) (privatePhase index 12)
      (privatePhase index 13) := by
  have privateBound : ∀ offset, offset < 14 →
      privatePhase index offset < totalPhaseCount := by
    intro offset offsetBound
    have bounded := privateBlock_bounded indexedMem
      (twoPrivate_inBlock (index := index) instructionEq offsetBound)
    unfold totalPhaseCount
    omega
  constructor <;> try { exact privateBound _ (by omega) } <;>
    unfold privatePhase <;> omega

private theorem threeProjectionLayout
    {edge : Edge Nat} {index : Nat}
    (indexedMem : (edge, index) ∈ fixedProgram.edges.zipIdx)
    (instructionEq : edge.instruction = .contractThree) :
    ThreeProjectionModule.PhaseLayout totalPhaseCount
      (privatePhase index 1) (privatePhase index 9)
      (privatePhase index 10) (privatePhase index 11)
      (privatePhase index 12) (privatePhase index 13)
      (privatePhase index 14) := by
  have privateBound : ∀ offset, offset < 15 →
      privatePhase index offset < totalPhaseCount := by
    intro offset offsetBound
    have bounded := privateBlock_bounded indexedMem
      (threePrivate_inBlock (index := index) instructionEq offsetBound)
    unfold totalPhaseCount
    omega
  constructor <;> try { exact privateBound _ (by omega) } <;>
    unfold privatePhase <;> omega

private theorem sourceTargetBoundaryDistinct
    {edge : Edge Nat} {index : Nat}
    (indexedMem : (edge, index) ∈ fixedProgram.edges.zipIdx)
    (notIncrement : edge.instruction ≠ .increment) :
    boundaryPhase edge.source ≠ boundaryPhase edge.target := by
  intro phaseEq
  have endpoints := fixedEdge_endpoints_mem (indexedEdge_mem indexedMem)
  have stateEq := boundaryPhase_injective_on_quotientStates endpoints.1
    endpoints.2 phaseEq
  exact (fixedEdge_source_ne_target_of_not_increment indexedMem notIncrement)
    stateEq

private theorem foreignEndpoint_ne_twoPrivate
    {edge : Edge Nat} {index offset : Nat}
    (indexedMem : (edge, index) ∈ fixedProgram.edges.zipIdx)
    (instructionEq : edge.instruction = .contractTwo)
    (offsetBound : offset < 14)
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
      foreign.digit vector := by simpa [phaseEq] using membership
  have localMem := survivingListedLetter_at_private indexedMem
    (twoPrivate_inBlock (index := index) instructionEq offsetBound)
    privateMembership foreignGlobal outputLocal
  exact foreignNotLocal localMem

private theorem foreignEndpoint_ne_threePrivate
    {edge : Edge Nat} {index offset : Nat}
    (indexedMem : (edge, index) ∈ fixedProgram.edges.zipIdx)
    (instructionEq : edge.instruction = .contractThree)
    (offsetBound : offset < 15)
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
      foreign.digit vector := by simpa [phaseEq] using membership
  have localMem := survivingListedLetter_at_private indexedMem
    (threePrivate_inBlock (index := index) instructionEq offsetBound)
    privateMembership foreignGlobal outputLocal
  exact foreignNotLocal localMem

/-- A nonempty local two-to-one contraction path ending outside its private
block is exactly one successful instruction word. -/
private theorem localContractTwoWord_unique
    {edge : Edge Nat} {index counter endpointPhase : Nat}
    {endpointDigit : Int} {endpoint : Vec2}
    (indexedMem : (edge, index) ∈ fixedProgram.edges.zipIdx)
    (instructionEq : edge.instruction = .contractTwo)
    (endpointBound : endpointPhase < totalPhaseCount)
    (privateDistinct : ∀ offset, offset < 14 →
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
  let source := boundaryPhase edge.source
  let target := boundaryPhase edge.target
  let p := privatePhase index
  have edgeMem := indexedEdge_mem indexedMem
  have endpoints := fixedEdge_endpoints_mem edgeMem
  have sourceBoundDense := boundaryPhase_bound endpoints.1
  have targetBoundDense := boundaryPhase_bound endpoints.2
  have boundariesFit : SourceMachine.quotientStates.length ≤
      genuinePhaseBound := by decide
  have sourceBound : source < totalPhaseCount := by
    dsimp [source]
    unfold totalPhaseCount
    omega
  have targetBound : target < totalPhaseCount := by
    dsimp [target]
    unfold totalPhaseCount
    omega
  have privateBound : ∀ offset, offset < 14 →
      p offset < totalPhaseCount := by
    intro offset offsetBound
    have bounded := privateBlock_bounded indexedMem
      (twoPrivate_inBlock (index := index) instructionEq offsetBound)
    dsimp [p]
    unfold totalPhaseCount
    omega
  have sourcePrivate : ∀ offset, offset < 14 →
      source ≠ p offset := by
    intro offset offsetBound
    exact boundary_ne_private endpoints.1 indexedMem
      (twoPrivate_inBlock (index := index) instructionEq offsetBound)
  have targetPrivate : ∀ offset, offset < 14 →
      target ≠ p offset := by
    intro offset offsetBound
    exact boundary_ne_private endpoints.2 indexedMem
      (twoPrivate_inBlock (index := index) instructionEq offsetBound)
  have notIncrement : edge.instruction ≠ .increment := by
    simp [instructionEq]
  have sourceTarget : source ≠ target := by
    exact sourceTargetBoundaryDistinct indexedMem notIncrement
  have frontLayout := twoFrontLayout indexedMem instructionEq
  have projectionLayout := twoProjectionLayout indexedMem instructionEq
  have frontHandoffNotCore : p 0 ∉
      [source, p 3, p 4, p 5, p 6, p 7, p 8, p 9] := by
    have s0 := sourcePrivate 0 (by omega)
    simp [p, privatePhase] at s0 ⊢
    omega
  have intermediateNotCore : p 1 ∉
      [source, p 3, p 4, p 5, p 6, p 7, p 8, p 9] := by
    have s1 := sourcePrivate 1 (by omega)
    simp [p, privatePhase] at s1 ⊢
    omega
  have frontInternalDistinct : p 0 ≠ p 1 := by
    dsimp [p]
    unfold privatePhase
    omega
  have frontProjectionDisjoint : PhaseDisjoint
      (doubleSourcePhases source (p 0) (p 1)
        (p 3) (p 4) (p 5) (p 6) (p 7) (p 8) (p 9))
      (twoProjectionSourcePhases (p 2) (p 10) (p 11) (p 12) (p 13)) := by
    intro phase frontMem projectionMem
    have s2 := sourcePrivate 2 (by omega)
    have s10 := sourcePrivate 10 (by omega)
    have s11 := sourcePrivate 11 (by omega)
    have s12 := sourcePrivate 12 (by omega)
    have s13 := sourcePrivate 13 (by omega)
    simp [doubleSourcePhases, twoProjectionSourcePhases, p, privatePhase]
      at frontMem projectionMem s2 s10 s11 s12 s13
    omega
  have targetNotFront : target ∉
      doubleSourcePhases source (p 0) (p 1)
        (p 3) (p 4) (p 5) (p 6) (p 7) (p 8) (p 9) := by
    intro targetMem
    have t0 := targetPrivate 0 (by omega)
    have t1 := targetPrivate 1 (by omega)
    have t3 := targetPrivate 3 (by omega)
    have t4 := targetPrivate 4 (by omega)
    have t5 := targetPrivate 5 (by omega)
    have t6 := targetPrivate 6 (by omega)
    have t7 := targetPrivate 7 (by omega)
    have t8 := targetPrivate 8 (by omega)
    have t9 := targetPrivate 9 (by omega)
    simp [doubleSourcePhases] at targetMem
    omega
  have targetNotProjection : target ∉
      twoProjectionSourcePhases (p 2) (p 10) (p 11) (p 12) (p 13) := by
    intro targetMem
    have t2 := targetPrivate 2 (by omega)
    have t10 := targetPrivate 10 (by omega)
    have t11 := targetPrivate 11 (by omega)
    have t12 := targetPrivate 12 (by omega)
    have t13 := targetPrivate 13 (by omega)
    simp [twoProjectionSourcePhases] at targetMem
    omega
  have endpointNotFrontInternal : endpointPhase ∉
      [p 0, p 1, p 3, p 4, p 5, p 6, p 7, p 8, p 9] := by
    intro endpointMem
    have d0 := privateDistinct 0 (by omega)
    have d1 := privateDistinct 1 (by omega)
    have d3 := privateDistinct 3 (by omega)
    have d4 := privateDistinct 4 (by omega)
    have d5 := privateDistinct 5 (by omega)
    have d6 := privateDistinct 6 (by omega)
    have d7 := privateDistinct 7 (by omega)
    have d8 := privateDistinct 8 (by omega)
    have d9 := privateDistinct 9 (by omega)
    change p 0 ≠ endpointPhase at d0
    change p 1 ≠ endpointPhase at d1
    change p 3 ≠ endpointPhase at d3
    change p 4 ≠ endpointPhase at d4
    change p 5 ≠ endpointPhase at d5
    change p 6 ≠ endpointPhase at d6
    change p 7 ≠ endpointPhase at d7
    change p 8 ≠ endpointPhase at d8
    change p 9 ≠ endpointPhase at d9
    simp at endpointMem
    omega
  have endpointNotProjection : endpointPhase ∉
      twoProjectionSourcePhases (p 2) (p 10) (p 11) (p 12) (p 13) := by
    intro endpointMem
    have d2 := privateDistinct 2 (by omega)
    have d10 := privateDistinct 10 (by omega)
    have d11 := privateDistinct 11 (by omega)
    have d12 := privateDistinct 12 (by omega)
    have d13 := privateDistinct 13 (by omega)
    change p 2 ≠ endpointPhase at d2
    change p 10 ≠ endpointPhase at d10
    change p 11 ≠ endpointPhase at d11
    change p 12 ≠ endpointPhase at d12
    change p 13 ≠ endpointPhase at d13
    simp [twoProjectionSourcePhases] at endpointMem
    omega
  have moduleOver : WordOver
      (twoAlphabet source (p 0) (p 1) (p 2) target
        (p 3) (p 4) (p 5) (p 6) (p 7) (p 8) (p 9)
        (p 10) (p 11) (p 12) (p 13)) word := by
    simpa [source, target, p, edgeAlphabet_eq_two instructionEq] using wordOver
  have inputLocal := IncrementModule.phaseUnaryCode_local codingPrime source
    counter codingPrime_isPrime.1
  have outputNonzero := physicalWordAction_nonzero
    (prime := codingPrime) (by have := codingPrime_isPrime.1; omega)
    word inputLocal.1
  have finalLocal := LocalAt.of_sameLine endpointMembership.local
    outputNonzero completeRun
  have allLocal := allStatesLocal_of_final_local
    (by have := codingPrime_isPrime.1; omega) word inputLocal.1 finalLocal
  have counterPositive : 0 < counter := by
    cases counter with
    | succ previous => omega
    | zero =>
        cases word with
        | nil => exact False.elim (wordNonempty rfl)
        | cons letter tail =>
            have letterMem := moduleOver letter (by simp)
            have letterLocalMem : letter ∈ edgeAlphabet index edge := by
              simpa [source, target, p, edgeAlphabet_eq_two instructionEq]
                using letterMem
            have letterListed := edgeLetter_listed indexedMem letterLocalMem
            have guard := listedLetter_guard letterListed
            have inputMembership : InPhaseAt codingPrime source 1
                (phaseAffine source (unaryCode codingPrime 0)) := by
              simpa [unaryCode, unaryDigits] using
                (periodicCode_inPhaseAt codingPrime source 1 []
                  codingPrime_isPrime.1 (by simp [ReservedDigit]))
            have letterMembership : InPhaseAt codingPrime letter.sourcePhase
                letter.digit (phaseAffine source (unaryCode codingPrime 0)) := by
              apply physicalLetter_input_inPhaseAt codingPrime_isPrime
                guard.2.2 inputLocal
              simpa [PhysicalTemplate.act, PhysicalTemplate.matrix] using
                allLocal.2.start
            have sourceEq := (inputMembership.unique codingPrime_isPrime
              codingPrime_phase_bound sourceBound
              (by have := guard.1; unfold totalPhaseCount; omega)
              letterMembership (SameLine.refl _)).1.symm
            have splitMem :
                letter ∈ FivefoldFrontModule.alphabet source (p 0)
                    (p 3) (p 4) (p 5) (p 6) (p 7) (p 8) (p 9) ∨
                letter ∈ doubleValidatorAlphabet (p 0) (p 1) (p 2) ∨
                letter ∈ TwoProjectionModule.alphabet (p 2) target
                    (p 10) (p 11) (p 12) (p 13) := by
              simpa [twoAlphabet, doubleAlphabet_eq] using letterMem
            rcases splitMem with coreMem | validatorMem | projectionMem
            · have forced := FivefoldFrontModule.source_letter
                codingPrime_isPrime codingPrime_phase_bound frontLayout
                inputMembership coreMem allLocal.2.start
              omega
            · rcases doubleValidatorLetter_source validatorMem with
                handoffSource | intermediateSource
              · have distinct := sourcePrivate 0 (by omega)
                exact False.elim (distinct (sourceEq.symm.trans handoffSource))
              · have distinct := sourcePrivate 1 (by omega)
                exact False.elim
                  (distinct (sourceEq.symm.trans intermediateSource))
            · have active := twoProjectionLetter_source_mem projectionMem
              simp [twoProjectionSourcePhases] at active
              rcases active with h | h | h | h | h
              · exact False.elim
                  ((sourcePrivate 2 (by omega)) (sourceEq.symm.trans h))
              · exact False.elim
                  ((sourcePrivate 10 (by omega)) (sourceEq.symm.trans h))
              · exact False.elim
                  ((sourcePrivate 11 (by omega)) (sourceEq.symm.trans h))
              · exact False.elim
                  ((sourcePrivate 12 (by omega)) (sourceEq.symm.trans h))
              · exact False.elim
                  ((sourcePrivate 13 (by omega)) (sourceEq.symm.trans h))
  obtain ⟨first, residual, counterEq, wordEq, residualOver, residualLocal,
      _⟩ :=
    twoWord_forces_prefix_general_to_endpoint_of_nonempty codingPrime_isPrime
      codingPrime_phase_bound frontLayout projectionLayout
      (privateBound 0 (by omega)) (privateBound 1 (by omega)) targetBound
      endpointBound frontHandoffNotCore intermediateNotCore
      frontInternalDistinct frontProjectionDisjoint targetNotFront
      targetNotProjection endpointNotFrontInternal endpointNotProjection
      endpointMembership counterPositive moduleOver wordNonempty allLocal
      completeRun
  have residualLocalOver : WordOver (edgeAlphabet index edge) residual := by
    simpa [source, target, p, edgeAlphabet_eq_two instructionEq] using
      residualOver
  have residualEmpty := localWord_from_target_empty indexedMem notIncrement
    residualLocalOver residualLocal
  subst residual
  refine ⟨2 * first + 1, ?_, ?_⟩
  · rw [instructionEq]
    apply Instruction.evaluate_contractTwo_iff.mpr
    exact ⟨first, counterEq, rfl⟩
  · have quotientEq : counter / 5 = first := by omega
    simpa [FixedForward.edgeWord, instructionEq, source, target, p,
      quotientEq] using wordEq

/-- A nonempty local three-to-one contraction path ending outside its private
block is exactly one successful instruction word. -/
private theorem localContractThreeWord_unique
    {edge : Edge Nat} {index counter endpointPhase : Nat}
    {endpointDigit : Int} {endpoint : Vec2}
    (indexedMem : (edge, index) ∈ fixedProgram.edges.zipIdx)
    (instructionEq : edge.instruction = .contractThree)
    (endpointBound : endpointPhase < totalPhaseCount)
    (privateDistinct : ∀ offset, offset < 15 →
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
  let source := boundaryPhase edge.source
  let target := boundaryPhase edge.target
  let p := privatePhase index
  have edgeMem := indexedEdge_mem indexedMem
  have endpoints := fixedEdge_endpoints_mem edgeMem
  have sourceBoundDense := boundaryPhase_bound endpoints.1
  have targetBoundDense := boundaryPhase_bound endpoints.2
  have boundariesFit : SourceMachine.quotientStates.length ≤
      genuinePhaseBound := by decide
  have sourceBound : source < totalPhaseCount := by
    dsimp [source]
    unfold totalPhaseCount
    omega
  have targetBound : target < totalPhaseCount := by
    dsimp [target]
    unfold totalPhaseCount
    omega
  have privateBound : ∀ offset, offset < 15 →
      p offset < totalPhaseCount := by
    intro offset offsetBound
    have bounded := privateBlock_bounded indexedMem
      (threePrivate_inBlock (index := index) instructionEq offsetBound)
    dsimp [p]
    unfold totalPhaseCount
    omega
  have sourcePrivate : ∀ offset, offset < 15 →
      source ≠ p offset := by
    intro offset offsetBound
    exact boundary_ne_private endpoints.1 indexedMem
      (threePrivate_inBlock (index := index) instructionEq offsetBound)
  have targetPrivate : ∀ offset, offset < 15 →
      target ≠ p offset := by
    intro offset offsetBound
    exact boundary_ne_private endpoints.2 indexedMem
      (threePrivate_inBlock (index := index) instructionEq offsetBound)
  have notIncrement : edge.instruction ≠ .increment := by
    simp [instructionEq]
  have sourceTarget : source ≠ target :=
    sourceTargetBoundaryDistinct indexedMem notIncrement
  have frontLayout := threeFrontLayout indexedMem instructionEq
  have projectionLayout := threeProjectionLayout indexedMem instructionEq
  have frontHandoffNotCore : p 0 ∉
      [source, p 2, p 3, p 4, p 5, p 6, p 7, p 8] := by
    have s0 := sourcePrivate 0 (by omega)
    simp [p, privatePhase] at s0 ⊢
    omega
  have frontProjectionDisjoint : PhaseDisjoint
      (singleSourcePhases source (p 0)
        (p 2) (p 3) (p 4) (p 5) (p 6) (p 7) (p 8))
      (threeProjectionSourcePhases (p 1) (p 9) (p 10) (p 11)
        (p 12) (p 13) (p 14)) := by
    intro phase frontMem projectionMem
    have s1 := sourcePrivate 1 (by omega)
    have s9 := sourcePrivate 9 (by omega)
    have s10 := sourcePrivate 10 (by omega)
    have s11 := sourcePrivate 11 (by omega)
    have s12 := sourcePrivate 12 (by omega)
    have s13 := sourcePrivate 13 (by omega)
    have s14 := sourcePrivate 14 (by omega)
    simp [singleSourcePhases, threeProjectionSourcePhases, p, privatePhase]
      at frontMem projectionMem s1 s9 s10 s11 s12 s13 s14
    omega
  have targetNotFront : target ∉
      singleSourcePhases source (p 0)
        (p 2) (p 3) (p 4) (p 5) (p 6) (p 7) (p 8) := by
    intro targetMem
    have t0 := targetPrivate 0 (by omega)
    have t2 := targetPrivate 2 (by omega)
    have t3 := targetPrivate 3 (by omega)
    have t4 := targetPrivate 4 (by omega)
    have t5 := targetPrivate 5 (by omega)
    have t6 := targetPrivate 6 (by omega)
    have t7 := targetPrivate 7 (by omega)
    have t8 := targetPrivate 8 (by omega)
    simp [singleSourcePhases] at targetMem
    omega
  have targetNotProjection : target ∉
      threeProjectionSourcePhases (p 1) (p 9) (p 10) (p 11)
        (p 12) (p 13) (p 14) := by
    intro targetMem
    have t1 := targetPrivate 1 (by omega)
    have t9 := targetPrivate 9 (by omega)
    have t10 := targetPrivate 10 (by omega)
    have t11 := targetPrivate 11 (by omega)
    have t12 := targetPrivate 12 (by omega)
    have t13 := targetPrivate 13 (by omega)
    have t14 := targetPrivate 14 (by omega)
    simp [threeProjectionSourcePhases] at targetMem
    omega
  have endpointNotFrontInternal : endpointPhase ∉
      [p 0, p 2, p 3, p 4, p 5, p 6, p 7, p 8] := by
    intro endpointMem
    have d0 := privateDistinct 0 (by omega)
    have d2 := privateDistinct 2 (by omega)
    have d3 := privateDistinct 3 (by omega)
    have d4 := privateDistinct 4 (by omega)
    have d5 := privateDistinct 5 (by omega)
    have d6 := privateDistinct 6 (by omega)
    have d7 := privateDistinct 7 (by omega)
    have d8 := privateDistinct 8 (by omega)
    change p 0 ≠ endpointPhase at d0
    change p 2 ≠ endpointPhase at d2
    change p 3 ≠ endpointPhase at d3
    change p 4 ≠ endpointPhase at d4
    change p 5 ≠ endpointPhase at d5
    change p 6 ≠ endpointPhase at d6
    change p 7 ≠ endpointPhase at d7
    change p 8 ≠ endpointPhase at d8
    simp at endpointMem
    omega
  have endpointNotProjection : endpointPhase ∉
      threeProjectionSourcePhases (p 1) (p 9) (p 10) (p 11)
        (p 12) (p 13) (p 14) := by
    intro endpointMem
    have d1 := privateDistinct 1 (by omega)
    have d9 := privateDistinct 9 (by omega)
    have d10 := privateDistinct 10 (by omega)
    have d11 := privateDistinct 11 (by omega)
    have d12 := privateDistinct 12 (by omega)
    have d13 := privateDistinct 13 (by omega)
    have d14 := privateDistinct 14 (by omega)
    change p 1 ≠ endpointPhase at d1
    change p 9 ≠ endpointPhase at d9
    change p 10 ≠ endpointPhase at d10
    change p 11 ≠ endpointPhase at d11
    change p 12 ≠ endpointPhase at d12
    change p 13 ≠ endpointPhase at d13
    change p 14 ≠ endpointPhase at d14
    simp [threeProjectionSourcePhases] at endpointMem
    omega
  have moduleOver : WordOver
      (threeAlphabet source (p 0) (p 1) target
        (p 2) (p 3) (p 4) (p 5) (p 6) (p 7) (p 8)
        (p 9) (p 10) (p 11) (p 12) (p 13) (p 14)) word := by
    simpa [source, target, p, edgeAlphabet_eq_three instructionEq] using
      wordOver
  have inputLocal := IncrementModule.phaseUnaryCode_local codingPrime source
    counter codingPrime_isPrime.1
  have outputNonzero := physicalWordAction_nonzero
    (prime := codingPrime) (by have := codingPrime_isPrime.1; omega)
    word inputLocal.1
  have finalLocal := LocalAt.of_sameLine endpointMembership.local
    outputNonzero completeRun
  have allLocal := allStatesLocal_of_final_local
    (by have := codingPrime_isPrime.1; omega) word inputLocal.1 finalLocal
  have counterPositive : 0 < counter := by
    cases counter with
    | succ previous => omega
    | zero =>
        cases word with
        | nil => exact False.elim (wordNonempty rfl)
        | cons letter tail =>
            have letterMem := moduleOver letter (by simp)
            have letterLocalMem : letter ∈ edgeAlphabet index edge := by
              simpa [source, target, p, edgeAlphabet_eq_three instructionEq]
                using letterMem
            have letterListed := edgeLetter_listed indexedMem letterLocalMem
            have guard := listedLetter_guard letterListed
            have inputMembership : InPhaseAt codingPrime source 1
                (phaseAffine source (unaryCode codingPrime 0)) := by
              simpa [unaryCode, unaryDigits] using
                (periodicCode_inPhaseAt codingPrime source 1 []
                  codingPrime_isPrime.1 (by simp [ReservedDigit]))
            have letterMembership : InPhaseAt codingPrime letter.sourcePhase
                letter.digit (phaseAffine source (unaryCode codingPrime 0)) := by
              apply physicalLetter_input_inPhaseAt codingPrime_isPrime
                guard.2.2 inputLocal
              simpa [PhysicalTemplate.act, PhysicalTemplate.matrix] using
                allLocal.2.start
            have sourceEq := (inputMembership.unique codingPrime_isPrime
              codingPrime_phase_bound sourceBound
              (by have := guard.1; unfold totalPhaseCount; omega)
              letterMembership (SameLine.refl _)).1.symm
            have splitMem :
                letter ∈ FivefoldFrontModule.alphabet source (p 0)
                    (p 2) (p 3) (p 4) (p 5) (p 6) (p 7) (p 8) ∨
                letter ∈ RightSubtractionModule.subtractionAlphabet
                    (p 0) (p 1) ∨
                letter ∈ ThreeProjectionModule.alphabet (p 1) target
                    (p 9) (p 10) (p 11) (p 12) (p 13) (p 14) := by
              simpa [threeAlphabet, singleAlphabet] using letterMem
            rcases splitMem with coreMem | validatorMem | projectionMem
            · have forced := FivefoldFrontModule.source_letter
                codingPrime_isPrime codingPrime_phase_bound frontLayout
                inputMembership coreMem allLocal.2.start
              omega
            · have validatorSource : letter.sourcePhase = p 0 := by
                simp [RightSubtractionModule.subtractionAlphabet] at validatorMem
                rcases validatorMem with rfl | rfl <;> rfl
              exact False.elim
                ((sourcePrivate 0 (by omega))
                  (sourceEq.symm.trans validatorSource))
            · have active := threeProjectionLetter_source_mem projectionMem
              simp [threeProjectionSourcePhases] at active
              rcases active with h | h | h | h | h | h | h
              · exact False.elim
                  ((sourcePrivate 1 (by omega)) (sourceEq.symm.trans h))
              · exact False.elim
                  ((sourcePrivate 9 (by omega)) (sourceEq.symm.trans h))
              · exact False.elim
                  ((sourcePrivate 10 (by omega)) (sourceEq.symm.trans h))
              · exact False.elim
                  ((sourcePrivate 11 (by omega)) (sourceEq.symm.trans h))
              · exact False.elim
                  ((sourcePrivate 12 (by omega)) (sourceEq.symm.trans h))
              · exact False.elim
                  ((sourcePrivate 13 (by omega)) (sourceEq.symm.trans h))
              · exact False.elim
                  ((sourcePrivate 14 (by omega)) (sourceEq.symm.trans h))
  obtain ⟨first, residual, counterEq, wordEq, residualOver, residualLocal,
      _⟩ :=
    threeWord_forces_prefix_general_to_endpoint_of_nonempty
      codingPrime_isPrime codingPrime_phase_bound frontLayout projectionLayout
      (privateBound 0 (by omega)) targetBound endpointBound
      frontHandoffNotCore frontProjectionDisjoint targetNotFront
      targetNotProjection endpointNotFrontInternal endpointNotProjection
      endpointMembership counterPositive moduleOver wordNonempty allLocal
      completeRun
  have residualLocalOver : WordOver (edgeAlphabet index edge) residual := by
    simpa [source, target, p, edgeAlphabet_eq_three instructionEq] using
      residualOver
  have residualEmpty := localWord_from_target_empty indexedMem notIncrement
    residualLocalOver residualLocal
  subst residual
  refine ⟨3 * first + 2, ?_, ?_⟩
  · rw [instructionEq]
    apply Instruction.evaluate_contractThree_iff.mpr
    exact ⟨first, counterEq, rfl⟩
  · have quotientEq : counter / 5 = first := by omega
    simpa [FixedForward.edgeWord, instructionEq, source, target, p,
      quotientEq] using wordEq

/-- Parse one concrete two-to-one contraction occurrence at the front of an
arbitrary globally surviving word. -/
theorem globalContractTwo_split
    {edge : Edge Nat} {index counter finalState finalCounter : Nat}
    (indexedMem : (edge, index) ∈ fixedProgram.edges.zipIdx)
    (instructionEq : edge.instruction = .contractTwo)
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
    have privateDistinct : ∀ offset, offset < 14 →
        privatePhase index offset ≠ boundaryPhase finalState := by
      intro offset offsetBound
      exact (boundary_ne_private finalStateMem indexedMem
        (twoPrivate_inBlock (index := index) instructionEq offsetBound)).symm
    obtain ⟨output, evaluation, exactWord⟩ := localContractTwoWord_unique
      indexedMem instructionEq endpointBound privateDistinct finalMembership
      localOnly (by simp) completeRun
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
    have privateDistinct : ∀ offset, offset < 14 →
        privatePhase index offset ≠ foreign.sourcePhase := by
      intro offset offsetBound
      exact foreignEndpoint_ne_twoPrivate indexedMem instructionEq offsetBound
        foreignGlobal foreignNotLocal foreignMembership
        foreignTailLocal.2.start
    have initialNonempty : initial ≠ [] := by
      intro initialEmpty
      subst initial
      simp only [List.nil_append, List.cons.injEq] at wordEq
      exact foreignNotLocal (wordEq.1 ▸ letterLocal)
    obtain ⟨output, evaluation, initialEq⟩ := localContractTwoWord_unique
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
    have residualRun :=
      (physicalWordAction_preserves_sameLine codingPrime (foreign :: rest)
        boundarySame).trans residualRunRaw
    refine ⟨output, foreign :: rest, evaluation, ?_, ?_, residualLocal,
      residualRun⟩
    · rw [wordEq, initialEq]
    · exact wordOver_cons foreignGlobal restGlobal

/-- Parse one concrete three-to-one contraction occurrence at the front of an
arbitrary globally surviving word. -/
theorem globalContractThree_split
    {edge : Edge Nat} {index counter finalState finalCounter : Nat}
    (indexedMem : (edge, index) ∈ fixedProgram.edges.zipIdx)
    (instructionEq : edge.instruction = .contractThree)
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
    have privateDistinct : ∀ offset, offset < 15 →
        privatePhase index offset ≠ boundaryPhase finalState := by
      intro offset offsetBound
      exact (boundary_ne_private finalStateMem indexedMem
        (threePrivate_inBlock (index := index) instructionEq offsetBound)).symm
    obtain ⟨output, evaluation, exactWord⟩ :=
      localContractThreeWord_unique indexedMem instructionEq endpointBound
        privateDistinct finalMembership localOnly (by simp) completeRun
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
    have privateDistinct : ∀ offset, offset < 15 →
        privatePhase index offset ≠ foreign.sourcePhase := by
      intro offset offsetBound
      exact foreignEndpoint_ne_threePrivate indexedMem instructionEq
        offsetBound foreignGlobal foreignNotLocal foreignMembership
        foreignTailLocal.2.start
    have initialNonempty : initial ≠ [] := by
      intro initialEmpty
      subst initial
      simp only [List.nil_append, List.cons.injEq] at wordEq
      exact foreignNotLocal (wordEq.1 ▸ letterLocal)
    obtain ⟨output, evaluation, initialEq⟩ :=
      localContractThreeWord_unique indexedMem instructionEq endpointBound
        privateDistinct foreignMembership initialOver initialNonempty
        (SameLine.refl _)
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
    have residualRun :=
      (physicalWordAction_preserves_sameLine codingPrime (foreign :: rest)
        boundarySame).trans residualRunRaw
    refine ⟨output, foreign :: rest, evaluation, ?_, ?_, residualLocal,
      residualRun⟩
    · rw [wordEq, initialEq]
    · exact wordOver_cons foreignGlobal restGlobal



end Mortality.Compiler.GlobalContractions
