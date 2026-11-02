import Mortality.Compiler.FivefoldFrontModule
import Mortality.Compiler.RightSubtractionModule

/-!
# Validating the fivefold handoff

This file adjoins the positive subtraction scan that distinguishes the
accepted fivefold handoff from the sole false-survivor interval.  It first
proves the rejection theorem over the exact two-letter subtraction alphabet,
then packages the accepted eighteen-letter forward execution.
-/

namespace Mortality.Compiler.ValidatedFivefoldFrontModule

open Mortality.Compiler
open Mortality.PeriodicCode
open Mortality.Compiler.UnaryArithmetic
open Mortality.Compiler.IncrementModule
open Mortality.Compiler.OddHalvingModule
open Mortality.Compiler.TernaryFrontModule
open Mortality.Compiler.RightSubtractionModule
open Mortality.Compiler.FivefoldFrontClassification
open Mortality.Compiler.FivefoldFrontModule

def singleAlphabet (source handoff output guessPhase firstPhase secondPhase
    thirdPhase fourthPhase fifthPhase markerTwoPhase : Nat) :
    List PhysicalTemplate :=
  FivefoldFrontModule.alphabet source handoff guessPhase firstPhase secondPhase
      thirdPhase fourthPhase fifthPhase markerTwoPhase ++
    subtractionAlphabet handoff output

def singleWord (source handoff output guessPhase firstPhase secondPhase
    thirdPhase fourthPhase fifthPhase markerTwoPhase first : Nat) :
    List PhysicalTemplate :=
  FivefoldFrontModule.acceptedWord source handoff guessPhase firstPhase
      secondPhase thirdPhase fourthPhase fifthPhase markerTwoPhase first ++
    subtractionWord handoff output first

@[simp] theorem singleAlphabet_length
    (source handoff output guessPhase firstPhase secondPhase thirdPhase
      fourthPhase fifthPhase markerTwoPhase : Nat) :
    (singleAlphabet source handoff output guessPhase firstPhase secondPhase
      thirdPhase fourthPhase fifthPhase markerTwoPhase).length = 18 := by
  simp [singleAlphabet]

@[simp] theorem singleWord_length
    (source handoff output guessPhase firstPhase secondPhase thirdPhase
      fourthPhase fifthPhase markerTwoPhase first : Nat) :
    (singleWord source handoff output guessPhase firstPhase secondPhase
      thirdPhase fourthPhase fifthPhase markerTwoPhase first).length =
        11 * first + 11 := by
  simp [singleWord]
  omega

theorem singleWord_wordOver
    (source handoff output guessPhase firstPhase secondPhase thirdPhase
      fourthPhase fifthPhase markerTwoPhase first : Nat) :
    WordOver
      (singleAlphabet source handoff output guessPhase firstPhase secondPhase
        thirdPhase fourthPhase fifthPhase markerTwoPhase)
      (singleWord source handoff output guessPhase firstPhase secondPhase
        thirdPhase fourthPhase fifthPhase markerTwoPhase first) := by
  intro letter letterMem
  simp only [singleWord, List.mem_append] at letterMem
  rcases letterMem with frontMem | subtractionMem
  · exact List.mem_append_left _
      (FivefoldFrontModule.acceptedWord_wordOver source handoff guessPhase
        firstPhase secondPhase thirdPhase fourthPhase fifthPhase markerTwoPhase
        first letter frontMem)
  · exact List.mem_append_right _
      (subtractionWord_wordOver handoff output first letter subtractionMem)

theorem singleWord_correct
    (base source handoff output guessPhase firstPhase secondPhase thirdPhase
      fourthPhase fifthPhase markerTwoPhase first : Nat)
    (baseAtLeastTwo : 2 ≤ base) :
    SameLine
      (physicalWordAction base
        (singleWord source handoff output guessPhase firstPhase secondPhase
          thirdPhase fourthPhase fifthPhase markerTwoPhase first)
        (phaseAffine source (unaryCode base (5 * first + 4))))
      (phaseAffine output (twoFieldCode base first (3 * first + 2))) := by
  have frontRun := FivefoldFrontModule.acceptedWord_correct base source
    handoff guessPhase firstPhase secondPhase thirdPhase fourthPhase fifthPhase
    markerTwoPhase first baseAtLeastTwo
  have subtractionRun := subtractionWord_correct base handoff output first
    (4 * first + 3) baseAtLeastTwo (by omega)
  have combined := physicalWordAction_append_sameLine base
    (FivefoldFrontModule.acceptedWord source handoff guessPhase firstPhase
      secondPhase thirdPhase fourthPhase fifthPhase markerTwoPhase first)
    (subtractionWord handoff output first) frontRun subtractionRun
  simpa [singleWord, show 4 * first + 3 - first - 1 = 3 * first + 2 by
    omega] using combined

theorem single_execution
    (base source handoff output guessPhase firstPhase secondPhase thirdPhase
      fourthPhase fifthPhase markerTwoPhase first : Nat)
    (baseAtLeastTwo : 2 ≤ base) :
    let word := singleWord source handoff output guessPhase firstPhase
      secondPhase thirdPhase fourthPhase fifthPhase markerTwoPhase first
    WordOver
        (singleAlphabet source handoff output guessPhase firstPhase secondPhase
          thirdPhase fourthPhase fifthPhase markerTwoPhase) word ∧
      word.length = 11 * first + 11 ∧
      SameLine
        (physicalWordAction base word
          (phaseAffine source (unaryCode base (5 * first + 4))))
        (phaseAffine output (twoFieldCode base first (3 * first + 2))) ∧
      AllStatesLocal base word
        (phaseAffine source (unaryCode base (5 * first + 4))) := by
  dsimp
  have action := singleWord_correct base source handoff output guessPhase
    firstPhase secondPhase thirdPhase fourthPhase fifthPhase markerTwoPhase
    first baseAtLeastTwo
  have inputLocal := phaseUnaryCode_local base source (5 * first + 4)
    baseAtLeastTwo
  have outputLocal := phaseTwoFieldCode_local base output first
    (3 * first + 2) baseAtLeastTwo
  have outputNonzero := physicalWordAction_nonzero (prime := base) (by omega)
    (singleWord source handoff output guessPhase firstPhase secondPhase
      thirdPhase fourthPhase fifthPhase markerTwoPhase first) inputLocal.1
  have actualFinalLocal := LocalAt.of_sameLine outputLocal outputNonzero action
  exact ⟨singleWord_wordOver source handoff output guessPhase firstPhase
      secondPhase thirdPhase fourthPhase fifthPhase markerTwoPhase first,
    singleWord_length source handoff output guessPhase firstPhase secondPhase
      thirdPhase fourthPhase fifthPhase markerTwoPhase first,
    action, allStatesLocal_of_final_local (by omega) _ inputLocal.1
      actualFinalLocal⟩

theorem subtractionLetter_source_bound
    {phaseCount source target : Nat} {letter : PhysicalTemplate}
    (sourceBound : source < phaseCount)
    (letterMem : letter ∈ subtractionAlphabet source target) :
    letter.sourcePhase < phaseCount := by
  simp [subtractionAlphabet] at letterMem
  rcases letterMem with rfl | rfl <;>
    simpa [zeroLoop, markerExit] using sourceBound

theorem subtractionLetter_reserved
    {source target : Nat} {letter : PhysicalTemplate}
    (letterMem : letter ∈ subtractionAlphabet source target) :
    ReservedDigit letter.digit := by
  simp [subtractionAlphabet] at letterMem
  rcases letterMem with rfl | rfl <;>
    simp [zeroLoop, markerExit, ReservedDigit]

theorem subtraction_letter
    {prime phaseCount source target : Nat}
    {digit : Int} {state : Vec2} {letter : PhysicalTemplate}
    (primeProperty : IsPrime prime) (primeBound : 6 * phaseCount < prime)
    (sourceBound : source < phaseCount)
    (membership : InPhaseAt prime source digit state)
    (letterMem : letter ∈ subtractionAlphabet source target)
    (outputLocal : LocalAt prime (letter.act prime state)) :
    (digit = 0 ∧ letter = zeroLoop source) ∨
      (digit = 1 ∧ letter = markerExit source target) := by
  have forced := membership.physicalLetter_source_digit_unique primeProperty
    primeBound sourceBound (subtractionLetter_source_bound sourceBound
      letterMem) (subtractionLetter_reserved letterMem)
    (by simpa [PhysicalTemplate.act, PhysicalTemplate.matrix] using outputLocal)
  simp [subtractionAlphabet] at letterMem
  rcases letterMem with rfl | rfl
  · exact .inl ⟨by simpa [zeroLoop] using forced.2, rfl⟩
  · exact .inr ⟨by simpa [markerExit] using forced.2, rfl⟩

theorem subtractionState_inPhaseAt_before
    {prime phase first second deleted : Nat}
    (primeProperty : IsPrime prime) (deletedBelow : deleted < first) :
    InPhaseAt prime phase 0
      (phaseAffine phase (subtractionState prime first second deleted)) := by
  have residue : (prime : Int) ∣
      (prime : Int) ^ (first - deleted) *
          (1 - (prime : Int) ^ (second + 1)) -
        0 * (1 - (prime : Int) ^ (first + 1)) := by
    rcases base_dvd_positive_power prime (first - deleted) (by omega) with
      ⟨factor, factorEq⟩
    refine ⟨factor * (1 - (prime : Int) ^ (second + 1)), ?_⟩
    simp only [Int.zero_mul, Int.sub_zero]
    rw [factorEq]
    grind
  apply inPhaseAt_phaseAffine_integer (by simp [ReservedDigit])
    (one_sub_power_not_dvd prime (first + 1) primeProperty.1 (by omega))
    residue
  exact subtractionState_sameLine_integer prime first second deleted
    primeProperty.1

theorem subtractionState_inPhaseAt_marker
    {prime phase first second : Nat} (primeProperty : IsPrime prime) :
    InPhaseAt prime phase 1
      (phaseAffine phase (subtractionState prime first second first)) := by
  have firstPower := base_dvd_positive_power prime (first + 1) (by omega)
  have secondPower := base_dvd_positive_power prime (second + 1) (by omega)
  rcases firstPower with ⟨firstFactor, firstEq⟩
  rcases secondPower with ⟨secondFactor, secondEq⟩
  have residue : (prime : Int) ∣
      (prime : Int) ^ (first - first) *
          (1 - (prime : Int) ^ (second + 1)) -
        1 * (1 - (prime : Int) ^ (first + 1)) := by
    refine ⟨firstFactor - secondFactor, ?_⟩
    simp only [Nat.sub_self, Int.pow_zero, Int.one_mul]
    rw [firstEq, secondEq]
    grind
  apply inPhaseAt_phaseAffine_integer (by simp [ReservedDigit])
    (one_sub_power_not_dvd prime (first + 1) primeProperty.1 (by omega))
    residue
  exact subtractionState_sameLine_integer prime first second first
    primeProperty.1

theorem acceptedHandoff_inPhaseAt
    {prime handoff first : Nat} (primeProperty : IsPrime prime) :
    ∃ digit, InPhaseAt prime handoff digit
      (phaseAffine handoff (acceptedHandoffState prime first)) := by
  rw [acceptedHandoffState_eq prime first primeProperty.1]
  rw [← subtractionState_zero prime first (4 * first + 3) primeProperty.1]
  by_cases firstZero : first = 0
  · subst first
    exact ⟨1, subtractionState_inPhaseAt_marker
      (phase := handoff) (first := 0) (second := 3) primeProperty⟩
  · exact ⟨0, subtractionState_inPhaseAt_before
      (phase := handoff) (first := first) (second := 4 * first + 3)
      (deleted := 0) primeProperty (by omega)⟩

theorem falseHandoffState_inPhaseAt_before
    {prime handoff first guess deleted : Nat}
    (primeProperty : IsPrime prime) (QBelowGuess : first + 1 < guess)
    (guessBelowTwoQ : guess < 2 * (first + 1))
    (deletedBelow : deleted < falseHandoffZeroCount first guess) :
    InPhaseAt prime handoff 0
      (phaseAffine handoff (falseHandoffState prime first guess deleted)) := by
  apply inPhaseAt_phaseAffine_integer (by simp [ReservedDigit])
    (falseHandoffDenominator_not_dvd prime first guess primeProperty.1)
    (by
      simpa using (show (prime : Int) ∣
          falseHandoffNumerator prime first guess deleted from
        ⟨falseHandoffNumerator prime first guess (deleted + 1),
          falseHandoffNumerator_step prime first guess deleted QBelowGuess
            guessBelowTwoQ deletedBelow⟩))
  exact falseHandoffState_sameLine_integer prime first guess deleted
    primeProperty.1

theorem falseHandoffState_inPhaseAt_marker_four
    {prime handoff first guess : Nat}
    (primeProperty : IsPrime prime) (QBelowGuess : first + 1 < guess)
    (twoGuessBelowThreeQ : 2 * guess < 3 * (first + 1)) :
    InPhaseAt prime handoff 4
      (phaseAffine handoff (falseHandoffState prime first guess
        (falseHandoffZeroCount first guess))) := by
  apply inPhaseAt_phaseAffine_integer (by simp [ReservedDigit])
    (falseHandoffDenominator_not_dvd prime first guess primeProperty.1)
    (falseHandoff_marker_residue_four prime first guess QBelowGuess
      twoGuessBelowThreeQ)
  exact falseHandoffState_sameLine_integer prime first guess
    (falseHandoffZeroCount first guess) primeProperty.1

theorem falseHandoffState_inPhaseAt_marker_three
    {prime handoff first guess : Nat}
    (primeProperty : IsPrime prime) (QBelowGuess : first + 1 < guess)
    (twoGuessEqThreeQ : 2 * guess = 3 * (first + 1)) :
    InPhaseAt prime handoff 3
      (phaseAffine handoff (falseHandoffState prime first guess
        (falseHandoffZeroCount first guess))) := by
  apply inPhaseAt_phaseAffine_integer (by simp [ReservedDigit])
    (falseHandoffDenominator_not_dvd prime first guess primeProperty.1)
    (falseHandoff_marker_residue_three prime first guess QBelowGuess
      twoGuessEqThreeQ)
  exact falseHandoffState_sameLine_integer prime first guess
    (falseHandoffZeroCount first guess) primeProperty.1

theorem falseHandoffState_inPhaseAt_marker_negative_one
    {prime handoff first guess : Nat}
    (primeProperty : IsPrime prime)
    (threeQBelowTwoGuess : 3 * (first + 1) < 2 * guess)
    (guessBelowTwoQ : guess < 2 * (first + 1)) :
    InPhaseAt prime handoff (-1)
      (phaseAffine handoff (falseHandoffState prime first guess
        (falseHandoffZeroCount first guess))) := by
  apply inPhaseAt_phaseAffine_integer (by simp [ReservedDigit])
    (falseHandoffDenominator_not_dvd prime first guess primeProperty.1)
    (falseHandoff_marker_residue_negative_one prime first guess
      threeQBelowTwoGuess guessBelowTwoQ)
  exact falseHandoffState_sameLine_integer prime first guess
    (falseHandoffZeroCount first guess) primeProperty.1

theorem falseHandoff_inPhaseAt
    {prime handoff first guess : Nat} (primeProperty : IsPrime prime)
    (QBelowGuess : first + 1 < guess)
    (guessBelowTwoQ : guess < 2 * (first + 1)) :
    ∃ digit, InPhaseAt prime handoff digit
      (phaseAffine handoff (falseHandoffState prime first guess 0)) := by
  by_cases countPositive : 0 < falseHandoffZeroCount first guess
  · exact ⟨0, falseHandoffState_inPhaseAt_before (handoff := handoff)
      primeProperty QBelowGuess guessBelowTwoQ countPositive⟩
  · have countZero : falseHandoffZeroCount first guess = 0 := by omega
    rcases Nat.lt_trichotomy (2 * guess) (3 * (first + 1)) with
      below | equal | above
    · refine ⟨4, ?_⟩
      simpa [countZero] using
        (falseHandoffState_inPhaseAt_marker_four (handoff := handoff)
          primeProperty QBelowGuess below)
    · refine ⟨3, ?_⟩
      simpa [countZero] using
        (falseHandoffState_inPhaseAt_marker_three (handoff := handoff)
          primeProperty QBelowGuess equal)
    · refine ⟨-1, ?_⟩
      simpa [countZero] using
        (falseHandoffState_inPhaseAt_marker_negative_one (handoff := handoff)
          primeProperty above guessBelowTwoQ)

theorem falseHandoffZero_step
    (base handoff first guess deleted : Nat) (baseAtLeastTwo : 2 ≤ base)
    (QBelowGuess : first + 1 < guess)
    (guessBelowTwoQ : guess < 2 * (first + 1))
    (deletedBelow : deleted < falseHandoffZeroCount first guess) :
    SameLine
      ((zeroLoop handoff).act base
        (phaseAffine handoff (falseHandoffState base first guess deleted)))
      (phaseAffine handoff
        (falseHandoffState base first guess (deleted + 1))) := by
  have step := OddHalvingModule.identityZero_step
    (base := base) (phase := handoff) (by omega)
    (falseHandoffState_local base first guess deleted baseAtLeastTwo)
    (falseHandoffState_local base first guess (deleted + 1) baseAtLeastTwo)
    (falseHandoffState_delete_zero base first guess deleted baseAtLeastTwo
      QBelowGuess guessBelowTwoQ deletedBelow)
  simpa [zeroLoop, identityZero, PhysicalTemplate.act,
    PhysicalTemplate.matrix] using step

theorem falseHandoff_rejects_marker
    {prime phaseCount handoff output endpointPhase first guess : Nat}
    {endpointDigit markerDigit : Int} {endpoint : Vec2}
    (primeProperty : IsPrime prime) (primeBound : 6 * phaseCount < prime)
    (handoffBound : handoff < phaseCount)
    (endpointBound : endpointPhase < phaseCount)
    (handoffEndpointDistinct : handoff ≠ endpointPhase)
    (endpointMembership : InPhaseAt prime endpointPhase endpointDigit endpoint)
    (QBelowGuess : first + 1 < guess)
    (guessBelowTwoQ : guess < 2 * (first + 1))
    (markerNeZero : markerDigit ≠ 0) (markerNeOne : markerDigit ≠ 1)
    (markerMembership : InPhaseAt prime handoff markerDigit
      (phaseAffine handoff (falseHandoffState prime first guess
        (falseHandoffZeroCount first guess))))
    {deleted remaining : Nat}
    (sumEq : deleted + remaining = falseHandoffZeroCount first guess)
    {word : List PhysicalTemplate}
    (wordOver : WordOver (subtractionAlphabet handoff output) word)
    (allLocal : AllStatesLocal prime word
      (phaseAffine handoff (falseHandoffState prime first guess deleted)))
    (completeRun : SameLine
      (physicalWordAction prime word
        (phaseAffine handoff (falseHandoffState prime first guess deleted)))
      endpoint) : False := by
  apply forcedScanRejectsAtMarker
    (primeProperty := primeProperty) (primeBound := primeBound)
    (currentBound := handoffBound) (endpointBound := endpointBound)
    (phaseDistinct := handoffEndpointDistinct)
    (endpointMembership := endpointMembership)
    (beforeMembership := fun position positionBelow =>
      falseHandoffState_inPhaseAt_before (handoff := handoff) primeProperty
        QBelowGuess guessBelowTwoQ positionBelow)
    (markerMembership := markerMembership)
    (stateLocal := fun position _ =>
      phaseLocal (falseHandoffState_local prime first guess position
        primeProperty.1))
    (forceLoop := fun position positionBelow {letter} letterMem outputLocal =>
      by
        rcases subtraction_letter primeProperty primeBound handoffBound
            (falseHandoffState_inPhaseAt_before (handoff := handoff)
              primeProperty QBelowGuess guessBelowTwoQ positionBelow)
            letterMem outputLocal with
          ⟨_, letterEq⟩ | ⟨digitEq, _⟩
        · exact letterEq
        · omega)
    (rejectMarker := fun {letter} letterMem outputLocal => by
      rcases subtraction_letter primeProperty primeBound handoffBound
          markerMembership letterMem outputLocal with
        ⟨digitEq, _⟩ | ⟨digitEq, _⟩
      · exact False.elim (markerNeZero digitEq)
      · exact False.elim (markerNeOne digitEq))
    (loopStep := fun position positionBelow =>
      falseHandoffZero_step prime handoff first guess position
        primeProperty.1 QBelowGuess guessBelowTwoQ positionBelow)
    sumEq wordOver allLocal completeRun

/-- Every false survivor from the sixteen-letter core is rejected by the
following positive subtraction scan. -/
theorem falseHandoff_rejects_subtraction
    {prime phaseCount handoff output endpointPhase first guess : Nat}
    {endpointDigit : Int} {endpoint : Vec2}
    (primeProperty : IsPrime prime) (primeBound : 6 * phaseCount < prime)
    (handoffBound : handoff < phaseCount)
    (endpointBound : endpointPhase < phaseCount)
    (handoffEndpointDistinct : handoff ≠ endpointPhase)
    (endpointMembership : InPhaseAt prime endpointPhase endpointDigit endpoint)
    (QBelowGuess : first + 1 < guess)
    (guessBelowTwoQ : guess < 2 * (first + 1))
    {word : List PhysicalTemplate}
    (wordOver : WordOver (subtractionAlphabet handoff output) word)
    (allLocal : AllStatesLocal prime word
      (phaseAffine handoff (falseHandoffState prime first guess 0)))
    (completeRun : SameLine
      (physicalWordAction prime word
        (phaseAffine handoff (falseHandoffState prime first guess 0)))
      endpoint) : False := by
  rcases Nat.lt_trichotomy (2 * guess) (3 * (first + 1)) with
    below | equal | above
  · exact falseHandoff_rejects_marker primeProperty primeBound handoffBound
      endpointBound handoffEndpointDistinct endpointMembership QBelowGuess
      guessBelowTwoQ (by omega) (by omega)
      (falseHandoffState_inPhaseAt_marker_four (handoff := handoff)
        primeProperty QBelowGuess below)
      (deleted := 0) (remaining := falseHandoffZeroCount first guess)
      (by omega) wordOver allLocal completeRun
  · exact falseHandoff_rejects_marker primeProperty primeBound handoffBound
      endpointBound handoffEndpointDistinct endpointMembership QBelowGuess
      guessBelowTwoQ (by omega) (by omega)
      (falseHandoffState_inPhaseAt_marker_three (handoff := handoff)
        primeProperty QBelowGuess equal)
      (deleted := 0) (remaining := falseHandoffZeroCount first guess)
      (by omega) wordOver allLocal completeRun
  · exact falseHandoff_rejects_marker primeProperty primeBound handoffBound
      endpointBound handoffEndpointDistinct endpointMembership QBelowGuess
      guessBelowTwoQ (by omega) (by omega)
      (falseHandoffState_inPhaseAt_marker_negative_one (handoff := handoff)
        primeProperty above guessBelowTwoQ)
      (deleted := 0) (remaining := falseHandoffZeroCount first guess)
      (by omega) wordOver allLocal completeRun

theorem subtractionTail_forced_prefix_to_endpoint
    {prime phaseCount source target endpointPhase first second deleted
      remaining : Nat}
    {endpointDigit : Int} {endpoint : Vec2}
    (primeProperty : IsPrime prime) (primeBound : 6 * phaseCount < prime)
    (sourceBound : source < phaseCount)
    (endpointBound : endpointPhase < phaseCount)
    (sourceEndpointDistinct : source ≠ endpointPhase)
    (endpointMembership : InPhaseAt prime endpointPhase endpointDigit endpoint)
    (less : first < second) (sumEq : deleted + remaining = first)
    {word : List PhysicalTemplate}
    (wordOver : WordOver (subtractionAlphabet source target) word)
    (allLocal : AllStatesLocal prime word
      (phaseAffine source (subtractionState prime first second deleted)))
    (completeRun : SameLine
      (physicalWordAction prime word
        (phaseAffine source (subtractionState prime first second deleted)))
      endpoint) :
    ∃ suffix,
      word = List.replicate remaining (zeroLoop source) ++
          [markerExit source target] ++ suffix ∧
      WordOver (subtractionAlphabet source target) suffix ∧
      AllStatesLocal prime suffix
        (phaseAffine target
          (twoFieldCode prime first (second - first - 1))) ∧
      SameLine
        (physicalWordAction prime suffix
          (phaseAffine target
            (twoFieldCode prime first (second - first - 1)))) endpoint := by
  have parsed := forcedScanPrefixToEndpoint
    (Certificate := True) (primeProperty := primeProperty)
    (primeBound := primeBound) (currentBound := sourceBound)
    (endpointBound := endpointBound) (phaseDistinct := sourceEndpointDistinct)
    (endpointMembership := endpointMembership)
    (beforeMembership := fun position positionBelow =>
      subtractionState_inPhaseAt_before (phase := source)
        (first := first) (second := second) (deleted := position)
        primeProperty positionBelow)
    (markerMembership := subtractionState_inPhaseAt_marker
      (phase := source) (first := first) (second := second) primeProperty)
    (stateLocal := fun position _ =>
      phaseSubtractionState_local prime source first second position
        primeProperty.1)
    (nextLocal := phaseTwoFieldCode_local prime target first
      (second - first - 1) primeProperty.1)
    (forceLoop := fun position positionBelow {letter} letterMem outputLocal =>
      by
        rcases subtraction_letter primeProperty primeBound sourceBound
            (subtractionState_inPhaseAt_before (phase := source)
              (first := first) (second := second) (deleted := position)
              primeProperty positionBelow) letterMem outputLocal with
          ⟨_, letterEq⟩ | ⟨digitEq, _⟩
        · exact letterEq
        · omega)
    (forceExit := fun {letter} letterMem outputLocal => by
      rcases subtraction_letter primeProperty primeBound sourceBound
          (subtractionState_inPhaseAt_marker (phase := source)
            (first := first) (second := second) primeProperty)
          letterMem outputLocal with
        ⟨digitEq, _⟩ | ⟨_, letterEq⟩
      · omega
      · exact ⟨True.intro, letterEq⟩)
    (loopStep := fun position positionBelow =>
      zeroLoop_step prime source first second position primeProperty.1
        positionBelow)
    (exitStep := fun _ =>
      markerExit_step prime source target first second primeProperty.1 less)
    sumEq wordOver allLocal completeRun
  rcases parsed with ⟨suffix, _, wordEq, suffixOver, suffixLocal, suffixRun⟩
  exact ⟨suffix, wordEq, suffixOver, suffixLocal, suffixRun⟩

theorem subtractionWord_forced_prefix_to_endpoint
    {prime phaseCount source target endpointPhase first second : Nat}
    {endpointDigit : Int} {endpoint : Vec2}
    (primeProperty : IsPrime prime) (primeBound : 6 * phaseCount < prime)
    (sourceBound : source < phaseCount)
    (endpointBound : endpointPhase < phaseCount)
    (sourceEndpointDistinct : source ≠ endpointPhase)
    (endpointMembership : InPhaseAt prime endpointPhase endpointDigit endpoint)
    (less : first < second)
    {word : List PhysicalTemplate}
    (wordOver : WordOver (subtractionAlphabet source target) word)
    (allLocal : AllStatesLocal prime word
      (phaseAffine source (T prime (twoFieldCode prime first second))))
    (completeRun : SameLine
      (physicalWordAction prime word
        (phaseAffine source (T prime (twoFieldCode prime first second))))
      endpoint) :
    ∃ suffix,
      word = subtractionWord source target first ++ suffix ∧
      WordOver (subtractionAlphabet source target) suffix ∧
      AllStatesLocal prime suffix
        (phaseAffine target
          (twoFieldCode prime first (second - first - 1))) ∧
      SameLine
        (physicalWordAction prime suffix
          (phaseAffine target
            (twoFieldCode prime first (second - first - 1)))) endpoint := by
  rw [← subtractionState_zero prime first second primeProperty.1] at allLocal completeRun
  simpa [subtractionWord] using
    (subtractionTail_forced_prefix_to_endpoint primeProperty primeBound
      sourceBound endpointBound sourceEndpointDistinct endpointMembership less
      (deleted := 0) (remaining := first) (by omega) wordOver allLocal
      completeRun)

theorem no_subtraction_letter_from_target
    {prime phaseCount source target : Nat}
    {digit : Int} {state : Vec2} {letter : PhysicalTemplate}
    (primeProperty : IsPrime prime) (primeBound : 6 * phaseCount < prime)
    (sourceBound : source < phaseCount) (targetBound : target < phaseCount)
    (sourceTargetDistinct : source ≠ target)
    (membership : InPhaseAt prime target digit state)
    (letterMem : letter ∈ subtractionAlphabet source target)
    (outputLocal : LocalAt prime (letter.act prime state)) : False := by
  have forced := membership.physicalLetter_source_digit_unique primeProperty
    primeBound targetBound (subtractionLetter_source_bound sourceBound
      letterMem) (subtractionLetter_reserved letterMem)
    (by simpa [PhysicalTemplate.act, PhysicalTemplate.matrix] using outputLocal)
  simp [subtractionAlphabet] at letterMem
  rcases letterMem with rfl | rfl <;>
    simp [zeroLoop, markerExit] at forced <;>
    exact sourceTargetDistinct forced.1.symm

theorem subtraction_word_from_target_eq_nil
    {prime phaseCount source target : Nat}
    {digit : Int} {state : Vec2}
    (primeProperty : IsPrime prime) (primeBound : 6 * phaseCount < prime)
    (sourceBound : source < phaseCount) (targetBound : target < phaseCount)
    (sourceTargetDistinct : source ≠ target)
    (membership : InPhaseAt prime target digit state)
    {word : List PhysicalTemplate}
    (wordOver : WordOver (subtractionAlphabet source target) word)
    (allLocal : AllStatesLocal prime word state) : word = [] := by
  cases word with
  | nil => rfl
  | cons letter tail =>
      exact False.elim (no_subtraction_letter_from_target primeProperty
        primeBound sourceBound targetBound sourceTargetDistinct membership
        (wordOver letter (by simp)) allLocal.2.start)

def doubleAlphabet (source handoff intermediate output guessPhase firstPhase
    secondPhase thirdPhase fourthPhase fifthPhase markerTwoPhase : Nat) :
    List PhysicalTemplate :=
  FivefoldFrontModule.alphabet source handoff guessPhase firstPhase secondPhase
      thirdPhase fourthPhase fifthPhase markerTwoPhase ++
    [identityZero handoff, identityMarker handoff intermediate,
      identityZero intermediate, inverseTMarker intermediate output]

def doubleWord (source handoff intermediate output guessPhase firstPhase
    secondPhase thirdPhase fourthPhase fifthPhase markerTwoPhase first : Nat) :
    List PhysicalTemplate :=
  FivefoldFrontModule.acceptedWord source handoff guessPhase firstPhase
      secondPhase thirdPhase fourthPhase fifthPhase markerTwoPhase first ++
    plainScanWord handoff intermediate first ++
    fifthScanWord intermediate output first

@[simp] theorem doubleAlphabet_length
    (source handoff intermediate output guessPhase firstPhase secondPhase
      thirdPhase fourthPhase fifthPhase markerTwoPhase : Nat) :
    (doubleAlphabet source handoff intermediate output guessPhase firstPhase
      secondPhase thirdPhase fourthPhase fifthPhase markerTwoPhase).length =
        20 := by
  simp [doubleAlphabet]

@[simp] theorem doubleWord_length
    (source handoff intermediate output guessPhase firstPhase secondPhase
      thirdPhase fourthPhase fifthPhase markerTwoPhase first : Nat) :
    (doubleWord source handoff intermediate output guessPhase firstPhase
      secondPhase thirdPhase fourthPhase fifthPhase markerTwoPhase first).length =
        12 * first + 12 := by
  simp [doubleWord, plainScanWord, fifthScanWord]
  omega

theorem doubleWord_wordOver
    (source handoff intermediate output guessPhase firstPhase secondPhase
      thirdPhase fourthPhase fifthPhase markerTwoPhase first : Nat) :
    WordOver
      (doubleAlphabet source handoff intermediate output guessPhase firstPhase
        secondPhase thirdPhase fourthPhase fifthPhase markerTwoPhase)
      (doubleWord source handoff intermediate output guessPhase firstPhase
        secondPhase thirdPhase fourthPhase fifthPhase markerTwoPhase first) := by
  intro letter letterMem
  simp [doubleWord, plainScanWord, fifthScanWord] at letterMem
  rcases letterMem with frontMem | ⟨_, rfl⟩ | rfl | ⟨_, rfl⟩ | rfl
  · exact List.mem_append_left _
      (FivefoldFrontModule.acceptedWord_wordOver source handoff guessPhase
        firstPhase secondPhase thirdPhase fourthPhase fifthPhase markerTwoPhase
        first letter frontMem)
  all_goals simp [doubleAlphabet]

/-- The middle value of right subtraction is the `T`-image of the reduced
two-field code.  This is the arithmetic used when the first of two adjacent
subtractions omits its final `T⁻¹`. -/
theorem plain_right_subtraction
    (base first second : Nat) (baseAtLeastTwo : 2 ≤ base)
    (less : first < second) :
    scanDigits (base : Rat) (unaryDigits first)
        (T base (twoFieldCode base first second)) =
      T base (twoFieldCode base first (second - first - 1)) := by
  rw [right_subtraction_middle base first second baseAtLeastTwo,
    T_twoFieldCode base first (second - first - 1) baseAtLeastTwo]
  have powerSplit : (base : Rat) ^ second =
      (base : Rat) ^ first * (base : Rat) ^ (second - first) := by
    rw [show second = first + (second - first) by omega]
    simpa using
      (Lean.Grind.Semiring.pow_add (base : Rat) first (second - first))
  rw [show second - first - 1 + 1 = second - first by omega, powerSplit]
  grind

theorem plainSubtractionMarker_step
    (base source target first second : Nat) (baseAtLeastTwo : 2 ≤ base)
    (less : first < second) :
    SameLine
      ((identityMarker source target).act base
        (phaseAffine source
          (subtractionState base first second first)))
      (phaseAffine target
        (T base (twoFieldCode base first (second - first - 1)))) := by
  have deletedEq := subtractionState_delete_marker base first second
    baseAtLeastTwo
  have arithmetic := plain_right_subtraction base first second baseAtLeastTwo
    less
  rw [right_subtraction_middle base first second baseAtLeastTwo] at arithmetic
  have deletedEq' : deleteDigit (base : Rat) 1
      (subtractionState base first second first) =
        T base (twoFieldCode base first (second - first - 1)) :=
    deletedEq.trans arithmetic
  have deletedLocal : LocalAt base
      (Vec2.affine
        (T base (twoFieldCode base first (second - first - 1)))) := by
    rw [← subtractionState_zero base first (second - first - 1)
      baseAtLeastTwo]
    exact subtractionState_local base first (second - first - 1) 0
      baseAtLeastTwo
  have step := OddHalvingModule.marker_step
    (base := base) (source := source) (target := target) (digit := 1)
    (coefficient := 0) (sign := .positive)
    (value := subtractionState base first second first)
    (deleted := T base (twoFieldCode base first (second - first - 1)))
    (output := T base (twoFieldCode base first (second - first - 1)))
    (by omega) (subtractionState_local base first second first baseAtLeastTwo)
    deletedLocal deletedEq' (mutationMap_positive_zero base _)
  simpa [identityMarker, PhysicalTemplate.act, PhysicalTemplate.matrix]
    using step

theorem plainSubtractionTail_correct
    (base source target deleted remaining second : Nat)
    (baseAtLeastTwo : 2 ≤ base) (less : deleted + remaining < second) :
    SameLine
      (physicalWordAction base
        (List.replicate remaining (identityZero source) ++
          [identityMarker source target])
        (phaseAffine source
          (subtractionState base (deleted + remaining) second deleted)))
      (phaseAffine target
        (T base (twoFieldCode base (deleted + remaining)
          (second - (deleted + remaining) - 1)))) := by
  induction remaining generalizing deleted with
  | zero =>
      simpa [physicalWordAction] using
        (plainSubtractionMarker_step base source target deleted second
          baseAtLeastTwo (by simpa using less))
  | succ remaining inductionHypothesis =>
      have firstStep := zeroLoop_step base source
        (deleted + (remaining + 1)) second deleted baseAtLeastTwo (by omega)
      have firstStep' : SameLine
          ((identityZero source).act base
            (phaseAffine source
              (subtractionState base (deleted + (remaining + 1)) second
                deleted)))
          (phaseAffine source
            (subtractionState base (deleted + (remaining + 1)) second
              (deleted + 1))) := by
        simpa [identityZero, zeroLoop, PhysicalTemplate.act,
          PhysicalTemplate.matrix] using firstStep
      have tailRun := inductionHypothesis (deleted := deleted + 1) (by omega)
      have tailRun' : SameLine
          (physicalWordAction base
            (List.replicate remaining (identityZero source) ++
              [identityMarker source target])
            (phaseAffine source
              (subtractionState base (deleted + (remaining + 1)) second
                (deleted + 1))))
          (phaseAffine target
            (T base (twoFieldCode base (deleted + (remaining + 1))
              (second - (deleted + (remaining + 1)) - 1)))) := by
        simpa only [show deleted + 1 + remaining =
          deleted + (remaining + 1) by omega] using tailRun
      have combined := physicalWordAction_cons_sameLine base
        (identityZero source)
        (List.replicate remaining (identityZero source) ++
          [identityMarker source target]) firstStep' tailRun'
      simpa [List.replicate_succ, physicalWordAction] using combined

theorem plainSubtractionWord_correct
    (base source target first second : Nat) (baseAtLeastTwo : 2 ≤ base)
    (less : first < second) :
    SameLine
      (physicalWordAction base (plainScanWord source target first)
        (phaseAffine source (T base (twoFieldCode base first second))))
      (phaseAffine target
        (T base (twoFieldCode base first (second - first - 1)))) := by
  rw [← subtractionState_zero base first second baseAtLeastTwo]
  simpa [plainScanWord] using
    (plainSubtractionTail_correct base source target 0 first second
      baseAtLeastTwo (by simpa using less))

theorem doubleWord_correct
    (base source handoff intermediate output guessPhase firstPhase secondPhase
      thirdPhase fourthPhase fifthPhase markerTwoPhase first : Nat)
    (baseAtLeastTwo : 2 ≤ base) :
    SameLine
      (physicalWordAction base
        (doubleWord source handoff intermediate output guessPhase firstPhase
          secondPhase thirdPhase fourthPhase fifthPhase markerTwoPhase first)
        (phaseAffine source (unaryCode base (5 * first + 4))))
      (phaseAffine output (twoFieldCode base first (2 * first + 1))) := by
  have frontRun := FivefoldFrontModule.acceptedWord_correct base source
    handoff guessPhase firstPhase secondPhase thirdPhase fourthPhase fifthPhase
    markerTwoPhase first baseAtLeastTwo
  have firstSubtraction := plainSubtractionWord_correct base handoff
    intermediate first (4 * first + 3) baseAtLeastTwo (by omega)
  have throughFirst := physicalWordAction_append_sameLine base
    (FivefoldFrontModule.acceptedWord source handoff guessPhase firstPhase
      secondPhase thirdPhase fourthPhase fifthPhase markerTwoPhase first)
    (plainScanWord handoff intermediate first) frontRun firstSubtraction
  have throughFirst' : SameLine
      (physicalWordAction base
        (FivefoldFrontModule.acceptedWord source handoff guessPhase firstPhase
            secondPhase thirdPhase fourthPhase fifthPhase markerTwoPhase first ++
          plainScanWord handoff intermediate first)
        (phaseAffine source (unaryCode base (5 * first + 4))))
      (phaseAffine intermediate
        (T base (twoFieldCode base first (3 * first + 2)))) := by
    simpa [show 4 * first + 3 - first - 1 = 3 * first + 2 by omega] using
      throughFirst
  have secondSubtraction := subtractionWord_correct base intermediate output
    first (3 * first + 2) baseAtLeastTwo (by omega)
  have complete := physicalWordAction_append_sameLine base
    (FivefoldFrontModule.acceptedWord source handoff guessPhase firstPhase
        secondPhase thirdPhase fourthPhase fifthPhase markerTwoPhase first ++
      plainScanWord handoff intermediate first)
    (fifthScanWord intermediate output first) throughFirst' (by
      simpa [fifthScanWord, subtractionWord, inverseTMarker, markerExit,
        identityZero, zeroLoop] using secondSubtraction)
  simpa [doubleWord,
    show 3 * first + 2 - first - 1 = 2 * first + 1 by omega,
    List.append_assoc] using complete

theorem double_execution
    (base source handoff intermediate output guessPhase firstPhase secondPhase
      thirdPhase fourthPhase fifthPhase markerTwoPhase first : Nat)
    (baseAtLeastTwo : 2 ≤ base) :
    let word := doubleWord source handoff intermediate output guessPhase
      firstPhase secondPhase thirdPhase fourthPhase fifthPhase markerTwoPhase
      first
    WordOver
        (doubleAlphabet source handoff intermediate output guessPhase
          firstPhase secondPhase thirdPhase fourthPhase fifthPhase
          markerTwoPhase) word ∧
      word.length = 12 * first + 12 ∧
      SameLine
        (physicalWordAction base word
          (phaseAffine source (unaryCode base (5 * first + 4))))
        (phaseAffine output (twoFieldCode base first (2 * first + 1))) ∧
      AllStatesLocal base word
        (phaseAffine source (unaryCode base (5 * first + 4))) := by
  dsimp
  have action := doubleWord_correct base source handoff intermediate output
    guessPhase firstPhase secondPhase thirdPhase fourthPhase fifthPhase
    markerTwoPhase first baseAtLeastTwo
  have inputLocal := phaseUnaryCode_local base source (5 * first + 4)
    baseAtLeastTwo
  have outputLocal := phaseTwoFieldCode_local base output first
    (2 * first + 1) baseAtLeastTwo
  have outputNonzero := physicalWordAction_nonzero (prime := base) (by omega)
    (doubleWord source handoff intermediate output guessPhase firstPhase
      secondPhase thirdPhase fourthPhase fifthPhase markerTwoPhase first)
    inputLocal.1
  have actualFinalLocal := LocalAt.of_sameLine outputLocal outputNonzero action
  exact ⟨doubleWord_wordOver source handoff intermediate output guessPhase
      firstPhase secondPhase thirdPhase fourthPhase fifthPhase markerTwoPhase
      first,
    doubleWord_length source handoff intermediate output guessPhase firstPhase
      secondPhase thirdPhase fourthPhase fifthPhase markerTwoPhase first,
    action, allStatesLocal_of_final_local (by omega) _ inputLocal.1
      actualFinalLocal⟩

end Mortality.Compiler.ValidatedFivefoldFrontModule
