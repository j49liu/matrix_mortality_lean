import Mortality.Compiler.SingleValidatedFivefoldConverse

/-!
# Unrestricted-word converse for the twenty-letter double validator

The double validator consists of a plain right-subtraction scan followed by
the typed subtraction scan.  This file proves that arbitrary interleavings
among the core and both scans cannot create another surviving path.
-/

namespace Mortality.Compiler.ValidatedFivefoldFrontModule

open Mortality.Compiler
open Mortality.PeriodicCode
open Mortality.Compiler.UnaryArithmetic
open Mortality.Compiler.OddHalvingModule
open Mortality.Compiler.TernaryFrontModule
open Mortality.Compiler.RightSubtractionModule
open Mortality.Compiler.FivefoldFrontClassification
open Mortality.Compiler.FivefoldFrontModule

def plainSubtractionAlphabet (source target : Nat) :
    List PhysicalTemplate :=
  [identityZero source, identityMarker source target]

def inverseSubtractionAlphabet (source target : Nat) :
    List PhysicalTemplate :=
  [identityZero source, inverseTMarker source target]

def doubleValidatorAlphabet (handoff intermediate output : Nat) :
    List PhysicalTemplate :=
  plainSubtractionAlphabet handoff intermediate ++
    inverseSubtractionAlphabet intermediate output

def doubleValidatorWord (handoff intermediate output first : Nat) :
    List PhysicalTemplate :=
  plainScanWord handoff intermediate first ++
    fifthScanWord intermediate output first

def doubleSourcePhases (source handoff intermediate guessPhase firstPhase
    secondPhase thirdPhase fourthPhase fifthPhase markerTwoPhase : Nat) :
    List Nat :=
  [source, guessPhase, firstPhase, secondPhase, thirdPhase, fourthPhase,
    fifthPhase, markerTwoPhase, handoff, intermediate]

theorem doubleAlphabet_eq
    (source handoff intermediate output guessPhase firstPhase secondPhase
      thirdPhase fourthPhase fifthPhase markerTwoPhase : Nat) :
    doubleAlphabet source handoff intermediate output guessPhase firstPhase
        secondPhase thirdPhase fourthPhase fifthPhase markerTwoPhase =
      FivefoldFrontModule.alphabet source handoff guessPhase firstPhase
          secondPhase thirdPhase fourthPhase fifthPhase markerTwoPhase ++
        doubleValidatorAlphabet handoff intermediate output := by
  simp [doubleAlphabet, doubleValidatorAlphabet, plainSubtractionAlphabet,
    inverseSubtractionAlphabet]

theorem doubleWord_eq
    (source handoff intermediate output guessPhase firstPhase secondPhase
      thirdPhase fourthPhase fifthPhase markerTwoPhase first : Nat) :
    doubleWord source handoff intermediate output guessPhase firstPhase
        secondPhase thirdPhase fourthPhase fifthPhase markerTwoPhase first =
      FivefoldFrontModule.acceptedWord source handoff guessPhase firstPhase
          secondPhase thirdPhase fourthPhase fifthPhase markerTwoPhase first ++
        doubleValidatorWord handoff intermediate output first := by
  simp [doubleWord, doubleValidatorWord, List.append_assoc]

theorem plainSubtractionLetter_source_bound
    {phaseCount source target : Nat} {letter : PhysicalTemplate}
    (sourceBound : source < phaseCount)
    (letterMem : letter ∈ plainSubtractionAlphabet source target) :
    letter.sourcePhase < phaseCount := by
  simp [plainSubtractionAlphabet] at letterMem
  rcases letterMem with rfl | rfl <;>
    simpa [identityZero, identityMarker] using sourceBound

theorem plainSubtractionLetter_reserved
    {source target : Nat} {letter : PhysicalTemplate}
    (letterMem : letter ∈ plainSubtractionAlphabet source target) :
    ReservedDigit letter.digit := by
  simp [plainSubtractionAlphabet] at letterMem
  rcases letterMem with rfl | rfl <;>
    simp [identityZero, identityMarker, ReservedDigit]

theorem plainSubtraction_letter
    {prime phaseCount source target : Nat}
    {digit : Int} {state : Vec2} {letter : PhysicalTemplate}
    (primeProperty : IsPrime prime) (primeBound : 6 * phaseCount < prime)
    (sourceBound : source < phaseCount)
    (membership : InPhaseAt prime source digit state)
    (letterMem : letter ∈ plainSubtractionAlphabet source target)
    (outputLocal : LocalAt prime (letter.act prime state)) :
    (digit = 0 ∧ letter = identityZero source) ∨
      (digit = 1 ∧ letter = identityMarker source target) := by
  have forced := membership.physicalLetter_source_digit_unique primeProperty
    primeBound sourceBound
    (plainSubtractionLetter_source_bound sourceBound letterMem)
    (plainSubtractionLetter_reserved letterMem)
    (by simpa [PhysicalTemplate.act, PhysicalTemplate.matrix] using outputLocal)
  simp [plainSubtractionAlphabet] at letterMem
  rcases letterMem with rfl | rfl
  · exact .inl ⟨by simpa [identityZero] using forced.2, rfl⟩
  · exact .inr ⟨by simpa [identityMarker] using forced.2, rfl⟩

theorem plainSubtractionZero_step
    (base phase first second deleted : Nat) (baseAtLeastTwo : 2 ≤ base)
    (deletedBelow : deleted < first) :
    SameLine
      ((identityZero phase).act base
        (phaseAffine phase (subtractionState base first second deleted)))
      (phaseAffine phase
        (subtractionState base first second (deleted + 1))) := by
  simpa [identityZero, zeroLoop, PhysicalTemplate.act,
    PhysicalTemplate.matrix] using
    (zeroLoop_step base phase first second deleted baseAtLeastTwo deletedBelow)

theorem plainSubtractionTail_forced_prefix_to_endpoint
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
    (wordOver : WordOver (plainSubtractionAlphabet source target) word)
    (allLocal : AllStatesLocal prime word
      (phaseAffine source (subtractionState prime first second deleted)))
    (completeRun : SameLine
      (physicalWordAction prime word
        (phaseAffine source (subtractionState prime first second deleted)))
      endpoint) :
    ∃ suffix,
      word = List.replicate remaining (identityZero source) ++
          [identityMarker source target] ++ suffix ∧
      WordOver (plainSubtractionAlphabet source target) suffix ∧
      AllStatesLocal prime suffix
        (phaseAffine target
          (T prime (twoFieldCode prime first (second - first - 1)))) ∧
      SameLine
        (physicalWordAction prime suffix
          (phaseAffine target
            (T prime (twoFieldCode prime first (second - first - 1)))))
        endpoint := by
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
    (nextLocal := by
      rw [← subtractionState_zero prime first (second - first - 1)
        primeProperty.1]
      exact phaseSubtractionState_local prime target first
        (second - first - 1) 0 primeProperty.1)
    (forceLoop := fun position positionBelow {letter} letterMem outputLocal =>
      by
        rcases plainSubtraction_letter primeProperty primeBound sourceBound
            (subtractionState_inPhaseAt_before (phase := source)
              (first := first) (second := second) (deleted := position)
              primeProperty positionBelow) letterMem outputLocal with
          ⟨_, letterEq⟩ | ⟨digitEq, _⟩
        · exact letterEq
        · omega)
    (forceExit := fun {letter} letterMem outputLocal => by
      rcases plainSubtraction_letter primeProperty primeBound sourceBound
          (subtractionState_inPhaseAt_marker (phase := source)
            (first := first) (second := second) primeProperty)
          letterMem outputLocal with
        ⟨digitEq, _⟩ | ⟨_, letterEq⟩
      · omega
      · exact ⟨True.intro, letterEq⟩)
    (loopStep := fun position positionBelow =>
      plainSubtractionZero_step prime source first second position
        primeProperty.1 positionBelow)
    (exitStep := fun _ =>
      plainSubtractionMarker_step prime source target first second
        primeProperty.1 less)
    sumEq wordOver allLocal completeRun
  rcases parsed with ⟨suffix, _, wordEq, suffixOver, suffixLocal, suffixRun⟩
  exact ⟨suffix, wordEq, suffixOver, suffixLocal, suffixRun⟩

theorem plainSubtractionWord_forced_prefix_to_endpoint
    {prime phaseCount source target endpointPhase first second : Nat}
    {endpointDigit : Int} {endpoint : Vec2}
    (primeProperty : IsPrime prime) (primeBound : 6 * phaseCount < prime)
    (sourceBound : source < phaseCount)
    (endpointBound : endpointPhase < phaseCount)
    (sourceEndpointDistinct : source ≠ endpointPhase)
    (endpointMembership : InPhaseAt prime endpointPhase endpointDigit endpoint)
    (less : first < second)
    {word : List PhysicalTemplate}
    (wordOver : WordOver (plainSubtractionAlphabet source target) word)
    (allLocal : AllStatesLocal prime word
      (phaseAffine source (T prime (twoFieldCode prime first second))))
    (completeRun : SameLine
      (physicalWordAction prime word
        (phaseAffine source (T prime (twoFieldCode prime first second))))
      endpoint) :
    ∃ suffix,
      word = plainScanWord source target first ++ suffix ∧
      WordOver (plainSubtractionAlphabet source target) suffix ∧
      AllStatesLocal prime suffix
        (phaseAffine target
          (T prime (twoFieldCode prime first (second - first - 1)))) ∧
      SameLine
        (physicalWordAction prime suffix
          (phaseAffine target
            (T prime (twoFieldCode prime first (second - first - 1)))))
        endpoint := by
  rw [← subtractionState_zero prime first second primeProperty.1] at allLocal completeRun
  simpa [plainScanWord] using
    (plainSubtractionTail_forced_prefix_to_endpoint primeProperty primeBound
      sourceBound endpointBound sourceEndpointDistinct endpointMembership less
      (deleted := 0) (remaining := first) (by omega) wordOver allLocal
      completeRun)

theorem TTwoFieldCode_inPhaseAt
    {prime phase first second : Nat} (primeProperty : IsPrime prime) :
    ∃ digit, InPhaseAt prime phase digit
      (phaseAffine phase (T prime (twoFieldCode prime first second))) := by
  rw [← subtractionState_zero prime first second primeProperty.1]
  by_cases firstZero : first = 0
  · subst first
    exact ⟨1, subtractionState_inPhaseAt_marker
      (phase := phase) (first := 0) (second := second) primeProperty⟩
  · exact ⟨0, subtractionState_inPhaseAt_before
      (phase := phase) (first := first) (second := second) (deleted := 0)
      primeProperty (by omega)⟩

theorem no_plainSubtraction_letter_from_target
    {prime phaseCount source target : Nat}
    {digit : Int} {state : Vec2} {letter : PhysicalTemplate}
    (primeProperty : IsPrime prime) (primeBound : 6 * phaseCount < prime)
    (sourceBound : source < phaseCount) (targetBound : target < phaseCount)
    (sourceTargetDistinct : source ≠ target)
    (membership : InPhaseAt prime target digit state)
    (letterMem : letter ∈ plainSubtractionAlphabet source target)
    (outputLocal : LocalAt prime (letter.act prime state)) : False := by
  have forced := membership.physicalLetter_source_digit_unique primeProperty
    primeBound targetBound
    (plainSubtractionLetter_source_bound sourceBound letterMem)
    (plainSubtractionLetter_reserved letterMem)
    (by simpa [PhysicalTemplate.act, PhysicalTemplate.matrix] using outputLocal)
  simp [plainSubtractionAlphabet] at letterMem
  rcases letterMem with rfl | rfl <;>
    simp only [identityZero, identityMarker] at forced <;>
    exact sourceTargetDistinct forced.1.symm

theorem plainSubtraction_word_from_target_eq_nil
    {prime phaseCount source target : Nat}
    {digit : Int} {state : Vec2}
    (primeProperty : IsPrime prime) (primeBound : 6 * phaseCount < prime)
    (sourceBound : source < phaseCount) (targetBound : target < phaseCount)
    (sourceTargetDistinct : source ≠ target)
    (membership : InPhaseAt prime target digit state)
    {word : List PhysicalTemplate}
    (wordOver : WordOver (plainSubtractionAlphabet source target) word)
    (allLocal : AllStatesLocal prime word state) : word = [] := by
  cases word with
  | nil => rfl
  | cons letter tail =>
      exact False.elim (no_plainSubtraction_letter_from_target primeProperty
        primeBound sourceBound targetBound sourceTargetDistinct membership
        (wordOver letter (by simp)) allLocal.2.start)

theorem falseHandoff_rejects_plain_marker
    {prime phaseCount handoff intermediate endpointPhase first guess : Nat}
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
    (wordOver : WordOver
      (plainSubtractionAlphabet handoff intermediate) word)
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
        rcases plainSubtraction_letter primeProperty primeBound handoffBound
            (falseHandoffState_inPhaseAt_before (handoff := handoff)
              primeProperty QBelowGuess guessBelowTwoQ positionBelow)
            letterMem outputLocal with
          ⟨_, letterEq⟩ | ⟨digitEq, _⟩
        · exact letterEq
        · omega)
    (rejectMarker := fun {letter} letterMem outputLocal => by
      rcases plainSubtraction_letter primeProperty primeBound handoffBound
          markerMembership letterMem outputLocal with
        ⟨digitEq, _⟩ | ⟨digitEq, _⟩
      · exact False.elim (markerNeZero digitEq)
      · exact False.elim (markerNeOne digitEq))
    (loopStep := fun position positionBelow => by
      simpa [identityZero, zeroLoop, PhysicalTemplate.act,
        PhysicalTemplate.matrix] using
        (falseHandoffZero_step prime handoff first guess position
          primeProperty.1 QBelowGuess guessBelowTwoQ positionBelow))
    sumEq wordOver allLocal completeRun

theorem falseHandoff_rejects_plainSubtraction
    {prime phaseCount handoff intermediate endpointPhase first guess : Nat}
    {endpointDigit : Int} {endpoint : Vec2}
    (primeProperty : IsPrime prime) (primeBound : 6 * phaseCount < prime)
    (handoffBound : handoff < phaseCount)
    (endpointBound : endpointPhase < phaseCount)
    (handoffEndpointDistinct : handoff ≠ endpointPhase)
    (endpointMembership : InPhaseAt prime endpointPhase endpointDigit endpoint)
    (QBelowGuess : first + 1 < guess)
    (guessBelowTwoQ : guess < 2 * (first + 1))
    {word : List PhysicalTemplate}
    (wordOver : WordOver
      (plainSubtractionAlphabet handoff intermediate) word)
    (allLocal : AllStatesLocal prime word
      (phaseAffine handoff (falseHandoffState prime first guess 0)))
    (completeRun : SameLine
      (physicalWordAction prime word
        (phaseAffine handoff (falseHandoffState prime first guess 0)))
      endpoint) : False := by
  rcases Nat.lt_trichotomy (2 * guess) (3 * (first + 1)) with
    below | equal | above
  · exact falseHandoff_rejects_plain_marker primeProperty primeBound
      handoffBound endpointBound handoffEndpointDistinct endpointMembership
      QBelowGuess guessBelowTwoQ (by omega) (by omega)
      (falseHandoffState_inPhaseAt_marker_four (handoff := handoff)
        primeProperty QBelowGuess below)
      (deleted := 0) (remaining := falseHandoffZeroCount first guess)
      (by omega) wordOver allLocal completeRun
  · exact falseHandoff_rejects_plain_marker primeProperty primeBound
      handoffBound endpointBound handoffEndpointDistinct endpointMembership
      QBelowGuess guessBelowTwoQ (by omega) (by omega)
      (falseHandoffState_inPhaseAt_marker_three (handoff := handoff)
        primeProperty QBelowGuess equal)
      (deleted := 0) (remaining := falseHandoffZeroCount first guess)
      (by omega) wordOver allLocal completeRun
  · exact falseHandoff_rejects_plain_marker primeProperty primeBound
      handoffBound endpointBound handoffEndpointDistinct endpointMembership
      QBelowGuess guessBelowTwoQ (by omega) (by omega)
      (falseHandoffState_inPhaseAt_marker_negative_one (handoff := handoff)
        primeProperty above guessBelowTwoQ)
      (deleted := 0) (remaining := falseHandoffZeroCount first guess)
      (by omega) wordOver allLocal completeRun

theorem inverseSubtractionAlphabet_eq (source target : Nat) :
    inverseSubtractionAlphabet source target =
      subtractionAlphabet source target := by
  simp [inverseSubtractionAlphabet, subtractionAlphabet, identityZero,
    zeroLoop, inverseTMarker, markerExit]

/-- Once the first scan has reached the intermediate phase, even arbitrary
interleavings with letters from the first scan leave only the canonical
typed subtraction word. -/
theorem intermediate_union_forces_inverseSubtraction
    {prime phaseCount handoff intermediate output first second : Nat}
    {endpointDigit : Int} {endpoint : Vec2}
    (primeProperty : IsPrime prime) (primeBound : 6 * phaseCount < prime)
    (handoffBound : handoff < phaseCount)
    (intermediateBound : intermediate < phaseCount)
    (outputBound : output < phaseCount)
    (handoffIntermediateDistinct : handoff ≠ intermediate)
    (handoffOutputDistinct : handoff ≠ output)
    (intermediateOutputDistinct : intermediate ≠ output)
    (endpointMembership : InPhaseAt prime output endpointDigit endpoint)
    (less : first < second)
    {word : List PhysicalTemplate}
    (wordOver : WordOver
      (doubleValidatorAlphabet handoff intermediate output) word)
    (allLocal : AllStatesLocal prime word
      (phaseAffine intermediate (T prime (twoFieldCode prime first second))))
    (completeRun : SameLine
      (physicalWordAction prime word
        (phaseAffine intermediate
          (T prime (twoFieldCode prime first second)))) endpoint) :
    word = fifthScanWord intermediate output first := by
  have reordered : WordOver
      (inverseSubtractionAlphabet intermediate output ++
        plainSubtractionAlphabet handoff intermediate) word := by
    intro letter letterMem
    have membership := wordOver letter letterMem
    simp only [doubleValidatorAlphabet, List.mem_append] at membership ⊢
    exact membership.symm
  rcases wordOver_append_first_right reordered with inverseOnly |
      ⟨initial, letter, suffix, wordEq, initialOver, letterPlain, _⟩
  · have standardOver : WordOver
        (subtractionAlphabet intermediate output) word := by
      simpa [inverseSubtractionAlphabet_eq] using inverseOnly
    obtain ⟨residual, parsedEq, residualOver, residualLocal, _⟩ :=
      subtractionWord_forced_prefix_to_endpoint primeProperty primeBound
        intermediateBound outputBound intermediateOutputDistinct
        endpointMembership less standardOver allLocal completeRun
    obtain ⟨outputDigit, canonicalOutputMembership⟩ :=
      twoFieldCode_inPhaseAt (phase := output) (first := first)
        (second := second - first - 1) primeProperty
    have residualEq := subtraction_word_from_target_eq_nil primeProperty
      primeBound intermediateBound outputBound intermediateOutputDistinct
      canonicalOutputMembership residualOver residualLocal
    subst residual
    simpa [fifthScanWord, subtractionWord, identityZero, zeroLoop,
      inverseTMarker, markerExit] using parsedEq
  · obtain ⟨initialLocal, boundaryLocal⟩ :=
      allLocal.split_append_cons wordEq
    have boundaryMembership : InPhaseAt prime letter.sourcePhase letter.digit
        (physicalWordAction prime initial
          (phaseAffine intermediate
            (T prime (twoFieldCode prime first second)))) := by
      apply physicalLetter_input_inPhaseAt primeProperty
        (plainSubtractionLetter_reserved letterPlain) boundaryLocal.1
      simpa [PhysicalTemplate.act, PhysicalTemplate.matrix] using
        boundaryLocal.2.start
    have letterSource : letter.sourcePhase = handoff := by
      simp [plainSubtractionAlphabet] at letterPlain
      rcases letterPlain with rfl | rfl <;> rfl
    rw [letterSource] at boundaryMembership
    have standardInitialOver : WordOver
        (subtractionAlphabet intermediate output) initial := by
      simpa [inverseSubtractionAlphabet_eq] using initialOver
    obtain ⟨residual, _, residualOver, residualLocal, residualRun⟩ :=
      subtractionWord_forced_prefix_to_endpoint primeProperty primeBound
        intermediateBound handoffBound handoffIntermediateDistinct.symm
        boundaryMembership less standardInitialOver initialLocal
        (SameLine.refl _)
    obtain ⟨outputDigit, canonicalOutputMembership⟩ :=
      twoFieldCode_inPhaseAt (phase := output) (first := first)
        (second := second - first - 1) primeProperty
    have residualEq := subtraction_word_from_target_eq_nil primeProperty
      primeBound intermediateBound outputBound intermediateOutputDistinct
      canonicalOutputMembership residualOver residualLocal
    subst residual
    have phaseEq := (canonicalOutputMembership.unique primeProperty primeBound
      outputBound handoffBound boundaryMembership (by
        simpa [physicalWordAction] using residualRun)).1
    exact False.elim (handoffOutputDistinct phaseEq.symm)

/-- The accepted fivefold handoff forces both validation scans, in order,
even over their four-letter union alphabet. -/
theorem acceptedHandoff_union_forces_doubleValidator
    {prime phaseCount handoff intermediate output first : Nat}
    {endpointDigit : Int} {endpoint : Vec2}
    (primeProperty : IsPrime prime) (primeBound : 6 * phaseCount < prime)
    (handoffBound : handoff < phaseCount)
    (intermediateBound : intermediate < phaseCount)
    (outputBound : output < phaseCount)
    (handoffIntermediateDistinct : handoff ≠ intermediate)
    (handoffOutputDistinct : handoff ≠ output)
    (intermediateOutputDistinct : intermediate ≠ output)
    (endpointMembership : InPhaseAt prime output endpointDigit endpoint)
    {word : List PhysicalTemplate}
    (wordOver : WordOver
      (doubleValidatorAlphabet handoff intermediate output) word)
    (allLocal : AllStatesLocal prime word
      (phaseAffine handoff (acceptedHandoffState prime first)))
    (completeRun : SameLine
      (physicalWordAction prime word
        (phaseAffine handoff (acceptedHandoffState prime first))) endpoint) :
    word = doubleValidatorWord handoff intermediate output first := by
  rcases wordOver_append_first_right wordOver with plainOnly |
      ⟨initial, letter, suffix, wordEq, initialOver, letterInverse,
        suffixOver⟩
  · rw [acceptedHandoffState_eq prime first primeProperty.1] at allLocal completeRun
    obtain ⟨residual, _, residualOver, residualLocal, residualRun⟩ :=
      plainSubtractionWord_forced_prefix_to_endpoint primeProperty primeBound
        handoffBound outputBound handoffOutputDistinct endpointMembership
        (by omega : first < 4 * first + 3) plainOnly allLocal completeRun
    obtain ⟨intermediateDigit, intermediateMembership⟩ :=
      TTwoFieldCode_inPhaseAt (phase := intermediate) (first := first)
        (second := 4 * first + 3 - first - 1) primeProperty
    have residualEq := plainSubtraction_word_from_target_eq_nil primeProperty
      primeBound handoffBound intermediateBound handoffIntermediateDistinct
      intermediateMembership residualOver residualLocal
    subst residual
    have phaseEq := (intermediateMembership.unique primeProperty primeBound
      intermediateBound outputBound endpointMembership (by
        simpa [physicalWordAction] using residualRun)).1
    exact False.elim (intermediateOutputDistinct phaseEq)
  · obtain ⟨initialLocal, boundaryLocal⟩ :=
      allLocal.split_append_cons wordEq
    have inverseMem : letter ∈ subtractionAlphabet intermediate output := by
      simpa [inverseSubtractionAlphabet_eq] using letterInverse
    have boundaryMembership : InPhaseAt prime letter.sourcePhase letter.digit
        (physicalWordAction prime initial
          (phaseAffine handoff (acceptedHandoffState prime first))) := by
      apply physicalLetter_input_inPhaseAt primeProperty
        (subtractionLetter_reserved inverseMem) boundaryLocal.1
      simpa [PhysicalTemplate.act, PhysicalTemplate.matrix] using
        boundaryLocal.2.start
    have letterSource : letter.sourcePhase = intermediate := by
      simp [subtractionAlphabet] at inverseMem
      rcases inverseMem with rfl | rfl <;> rfl
    rw [letterSource] at boundaryMembership
    rw [acceptedHandoffState_eq prime first primeProperty.1] at boundaryMembership initialLocal
    obtain ⟨residual, initialEq, residualOver, residualLocal, residualRun⟩ :=
      plainSubtractionWord_forced_prefix_to_endpoint primeProperty primeBound
        handoffBound intermediateBound handoffIntermediateDistinct
        boundaryMembership (by omega : first < 4 * first + 3) initialOver
        initialLocal (SameLine.refl _)
    obtain ⟨intermediateDigit, intermediateMembership⟩ :=
      TTwoFieldCode_inPhaseAt (phase := intermediate) (first := first)
        (second := 4 * first + 3 - first - 1) primeProperty
    have residualEq := plainSubtraction_word_from_target_eq_nil primeProperty
      primeBound handoffBound intermediateBound handoffIntermediateDistinct
      intermediateMembership residualOver residualLocal
    subst residual
    have handoffSame : SameLine
        (phaseAffine intermediate
          (T prime
            (twoFieldCode prime first (4 * first + 3 - first - 1))))
        (physicalWordAction prime initial
          (phaseAffine handoff (T prime
            (twoFieldCode prime first (4 * first + 3))))) := by
      simpa [physicalWordAction] using residualRun
    have handoffSameOriginal : SameLine
        (phaseAffine intermediate
          (T prime
            (twoFieldCode prime first (4 * first + 3 - first - 1))))
        (physicalWordAction prime initial
          (phaseAffine handoff (acceptedHandoffState prime first))) := by
      simpa [acceptedHandoffState_eq prime first primeProperty.1] using
        handoffSame
    have tailOver : WordOver
        (doubleValidatorAlphabet handoff intermediate output)
        (letter :: suffix) := by
      intro candidate candidateMem
      simp only [List.mem_cons] at candidateMem
      rcases candidateMem with rfl | candidateMem
      · exact List.mem_append_right _ letterInverse
      · exact suffixOver candidate candidateMem
    have tailRun : SameLine
        (physicalWordAction prime (letter :: suffix)
          (physicalWordAction prime initial
            (phaseAffine handoff (acceptedHandoffState prime first))))
        endpoint := by
      rw [wordEq, physicalWordAction_append] at completeRun
      exact completeRun
    have canonicalTailLocal : AllStatesLocal prime (letter :: suffix)
        (phaseAffine intermediate
          (T prime
            (twoFieldCode prime first (4 * first + 3 - first - 1)))) :=
      boundaryLocal.of_sameLine (by omega) intermediateMembership.local.1
        handoffSameOriginal
    have canonicalTailRun : SameLine
        (physicalWordAction prime (letter :: suffix)
          (phaseAffine intermediate
            (T prime
              (twoFieldCode prime first (4 * first + 3 - first - 1)))))
        endpoint :=
      (physicalWordAction_preserves_sameLine prime (letter :: suffix)
        handoffSameOriginal).trans tailRun
    have tailEq := intermediate_union_forces_inverseSubtraction
      primeProperty primeBound handoffBound intermediateBound outputBound
      handoffIntermediateDistinct handoffOutputDistinct
      intermediateOutputDistinct endpointMembership
      (by omega : first < 4 * first + 3 - first - 1) tailOver
      canonicalTailLocal canonicalTailRun
    rw [wordEq, initialEq, tailEq]
    simp [doubleValidatorWord]

/-- A false survivor cannot cross the first scan, even if letters from the
second scan are available for arbitrary interleaving. -/
theorem falseHandoff_union_rejects_doubleValidator
    {prime phaseCount handoff intermediate output first guess : Nat}
    {endpointDigit : Int} {endpoint : Vec2}
    (primeProperty : IsPrime prime) (primeBound : 6 * phaseCount < prime)
    (handoffBound : handoff < phaseCount)
    (intermediateBound : intermediate < phaseCount)
    (outputBound : output < phaseCount)
    (handoffIntermediateDistinct : handoff ≠ intermediate)
    (handoffOutputDistinct : handoff ≠ output)
    (endpointMembership : InPhaseAt prime output endpointDigit endpoint)
    (QBelowGuess : first + 1 < guess)
    (guessBelowTwoQ : guess < 2 * (first + 1))
    {word : List PhysicalTemplate}
    (wordOver : WordOver
      (doubleValidatorAlphabet handoff intermediate output) word)
    (allLocal : AllStatesLocal prime word
      (phaseAffine handoff (falseHandoffState prime first guess 0)))
    (completeRun : SameLine
      (physicalWordAction prime word
        (phaseAffine handoff (falseHandoffState prime first guess 0)))
      endpoint) : False := by
  rcases wordOver_append_first_right wordOver with plainOnly |
      ⟨initial, letter, suffix, wordEq, initialOver, letterInverse, _⟩
  · exact falseHandoff_rejects_plainSubtraction primeProperty primeBound
      handoffBound outputBound handoffOutputDistinct endpointMembership
      QBelowGuess guessBelowTwoQ plainOnly allLocal completeRun
  · obtain ⟨initialLocal, boundaryLocal⟩ :=
      allLocal.split_append_cons wordEq
    have inverseMem : letter ∈ subtractionAlphabet intermediate output := by
      simpa [inverseSubtractionAlphabet_eq] using letterInverse
    have boundaryMembership : InPhaseAt prime letter.sourcePhase letter.digit
        (physicalWordAction prime initial
          (phaseAffine handoff (falseHandoffState prime first guess 0))) := by
      apply physicalLetter_input_inPhaseAt primeProperty
        (subtractionLetter_reserved inverseMem) boundaryLocal.1
      simpa [PhysicalTemplate.act, PhysicalTemplate.matrix] using
        boundaryLocal.2.start
    have letterSource : letter.sourcePhase = intermediate := by
      simp [subtractionAlphabet] at inverseMem
      rcases inverseMem with rfl | rfl <;> rfl
    rw [letterSource] at boundaryMembership
    exact falseHandoff_rejects_plainSubtraction primeProperty primeBound
      handoffBound intermediateBound handoffIntermediateDistinct
      boundaryMembership QBelowGuess guessBelowTwoQ initialOver initialLocal
      (SameLine.refl _)

/-- Starting in the intermediate phase, a validator-only word cannot end in
a guarded phase different from the declared output. -/
theorem intermediate_union_cannot_reach_foreign_phase
    {prime phaseCount handoff intermediate output endpointPhase first second :
      Nat}
    {endpointDigit : Int} {endpoint : Vec2}
    (primeProperty : IsPrime prime) (primeBound : 6 * phaseCount < prime)
    (handoffBound : handoff < phaseCount)
    (intermediateBound : intermediate < phaseCount)
    (outputBound : output < phaseCount)
    (endpointBound : endpointPhase < phaseCount)
    (handoffIntermediateDistinct : handoff ≠ intermediate)
    (handoffOutputDistinct : handoff ≠ output)
    (intermediateOutputDistinct : intermediate ≠ output)
    (intermediateEndpointDistinct : intermediate ≠ endpointPhase)
    (outputEndpointDistinct : output ≠ endpointPhase)
    (endpointMembership : InPhaseAt prime endpointPhase endpointDigit endpoint)
    (less : first < second)
    {word : List PhysicalTemplate}
    (wordOver : WordOver
      (doubleValidatorAlphabet handoff intermediate output) word)
    (allLocal : AllStatesLocal prime word
      (phaseAffine intermediate (T prime (twoFieldCode prime first second))))
    (completeRun : SameLine
      (physicalWordAction prime word
        (phaseAffine intermediate
          (T prime (twoFieldCode prime first second)))) endpoint) : False := by
  have reordered : WordOver
      (inverseSubtractionAlphabet intermediate output ++
        plainSubtractionAlphabet handoff intermediate) word := by
    intro letter letterMem
    have membership := wordOver letter letterMem
    simp only [doubleValidatorAlphabet, List.mem_append] at membership ⊢
    exact membership.symm
  rcases wordOver_append_first_right reordered with inverseOnly |
      ⟨initial, letter, suffix, wordEq, initialOver, letterPlain, _⟩
  · have standardOver : WordOver
        (subtractionAlphabet intermediate output) word := by
      simpa [inverseSubtractionAlphabet_eq] using inverseOnly
    obtain ⟨residual, _, residualOver, residualLocal, residualRun⟩ :=
      subtractionWord_forced_prefix_to_endpoint primeProperty primeBound
        intermediateBound endpointBound intermediateEndpointDistinct
        endpointMembership less standardOver allLocal completeRun
    obtain ⟨outputDigit, canonicalOutputMembership⟩ :=
      twoFieldCode_inPhaseAt (phase := output) (first := first)
        (second := second - first - 1) primeProperty
    have residualEq := subtraction_word_from_target_eq_nil primeProperty
      primeBound intermediateBound outputBound intermediateOutputDistinct
      canonicalOutputMembership residualOver residualLocal
    subst residual
    have phaseEq := (canonicalOutputMembership.unique primeProperty primeBound
      outputBound endpointBound endpointMembership (by
        simpa [physicalWordAction] using residualRun)).1
    exact outputEndpointDistinct phaseEq
  · obtain ⟨initialLocal, boundaryLocal⟩ :=
      allLocal.split_append_cons wordEq
    have boundaryMembership : InPhaseAt prime letter.sourcePhase letter.digit
        (physicalWordAction prime initial
          (phaseAffine intermediate
            (T prime (twoFieldCode prime first second)))) := by
      apply physicalLetter_input_inPhaseAt primeProperty
        (plainSubtractionLetter_reserved letterPlain) boundaryLocal.1
      simpa [PhysicalTemplate.act, PhysicalTemplate.matrix] using
        boundaryLocal.2.start
    have letterSource : letter.sourcePhase = handoff := by
      simp [plainSubtractionAlphabet] at letterPlain
      rcases letterPlain with rfl | rfl <;> rfl
    rw [letterSource] at boundaryMembership
    have standardInitialOver : WordOver
        (subtractionAlphabet intermediate output) initial := by
      simpa [inverseSubtractionAlphabet_eq] using initialOver
    obtain ⟨residual, _, residualOver, residualLocal, residualRun⟩ :=
      subtractionWord_forced_prefix_to_endpoint primeProperty primeBound
        intermediateBound handoffBound handoffIntermediateDistinct.symm
        boundaryMembership less standardInitialOver initialLocal
        (SameLine.refl _)
    obtain ⟨outputDigit, canonicalOutputMembership⟩ :=
      twoFieldCode_inPhaseAt (phase := output) (first := first)
        (second := second - first - 1) primeProperty
    have residualEq := subtraction_word_from_target_eq_nil primeProperty
      primeBound intermediateBound outputBound intermediateOutputDistinct
      canonicalOutputMembership residualOver residualLocal
    subst residual
    have phaseEq := (canonicalOutputMembership.unique primeProperty primeBound
      outputBound handoffBound boundaryMembership (by
        simpa [physicalWordAction] using residualRun)).1
    exact handoffOutputDistinct phaseEq.symm

/-- The accepted handoff cannot reach a guarded phase foreign to all three
validator control phases by a validator-only word. -/
theorem acceptedHandoff_doubleValidator_cannot_reach_foreign_phase
    {prime phaseCount handoff intermediate output endpointPhase first : Nat}
    {endpointDigit : Int} {endpoint : Vec2}
    (primeProperty : IsPrime prime) (primeBound : 6 * phaseCount < prime)
    (handoffBound : handoff < phaseCount)
    (intermediateBound : intermediate < phaseCount)
    (outputBound : output < phaseCount)
    (endpointBound : endpointPhase < phaseCount)
    (handoffIntermediateDistinct : handoff ≠ intermediate)
    (handoffOutputDistinct : handoff ≠ output)
    (intermediateOutputDistinct : intermediate ≠ output)
    (handoffEndpointDistinct : handoff ≠ endpointPhase)
    (intermediateEndpointDistinct : intermediate ≠ endpointPhase)
    (outputEndpointDistinct : output ≠ endpointPhase)
    (endpointMembership : InPhaseAt prime endpointPhase endpointDigit endpoint)
    {word : List PhysicalTemplate}
    (wordOver : WordOver
      (doubleValidatorAlphabet handoff intermediate output) word)
    (allLocal : AllStatesLocal prime word
      (phaseAffine handoff (acceptedHandoffState prime first)))
    (completeRun : SameLine
      (physicalWordAction prime word
        (phaseAffine handoff (acceptedHandoffState prime first))) endpoint) :
    False := by
  rcases wordOver_append_first_right wordOver with plainOnly |
      ⟨initial, letter, suffix, wordEq, initialOver, letterInverse,
        suffixOver⟩
  · rw [acceptedHandoffState_eq prime first primeProperty.1] at allLocal completeRun
    obtain ⟨residual, _, residualOver, residualLocal, residualRun⟩ :=
      plainSubtractionWord_forced_prefix_to_endpoint primeProperty primeBound
        handoffBound endpointBound handoffEndpointDistinct endpointMembership
        (by omega : first < 4 * first + 3) plainOnly allLocal completeRun
    obtain ⟨intermediateDigit, intermediateMembership⟩ :=
      TTwoFieldCode_inPhaseAt (phase := intermediate) (first := first)
        (second := 4 * first + 3 - first - 1) primeProperty
    have residualEq := plainSubtraction_word_from_target_eq_nil primeProperty
      primeBound handoffBound intermediateBound handoffIntermediateDistinct
      intermediateMembership residualOver residualLocal
    subst residual
    have phaseEq := (intermediateMembership.unique primeProperty primeBound
      intermediateBound endpointBound endpointMembership (by
        simpa [physicalWordAction] using residualRun)).1
    exact intermediateEndpointDistinct phaseEq
  · obtain ⟨initialLocal, boundaryLocal⟩ :=
      allLocal.split_append_cons wordEq
    have inverseMem : letter ∈ subtractionAlphabet intermediate output := by
      simpa [inverseSubtractionAlphabet_eq] using letterInverse
    have boundaryMembership : InPhaseAt prime letter.sourcePhase letter.digit
        (physicalWordAction prime initial
          (phaseAffine handoff (acceptedHandoffState prime first))) := by
      apply physicalLetter_input_inPhaseAt primeProperty
        (subtractionLetter_reserved inverseMem) boundaryLocal.1
      simpa [PhysicalTemplate.act, PhysicalTemplate.matrix] using
        boundaryLocal.2.start
    have letterSource : letter.sourcePhase = intermediate := by
      simp [subtractionAlphabet] at inverseMem
      rcases inverseMem with rfl | rfl <;> rfl
    rw [letterSource] at boundaryMembership
    rw [acceptedHandoffState_eq prime first primeProperty.1] at boundaryMembership initialLocal
    obtain ⟨residual, _, residualOver, residualLocal, residualRun⟩ :=
      plainSubtractionWord_forced_prefix_to_endpoint primeProperty primeBound
        handoffBound intermediateBound handoffIntermediateDistinct
        boundaryMembership (by omega : first < 4 * first + 3) initialOver
        initialLocal (SameLine.refl _)
    obtain ⟨intermediateDigit, intermediateMembership⟩ :=
      TTwoFieldCode_inPhaseAt (phase := intermediate) (first := first)
        (second := 4 * first + 3 - first - 1) primeProperty
    have residualEq := plainSubtraction_word_from_target_eq_nil primeProperty
      primeBound handoffBound intermediateBound handoffIntermediateDistinct
      intermediateMembership residualOver residualLocal
    subst residual
    have handoffSame : SameLine
        (phaseAffine intermediate
          (T prime
            (twoFieldCode prime first (4 * first + 3 - first - 1))))
        (physicalWordAction prime initial
          (phaseAffine handoff (acceptedHandoffState prime first))) := by
      simpa [physicalWordAction, acceptedHandoffState_eq prime first
        primeProperty.1] using residualRun
    have tailOver : WordOver
        (doubleValidatorAlphabet handoff intermediate output)
        (letter :: suffix) := by
      intro candidate candidateMem
      simp only [List.mem_cons] at candidateMem
      rcases candidateMem with rfl | candidateMem
      · exact List.mem_append_right _ letterInverse
      · exact suffixOver candidate candidateMem
    have tailRun : SameLine
        (physicalWordAction prime (letter :: suffix)
          (physicalWordAction prime initial
            (phaseAffine handoff (acceptedHandoffState prime first))))
        endpoint := by
      rw [wordEq, physicalWordAction_append] at completeRun
      exact completeRun
    have canonicalTailLocal : AllStatesLocal prime (letter :: suffix)
        (phaseAffine intermediate
          (T prime
            (twoFieldCode prime first (4 * first + 3 - first - 1)))) :=
      boundaryLocal.of_sameLine (by omega) intermediateMembership.local.1
        handoffSame
    have canonicalTailRun : SameLine
        (physicalWordAction prime (letter :: suffix)
          (phaseAffine intermediate
            (T prime
              (twoFieldCode prime first (4 * first + 3 - first - 1)))))
        endpoint :=
      (physicalWordAction_preserves_sameLine prime (letter :: suffix)
        handoffSame).trans tailRun
    exact intermediate_union_cannot_reach_foreign_phase primeProperty
      primeBound handoffBound intermediateBound outputBound endpointBound
      handoffIntermediateDistinct handoffOutputDistinct
      intermediateOutputDistinct intermediateEndpointDistinct
      outputEndpointDistinct endpointMembership
      (by omega : first < 4 * first + 3 - first - 1) tailOver
      canonicalTailLocal canonicalTailRun

/-- The false handoff cannot reach any foreign guarded phase through the
double-validator alphabet. -/
theorem falseHandoff_doubleValidator_cannot_reach_foreign_phase
    {prime phaseCount handoff intermediate output endpointPhase first guess :
      Nat}
    {endpointDigit : Int} {endpoint : Vec2}
    (primeProperty : IsPrime prime) (primeBound : 6 * phaseCount < prime)
    (handoffBound : handoff < phaseCount)
    (intermediateBound : intermediate < phaseCount)
    (endpointBound : endpointPhase < phaseCount)
    (handoffIntermediateDistinct : handoff ≠ intermediate)
    (handoffEndpointDistinct : handoff ≠ endpointPhase)
    (endpointMembership : InPhaseAt prime endpointPhase endpointDigit endpoint)
    (QBelowGuess : first + 1 < guess)
    (guessBelowTwoQ : guess < 2 * (first + 1))
    {word : List PhysicalTemplate}
    (wordOver : WordOver
      (doubleValidatorAlphabet handoff intermediate output) word)
    (allLocal : AllStatesLocal prime word
      (phaseAffine handoff (falseHandoffState prime first guess 0)))
    (completeRun : SameLine
      (physicalWordAction prime word
        (phaseAffine handoff (falseHandoffState prime first guess 0)))
      endpoint) : False := by
  rcases wordOver_append_first_right wordOver with plainOnly |
      ⟨initial, letter, suffix, wordEq, initialOver, letterInverse, _⟩
  · exact falseHandoff_rejects_plainSubtraction primeProperty primeBound
      handoffBound endpointBound handoffEndpointDistinct endpointMembership
      QBelowGuess guessBelowTwoQ plainOnly allLocal completeRun
  · obtain ⟨initialLocal, boundaryLocal⟩ :=
      allLocal.split_append_cons wordEq
    have inverseMem : letter ∈ subtractionAlphabet intermediate output := by
      simpa [inverseSubtractionAlphabet_eq] using letterInverse
    have boundaryMembership : InPhaseAt prime letter.sourcePhase letter.digit
        (physicalWordAction prime initial
          (phaseAffine handoff (falseHandoffState prime first guess 0))) := by
      apply physicalLetter_input_inPhaseAt primeProperty
        (subtractionLetter_reserved inverseMem) boundaryLocal.1
      simpa [PhysicalTemplate.act, PhysicalTemplate.matrix] using
        boundaryLocal.2.start
    have letterSource : letter.sourcePhase = intermediate := by
      simp [subtractionAlphabet] at inverseMem
      rcases inverseMem with rfl | rfl <;> rfl
    rw [letterSource] at boundaryMembership
    exact falseHandoff_rejects_plainSubtraction primeProperty primeBound
      handoffBound intermediateBound handoffIntermediateDistinct
      boundaryMembership QBelowGuess guessBelowTwoQ initialOver initialLocal
      (SameLine.refl _)

private theorem core_source_ne_foreign
    {source handoff guessPhase firstPhase secondPhase thirdPhase fourthPhase
      fifthPhase markerTwoPhase foreign : Nat} {letter : PhysicalTemplate}
    (foreignNotActive : foreign ∉
      [source, guessPhase, firstPhase, secondPhase, thirdPhase, fourthPhase,
        fifthPhase, markerTwoPhase])
    (letterMem : letter ∈ FivefoldFrontModule.alphabet source handoff
      guessPhase firstPhase secondPhase thirdPhase fourthPhase fifthPhase
      markerTwoPhase) :
    letter.sourcePhase ≠ foreign := by
  intro phaseEq
  apply foreignNotActive
  rw [← phaseEq]
  exact FivefoldFrontModule.letter_source_mem_active letterMem

theorem doubleValidatorLetter_reserved
    {handoff intermediate output : Nat} {letter : PhysicalTemplate}
    (letterMem : letter ∈
      doubleValidatorAlphabet handoff intermediate output) :
    ReservedDigit letter.digit := by
  simp only [doubleValidatorAlphabet, List.mem_append] at letterMem
  rcases letterMem with plainMem | inverseMem
  · exact plainSubtractionLetter_reserved plainMem
  · apply subtractionLetter_reserved
    simpa [inverseSubtractionAlphabet_eq] using inverseMem

theorem doubleValidatorLetter_source
    {handoff intermediate output : Nat} {letter : PhysicalTemplate}
    (letterMem : letter ∈
      doubleValidatorAlphabet handoff intermediate output) :
    letter.sourcePhase = handoff ∨ letter.sourcePhase = intermediate := by
  simp [doubleValidatorAlphabet, plainSubtractionAlphabet,
    inverseSubtractionAlphabet] at letterMem
  rcases letterMem with rfl | rfl | rfl | rfl
  · exact .inl rfl
  · exact .inl rfl
  · exact .inr rfl
  · exact .inr rfl

theorem doubleLetter_source_mem
    {source handoff intermediate output guessPhase firstPhase secondPhase
      thirdPhase fourthPhase fifthPhase markerTwoPhase : Nat}
    {letter : PhysicalTemplate}
    (letterMem : letter ∈ doubleAlphabet source handoff intermediate output
      guessPhase firstPhase secondPhase thirdPhase fourthPhase fifthPhase
      markerTwoPhase) :
    letter.sourcePhase ∈ doubleSourcePhases source handoff intermediate
      guessPhase firstPhase secondPhase thirdPhase fourthPhase fifthPhase
      markerTwoPhase := by
  rw [doubleAlphabet_eq] at letterMem
  simp only [List.mem_append] at letterMem
  rcases letterMem with coreMem | validatorMem
  · have active := FivefoldFrontModule.letter_source_mem_active coreMem
    simp [doubleSourcePhases] at active ⊢
    grind
  · rcases doubleValidatorLetter_source validatorMem with sourceEq | sourceEq
    · simp [doubleSourcePhases, sourceEq]
    · simp [doubleSourcePhases, sourceEq]

theorem doubleLetter_source_bound
    {phaseCount source handoff intermediate output guessPhase firstPhase
      secondPhase thirdPhase fourthPhase fifthPhase markerTwoPhase : Nat}
    (layout : FivefoldFrontModule.PhaseLayout phaseCount source guessPhase
      firstPhase secondPhase thirdPhase fourthPhase fifthPhase markerTwoPhase)
    (handoffBound : handoff < phaseCount)
    (intermediateBound : intermediate < phaseCount)
    {letter : PhysicalTemplate}
    (letterMem : letter ∈ doubleAlphabet source handoff intermediate output
      guessPhase firstPhase secondPhase thirdPhase fourthPhase fifthPhase
      markerTwoPhase) :
    letter.sourcePhase < phaseCount := by
  rw [doubleAlphabet_eq] at letterMem
  simp only [List.mem_append] at letterMem
  rcases letterMem with coreMem | validatorMem
  · exact FivefoldFrontModule.letter_source_bound layout coreMem
  · rcases doubleValidatorLetter_source validatorMem with sourceEq | sourceEq
    · simpa [sourceEq] using handoffBound
    · simpa [sourceEq] using intermediateBound

theorem doubleLetter_reserved
    {source handoff intermediate output guessPhase firstPhase secondPhase
      thirdPhase fourthPhase fifthPhase markerTwoPhase : Nat}
    {letter : PhysicalTemplate}
    (letterMem : letter ∈ doubleAlphabet source handoff intermediate output
      guessPhase firstPhase secondPhase thirdPhase fourthPhase fifthPhase
      markerTwoPhase) : ReservedDigit letter.digit := by
  rw [doubleAlphabet_eq] at letterMem
  simp only [List.mem_append] at letterMem
  rcases letterMem with coreMem | validatorMem
  · exact FivefoldFrontModule.letter_reserved coreMem
  · exact doubleValidatorLetter_reserved validatorMem

/-- Core letters cannot be inserted after the accepted handoff: cutting at
the first such letter reduces the prefix to the foreign-phase impossibility
for the validator alphabet. -/
theorem acceptedHandoff_full_union_forces_doubleValidator
    {prime phaseCount source handoff intermediate output guessPhase firstPhase
      secondPhase thirdPhase fourthPhase fifthPhase markerTwoPhase first : Nat}
    {endpointDigit : Int} {endpoint : Vec2}
    (primeProperty : IsPrime prime) (primeBound : 6 * phaseCount < prime)
    (layout : FivefoldFrontModule.PhaseLayout phaseCount source guessPhase
      firstPhase secondPhase thirdPhase fourthPhase fifthPhase markerTwoPhase)
    (handoffBound : handoff < phaseCount)
    (intermediateBound : intermediate < phaseCount)
    (outputBound : output < phaseCount)
    (handoffNotActive : handoff ∉
      [source, guessPhase, firstPhase, secondPhase, thirdPhase, fourthPhase,
        fifthPhase, markerTwoPhase])
    (intermediateNotActive : intermediate ∉
      [source, guessPhase, firstPhase, secondPhase, thirdPhase, fourthPhase,
        fifthPhase, markerTwoPhase])
    (outputNotActive : output ∉
      [source, guessPhase, firstPhase, secondPhase, thirdPhase, fourthPhase,
        fifthPhase, markerTwoPhase])
    (handoffIntermediateDistinct : handoff ≠ intermediate)
    (handoffOutputDistinct : handoff ≠ output)
    (intermediateOutputDistinct : intermediate ≠ output)
    (endpointMembership : InPhaseAt prime output endpointDigit endpoint)
    {word : List PhysicalTemplate}
    (wordOver : WordOver
      (FivefoldFrontModule.alphabet source handoff guessPhase firstPhase
          secondPhase thirdPhase fourthPhase fifthPhase markerTwoPhase ++
        doubleValidatorAlphabet handoff intermediate output) word)
    (allLocal : AllStatesLocal prime word
      (phaseAffine handoff (acceptedHandoffState prime first)))
    (completeRun : SameLine
      (physicalWordAction prime word
        (phaseAffine handoff (acceptedHandoffState prime first))) endpoint) :
    word = doubleValidatorWord handoff intermediate output first := by
  have reordered : WordOver
      (doubleValidatorAlphabet handoff intermediate output ++
        FivefoldFrontModule.alphabet source handoff guessPhase firstPhase
          secondPhase thirdPhase fourthPhase fifthPhase markerTwoPhase) word := by
    intro letter letterMem
    have membership := wordOver letter letterMem
    simp only [List.mem_append] at membership ⊢
    exact membership.symm
  rcases wordOver_append_first_right reordered with validatorOnly |
      ⟨initial, letter, suffix, wordEq, initialOver, letterCore, _⟩
  · exact acceptedHandoff_union_forces_doubleValidator primeProperty
      primeBound handoffBound intermediateBound outputBound
      handoffIntermediateDistinct handoffOutputDistinct
      intermediateOutputDistinct endpointMembership validatorOnly allLocal
      completeRun
  · obtain ⟨initialLocal, boundaryLocal⟩ :=
      allLocal.split_append_cons wordEq
    have boundaryMembership : InPhaseAt prime letter.sourcePhase letter.digit
        (physicalWordAction prime initial
          (phaseAffine handoff (acceptedHandoffState prime first))) := by
      apply physicalLetter_input_inPhaseAt primeProperty
        (FivefoldFrontModule.letter_reserved letterCore) boundaryLocal.1
      simpa [PhysicalTemplate.act, PhysicalTemplate.matrix] using
        boundaryLocal.2.start
    exact False.elim
      (acceptedHandoff_doubleValidator_cannot_reach_foreign_phase
        primeProperty primeBound handoffBound intermediateBound outputBound
        (FivefoldFrontModule.letter_source_bound layout letterCore)
        handoffIntermediateDistinct handoffOutputDistinct
        intermediateOutputDistinct
        (core_source_ne_foreign handoffNotActive letterCore).symm
        (core_source_ne_foreign intermediateNotActive letterCore).symm
        (core_source_ne_foreign outputNotActive letterCore).symm
        boundaryMembership initialOver initialLocal (SameLine.refl _))

/-- The false handoff remains rejecting over the complete core-plus-validator
union alphabet. -/
theorem falseHandoff_full_union_rejects_doubleValidator
    {prime phaseCount source handoff intermediate output guessPhase firstPhase
      secondPhase thirdPhase fourthPhase fifthPhase markerTwoPhase first guess :
      Nat}
    {endpointDigit : Int} {endpoint : Vec2}
    (primeProperty : IsPrime prime) (primeBound : 6 * phaseCount < prime)
    (layout : FivefoldFrontModule.PhaseLayout phaseCount source guessPhase
      firstPhase secondPhase thirdPhase fourthPhase fifthPhase markerTwoPhase)
    (handoffBound : handoff < phaseCount)
    (intermediateBound : intermediate < phaseCount)
    (outputBound : output < phaseCount)
    (handoffNotActive : handoff ∉
      [source, guessPhase, firstPhase, secondPhase, thirdPhase, fourthPhase,
        fifthPhase, markerTwoPhase])
    (handoffIntermediateDistinct : handoff ≠ intermediate)
    (handoffOutputDistinct : handoff ≠ output)
    (endpointMembership : InPhaseAt prime output endpointDigit endpoint)
    (QBelowGuess : first + 1 < guess)
    (guessBelowTwoQ : guess < 2 * (first + 1))
    {word : List PhysicalTemplate}
    (wordOver : WordOver
      (FivefoldFrontModule.alphabet source handoff guessPhase firstPhase
          secondPhase thirdPhase fourthPhase fifthPhase markerTwoPhase ++
        doubleValidatorAlphabet handoff intermediate output) word)
    (allLocal : AllStatesLocal prime word
      (phaseAffine handoff (falseHandoffState prime first guess 0)))
    (completeRun : SameLine
      (physicalWordAction prime word
        (phaseAffine handoff (falseHandoffState prime first guess 0)))
      endpoint) : False := by
  have reordered : WordOver
      (doubleValidatorAlphabet handoff intermediate output ++
        FivefoldFrontModule.alphabet source handoff guessPhase firstPhase
          secondPhase thirdPhase fourthPhase fifthPhase markerTwoPhase) word := by
    intro letter letterMem
    have membership := wordOver letter letterMem
    simp only [List.mem_append] at membership ⊢
    exact membership.symm
  rcases wordOver_append_first_right reordered with validatorOnly |
      ⟨initial, letter, suffix, wordEq, initialOver, letterCore, _⟩
  · exact falseHandoff_union_rejects_doubleValidator primeProperty
      primeBound handoffBound intermediateBound outputBound
      handoffIntermediateDistinct handoffOutputDistinct endpointMembership
      QBelowGuess guessBelowTwoQ validatorOnly allLocal completeRun
  · obtain ⟨initialLocal, boundaryLocal⟩ :=
      allLocal.split_append_cons wordEq
    have boundaryMembership : InPhaseAt prime letter.sourcePhase letter.digit
        (physicalWordAction prime initial
          (phaseAffine handoff (falseHandoffState prime first guess 0))) := by
      apply physicalLetter_input_inPhaseAt primeProperty
        (FivefoldFrontModule.letter_reserved letterCore) boundaryLocal.1
      simpa [PhysicalTemplate.act, PhysicalTemplate.matrix] using
        boundaryLocal.2.start
    exact falseHandoff_doubleValidator_cannot_reach_foreign_phase
      primeProperty primeBound handoffBound intermediateBound
      (FivefoldFrontModule.letter_source_bound layout letterCore)
      handoffIntermediateDistinct
      (core_source_ne_foreign handoffNotActive letterCore).symm
      boundaryMembership QBelowGuess guessBelowTwoQ initialOver initialLocal
      (SameLine.refl _)

/-- Full unrestricted-word converse for the twenty-letter double validated
front. -/
theorem doubleWord_unique
    {prime phaseCount source handoff intermediate output guessPhase firstPhase
      secondPhase thirdPhase fourthPhase fifthPhase markerTwoPhase inputFirst :
      Nat}
    {endpointDigit : Int} {endpoint : Vec2}
    (primeProperty : IsPrime prime) (primeBound : 6 * phaseCount < prime)
    (layout : FivefoldFrontModule.PhaseLayout phaseCount source guessPhase
      firstPhase secondPhase thirdPhase fourthPhase fifthPhase markerTwoPhase)
    (handoffBound : handoff < phaseCount)
    (intermediateBound : intermediate < phaseCount)
    (outputBound : output < phaseCount)
    (handoffNotActive : handoff ∉
      [source, guessPhase, firstPhase, secondPhase, thirdPhase, fourthPhase,
        fifthPhase, markerTwoPhase])
    (intermediateNotActive : intermediate ∉
      [source, guessPhase, firstPhase, secondPhase, thirdPhase, fourthPhase,
        fifthPhase, markerTwoPhase])
    (outputNotActive : output ∉
      [source, guessPhase, firstPhase, secondPhase, thirdPhase, fourthPhase,
        fifthPhase, markerTwoPhase])
    (handoffIntermediateDistinct : handoff ≠ intermediate)
    (handoffOutputDistinct : handoff ≠ output)
    (intermediateOutputDistinct : intermediate ≠ output)
    (endpointMembership : InPhaseAt prime output endpointDigit endpoint)
    {word : List PhysicalTemplate}
    (wordOver : WordOver
      (doubleAlphabet source handoff intermediate output guessPhase firstPhase
        secondPhase thirdPhase fourthPhase fifthPhase markerTwoPhase) word)
    (allLocal : AllStatesLocal prime word
      (phaseAffine source (unaryCode prime (5 * inputFirst + 4))))
    (completeRun : SameLine
      (physicalWordAction prime word
        (phaseAffine source (unaryCode prime (5 * inputFirst + 4))))
      endpoint) :
    word = doubleWord source handoff intermediate output guessPhase firstPhase
      secondPhase thirdPhase fourthPhase fifthPhase markerTwoPhase inputFirst := by
  have unionOver : WordOver
      (FivefoldFrontModule.alphabet source handoff guessPhase firstPhase
          secondPhase thirdPhase fourthPhase fifthPhase markerTwoPhase ++
        doubleValidatorAlphabet handoff intermediate output) word := by
    simpa [doubleAlphabet_eq] using wordOver
  rcases wordOver_append_first_right unionOver with coreOnly |
      ⟨initial, letter, suffix, wordEq, initialOver, letterValidator,
        suffixOver⟩
  · exact False.elim (coreWord_cannot_reach_foreign_phase primeProperty
      primeBound layout handoffBound outputBound handoffNotActive
      outputNotActive handoffOutputDistinct endpointMembership coreOnly
      allLocal completeRun)
  · obtain ⟨initialLocal, boundaryLocal⟩ :=
      allLocal.split_append_cons wordEq
    have boundaryMembership : InPhaseAt prime letter.sourcePhase letter.digit
        (physicalWordAction prime initial
          (phaseAffine source (unaryCode prime (5 * inputFirst + 4)))) := by
      apply physicalLetter_input_inPhaseAt primeProperty
        (doubleValidatorLetter_reserved letterValidator) boundaryLocal.1
      simpa [PhysicalTemplate.act, PhysicalTemplate.matrix] using
        boundaryLocal.2.start
    rcases doubleValidatorLetter_source letterValidator with
      sourceHandoff | sourceIntermediate
    · rw [sourceHandoff] at boundaryMembership
      have prefixClassification := corePrefix_to_handoff_classifies
        primeProperty primeBound layout handoffBound handoffNotActive
        boundaryMembership initialOver initialLocal (SameLine.refl _)
      have tailOver : WordOver
          (FivefoldFrontModule.alphabet source handoff guessPhase firstPhase
              secondPhase thirdPhase fourthPhase fifthPhase markerTwoPhase ++
            doubleValidatorAlphabet handoff intermediate output)
          (letter :: suffix) := by
        intro candidate candidateMem
        simp only [List.mem_cons] at candidateMem
        rcases candidateMem with rfl | candidateMem
        · exact List.mem_append_right _ letterValidator
        · exact suffixOver candidate candidateMem
      have tailRun : SameLine
          (physicalWordAction prime (letter :: suffix)
            (physicalWordAction prime initial
              (phaseAffine source (unaryCode prime (5 * inputFirst + 4)))))
          endpoint := by
        rw [wordEq, physicalWordAction_append] at completeRun
        exact completeRun
      rcases prefixClassification with accepted | falseSurvivor
      · rcases accepted with ⟨initialEq, handoffSame⟩
        obtain ⟨handoffDigit, handoffMembership⟩ :=
          acceptedHandoff_inPhaseAt (handoff := handoff)
            (first := inputFirst) primeProperty
        have canonicalTailLocal : AllStatesLocal prime (letter :: suffix)
            (phaseAffine handoff
              (acceptedHandoffState prime inputFirst)) :=
          boundaryLocal.of_sameLine (by omega) handoffMembership.local.1
            handoffSame
        have canonicalTailRun : SameLine
            (physicalWordAction prime (letter :: suffix)
              (phaseAffine handoff
                (acceptedHandoffState prime inputFirst))) endpoint :=
          (physicalWordAction_preserves_sameLine prime (letter :: suffix)
            handoffSame).trans tailRun
        have tailEq := acceptedHandoff_full_union_forces_doubleValidator
          primeProperty primeBound layout handoffBound intermediateBound
          outputBound handoffNotActive intermediateNotActive outputNotActive
          handoffIntermediateDistinct handoffOutputDistinct
          intermediateOutputDistinct endpointMembership tailOver
          canonicalTailLocal canonicalTailRun
        rw [wordEq, initialEq, tailEq]
        exact (doubleWord_eq source handoff intermediate output guessPhase
          firstPhase secondPhase thirdPhase fourthPhase fifthPhase
          markerTwoPhase inputFirst).symm
      · rcases falseSurvivor with
          ⟨first, guess, _, QBelowGuess, guessBelowTwoQ, _, handoffSame⟩
        obtain ⟨handoffDigit, handoffMembership⟩ := falseHandoff_inPhaseAt
          (handoff := handoff) primeProperty QBelowGuess guessBelowTwoQ
        have canonicalTailLocal : AllStatesLocal prime (letter :: suffix)
            (phaseAffine handoff
              (falseHandoffState prime first guess 0)) :=
          boundaryLocal.of_sameLine (by omega) handoffMembership.local.1
            handoffSame
        have canonicalTailRun : SameLine
            (physicalWordAction prime (letter :: suffix)
              (phaseAffine handoff
                (falseHandoffState prime first guess 0))) endpoint :=
          (physicalWordAction_preserves_sameLine prime (letter :: suffix)
            handoffSame).trans tailRun
        exact False.elim
          (falseHandoff_full_union_rejects_doubleValidator primeProperty
            primeBound layout handoffBound intermediateBound outputBound
            handoffNotActive handoffIntermediateDistinct
            handoffOutputDistinct endpointMembership QBelowGuess
            guessBelowTwoQ tailOver canonicalTailLocal canonicalTailRun)
    · rw [sourceIntermediate] at boundaryMembership
      exact False.elim (coreWord_cannot_reach_foreign_phase primeProperty
        primeBound layout handoffBound intermediateBound handoffNotActive
        intermediateNotActive handoffIntermediateDistinct boundaryMembership
        initialOver initialLocal (SameLine.refl _))

/-- General positive-input converse for the twenty-letter double validated
front.  It derives the unique parameter and the input congruence. -/
theorem doubleWord_unique_general
    {prime phaseCount source handoff intermediate output guessPhase firstPhase
      secondPhase thirdPhase fourthPhase fifthPhase markerTwoPhase counter : Nat}
    {endpointDigit : Int} {endpoint : Vec2}
    (primeProperty : IsPrime prime) (primeBound : 6 * phaseCount < prime)
    (layout : FivefoldFrontModule.PhaseLayout phaseCount source guessPhase
      firstPhase secondPhase thirdPhase fourthPhase fifthPhase markerTwoPhase)
    (handoffBound : handoff < phaseCount)
    (intermediateBound : intermediate < phaseCount)
    (outputBound : output < phaseCount)
    (handoffNotActive : handoff ∉
      [source, guessPhase, firstPhase, secondPhase, thirdPhase, fourthPhase,
        fifthPhase, markerTwoPhase])
    (intermediateNotActive : intermediate ∉
      [source, guessPhase, firstPhase, secondPhase, thirdPhase, fourthPhase,
        fifthPhase, markerTwoPhase])
    (outputNotActive : output ∉
      [source, guessPhase, firstPhase, secondPhase, thirdPhase, fourthPhase,
        fifthPhase, markerTwoPhase])
    (handoffIntermediateDistinct : handoff ≠ intermediate)
    (handoffOutputDistinct : handoff ≠ output)
    (intermediateOutputDistinct : intermediate ≠ output)
    (endpointMembership : InPhaseAt prime output endpointDigit endpoint)
    (counterPositive : 0 < counter)
    {word : List PhysicalTemplate}
    (wordOver : WordOver
      (doubleAlphabet source handoff intermediate output guessPhase firstPhase
        secondPhase thirdPhase fourthPhase fifthPhase markerTwoPhase) word)
    (allLocal : AllStatesLocal prime word
      (phaseAffine source (unaryCode prime counter)))
    (completeRun : SameLine
      (physicalWordAction prime word
        (phaseAffine source (unaryCode prime counter))) endpoint) :
    ∃ first,
      counter = 5 * first + 4 ∧
      word = doubleWord source handoff intermediate output guessPhase
        firstPhase secondPhase thirdPhase fourthPhase fifthPhase markerTwoPhase
        first := by
  have unionOver : WordOver
      (FivefoldFrontModule.alphabet source handoff guessPhase firstPhase
          secondPhase thirdPhase fourthPhase fifthPhase markerTwoPhase ++
        doubleValidatorAlphabet handoff intermediate output) word := by
    simpa [doubleAlphabet_eq] using wordOver
  obtain ⟨sourceDigit, sourceMembership⟩ := unaryCode_inPhaseAt
    (base := prime) (phase := source) (counter := counter) primeProperty.1
  have sourceOutputDistinct : source ≠ output := by
    intro phaseEq
    apply outputNotActive
    simp [← phaseEq]
  have wordNonempty : word ≠ [] := by
    intro wordEmpty
    subst word
    have phaseEq := (sourceMembership.unique primeProperty primeBound
      layout.sourceBound outputBound endpointMembership (by
        simpa [physicalWordAction] using completeRun)).1
    exact sourceOutputDistinct phaseEq
  rcases wordOver_append_first_right unionOver with coreOnly |
      ⟨initial, letter, suffix, wordEq, initialOver, letterValidator,
        suffixOver⟩
  · exact False.elim
      (coreWord_cannot_reach_foreign_phase_general_of_nonempty primeProperty
        primeBound layout handoffBound outputBound handoffNotActive
        (by
          intro internalMem
          apply outputNotActive
          simp at internalMem ⊢
          grind)
        handoffOutputDistinct endpointMembership counterPositive coreOnly
        wordNonempty allLocal completeRun)
  · obtain ⟨initialLocal, boundaryLocal⟩ :=
      allLocal.split_append_cons wordEq
    have boundaryMembership : InPhaseAt prime letter.sourcePhase letter.digit
        (physicalWordAction prime initial
          (phaseAffine source (unaryCode prime counter))) := by
      apply physicalLetter_input_inPhaseAt primeProperty
        (doubleValidatorLetter_reserved letterValidator) boundaryLocal.1
      simpa [PhysicalTemplate.act, PhysicalTemplate.matrix] using
        boundaryLocal.2.start
    rcases doubleValidatorLetter_source letterValidator with
      sourceHandoff | sourceIntermediate
    · rw [sourceHandoff] at boundaryMembership
      have prefixClassification := corePrefix_to_handoff_classifies_general
        primeProperty primeBound layout handoffBound handoffNotActive
        boundaryMembership counterPositive initialOver initialLocal
        (SameLine.refl _)
      have tailOver : WordOver
          (FivefoldFrontModule.alphabet source handoff guessPhase firstPhase
              secondPhase thirdPhase fourthPhase fifthPhase markerTwoPhase ++
            doubleValidatorAlphabet handoff intermediate output)
          (letter :: suffix) := by
        intro candidate candidateMem
        simp only [List.mem_cons] at candidateMem
        rcases candidateMem with rfl | candidateMem
        · exact List.mem_append_right _ letterValidator
        · exact suffixOver candidate candidateMem
      have tailRun : SameLine
          (physicalWordAction prime (letter :: suffix)
            (physicalWordAction prime initial
              (phaseAffine source (unaryCode prime counter)))) endpoint := by
        rw [wordEq, physicalWordAction_append] at completeRun
        exact completeRun
      rcases prefixClassification with accepted | falseSurvivor
      · rcases accepted with ⟨first, counterEq, initialEq, handoffSame⟩
        obtain ⟨handoffDigit, handoffMembership⟩ :=
          acceptedHandoff_inPhaseAt (handoff := handoff) (first := first)
            primeProperty
        have canonicalTailLocal : AllStatesLocal prime (letter :: suffix)
            (phaseAffine handoff (acceptedHandoffState prime first)) :=
          boundaryLocal.of_sameLine (by omega) handoffMembership.local.1
            handoffSame
        have canonicalTailRun : SameLine
            (physicalWordAction prime (letter :: suffix)
              (phaseAffine handoff (acceptedHandoffState prime first)))
            endpoint :=
          (physicalWordAction_preserves_sameLine prime (letter :: suffix)
            handoffSame).trans tailRun
        have tailEq := acceptedHandoff_full_union_forces_doubleValidator
          primeProperty primeBound layout handoffBound intermediateBound
          outputBound handoffNotActive intermediateNotActive outputNotActive
          handoffIntermediateDistinct handoffOutputDistinct
          intermediateOutputDistinct endpointMembership tailOver
          canonicalTailLocal canonicalTailRun
        refine ⟨first, counterEq, ?_⟩
        rw [wordEq, initialEq, tailEq]
        exact (doubleWord_eq source handoff intermediate output guessPhase
          firstPhase secondPhase thirdPhase fourthPhase fifthPhase
          markerTwoPhase first).symm
      · rcases falseSurvivor with
          ⟨first, guess, _, QBelowGuess, guessBelowTwoQ, _, handoffSame⟩
        obtain ⟨handoffDigit, handoffMembership⟩ := falseHandoff_inPhaseAt
          (handoff := handoff) primeProperty QBelowGuess guessBelowTwoQ
        have canonicalTailLocal : AllStatesLocal prime (letter :: suffix)
            (phaseAffine handoff
              (falseHandoffState prime first guess 0)) :=
          boundaryLocal.of_sameLine (by omega) handoffMembership.local.1
            handoffSame
        have canonicalTailRun : SameLine
            (physicalWordAction prime (letter :: suffix)
              (phaseAffine handoff
                (falseHandoffState prime first guess 0))) endpoint :=
          (physicalWordAction_preserves_sameLine prime (letter :: suffix)
            handoffSame).trans tailRun
        exact False.elim
          (falseHandoff_full_union_rejects_doubleValidator primeProperty
            primeBound layout handoffBound intermediateBound outputBound
            handoffNotActive handoffIntermediateDistinct
            handoffOutputDistinct endpointMembership QBelowGuess
            guessBelowTwoQ tailOver canonicalTailLocal canonicalTailRun)
    · rw [sourceIntermediate] at boundaryMembership
      exact False.elim
        (coreWord_cannot_reach_foreign_phase_general_of_nonempty primeProperty
          primeBound layout handoffBound intermediateBound handoffNotActive
          (by
            intro internalMem
            apply intermediateNotActive
            simp at internalMem ⊢
            grind)
          handoffIntermediateDistinct boundaryMembership counterPositive
          initialOver (by
            intro initialEmpty
            subst initial
            have sourceIntermediateDistinct : source ≠ intermediate := by
              intro phaseEq
              apply intermediateNotActive
              simp [← phaseEq]
            obtain ⟨sourceDigit, sourceMembership⟩ := unaryCode_inPhaseAt
              (base := prime) (phase := source) (counter := counter)
              primeProperty.1
            have phaseEq := (sourceMembership.unique primeProperty primeBound
              layout.sourceBound intermediateBound boundaryMembership
              (SameLine.refl _)).1
            exact sourceIntermediateDistinct phaseEq)
          initialLocal (SameLine.refl _))

/-- The accepted handoff cannot reach a foreign guarded phase through the
complete core-plus-double-validator alphabet. -/
theorem acceptedHandoff_doubleFullUnion_cannot_reach_foreign_phase
    {prime phaseCount source handoff intermediate output guessPhase firstPhase
      secondPhase thirdPhase fourthPhase fifthPhase markerTwoPhase endpointPhase
      first : Nat}
    {endpointDigit : Int} {endpoint : Vec2}
    (primeProperty : IsPrime prime) (primeBound : 6 * phaseCount < prime)
    (layout : FivefoldFrontModule.PhaseLayout phaseCount source guessPhase
      firstPhase secondPhase thirdPhase fourthPhase fifthPhase markerTwoPhase)
    (handoffBound : handoff < phaseCount)
    (intermediateBound : intermediate < phaseCount)
    (outputBound : output < phaseCount)
    (endpointBound : endpointPhase < phaseCount)
    (handoffNotActive : handoff ∉
      [source, guessPhase, firstPhase, secondPhase, thirdPhase, fourthPhase,
        fifthPhase, markerTwoPhase])
    (intermediateNotActive : intermediate ∉
      [source, guessPhase, firstPhase, secondPhase, thirdPhase, fourthPhase,
        fifthPhase, markerTwoPhase])
    (outputNotActive : output ∉
      [source, guessPhase, firstPhase, secondPhase, thirdPhase, fourthPhase,
        fifthPhase, markerTwoPhase])
    (handoffIntermediateDistinct : handoff ≠ intermediate)
    (handoffOutputDistinct : handoff ≠ output)
    (intermediateOutputDistinct : intermediate ≠ output)
    (handoffEndpointDistinct : handoff ≠ endpointPhase)
    (intermediateEndpointDistinct : intermediate ≠ endpointPhase)
    (outputEndpointDistinct : output ≠ endpointPhase)
    (endpointMembership : InPhaseAt prime endpointPhase endpointDigit endpoint)
    {word : List PhysicalTemplate}
    (wordOver : WordOver
      (FivefoldFrontModule.alphabet source handoff guessPhase firstPhase
          secondPhase thirdPhase fourthPhase fifthPhase markerTwoPhase ++
        doubleValidatorAlphabet handoff intermediate output) word)
    (allLocal : AllStatesLocal prime word
      (phaseAffine handoff (acceptedHandoffState prime first)))
    (completeRun : SameLine
      (physicalWordAction prime word
        (phaseAffine handoff (acceptedHandoffState prime first))) endpoint) :
    False := by
  have reordered : WordOver
      (doubleValidatorAlphabet handoff intermediate output ++
        FivefoldFrontModule.alphabet source handoff guessPhase firstPhase
          secondPhase thirdPhase fourthPhase fifthPhase markerTwoPhase) word := by
    intro letter letterMem
    have membership := wordOver letter letterMem
    simp only [List.mem_append] at membership ⊢
    exact membership.symm
  rcases wordOver_append_first_right reordered with validatorOnly |
      ⟨initial, letter, suffix, wordEq, initialOver, letterCore, _⟩
  · exact acceptedHandoff_doubleValidator_cannot_reach_foreign_phase
      primeProperty primeBound handoffBound intermediateBound outputBound
      endpointBound handoffIntermediateDistinct handoffOutputDistinct
      intermediateOutputDistinct handoffEndpointDistinct
      intermediateEndpointDistinct outputEndpointDistinct endpointMembership
      validatorOnly allLocal completeRun
  · obtain ⟨initialLocal, boundaryLocal⟩ :=
      allLocal.split_append_cons wordEq
    have boundaryMembership : InPhaseAt prime letter.sourcePhase letter.digit
        (physicalWordAction prime initial
          (phaseAffine handoff (acceptedHandoffState prime first))) := by
      apply physicalLetter_input_inPhaseAt primeProperty
        (FivefoldFrontModule.letter_reserved letterCore) boundaryLocal.1
      simpa [PhysicalTemplate.act, PhysicalTemplate.matrix] using
        boundaryLocal.2.start
    exact acceptedHandoff_doubleValidator_cannot_reach_foreign_phase
      primeProperty primeBound handoffBound intermediateBound outputBound
      (FivefoldFrontModule.letter_source_bound layout letterCore)
      handoffIntermediateDistinct handoffOutputDistinct
      intermediateOutputDistinct
      (core_source_ne_foreign handoffNotActive letterCore).symm
      (core_source_ne_foreign intermediateNotActive letterCore).symm
      (core_source_ne_foreign outputNotActive letterCore).symm
      boundaryMembership initialOver initialLocal (SameLine.refl _)

/-- The false handoff cannot reach a foreign guarded phase through the
complete core-plus-double-validator alphabet. -/
theorem falseHandoff_doubleFullUnion_cannot_reach_foreign_phase
    {prime phaseCount source handoff intermediate output guessPhase firstPhase
      secondPhase thirdPhase fourthPhase fifthPhase markerTwoPhase endpointPhase
      first guess : Nat}
    {endpointDigit : Int} {endpoint : Vec2}
    (primeProperty : IsPrime prime) (primeBound : 6 * phaseCount < prime)
    (layout : FivefoldFrontModule.PhaseLayout phaseCount source guessPhase
      firstPhase secondPhase thirdPhase fourthPhase fifthPhase markerTwoPhase)
    (handoffBound : handoff < phaseCount)
    (intermediateBound : intermediate < phaseCount)
    (endpointBound : endpointPhase < phaseCount)
    (handoffNotActive : handoff ∉
      [source, guessPhase, firstPhase, secondPhase, thirdPhase, fourthPhase,
        fifthPhase, markerTwoPhase])
    (handoffIntermediateDistinct : handoff ≠ intermediate)
    (handoffEndpointDistinct : handoff ≠ endpointPhase)
    (endpointMembership : InPhaseAt prime endpointPhase endpointDigit endpoint)
    (QBelowGuess : first + 1 < guess)
    (guessBelowTwoQ : guess < 2 * (first + 1))
    {word : List PhysicalTemplate}
    (wordOver : WordOver
      (FivefoldFrontModule.alphabet source handoff guessPhase firstPhase
          secondPhase thirdPhase fourthPhase fifthPhase markerTwoPhase ++
        doubleValidatorAlphabet handoff intermediate output) word)
    (allLocal : AllStatesLocal prime word
      (phaseAffine handoff (falseHandoffState prime first guess 0)))
    (completeRun : SameLine
      (physicalWordAction prime word
        (phaseAffine handoff (falseHandoffState prime first guess 0)))
      endpoint) : False := by
  have reordered : WordOver
      (doubleValidatorAlphabet handoff intermediate output ++
        FivefoldFrontModule.alphabet source handoff guessPhase firstPhase
          secondPhase thirdPhase fourthPhase fifthPhase markerTwoPhase) word := by
    intro letter letterMem
    have membership := wordOver letter letterMem
    simp only [List.mem_append] at membership ⊢
    exact membership.symm
  rcases wordOver_append_first_right reordered with validatorOnly |
      ⟨initial, letter, suffix, wordEq, initialOver, letterCore, _⟩
  · exact falseHandoff_doubleValidator_cannot_reach_foreign_phase
      primeProperty primeBound handoffBound intermediateBound endpointBound
      handoffIntermediateDistinct handoffEndpointDistinct endpointMembership
      QBelowGuess guessBelowTwoQ validatorOnly allLocal completeRun
  · obtain ⟨initialLocal, boundaryLocal⟩ :=
      allLocal.split_append_cons wordEq
    have boundaryMembership : InPhaseAt prime letter.sourcePhase letter.digit
        (physicalWordAction prime initial
          (phaseAffine handoff (falseHandoffState prime first guess 0))) := by
      apply physicalLetter_input_inPhaseAt primeProperty
        (FivefoldFrontModule.letter_reserved letterCore) boundaryLocal.1
      simpa [PhysicalTemplate.act, PhysicalTemplate.matrix] using
        boundaryLocal.2.start
    exact falseHandoff_doubleValidator_cannot_reach_foreign_phase
      primeProperty primeBound handoffBound intermediateBound
      (FivefoldFrontModule.letter_source_bound layout letterCore)
      handoffIntermediateDistinct
      (core_source_ne_foreign handoffNotActive letterCore).symm
      boundaryMembership QBelowGuess guessBelowTwoQ initialOver initialLocal
      (SameLine.refl _)

/-- A nonempty word over the complete twenty-letter front cannot stop in a
guarded phase foreign to its internal controls and declared output.  The
endpoint may equal the source boundary. -/
theorem doubleWord_cannot_reach_foreign_phase_of_nonempty
    {prime phaseCount source handoff intermediate output guessPhase firstPhase
      secondPhase thirdPhase fourthPhase fifthPhase markerTwoPhase endpointPhase
      inputFirst : Nat}
    {endpointDigit : Int} {endpoint : Vec2}
    (primeProperty : IsPrime prime) (primeBound : 6 * phaseCount < prime)
    (layout : FivefoldFrontModule.PhaseLayout phaseCount source guessPhase
      firstPhase secondPhase thirdPhase fourthPhase fifthPhase markerTwoPhase)
    (handoffBound : handoff < phaseCount)
    (intermediateBound : intermediate < phaseCount)
    (outputBound : output < phaseCount)
    (endpointBound : endpointPhase < phaseCount)
    (handoffNotActive : handoff ∉
      [source, guessPhase, firstPhase, secondPhase, thirdPhase, fourthPhase,
        fifthPhase, markerTwoPhase])
    (intermediateNotActive : intermediate ∉
      [source, guessPhase, firstPhase, secondPhase, thirdPhase, fourthPhase,
        fifthPhase, markerTwoPhase])
    (outputNotActive : output ∉
      [source, guessPhase, firstPhase, secondPhase, thirdPhase, fourthPhase,
        fifthPhase, markerTwoPhase])
    (endpointNotInternal : endpointPhase ∉
      [guessPhase, firstPhase, secondPhase, thirdPhase, fourthPhase,
        fifthPhase, markerTwoPhase])
    (handoffIntermediateDistinct : handoff ≠ intermediate)
    (handoffOutputDistinct : handoff ≠ output)
    (intermediateOutputDistinct : intermediate ≠ output)
    (handoffEndpointDistinct : handoff ≠ endpointPhase)
    (intermediateEndpointDistinct : intermediate ≠ endpointPhase)
    (outputEndpointDistinct : output ≠ endpointPhase)
    (endpointMembership : InPhaseAt prime endpointPhase endpointDigit endpoint)
    {word : List PhysicalTemplate}
    (wordOver : WordOver
      (doubleAlphabet source handoff intermediate output guessPhase firstPhase
        secondPhase thirdPhase fourthPhase fifthPhase markerTwoPhase) word)
    (wordNonempty : word ≠ [])
    (allLocal : AllStatesLocal prime word
      (phaseAffine source (unaryCode prime (5 * inputFirst + 4))))
    (completeRun : SameLine
      (physicalWordAction prime word
        (phaseAffine source (unaryCode prime (5 * inputFirst + 4))))
      endpoint) : False := by
  have unionOver : WordOver
      (FivefoldFrontModule.alphabet source handoff guessPhase firstPhase
          secondPhase thirdPhase fourthPhase fifthPhase markerTwoPhase ++
        doubleValidatorAlphabet handoff intermediate output) word := by
    simpa [doubleAlphabet_eq] using wordOver
  rcases wordOver_append_first_right unionOver with coreOnly |
      ⟨initial, letter, suffix, wordEq, initialOver, letterValidator,
        suffixOver⟩
  · exact coreWord_cannot_reach_foreign_phase_of_nonempty primeProperty
      primeBound layout handoffBound endpointBound handoffNotActive
      endpointNotInternal handoffEndpointDistinct endpointMembership coreOnly
      wordNonempty allLocal completeRun
  · obtain ⟨initialLocal, boundaryLocal⟩ :=
      allLocal.split_append_cons wordEq
    have boundaryMembership : InPhaseAt prime letter.sourcePhase letter.digit
        (physicalWordAction prime initial
          (phaseAffine source (unaryCode prime (5 * inputFirst + 4)))) := by
      apply physicalLetter_input_inPhaseAt primeProperty
        (doubleValidatorLetter_reserved letterValidator) boundaryLocal.1
      simpa [PhysicalTemplate.act, PhysicalTemplate.matrix] using
        boundaryLocal.2.start
    rcases doubleValidatorLetter_source letterValidator with
      sourceHandoff | sourceIntermediate
    · rw [sourceHandoff] at boundaryMembership
      have prefixClassification := corePrefix_to_handoff_classifies
        primeProperty primeBound layout handoffBound handoffNotActive
        boundaryMembership initialOver initialLocal (SameLine.refl _)
      have tailOver : WordOver
          (FivefoldFrontModule.alphabet source handoff guessPhase firstPhase
              secondPhase thirdPhase fourthPhase fifthPhase markerTwoPhase ++
            doubleValidatorAlphabet handoff intermediate output)
          (letter :: suffix) := by
        intro candidate candidateMem
        simp only [List.mem_cons] at candidateMem
        rcases candidateMem with rfl | candidateMem
        · exact List.mem_append_right _ letterValidator
        · exact suffixOver candidate candidateMem
      have tailRun : SameLine
          (physicalWordAction prime (letter :: suffix)
            (physicalWordAction prime initial
              (phaseAffine source (unaryCode prime (5 * inputFirst + 4)))))
          endpoint := by
        rw [wordEq, physicalWordAction_append] at completeRun
        exact completeRun
      rcases prefixClassification with accepted | falseSurvivor
      · rcases accepted with ⟨_, handoffSame⟩
        obtain ⟨handoffDigit, handoffMembership⟩ :=
          acceptedHandoff_inPhaseAt (handoff := handoff)
            (first := inputFirst) primeProperty
        have canonicalTailLocal : AllStatesLocal prime (letter :: suffix)
            (phaseAffine handoff
              (acceptedHandoffState prime inputFirst)) :=
          boundaryLocal.of_sameLine (by omega) handoffMembership.local.1
            handoffSame
        have canonicalTailRun : SameLine
            (physicalWordAction prime (letter :: suffix)
              (phaseAffine handoff
                (acceptedHandoffState prime inputFirst))) endpoint :=
          (physicalWordAction_preserves_sameLine prime (letter :: suffix)
            handoffSame).trans tailRun
        exact acceptedHandoff_doubleFullUnion_cannot_reach_foreign_phase
          primeProperty primeBound layout handoffBound intermediateBound
          outputBound endpointBound handoffNotActive intermediateNotActive
          outputNotActive handoffIntermediateDistinct handoffOutputDistinct
          intermediateOutputDistinct handoffEndpointDistinct
          intermediateEndpointDistinct outputEndpointDistinct
          endpointMembership tailOver canonicalTailLocal canonicalTailRun
      · rcases falseSurvivor with
          ⟨first, guess, _, QBelowGuess, guessBelowTwoQ, _, handoffSame⟩
        obtain ⟨handoffDigit, handoffMembership⟩ := falseHandoff_inPhaseAt
          (handoff := handoff) primeProperty QBelowGuess guessBelowTwoQ
        have canonicalTailLocal : AllStatesLocal prime (letter :: suffix)
            (phaseAffine handoff
              (falseHandoffState prime first guess 0)) :=
          boundaryLocal.of_sameLine (by omega) handoffMembership.local.1
            handoffSame
        have canonicalTailRun : SameLine
            (physicalWordAction prime (letter :: suffix)
              (phaseAffine handoff
                (falseHandoffState prime first guess 0))) endpoint :=
          (physicalWordAction_preserves_sameLine prime (letter :: suffix)
            handoffSame).trans tailRun
        exact falseHandoff_doubleFullUnion_cannot_reach_foreign_phase
          primeProperty primeBound layout handoffBound intermediateBound
          endpointBound handoffNotActive handoffIntermediateDistinct
          handoffEndpointDistinct endpointMembership QBelowGuess
          guessBelowTwoQ tailOver canonicalTailLocal canonicalTailRun
    · rw [sourceIntermediate] at boundaryMembership
      exact coreWord_cannot_reach_foreign_phase primeProperty primeBound
        layout handoffBound intermediateBound handoffNotActive
        intermediateNotActive handoffIntermediateDistinct boundaryMembership
        initialOver initialLocal (SameLine.refl _)

/-- General positive-input version of
`doubleWord_cannot_reach_foreign_phase_of_nonempty`. -/
theorem doubleWord_cannot_reach_foreign_phase_general_of_nonempty
    {prime phaseCount source handoff intermediate output guessPhase firstPhase
      secondPhase thirdPhase fourthPhase fifthPhase markerTwoPhase endpointPhase
      counter : Nat}
    {endpointDigit : Int} {endpoint : Vec2}
    (primeProperty : IsPrime prime) (primeBound : 6 * phaseCount < prime)
    (layout : FivefoldFrontModule.PhaseLayout phaseCount source guessPhase
      firstPhase secondPhase thirdPhase fourthPhase fifthPhase markerTwoPhase)
    (handoffBound : handoff < phaseCount)
    (intermediateBound : intermediate < phaseCount)
    (outputBound : output < phaseCount)
    (endpointBound : endpointPhase < phaseCount)
    (handoffNotActive : handoff ∉
      [source, guessPhase, firstPhase, secondPhase, thirdPhase, fourthPhase,
        fifthPhase, markerTwoPhase])
    (intermediateNotActive : intermediate ∉
      [source, guessPhase, firstPhase, secondPhase, thirdPhase, fourthPhase,
        fifthPhase, markerTwoPhase])
    (outputNotActive : output ∉
      [source, guessPhase, firstPhase, secondPhase, thirdPhase, fourthPhase,
        fifthPhase, markerTwoPhase])
    (endpointNotInternal : endpointPhase ∉
      [guessPhase, firstPhase, secondPhase, thirdPhase, fourthPhase,
        fifthPhase, markerTwoPhase])
    (handoffIntermediateDistinct : handoff ≠ intermediate)
    (handoffOutputDistinct : handoff ≠ output)
    (intermediateOutputDistinct : intermediate ≠ output)
    (handoffEndpointDistinct : handoff ≠ endpointPhase)
    (intermediateEndpointDistinct : intermediate ≠ endpointPhase)
    (outputEndpointDistinct : output ≠ endpointPhase)
    (endpointMembership : InPhaseAt prime endpointPhase endpointDigit endpoint)
    (counterPositive : 0 < counter)
    {word : List PhysicalTemplate}
    (wordOver : WordOver
      (doubleAlphabet source handoff intermediate output guessPhase firstPhase
        secondPhase thirdPhase fourthPhase fifthPhase markerTwoPhase) word)
    (wordNonempty : word ≠ [])
    (allLocal : AllStatesLocal prime word
      (phaseAffine source (unaryCode prime counter)))
    (completeRun : SameLine
      (physicalWordAction prime word
        (phaseAffine source (unaryCode prime counter))) endpoint) : False := by
  have unionOver : WordOver
      (FivefoldFrontModule.alphabet source handoff guessPhase firstPhase
          secondPhase thirdPhase fourthPhase fifthPhase markerTwoPhase ++
        doubleValidatorAlphabet handoff intermediate output) word := by
    simpa [doubleAlphabet_eq] using wordOver
  rcases wordOver_append_first_right unionOver with coreOnly |
      ⟨initial, letter, suffix, wordEq, initialOver, letterValidator,
        suffixOver⟩
  · exact coreWord_cannot_reach_foreign_phase_general_of_nonempty
      primeProperty primeBound layout handoffBound endpointBound
      handoffNotActive endpointNotInternal handoffEndpointDistinct
      endpointMembership counterPositive coreOnly wordNonempty allLocal
      completeRun
  · obtain ⟨initialLocal, boundaryLocal⟩ :=
      allLocal.split_append_cons wordEq
    have boundaryMembership : InPhaseAt prime letter.sourcePhase letter.digit
        (physicalWordAction prime initial
          (phaseAffine source (unaryCode prime counter))) := by
      apply physicalLetter_input_inPhaseAt primeProperty
        (doubleValidatorLetter_reserved letterValidator) boundaryLocal.1
      simpa [PhysicalTemplate.act, PhysicalTemplate.matrix] using
        boundaryLocal.2.start
    rcases doubleValidatorLetter_source letterValidator with
      sourceHandoff | sourceIntermediate
    · rw [sourceHandoff] at boundaryMembership
      have prefixClassification := corePrefix_to_handoff_classifies_general
        primeProperty primeBound layout handoffBound handoffNotActive
        boundaryMembership counterPositive initialOver initialLocal
        (SameLine.refl _)
      have tailOver : WordOver
          (FivefoldFrontModule.alphabet source handoff guessPhase firstPhase
              secondPhase thirdPhase fourthPhase fifthPhase markerTwoPhase ++
            doubleValidatorAlphabet handoff intermediate output)
          (letter :: suffix) := by
        intro candidate candidateMem
        simp only [List.mem_cons] at candidateMem
        rcases candidateMem with rfl | candidateMem
        · exact List.mem_append_right _ letterValidator
        · exact suffixOver candidate candidateMem
      have tailRun : SameLine
          (physicalWordAction prime (letter :: suffix)
            (physicalWordAction prime initial
              (phaseAffine source (unaryCode prime counter)))) endpoint := by
        rw [wordEq, physicalWordAction_append] at completeRun
        exact completeRun
      rcases prefixClassification with accepted | falseSurvivor
      · rcases accepted with ⟨first, _, _, handoffSame⟩
        obtain ⟨handoffDigit, handoffMembership⟩ :=
          acceptedHandoff_inPhaseAt (handoff := handoff) (first := first)
            primeProperty
        have canonicalTailLocal : AllStatesLocal prime (letter :: suffix)
            (phaseAffine handoff (acceptedHandoffState prime first)) :=
          boundaryLocal.of_sameLine (by omega) handoffMembership.local.1
            handoffSame
        have canonicalTailRun : SameLine
            (physicalWordAction prime (letter :: suffix)
              (phaseAffine handoff (acceptedHandoffState prime first)))
            endpoint :=
          (physicalWordAction_preserves_sameLine prime (letter :: suffix)
            handoffSame).trans tailRun
        exact acceptedHandoff_doubleFullUnion_cannot_reach_foreign_phase
          primeProperty primeBound layout handoffBound intermediateBound
          outputBound endpointBound handoffNotActive intermediateNotActive
          outputNotActive handoffIntermediateDistinct handoffOutputDistinct
          intermediateOutputDistinct handoffEndpointDistinct
          intermediateEndpointDistinct outputEndpointDistinct
          endpointMembership tailOver canonicalTailLocal canonicalTailRun
      · rcases falseSurvivor with
          ⟨first, guess, _, QBelowGuess, guessBelowTwoQ, _, handoffSame⟩
        obtain ⟨handoffDigit, handoffMembership⟩ := falseHandoff_inPhaseAt
          (handoff := handoff) primeProperty QBelowGuess guessBelowTwoQ
        have canonicalTailLocal : AllStatesLocal prime (letter :: suffix)
            (phaseAffine handoff
              (falseHandoffState prime first guess 0)) :=
          boundaryLocal.of_sameLine (by omega) handoffMembership.local.1
            handoffSame
        have canonicalTailRun : SameLine
            (physicalWordAction prime (letter :: suffix)
              (phaseAffine handoff
                (falseHandoffState prime first guess 0))) endpoint :=
          (physicalWordAction_preserves_sameLine prime (letter :: suffix)
            handoffSame).trans tailRun
        exact falseHandoff_doubleFullUnion_cannot_reach_foreign_phase
          primeProperty primeBound layout handoffBound intermediateBound
          endpointBound handoffNotActive handoffIntermediateDistinct
          handoffEndpointDistinct endpointMembership QBelowGuess
          guessBelowTwoQ tailOver canonicalTailLocal canonicalTailRun
    · rw [sourceIntermediate] at boundaryMembership
      have sourceIntermediateDistinct : source ≠ intermediate := by
        intro phaseEq
        apply intermediateNotActive
        simp [← phaseEq]
      obtain ⟨sourceDigit, sourceMembership⟩ := unaryCode_inPhaseAt
        (base := prime) (phase := source) (counter := counter) primeProperty.1
      have initialNonempty : initial ≠ [] := by
        intro initialEmpty
        subst initial
        have phaseEq := (sourceMembership.unique primeProperty primeBound
          layout.sourceBound intermediateBound boundaryMembership
          (SameLine.refl _)).1
        exact sourceIntermediateDistinct phaseEq
      exact coreWord_cannot_reach_foreign_phase_general_of_nonempty
        primeProperty primeBound layout handoffBound intermediateBound
        handoffNotActive
        (by
          intro internalMem
          apply intermediateNotActive
          simp at internalMem ⊢
          grind)
        handoffIntermediateDistinct boundaryMembership counterPositive
        initialOver initialNonempty initialLocal (SameLine.refl _)

/-- A word over the complete twenty-letter front cannot stop in a guarded
phase foreign to all front controls and its declared output. -/
theorem doubleWord_cannot_reach_foreign_phase
    {prime phaseCount source handoff intermediate output guessPhase firstPhase
      secondPhase thirdPhase fourthPhase fifthPhase markerTwoPhase endpointPhase
      inputFirst : Nat}
    {endpointDigit : Int} {endpoint : Vec2}
    (primeProperty : IsPrime prime) (primeBound : 6 * phaseCount < prime)
    (layout : FivefoldFrontModule.PhaseLayout phaseCount source guessPhase
      firstPhase secondPhase thirdPhase fourthPhase fifthPhase markerTwoPhase)
    (handoffBound : handoff < phaseCount)
    (intermediateBound : intermediate < phaseCount)
    (outputBound : output < phaseCount)
    (endpointBound : endpointPhase < phaseCount)
    (handoffNotActive : handoff ∉
      [source, guessPhase, firstPhase, secondPhase, thirdPhase, fourthPhase,
        fifthPhase, markerTwoPhase])
    (intermediateNotActive : intermediate ∉
      [source, guessPhase, firstPhase, secondPhase, thirdPhase, fourthPhase,
        fifthPhase, markerTwoPhase])
    (outputNotActive : output ∉
      [source, guessPhase, firstPhase, secondPhase, thirdPhase, fourthPhase,
        fifthPhase, markerTwoPhase])
    (endpointNotActive : endpointPhase ∉
      [source, guessPhase, firstPhase, secondPhase, thirdPhase, fourthPhase,
        fifthPhase, markerTwoPhase])
    (handoffIntermediateDistinct : handoff ≠ intermediate)
    (handoffOutputDistinct : handoff ≠ output)
    (intermediateOutputDistinct : intermediate ≠ output)
    (handoffEndpointDistinct : handoff ≠ endpointPhase)
    (intermediateEndpointDistinct : intermediate ≠ endpointPhase)
    (outputEndpointDistinct : output ≠ endpointPhase)
    (endpointMembership : InPhaseAt prime endpointPhase endpointDigit endpoint)
    {word : List PhysicalTemplate}
    (wordOver : WordOver
      (doubleAlphabet source handoff intermediate output guessPhase firstPhase
        secondPhase thirdPhase fourthPhase fifthPhase markerTwoPhase) word)
    (allLocal : AllStatesLocal prime word
      (phaseAffine source (unaryCode prime (5 * inputFirst + 4))))
    (completeRun : SameLine
      (physicalWordAction prime word
        (phaseAffine source (unaryCode prime (5 * inputFirst + 4))))
      endpoint) : False := by
  have sourceEndpointDistinct : source ≠ endpointPhase := by
    intro phaseEq
    apply endpointNotActive
    simp [phaseEq]
  obtain ⟨sourceDigit, sourceMembership⟩ := unaryCode_inPhaseAt
    (base := prime) (phase := source) (counter := 5 * inputFirst + 4)
    primeProperty.1
  have wordNonempty : word ≠ [] := by
    intro wordEmpty
    subst word
    have phaseEq := (sourceMembership.unique primeProperty primeBound
      layout.sourceBound endpointBound endpointMembership (by
        simpa [physicalWordAction] using completeRun)).1
    exact sourceEndpointDistinct phaseEq
  apply doubleWord_cannot_reach_foreign_phase_of_nonempty primeProperty
    primeBound layout handoffBound intermediateBound outputBound endpointBound
    handoffNotActive intermediateNotActive outputNotActive
  · intro internalMem
    apply endpointNotActive
    simp at internalMem ⊢
    grind
  · exact handoffIntermediateDistinct
  · exact handoffOutputDistinct
  · exact intermediateOutputDistinct
  · exact handoffEndpointDistinct
  · exact intermediateEndpointDistinct
  · exact outputEndpointDistinct
  · exact endpointMembership
  · exact wordOver
  · exact wordNonempty
  · exact allLocal
  · exact completeRun

end Mortality.Compiler.ValidatedFivefoldFrontModule
