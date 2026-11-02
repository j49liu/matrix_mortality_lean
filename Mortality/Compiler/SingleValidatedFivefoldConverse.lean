import Mortality.Compiler.ValidatedFivefoldFrontModule

/-!
# Unrestricted-word converse for the eighteen-letter validated front

This file proves the composition theorem that is invisible at the level of
the two component alphabets: a locally surviving word over their union must
cross from the sixteen-letter fivefold core to the two-letter subtraction
validator at the unique intended boundary.
-/

namespace Mortality.Compiler.ValidatedFivefoldFrontModule

open Mortality.Compiler
open Mortality.PeriodicCode
open Mortality.Compiler.UnaryArithmetic
open Mortality.Compiler.RightSubtractionModule
open Mortality.Compiler.FivefoldFrontClassification
open Mortality.Compiler.FivefoldFrontModule

private theorem active_ne_endpoint
    {source guessPhase firstPhase secondPhase thirdPhase fourthPhase fifthPhase
      markerTwoPhase endpointPhase : Nat}
    (endpointNotActive : endpointPhase ∉
      [source, guessPhase, firstPhase, secondPhase, thirdPhase, fourthPhase,
        fifthPhase, markerTwoPhase])
    {phase : Nat}
    (phaseActive : phase ∈
      [source, guessPhase, firstPhase, secondPhase, thirdPhase, fourthPhase,
        fifthPhase, markerTwoPhase]) :
    phase ≠ endpointPhase := by
  intro phaseEq
  apply endpointNotActive
  simpa [phaseEq] using phaseActive

private theorem core_letter_source_ne_endpoint
    {source handoff guessPhase firstPhase secondPhase thirdPhase fourthPhase
      fifthPhase markerTwoPhase endpointPhase : Nat}
    (endpointNotActive : endpointPhase ∉
      [source, guessPhase, firstPhase, secondPhase, thirdPhase, fourthPhase,
        fifthPhase, markerTwoPhase])
    {letter : PhysicalTemplate}
    (letterMem : letter ∈ FivefoldFrontModule.alphabet source handoff
      guessPhase firstPhase secondPhase thirdPhase fourthPhase fifthPhase
      markerTwoPhase) :
    letter.sourcePhase ≠ endpointPhase :=
  active_ne_endpoint endpointNotActive
    (FivefoldFrontModule.letter_source_mem_active letterMem)

/-- The first digit of a two-field code is zero unless the first zero block
is empty, in which case it is the separating marker one. -/
theorem twoFieldCode_inPhaseAt
    {prime phase first second : Nat} (primeProperty : IsPrime prime) :
    ∃ digit, InPhaseAt prime phase digit
      (phaseAffine phase (twoFieldCode prime first second)) := by
  cases first with
  | zero =>
      refine ⟨1, ?_⟩
      simpa [twoFieldCode, twoFieldDigits] using
        (periodicCode_inPhaseAt prime phase 1
          (List.replicate second 0 ++ [-1]) primeProperty.1
          (by simp [ReservedDigit]))
  | succ first =>
      refine ⟨0, ?_⟩
      simpa [twoFieldCode, twoFieldDigits, List.replicate_succ,
        List.append_assoc] using
        (periodicCode_inPhaseAt prime phase 0
          (List.replicate first 0 ++
            1 :: (List.replicate second 0 ++ [-1]))
          primeProperty.1 (by simp [ReservedDigit]))

def singleSourcePhases (source handoff guessPhase firstPhase secondPhase
    thirdPhase fourthPhase fifthPhase markerTwoPhase : Nat) : List Nat :=
  [source, guessPhase, firstPhase, secondPhase, thirdPhase, fourthPhase,
    fifthPhase, markerTwoPhase, handoff]

theorem singleLetter_source_mem
    {source handoff output guessPhase firstPhase secondPhase thirdPhase
      fourthPhase fifthPhase markerTwoPhase : Nat} {letter : PhysicalTemplate}
    (letterMem : letter ∈ singleAlphabet source handoff output guessPhase
      firstPhase secondPhase thirdPhase fourthPhase fifthPhase markerTwoPhase) :
    letter.sourcePhase ∈ singleSourcePhases source handoff guessPhase
      firstPhase secondPhase thirdPhase fourthPhase fifthPhase markerTwoPhase := by
  simp only [singleAlphabet, List.mem_append] at letterMem
  rcases letterMem with coreMem | subtractionMem
  · have active := FivefoldFrontModule.letter_source_mem_active coreMem
    simp [singleSourcePhases] at active ⊢
    grind
  · simp [subtractionAlphabet] at subtractionMem
    rcases subtractionMem with rfl | rfl <;>
      simp [singleSourcePhases, zeroLoop, markerExit]

theorem singleLetter_source_bound
    {phaseCount source handoff output guessPhase firstPhase secondPhase
      thirdPhase fourthPhase fifthPhase markerTwoPhase : Nat}
    (layout : FivefoldFrontModule.PhaseLayout phaseCount source guessPhase
      firstPhase secondPhase thirdPhase fourthPhase fifthPhase markerTwoPhase)
    (handoffBound : handoff < phaseCount)
    {letter : PhysicalTemplate}
    (letterMem : letter ∈ singleAlphabet source handoff output guessPhase
      firstPhase secondPhase thirdPhase fourthPhase fifthPhase markerTwoPhase) :
    letter.sourcePhase < phaseCount := by
  simp only [singleAlphabet, List.mem_append] at letterMem
  rcases letterMem with coreMem | subtractionMem
  · exact FivefoldFrontModule.letter_source_bound layout coreMem
  · exact subtractionLetter_source_bound handoffBound subtractionMem

theorem singleLetter_reserved
    {source handoff output guessPhase firstPhase secondPhase thirdPhase
      fourthPhase fifthPhase markerTwoPhase : Nat} {letter : PhysicalTemplate}
    (letterMem : letter ∈ singleAlphabet source handoff output guessPhase
      firstPhase secondPhase thirdPhase fourthPhase fifthPhase markerTwoPhase) :
    ReservedDigit letter.digit := by
  simp only [singleAlphabet, List.mem_append] at letterMem
  rcases letterMem with coreMem | subtractionMem
  · exact FivefoldFrontModule.letter_reserved coreMem
  · exact subtractionLetter_reserved subtractionMem

/-- A completed core-only word cannot end in a foreign guarded phase.  The
core parser first reaches its handoff, after which no core letter can move.
Phase uniqueness then separates that handoff from the requested endpoint. -/
theorem coreWord_cannot_reach_foreign_phase
    {prime phaseCount source handoff guessPhase firstPhase secondPhase
      thirdPhase fourthPhase fifthPhase markerTwoPhase endpointPhase inputFirst :
      Nat}
    {endpointDigit : Int} {endpoint : Vec2}
    (primeProperty : IsPrime prime) (primeBound : 6 * phaseCount < prime)
    (layout : FivefoldFrontModule.PhaseLayout phaseCount source guessPhase
      firstPhase secondPhase thirdPhase fourthPhase fifthPhase markerTwoPhase)
    (handoffBound : handoff < phaseCount)
    (endpointBound : endpointPhase < phaseCount)
    (handoffNotActive : handoff ∉
      [source, guessPhase, firstPhase, secondPhase, thirdPhase, fourthPhase,
        fifthPhase, markerTwoPhase])
    (endpointNotActive : endpointPhase ∉
      [source, guessPhase, firstPhase, secondPhase, thirdPhase, fourthPhase,
        fifthPhase, markerTwoPhase])
    (handoffEndpointDistinct : handoff ≠ endpointPhase)
    (endpointMembership : InPhaseAt prime endpointPhase endpointDigit endpoint)
    {word : List PhysicalTemplate}
    (wordOver : WordOver
      (FivefoldFrontModule.alphabet source handoff guessPhase firstPhase
        secondPhase thirdPhase fourthPhase fifthPhase markerTwoPhase) word)
    (allLocal : AllStatesLocal prime word
      (phaseAffine source (unaryCode prime (5 * inputFirst + 4))))
    (completeRun : SameLine
      (physicalWordAction prime word
        (phaseAffine source (unaryCode prime (5 * inputFirst + 4))))
      endpoint) : False := by
  obtain ⟨suffix, accepted | falseSurvivor⟩ :=
    FivefoldFrontModule.completedPath_classifies primeProperty primeBound
      layout endpointBound
      (active_ne_endpoint endpointNotActive (by simp))
      (active_ne_endpoint endpointNotActive (by simp))
      (active_ne_endpoint endpointNotActive (by simp))
      (active_ne_endpoint endpointNotActive (by simp))
      (active_ne_endpoint endpointNotActive (by simp))
      (active_ne_endpoint endpointNotActive (by simp))
      (active_ne_endpoint endpointNotActive (by simp))
      (active_ne_endpoint endpointNotActive (by simp))
      endpointMembership wordOver allLocal completeRun
  · rcases accepted with ⟨_, suffixOver, suffixLocal, suffixRun⟩
    obtain ⟨digit, handoffMembership⟩ :=
      acceptedHandoff_inPhaseAt (handoff := handoff) (first := inputFirst)
        primeProperty
    have suffixEq := FivefoldFrontModule.core_word_from_target_eq_nil
      primeProperty primeBound layout handoffBound handoffNotActive
      handoffMembership suffixOver suffixLocal
    subst suffix
    have phaseEq := (handoffMembership.unique primeProperty primeBound
      handoffBound endpointBound endpointMembership (by
        simpa [physicalWordAction] using suffixRun)).1
    exact handoffEndpointDistinct phaseEq
  · rcases falseSurvivor with
      ⟨first, guess, _, QBelowGuess, guessBelowTwoQ, _, suffixOver,
        suffixLocal, suffixRun⟩
    obtain ⟨digit, handoffMembership⟩ := falseHandoff_inPhaseAt
      (handoff := handoff) primeProperty QBelowGuess guessBelowTwoQ
    have suffixEq := FivefoldFrontModule.core_word_from_target_eq_nil
      primeProperty primeBound layout handoffBound handoffNotActive
      handoffMembership suffixOver suffixLocal
    subst suffix
    have phaseEq := (handoffMembership.unique primeProperty primeBound
      handoffBound endpointBound endpointMembership (by
        simpa [physicalWordAction] using suffixRun)).1
    exact handoffEndpointDistinct phaseEq

/-- Nonempty variant of `coreWord_cannot_reach_foreign_phase`.  It allows
the guarded endpoint to equal the core source, since the first core letter
leaves the source immediately. -/
theorem coreWord_cannot_reach_foreign_phase_of_nonempty
    {prime phaseCount source handoff guessPhase firstPhase secondPhase
      thirdPhase fourthPhase fifthPhase markerTwoPhase endpointPhase inputFirst :
      Nat}
    {endpointDigit : Int} {endpoint : Vec2}
    (primeProperty : IsPrime prime) (primeBound : 6 * phaseCount < prime)
    (layout : FivefoldFrontModule.PhaseLayout phaseCount source guessPhase
      firstPhase secondPhase thirdPhase fourthPhase fifthPhase markerTwoPhase)
    (handoffBound : handoff < phaseCount)
    (endpointBound : endpointPhase < phaseCount)
    (handoffNotActive : handoff ∉
      [source, guessPhase, firstPhase, secondPhase, thirdPhase, fourthPhase,
        fifthPhase, markerTwoPhase])
    (endpointNotInternal : endpointPhase ∉
      [guessPhase, firstPhase, secondPhase, thirdPhase, fourthPhase,
        fifthPhase, markerTwoPhase])
    (handoffEndpointDistinct : handoff ≠ endpointPhase)
    (endpointMembership : InPhaseAt prime endpointPhase endpointDigit endpoint)
    {word : List PhysicalTemplate}
    (wordOver : WordOver
      (FivefoldFrontModule.alphabet source handoff guessPhase firstPhase
        secondPhase thirdPhase fourthPhase fifthPhase markerTwoPhase) word)
    (wordNonempty : word ≠ [])
    (allLocal : AllStatesLocal prime word
      (phaseAffine source (unaryCode prime (5 * inputFirst + 4))))
    (completeRun : SameLine
      (physicalWordAction prime word
        (phaseAffine source (unaryCode prime (5 * inputFirst + 4))))
      endpoint) : False := by
  have internal_ne {phase : Nat}
      (phaseMem : phase ∈ [guessPhase, firstPhase, secondPhase, thirdPhase,
        fourthPhase, fifthPhase, markerTwoPhase]) :
      phase ≠ endpointPhase := by
    intro phaseEq
    apply endpointNotInternal
    simpa [phaseEq] using phaseMem
  obtain ⟨suffix, accepted | falseSurvivor⟩ :=
    FivefoldFrontModule.completedPath_classifies_of_nonempty primeProperty
      primeBound layout endpointBound
      (internal_ne (by simp)) (internal_ne (by simp))
      (internal_ne (by simp)) (internal_ne (by simp))
      (internal_ne (by simp)) (internal_ne (by simp))
      (internal_ne (by simp)) endpointMembership wordOver wordNonempty allLocal
      completeRun
  · rcases accepted with ⟨_, suffixOver, suffixLocal, suffixRun⟩
    obtain ⟨digit, handoffMembership⟩ :=
      acceptedHandoff_inPhaseAt (handoff := handoff) (first := inputFirst)
        primeProperty
    have suffixEq := FivefoldFrontModule.core_word_from_target_eq_nil
      primeProperty primeBound layout handoffBound handoffNotActive
      handoffMembership suffixOver suffixLocal
    subst suffix
    have phaseEq := (handoffMembership.unique primeProperty primeBound
      handoffBound endpointBound endpointMembership (by
        simpa [physicalWordAction] using suffixRun)).1
    exact handoffEndpointDistinct phaseEq
  · rcases falseSurvivor with
      ⟨first, guess, _, QBelowGuess, guessBelowTwoQ, _, suffixOver,
        suffixLocal, suffixRun⟩
    obtain ⟨digit, handoffMembership⟩ := falseHandoff_inPhaseAt
      (handoff := handoff) primeProperty QBelowGuess guessBelowTwoQ
    have suffixEq := FivefoldFrontModule.core_word_from_target_eq_nil
      primeProperty primeBound layout handoffBound handoffNotActive
      handoffMembership suffixOver suffixLocal
    subst suffix
    have phaseEq := (handoffMembership.unique primeProperty primeBound
      handoffBound endpointBound endpointMembership (by
        simpa [physicalWordAction] using suffixRun)).1
    exact handoffEndpointDistinct phaseEq

/-- A positive-input core-only word cannot reach a guarded phase outside the
seven private core controls and its handoff. -/
theorem coreWord_cannot_reach_foreign_phase_general_of_nonempty
    {prime phaseCount source handoff guessPhase firstPhase secondPhase
      thirdPhase fourthPhase fifthPhase markerTwoPhase endpointPhase counter :
      Nat}
    {endpointDigit : Int} {endpoint : Vec2}
    (primeProperty : IsPrime prime) (primeBound : 6 * phaseCount < prime)
    (layout : FivefoldFrontModule.PhaseLayout phaseCount source guessPhase
      firstPhase secondPhase thirdPhase fourthPhase fifthPhase markerTwoPhase)
    (handoffBound : handoff < phaseCount)
    (endpointBound : endpointPhase < phaseCount)
    (handoffNotActive : handoff ∉
      [source, guessPhase, firstPhase, secondPhase, thirdPhase, fourthPhase,
        fifthPhase, markerTwoPhase])
    (endpointNotInternal : endpointPhase ∉
      [guessPhase, firstPhase, secondPhase, thirdPhase, fourthPhase,
        fifthPhase, markerTwoPhase])
    (handoffEndpointDistinct : handoff ≠ endpointPhase)
    (endpointMembership : InPhaseAt prime endpointPhase endpointDigit endpoint)
    (counterPositive : 0 < counter)
    {word : List PhysicalTemplate}
    (wordOver : WordOver
      (FivefoldFrontModule.alphabet source handoff guessPhase firstPhase
        secondPhase thirdPhase fourthPhase fifthPhase markerTwoPhase) word)
    (wordNonempty : word ≠ [])
    (allLocal : AllStatesLocal prime word
      (phaseAffine source (unaryCode prime counter)))
    (completeRun : SameLine
      (physicalWordAction prime word
        (phaseAffine source (unaryCode prime counter))) endpoint) : False := by
  have internal_ne {phase : Nat}
      (phaseMem : phase ∈ [guessPhase, firstPhase, secondPhase, thirdPhase,
        fourthPhase, fifthPhase, markerTwoPhase]) :
      phase ≠ endpointPhase := by
    intro phaseEq
    apply endpointNotInternal
    simpa [phaseEq] using phaseMem
  obtain ⟨suffix, accepted | falseSurvivor⟩ :=
    FivefoldFrontModule.completedPath_classifies_general_of_nonempty
      primeProperty primeBound layout endpointBound
      (internal_ne (by simp)) (internal_ne (by simp))
      (internal_ne (by simp)) (internal_ne (by simp))
      (internal_ne (by simp)) (internal_ne (by simp))
      (internal_ne (by simp)) endpointMembership counterPositive wordOver
      wordNonempty allLocal completeRun
  · rcases accepted with
      ⟨first, _, _, suffixOver, suffixLocal, suffixRun⟩
    obtain ⟨digit, handoffMembership⟩ :=
      acceptedHandoff_inPhaseAt (handoff := handoff) (first := first)
        primeProperty
    have suffixEq := FivefoldFrontModule.core_word_from_target_eq_nil
      primeProperty primeBound layout handoffBound handoffNotActive
      handoffMembership suffixOver suffixLocal
    subst suffix
    have phaseEq := (handoffMembership.unique primeProperty primeBound
      handoffBound endpointBound endpointMembership (by
        simpa [physicalWordAction] using suffixRun)).1
    exact handoffEndpointDistinct phaseEq
  · rcases falseSurvivor with
      ⟨first, guess, _, QBelowGuess, guessBelowTwoQ, _, suffixOver,
        suffixLocal, suffixRun⟩
    obtain ⟨digit, handoffMembership⟩ := falseHandoff_inPhaseAt
      (handoff := handoff) primeProperty QBelowGuess guessBelowTwoQ
    have suffixEq := FivefoldFrontModule.core_word_from_target_eq_nil
      primeProperty primeBound layout handoffBound handoffNotActive
      handoffMembership suffixOver suffixLocal
    subst suffix
    have phaseEq := (handoffMembership.unique primeProperty primeBound
      handoffBound endpointBound endpointMembership (by
        simpa [physicalWordAction] using suffixRun)).1
    exact handoffEndpointDistinct phaseEq

/-- General positive-input classification of a core prefix that stops at its
handoff. -/
theorem corePrefix_to_handoff_classifies_general
    {prime phaseCount source handoff guessPhase firstPhase secondPhase
      thirdPhase fourthPhase fifthPhase markerTwoPhase counter : Nat}
    {handoffDigit : Int} {endpoint : Vec2}
    (primeProperty : IsPrime prime) (primeBound : 6 * phaseCount < prime)
    (layout : FivefoldFrontModule.PhaseLayout phaseCount source guessPhase
      firstPhase secondPhase thirdPhase fourthPhase fifthPhase markerTwoPhase)
    (handoffBound : handoff < phaseCount)
    (handoffNotActive : handoff ∉
      [source, guessPhase, firstPhase, secondPhase, thirdPhase, fourthPhase,
        fifthPhase, markerTwoPhase])
    (endpointMembership : InPhaseAt prime handoff handoffDigit endpoint)
    (counterPositive : 0 < counter)
    {word : List PhysicalTemplate}
    (wordOver : WordOver
      (FivefoldFrontModule.alphabet source handoff guessPhase firstPhase
        secondPhase thirdPhase fourthPhase fifthPhase markerTwoPhase) word)
    (allLocal : AllStatesLocal prime word
      (phaseAffine source (unaryCode prime counter)))
    (completeRun : SameLine
      (physicalWordAction prime word
        (phaseAffine source (unaryCode prime counter))) endpoint) :
    (∃ first,
      counter = 5 * first + 4 ∧
      word = FivefoldFrontModule.acceptedWord source handoff guessPhase
        firstPhase secondPhase thirdPhase fourthPhase fifthPhase markerTwoPhase
        first ∧
      SameLine (phaseAffine handoff
        (acceptedHandoffState prime first)) endpoint) ∨
    (∃ first guess,
      first + guess = counter ∧
      first + 1 < guess ∧ guess < 2 * (first + 1) ∧
      word = FivefoldFrontModule.falseSurvivorWord source handoff guessPhase
        firstPhase secondPhase thirdPhase fourthPhase fifthPhase markerTwoPhase
        first guess ∧
      SameLine (phaseAffine handoff
        (falseHandoffState prime first guess 0)) endpoint) := by
  obtain ⟨sourceDigit, sourceMembership⟩ := unaryCode_inPhaseAt
    (base := prime) (phase := source) (counter := counter) primeProperty.1
  have sourceHandoffDistinct : source ≠ handoff := by
    intro phaseEq
    apply handoffNotActive
    simp [← phaseEq]
  have wordNonempty : word ≠ [] := by
    intro wordEmpty
    subst word
    have phaseEq := (sourceMembership.unique primeProperty primeBound
      layout.sourceBound handoffBound endpointMembership (by
        simpa [physicalWordAction] using completeRun)).1
    exact sourceHandoffDistinct phaseEq
  obtain ⟨suffix, accepted | falseSurvivor⟩ :=
    FivefoldFrontModule.completedPath_classifies_general_of_nonempty
      primeProperty primeBound layout handoffBound
      (active_ne_endpoint handoffNotActive (by simp))
      (active_ne_endpoint handoffNotActive (by simp))
      (active_ne_endpoint handoffNotActive (by simp))
      (active_ne_endpoint handoffNotActive (by simp))
      (active_ne_endpoint handoffNotActive (by simp))
      (active_ne_endpoint handoffNotActive (by simp))
      (active_ne_endpoint handoffNotActive (by simp))
      endpointMembership counterPositive wordOver wordNonempty allLocal
      completeRun
  · rcases accepted with
      ⟨first, counterEq, wordEq, suffixOver, suffixLocal, suffixRun⟩
    obtain ⟨digit, handoffMembership⟩ := acceptedHandoff_inPhaseAt
      (handoff := handoff) (first := first) primeProperty
    have suffixEq := FivefoldFrontModule.core_word_from_target_eq_nil
      primeProperty primeBound layout handoffBound handoffNotActive
      handoffMembership suffixOver suffixLocal
    subst suffix
    exact .inl ⟨first, counterEq, by simpa using wordEq,
      by simpa [physicalWordAction] using suffixRun⟩
  · rcases falseSurvivor with
      ⟨first, guess, splitEq, QBelowGuess, guessBelowTwoQ, wordEq,
        suffixOver, suffixLocal, suffixRun⟩
    obtain ⟨digit, handoffMembership⟩ := falseHandoff_inPhaseAt
      (handoff := handoff) primeProperty QBelowGuess guessBelowTwoQ
    have suffixEq := FivefoldFrontModule.core_word_from_target_eq_nil
      primeProperty primeBound layout handoffBound handoffNotActive
      handoffMembership suffixOver suffixLocal
    subst suffix
    exact .inr ⟨first, guess, splitEq, QBelowGuess, guessBelowTwoQ,
      by simpa using wordEq, by simpa [physicalWordAction] using suffixRun⟩
/-- Classification of a core prefix stopped exactly before the first
validator letter.  No additional core suffix can remain at the handoff. -/
theorem corePrefix_to_handoff_classifies
    {prime phaseCount source handoff guessPhase firstPhase secondPhase
      thirdPhase fourthPhase fifthPhase markerTwoPhase inputFirst : Nat}
    {handoffDigit : Int} {endpoint : Vec2}
    (primeProperty : IsPrime prime) (primeBound : 6 * phaseCount < prime)
    (layout : FivefoldFrontModule.PhaseLayout phaseCount source guessPhase
      firstPhase secondPhase thirdPhase fourthPhase fifthPhase markerTwoPhase)
    (handoffBound : handoff < phaseCount)
    (handoffNotActive : handoff ∉
      [source, guessPhase, firstPhase, secondPhase, thirdPhase, fourthPhase,
        fifthPhase, markerTwoPhase])
    (endpointMembership : InPhaseAt prime handoff handoffDigit endpoint)
    {word : List PhysicalTemplate}
    (wordOver : WordOver
      (FivefoldFrontModule.alphabet source handoff guessPhase firstPhase
        secondPhase thirdPhase fourthPhase fifthPhase markerTwoPhase) word)
    (allLocal : AllStatesLocal prime word
      (phaseAffine source (unaryCode prime (5 * inputFirst + 4))))
    (completeRun : SameLine
      (physicalWordAction prime word
        (phaseAffine source (unaryCode prime (5 * inputFirst + 4))))
      endpoint) :
    (word = FivefoldFrontModule.acceptedWord source handoff guessPhase
        firstPhase secondPhase thirdPhase fourthPhase fifthPhase markerTwoPhase
        inputFirst ∧
      SameLine (phaseAffine handoff
        (acceptedHandoffState prime inputFirst)) endpoint) ∨
    (∃ first guess,
      first + guess = 5 * inputFirst + 4 ∧
      first + 1 < guess ∧ guess < 2 * (first + 1) ∧
      word = FivefoldFrontModule.falseSurvivorWord source handoff guessPhase
        firstPhase secondPhase thirdPhase fourthPhase fifthPhase markerTwoPhase
        first guess ∧
      SameLine (phaseAffine handoff
        (falseHandoffState prime first guess 0)) endpoint) := by
  obtain ⟨suffix, accepted | falseSurvivor⟩ :=
    FivefoldFrontModule.completedPath_classifies primeProperty primeBound
      layout handoffBound
      (active_ne_endpoint handoffNotActive (by simp))
      (active_ne_endpoint handoffNotActive (by simp))
      (active_ne_endpoint handoffNotActive (by simp))
      (active_ne_endpoint handoffNotActive (by simp))
      (active_ne_endpoint handoffNotActive (by simp))
      (active_ne_endpoint handoffNotActive (by simp))
      (active_ne_endpoint handoffNotActive (by simp))
      (active_ne_endpoint handoffNotActive (by simp))
      endpointMembership wordOver allLocal completeRun
  · rcases accepted with ⟨wordEq, suffixOver, suffixLocal, suffixRun⟩
    obtain ⟨digit, handoffMembership⟩ :=
      acceptedHandoff_inPhaseAt (handoff := handoff) (first := inputFirst)
        primeProperty
    have suffixEq := FivefoldFrontModule.core_word_from_target_eq_nil
      primeProperty primeBound layout handoffBound handoffNotActive
      handoffMembership suffixOver suffixLocal
    subst suffix
    exact .inl ⟨by simpa using wordEq,
      by simpa [physicalWordAction] using suffixRun⟩
  · rcases falseSurvivor with
      ⟨first, guess, splitEq, QBelowGuess, guessBelowTwoQ, wordEq,
        suffixOver, suffixLocal, suffixRun⟩
    obtain ⟨digit, handoffMembership⟩ := falseHandoff_inPhaseAt
      (handoff := handoff) primeProperty QBelowGuess guessBelowTwoQ
    have suffixEq := FivefoldFrontModule.core_word_from_target_eq_nil
      primeProperty primeBound layout handoffBound handoffNotActive
      handoffMembership suffixOver suffixLocal
    subst suffix
    exact .inr ⟨first, guess, splitEq, QBelowGuess, guessBelowTwoQ,
      by simpa using wordEq, by simpa [physicalWordAction] using suffixRun⟩

/-- From the accepted handoff, every locally surviving word over the union
alphabet that reaches the output phase is exactly the positive subtraction
word.  In particular, a core letter cannot be interleaved into the scan. -/
theorem acceptedHandoff_union_forces_subtraction
    {prime phaseCount source handoff output guessPhase firstPhase secondPhase
      thirdPhase fourthPhase fifthPhase markerTwoPhase first : Nat}
    {endpointDigit : Int} {endpoint : Vec2}
    (primeProperty : IsPrime prime) (primeBound : 6 * phaseCount < prime)
    (layout : FivefoldFrontModule.PhaseLayout phaseCount source guessPhase
      firstPhase secondPhase thirdPhase fourthPhase fifthPhase markerTwoPhase)
    (handoffBound : handoff < phaseCount) (outputBound : output < phaseCount)
    (handoffNotActive : handoff ∉
      [source, guessPhase, firstPhase, secondPhase, thirdPhase, fourthPhase,
        fifthPhase, markerTwoPhase])
    (outputNotActive : output ∉
      [source, guessPhase, firstPhase, secondPhase, thirdPhase, fourthPhase,
        fifthPhase, markerTwoPhase])
    (handoffOutputDistinct : handoff ≠ output)
    (endpointMembership : InPhaseAt prime output endpointDigit endpoint)
    {word : List PhysicalTemplate}
    (wordOver : WordOver
      (singleAlphabet source handoff output guessPhase firstPhase secondPhase
        thirdPhase fourthPhase fifthPhase markerTwoPhase) word)
    (allLocal : AllStatesLocal prime word
      (phaseAffine handoff (acceptedHandoffState prime first)))
    (completeRun : SameLine
      (physicalWordAction prime word
        (phaseAffine handoff (acceptedHandoffState prime first))) endpoint) :
    word = subtractionWord handoff output first := by
  have reordered : WordOver
      (subtractionAlphabet handoff output ++
        FivefoldFrontModule.alphabet source handoff guessPhase firstPhase
          secondPhase thirdPhase fourthPhase fifthPhase markerTwoPhase) word :=
    by
      intro candidate candidateMem
      have membership := wordOver candidate candidateMem
      simp only [singleAlphabet, List.mem_append] at membership ⊢
      exact membership.symm
  rcases wordOver_append_first_right reordered with subtractionOnly |
      ⟨initial, letter, suffix, wordEq, initialOver, letterCore, _⟩
  · rw [acceptedHandoffState_eq prime first primeProperty.1] at allLocal completeRun
    obtain ⟨residual, parsedEq, residualOver, residualLocal, _⟩ :=
      subtractionWord_forced_prefix_to_endpoint primeProperty primeBound
        handoffBound outputBound handoffOutputDistinct endpointMembership
        (by omega : first < 4 * first + 3) subtractionOnly allLocal completeRun
    obtain ⟨outputDigit, canonicalOutputMembership⟩ :=
      twoFieldCode_inPhaseAt (phase := output) (first := first)
        (second := 4 * first + 3 - first - 1) primeProperty
    have residualEq := subtraction_word_from_target_eq_nil primeProperty
      primeBound handoffBound outputBound handoffOutputDistinct
      canonicalOutputMembership residualOver residualLocal
    subst residual
    simpa using parsedEq
  · obtain ⟨initialLocal, boundaryLocal⟩ :=
      allLocal.split_append_cons wordEq
    have boundaryMembership : InPhaseAt prime letter.sourcePhase letter.digit
        (physicalWordAction prime initial
          (phaseAffine handoff (acceptedHandoffState prime first))) := by
      apply physicalLetter_input_inPhaseAt primeProperty
        (FivefoldFrontModule.letter_reserved letterCore) boundaryLocal.1
      simpa [PhysicalTemplate.act, PhysicalTemplate.matrix] using
        boundaryLocal.2.start
    have sourceNeHandoff : letter.sourcePhase ≠ handoff :=
      core_letter_source_ne_endpoint handoffNotActive letterCore
    rw [acceptedHandoffState_eq prime first primeProperty.1] at initialLocal boundaryMembership
    obtain ⟨residual, parsedEq, residualOver, residualLocal, residualRun⟩ :=
      subtractionWord_forced_prefix_to_endpoint primeProperty primeBound
        handoffBound (FivefoldFrontModule.letter_source_bound layout letterCore)
        sourceNeHandoff.symm boundaryMembership
        (by omega : first < 4 * first + 3) initialOver initialLocal
        (SameLine.refl _)
    obtain ⟨outputDigit, canonicalOutputMembership⟩ :=
      twoFieldCode_inPhaseAt (phase := output) (first := first)
        (second := 4 * first + 3 - first - 1) primeProperty
    have residualEq := subtraction_word_from_target_eq_nil primeProperty
      primeBound handoffBound outputBound handoffOutputDistinct
      canonicalOutputMembership residualOver residualLocal
    subst residual
    have phaseEq := (canonicalOutputMembership.unique primeProperty primeBound
      outputBound (FivefoldFrontModule.letter_source_bound layout letterCore)
      boundaryMembership (by
        simpa [physicalWordAction] using residualRun)).1
    exact False.elim
      ((core_letter_source_ne_endpoint outputNotActive letterCore)
        phaseEq.symm)

/-- The false-survivor handoff cannot be rescued by interleaving letters from
the fivefold core with letters from the subtraction validator. -/
theorem falseHandoff_union_rejects
    {prime phaseCount source handoff output guessPhase firstPhase secondPhase
      thirdPhase fourthPhase fifthPhase markerTwoPhase first guess : Nat}
    {endpointDigit : Int} {endpoint : Vec2}
    (primeProperty : IsPrime prime) (primeBound : 6 * phaseCount < prime)
    (layout : FivefoldFrontModule.PhaseLayout phaseCount source guessPhase
      firstPhase secondPhase thirdPhase fourthPhase fifthPhase markerTwoPhase)
    (handoffBound : handoff < phaseCount) (outputBound : output < phaseCount)
    (handoffNotActive : handoff ∉
      [source, guessPhase, firstPhase, secondPhase, thirdPhase, fourthPhase,
        fifthPhase, markerTwoPhase])
    (handoffOutputDistinct : handoff ≠ output)
    (endpointMembership : InPhaseAt prime output endpointDigit endpoint)
    (QBelowGuess : first + 1 < guess)
    (guessBelowTwoQ : guess < 2 * (first + 1))
    {word : List PhysicalTemplate}
    (wordOver : WordOver
      (singleAlphabet source handoff output guessPhase firstPhase secondPhase
        thirdPhase fourthPhase fifthPhase markerTwoPhase) word)
    (allLocal : AllStatesLocal prime word
      (phaseAffine handoff (falseHandoffState prime first guess 0)))
    (completeRun : SameLine
      (physicalWordAction prime word
        (phaseAffine handoff (falseHandoffState prime first guess 0)))
      endpoint) : False := by
  have reordered : WordOver
      (subtractionAlphabet handoff output ++
        FivefoldFrontModule.alphabet source handoff guessPhase firstPhase
          secondPhase thirdPhase fourthPhase fifthPhase markerTwoPhase) word :=
    by
      intro candidate candidateMem
      have membership := wordOver candidate candidateMem
      simp only [singleAlphabet, List.mem_append] at membership ⊢
      exact membership.symm
  rcases wordOver_append_first_right reordered with subtractionOnly |
      ⟨initial, letter, suffix, wordEq, initialOver, letterCore, _⟩
  · exact falseHandoff_rejects_subtraction primeProperty primeBound
      handoffBound outputBound handoffOutputDistinct endpointMembership
      QBelowGuess guessBelowTwoQ subtractionOnly allLocal completeRun
  · obtain ⟨initialLocal, boundaryLocal⟩ :=
      allLocal.split_append_cons wordEq
    have boundaryMembership : InPhaseAt prime letter.sourcePhase letter.digit
        (physicalWordAction prime initial
          (phaseAffine handoff (falseHandoffState prime first guess 0))) := by
      apply physicalLetter_input_inPhaseAt primeProperty
        (FivefoldFrontModule.letter_reserved letterCore) boundaryLocal.1
      simpa [PhysicalTemplate.act, PhysicalTemplate.matrix] using
        boundaryLocal.2.start
    exact falseHandoff_rejects_subtraction primeProperty primeBound
      handoffBound (FivefoldFrontModule.letter_source_bound layout letterCore)
      (core_letter_source_ne_endpoint handoffNotActive letterCore).symm
      boundaryMembership QBelowGuess guessBelowTwoQ initialOver initialLocal
      (SameLine.refl _)

/-- Full unrestricted-word converse for the eighteen-letter validated front.
Every locally surviving word from the encoded input boundary to the output
phase is the canonical accepted core word followed by its subtraction scan. -/
theorem singleWord_unique
    {prime phaseCount source handoff output guessPhase firstPhase secondPhase
      thirdPhase fourthPhase fifthPhase markerTwoPhase inputFirst : Nat}
    {endpointDigit : Int} {endpoint : Vec2}
    (primeProperty : IsPrime prime) (primeBound : 6 * phaseCount < prime)
    (layout : FivefoldFrontModule.PhaseLayout phaseCount source guessPhase
      firstPhase secondPhase thirdPhase fourthPhase fifthPhase markerTwoPhase)
    (handoffBound : handoff < phaseCount) (outputBound : output < phaseCount)
    (handoffNotActive : handoff ∉
      [source, guessPhase, firstPhase, secondPhase, thirdPhase, fourthPhase,
        fifthPhase, markerTwoPhase])
    (outputNotActive : output ∉
      [source, guessPhase, firstPhase, secondPhase, thirdPhase, fourthPhase,
        fifthPhase, markerTwoPhase])
    (handoffOutputDistinct : handoff ≠ output)
    (endpointMembership : InPhaseAt prime output endpointDigit endpoint)
    {word : List PhysicalTemplate}
    (wordOver : WordOver
      (singleAlphabet source handoff output guessPhase firstPhase secondPhase
        thirdPhase fourthPhase fifthPhase markerTwoPhase) word)
    (allLocal : AllStatesLocal prime word
      (phaseAffine source (unaryCode prime (5 * inputFirst + 4))))
    (completeRun : SameLine
      (physicalWordAction prime word
        (phaseAffine source (unaryCode prime (5 * inputFirst + 4))))
      endpoint) :
    word = singleWord source handoff output guessPhase firstPhase secondPhase
      thirdPhase fourthPhase fifthPhase markerTwoPhase inputFirst := by
  have unionOver : WordOver
      (FivefoldFrontModule.alphabet source handoff guessPhase firstPhase
          secondPhase thirdPhase fourthPhase fifthPhase markerTwoPhase ++
        subtractionAlphabet handoff output) word := by
    simpa [singleAlphabet] using wordOver
  rcases wordOver_append_first_right unionOver with coreOnly |
      ⟨initial, letter, suffix, wordEq, initialOver, letterSubtraction,
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
        (subtractionLetter_reserved letterSubtraction) boundaryLocal.1
      simpa [PhysicalTemplate.act, PhysicalTemplate.matrix] using
        boundaryLocal.2.start
    have letterSource : letter.sourcePhase = handoff := by
      simp [subtractionAlphabet] at letterSubtraction
      rcases letterSubtraction with rfl | rfl <;> rfl
    rw [letterSource] at boundaryMembership
    have prefixClassification := corePrefix_to_handoff_classifies
      primeProperty primeBound layout handoffBound handoffNotActive
      boundaryMembership initialOver initialLocal (SameLine.refl _)
    have tailOver : WordOver
        (singleAlphabet source handoff output guessPhase firstPhase secondPhase
          thirdPhase fourthPhase fifthPhase markerTwoPhase) (letter :: suffix) := by
      intro candidate candidateMem
      simp only [List.mem_cons] at candidateMem
      rcases candidateMem with rfl | candidateMem
      · exact List.mem_append_right _ letterSubtraction
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
        acceptedHandoff_inPhaseAt (handoff := handoff) (first := inputFirst)
          primeProperty
      have canonicalTailLocal : AllStatesLocal prime (letter :: suffix)
          (phaseAffine handoff (acceptedHandoffState prime inputFirst)) :=
        boundaryLocal.of_sameLine (by omega) handoffMembership.local.1
          handoffSame
      have canonicalTailRun : SameLine
          (physicalWordAction prime (letter :: suffix)
            (phaseAffine handoff (acceptedHandoffState prime inputFirst)))
          endpoint :=
        (physicalWordAction_preserves_sameLine prime (letter :: suffix)
          handoffSame).trans tailRun
      have tailEq := acceptedHandoff_union_forces_subtraction primeProperty
        primeBound layout handoffBound outputBound handoffNotActive
        outputNotActive handoffOutputDistinct endpointMembership tailOver
        canonicalTailLocal canonicalTailRun
      rw [wordEq, initialEq, tailEq]
      rfl
    · rcases falseSurvivor with
        ⟨first, guess, _, QBelowGuess, guessBelowTwoQ, initialEq,
          handoffSame⟩
      obtain ⟨handoffDigit, handoffMembership⟩ := falseHandoff_inPhaseAt
        (handoff := handoff) primeProperty QBelowGuess guessBelowTwoQ
      have canonicalTailLocal : AllStatesLocal prime (letter :: suffix)
          (phaseAffine handoff (falseHandoffState prime first guess 0)) :=
        boundaryLocal.of_sameLine (by omega) handoffMembership.local.1
          handoffSame
      have canonicalTailRun : SameLine
          (physicalWordAction prime (letter :: suffix)
            (phaseAffine handoff (falseHandoffState prime first guess 0)))
          endpoint :=
        (physicalWordAction_preserves_sameLine prime (letter :: suffix)
          handoffSame).trans tailRun
      exact False.elim (falseHandoff_union_rejects primeProperty primeBound
        layout handoffBound outputBound handoffNotActive
        handoffOutputDistinct endpointMembership QBelowGuess guessBelowTwoQ
        tailOver canonicalTailLocal canonicalTailRun)

/-- General positive-input converse for the eighteen-letter validated front.
It derives the unique parameter `first` and the input equation
`counter = 5 * first + 4`. -/
theorem singleWord_unique_general
    {prime phaseCount source handoff output guessPhase firstPhase secondPhase
      thirdPhase fourthPhase fifthPhase markerTwoPhase counter : Nat}
    {endpointDigit : Int} {endpoint : Vec2}
    (primeProperty : IsPrime prime) (primeBound : 6 * phaseCount < prime)
    (layout : FivefoldFrontModule.PhaseLayout phaseCount source guessPhase
      firstPhase secondPhase thirdPhase fourthPhase fifthPhase markerTwoPhase)
    (handoffBound : handoff < phaseCount) (outputBound : output < phaseCount)
    (handoffNotActive : handoff ∉
      [source, guessPhase, firstPhase, secondPhase, thirdPhase, fourthPhase,
        fifthPhase, markerTwoPhase])
    (outputNotActive : output ∉
      [source, guessPhase, firstPhase, secondPhase, thirdPhase, fourthPhase,
        fifthPhase, markerTwoPhase])
    (handoffOutputDistinct : handoff ≠ output)
    (endpointMembership : InPhaseAt prime output endpointDigit endpoint)
    (counterPositive : 0 < counter)
    {word : List PhysicalTemplate}
    (wordOver : WordOver
      (singleAlphabet source handoff output guessPhase firstPhase secondPhase
        thirdPhase fourthPhase fifthPhase markerTwoPhase) word)
    (allLocal : AllStatesLocal prime word
      (phaseAffine source (unaryCode prime counter)))
    (completeRun : SameLine
      (physicalWordAction prime word
        (phaseAffine source (unaryCode prime counter))) endpoint) :
    ∃ first,
      counter = 5 * first + 4 ∧
      word = singleWord source handoff output guessPhase firstPhase secondPhase
        thirdPhase fourthPhase fifthPhase markerTwoPhase first := by
  have unionOver : WordOver
      (FivefoldFrontModule.alphabet source handoff guessPhase firstPhase
          secondPhase thirdPhase fourthPhase fifthPhase markerTwoPhase ++
        subtractionAlphabet handoff output) word := by
    simpa [singleAlphabet] using wordOver
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
      ⟨initial, letter, suffix, wordEq, initialOver, letterSubtraction,
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
        (subtractionLetter_reserved letterSubtraction) boundaryLocal.1
      simpa [PhysicalTemplate.act, PhysicalTemplate.matrix] using
        boundaryLocal.2.start
    have letterSource : letter.sourcePhase = handoff := by
      simp [subtractionAlphabet] at letterSubtraction
      rcases letterSubtraction with rfl | rfl <;> rfl
    rw [letterSource] at boundaryMembership
    have prefixClassification := corePrefix_to_handoff_classifies_general
      primeProperty primeBound layout handoffBound handoffNotActive
      boundaryMembership counterPositive initialOver initialLocal
      (SameLine.refl _)
    have tailOver : WordOver
        (singleAlphabet source handoff output guessPhase firstPhase secondPhase
          thirdPhase fourthPhase fifthPhase markerTwoPhase) (letter :: suffix) := by
      intro candidate candidateMem
      simp only [List.mem_cons] at candidateMem
      rcases candidateMem with rfl | candidateMem
      · exact List.mem_append_right _ letterSubtraction
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
      have tailEq := acceptedHandoff_union_forces_subtraction primeProperty
        primeBound layout handoffBound outputBound handoffNotActive
        outputNotActive handoffOutputDistinct endpointMembership tailOver
        canonicalTailLocal canonicalTailRun
      refine ⟨first, counterEq, ?_⟩
      rw [wordEq, initialEq, tailEq]
      rfl
    · rcases falseSurvivor with
        ⟨first, guess, _, QBelowGuess, guessBelowTwoQ, _, handoffSame⟩
      obtain ⟨handoffDigit, handoffMembership⟩ := falseHandoff_inPhaseAt
        (handoff := handoff) primeProperty QBelowGuess guessBelowTwoQ
      have canonicalTailLocal : AllStatesLocal prime (letter :: suffix)
          (phaseAffine handoff (falseHandoffState prime first guess 0)) :=
        boundaryLocal.of_sameLine (by omega) handoffMembership.local.1
          handoffSame
      have canonicalTailRun : SameLine
          (physicalWordAction prime (letter :: suffix)
            (phaseAffine handoff (falseHandoffState prime first guess 0)))
          endpoint :=
        (physicalWordAction_preserves_sameLine prime (letter :: suffix)
          handoffSame).trans tailRun
      exact False.elim (falseHandoff_union_rejects primeProperty primeBound
        layout handoffBound outputBound handoffNotActive
        handoffOutputDistinct endpointMembership QBelowGuess guessBelowTwoQ
        tailOver canonicalTailLocal canonicalTailRun)

/-- The accepted handoff cannot reach a foreign guarded phase through the
full core-plus-subtraction union. -/
theorem acceptedHandoff_full_union_cannot_reach_foreign_phase
    {prime phaseCount source handoff output guessPhase firstPhase secondPhase
      thirdPhase fourthPhase fifthPhase markerTwoPhase endpointPhase first : Nat}
    {endpointDigit : Int} {endpoint : Vec2}
    (primeProperty : IsPrime prime) (primeBound : 6 * phaseCount < prime)
    (layout : FivefoldFrontModule.PhaseLayout phaseCount source guessPhase
      firstPhase secondPhase thirdPhase fourthPhase fifthPhase markerTwoPhase)
    (handoffBound : handoff < phaseCount) (outputBound : output < phaseCount)
    (endpointBound : endpointPhase < phaseCount)
    (handoffNotActive : handoff ∉
      [source, guessPhase, firstPhase, secondPhase, thirdPhase, fourthPhase,
        fifthPhase, markerTwoPhase])
    (outputNotActive : output ∉
      [source, guessPhase, firstPhase, secondPhase, thirdPhase, fourthPhase,
        fifthPhase, markerTwoPhase])
    (handoffOutputDistinct : handoff ≠ output)
    (handoffEndpointDistinct : handoff ≠ endpointPhase)
    (outputEndpointDistinct : output ≠ endpointPhase)
    (endpointMembership : InPhaseAt prime endpointPhase endpointDigit endpoint)
    {word : List PhysicalTemplate}
    (wordOver : WordOver
      (singleAlphabet source handoff output guessPhase firstPhase secondPhase
        thirdPhase fourthPhase fifthPhase markerTwoPhase) word)
    (allLocal : AllStatesLocal prime word
      (phaseAffine handoff (acceptedHandoffState prime first)))
    (completeRun : SameLine
      (physicalWordAction prime word
        (phaseAffine handoff (acceptedHandoffState prime first))) endpoint) :
    False := by
  have reordered : WordOver
      (subtractionAlphabet handoff output ++
        FivefoldFrontModule.alphabet source handoff guessPhase firstPhase
          secondPhase thirdPhase fourthPhase fifthPhase markerTwoPhase) word := by
    intro candidate candidateMem
    have membership := wordOver candidate candidateMem
    simp only [singleAlphabet, List.mem_append] at membership ⊢
    exact membership.symm
  rcases wordOver_append_first_right reordered with subtractionOnly |
      ⟨initial, letter, suffix, wordEq, initialOver, letterCore, _⟩
  · rw [acceptedHandoffState_eq prime first primeProperty.1] at allLocal completeRun
    obtain ⟨residual, _, residualOver, residualLocal, residualRun⟩ :=
      subtractionWord_forced_prefix_to_endpoint primeProperty primeBound
        handoffBound endpointBound handoffEndpointDistinct endpointMembership
        (by omega : first < 4 * first + 3) subtractionOnly allLocal completeRun
    obtain ⟨outputDigit, canonicalOutputMembership⟩ :=
      twoFieldCode_inPhaseAt (phase := output) (first := first)
        (second := 4 * first + 3 - first - 1) primeProperty
    have residualEq := subtraction_word_from_target_eq_nil primeProperty
      primeBound handoffBound outputBound handoffOutputDistinct
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
          (phaseAffine handoff (acceptedHandoffState prime first))) := by
      apply physicalLetter_input_inPhaseAt primeProperty
        (FivefoldFrontModule.letter_reserved letterCore) boundaryLocal.1
      simpa [PhysicalTemplate.act, PhysicalTemplate.matrix] using
        boundaryLocal.2.start
    have sourceNeHandoff : letter.sourcePhase ≠ handoff :=
      core_letter_source_ne_endpoint handoffNotActive letterCore
    rw [acceptedHandoffState_eq prime first primeProperty.1] at boundaryMembership initialLocal
    obtain ⟨residual, _, residualOver, residualLocal, residualRun⟩ :=
      subtractionWord_forced_prefix_to_endpoint primeProperty primeBound
        handoffBound (FivefoldFrontModule.letter_source_bound layout letterCore)
        sourceNeHandoff.symm boundaryMembership
        (by omega : first < 4 * first + 3) initialOver initialLocal
        (SameLine.refl _)
    obtain ⟨outputDigit, canonicalOutputMembership⟩ :=
      twoFieldCode_inPhaseAt (phase := output) (first := first)
        (second := 4 * first + 3 - first - 1) primeProperty
    have residualEq := subtraction_word_from_target_eq_nil primeProperty
      primeBound handoffBound outputBound handoffOutputDistinct
      canonicalOutputMembership residualOver residualLocal
    subst residual
    have phaseEq := (canonicalOutputMembership.unique primeProperty primeBound
      outputBound (FivefoldFrontModule.letter_source_bound layout letterCore)
      boundaryMembership (by
        simpa [physicalWordAction] using residualRun)).1
    exact (core_letter_source_ne_endpoint outputNotActive letterCore)
      phaseEq.symm

/-- The false handoff cannot reach a foreign guarded phase through the full
union alphabet. -/
theorem falseHandoff_full_union_cannot_reach_foreign_phase
    {prime phaseCount source handoff output guessPhase firstPhase secondPhase
      thirdPhase fourthPhase fifthPhase markerTwoPhase endpointPhase first guess :
      Nat}
    {endpointDigit : Int} {endpoint : Vec2}
    (primeProperty : IsPrime prime) (primeBound : 6 * phaseCount < prime)
    (layout : FivefoldFrontModule.PhaseLayout phaseCount source guessPhase
      firstPhase secondPhase thirdPhase fourthPhase fifthPhase markerTwoPhase)
    (handoffBound : handoff < phaseCount)
    (endpointBound : endpointPhase < phaseCount)
    (handoffNotActive : handoff ∉
      [source, guessPhase, firstPhase, secondPhase, thirdPhase, fourthPhase,
        fifthPhase, markerTwoPhase])
    (handoffEndpointDistinct : handoff ≠ endpointPhase)
    (endpointMembership : InPhaseAt prime endpointPhase endpointDigit endpoint)
    (QBelowGuess : first + 1 < guess)
    (guessBelowTwoQ : guess < 2 * (first + 1))
    {word : List PhysicalTemplate}
    (wordOver : WordOver
      (singleAlphabet source handoff output guessPhase firstPhase secondPhase
        thirdPhase fourthPhase fifthPhase markerTwoPhase) word)
    (allLocal : AllStatesLocal prime word
      (phaseAffine handoff (falseHandoffState prime first guess 0)))
    (completeRun : SameLine
      (physicalWordAction prime word
        (phaseAffine handoff (falseHandoffState prime first guess 0)))
      endpoint) : False := by
  have reordered : WordOver
      (subtractionAlphabet handoff output ++
        FivefoldFrontModule.alphabet source handoff guessPhase firstPhase
          secondPhase thirdPhase fourthPhase fifthPhase markerTwoPhase) word := by
    intro candidate candidateMem
    have membership := wordOver candidate candidateMem
    simp only [singleAlphabet, List.mem_append] at membership ⊢
    exact membership.symm
  rcases wordOver_append_first_right reordered with subtractionOnly |
      ⟨initial, letter, suffix, wordEq, initialOver, letterCore, _⟩
  · exact falseHandoff_rejects_subtraction primeProperty primeBound
      handoffBound endpointBound handoffEndpointDistinct endpointMembership
      QBelowGuess guessBelowTwoQ subtractionOnly allLocal completeRun
  · obtain ⟨initialLocal, boundaryLocal⟩ :=
      allLocal.split_append_cons wordEq
    have boundaryMembership : InPhaseAt prime letter.sourcePhase letter.digit
        (physicalWordAction prime initial
          (phaseAffine handoff (falseHandoffState prime first guess 0))) := by
      apply physicalLetter_input_inPhaseAt primeProperty
        (FivefoldFrontModule.letter_reserved letterCore) boundaryLocal.1
      simpa [PhysicalTemplate.act, PhysicalTemplate.matrix] using
        boundaryLocal.2.start
    exact falseHandoff_rejects_subtraction primeProperty primeBound
      handoffBound (FivefoldFrontModule.letter_source_bound layout letterCore)
      (core_letter_source_ne_endpoint handoffNotActive letterCore).symm
      boundaryMembership QBelowGuess guessBelowTwoQ initialOver initialLocal
      (SameLine.refl _)

/-- A nonempty word over the complete eighteen-letter front cannot stop in
a guarded phase foreign to its internal controls and declared output.  The
endpoint may equal the source boundary. -/
theorem singleWord_cannot_reach_foreign_phase_of_nonempty
    {prime phaseCount source handoff output guessPhase firstPhase secondPhase
      thirdPhase fourthPhase fifthPhase markerTwoPhase endpointPhase inputFirst :
      Nat}
    {endpointDigit : Int} {endpoint : Vec2}
    (primeProperty : IsPrime prime) (primeBound : 6 * phaseCount < prime)
    (layout : FivefoldFrontModule.PhaseLayout phaseCount source guessPhase
      firstPhase secondPhase thirdPhase fourthPhase fifthPhase markerTwoPhase)
    (handoffBound : handoff < phaseCount) (outputBound : output < phaseCount)
    (endpointBound : endpointPhase < phaseCount)
    (handoffNotActive : handoff ∉
      [source, guessPhase, firstPhase, secondPhase, thirdPhase, fourthPhase,
        fifthPhase, markerTwoPhase])
    (outputNotActive : output ∉
      [source, guessPhase, firstPhase, secondPhase, thirdPhase, fourthPhase,
        fifthPhase, markerTwoPhase])
    (endpointNotInternal : endpointPhase ∉
      [guessPhase, firstPhase, secondPhase, thirdPhase, fourthPhase,
        fifthPhase, markerTwoPhase])
    (handoffOutputDistinct : handoff ≠ output)
    (handoffEndpointDistinct : handoff ≠ endpointPhase)
    (outputEndpointDistinct : output ≠ endpointPhase)
    (endpointMembership : InPhaseAt prime endpointPhase endpointDigit endpoint)
    {word : List PhysicalTemplate}
    (wordOver : WordOver
      (singleAlphabet source handoff output guessPhase firstPhase secondPhase
        thirdPhase fourthPhase fifthPhase markerTwoPhase) word)
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
        subtractionAlphabet handoff output) word := by
    simpa [singleAlphabet] using wordOver
  rcases wordOver_append_first_right unionOver with coreOnly |
      ⟨initial, letter, suffix, wordEq, initialOver, letterSubtraction,
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
        (subtractionLetter_reserved letterSubtraction) boundaryLocal.1
      simpa [PhysicalTemplate.act, PhysicalTemplate.matrix] using
        boundaryLocal.2.start
    have letterSource : letter.sourcePhase = handoff := by
      simp [subtractionAlphabet] at letterSubtraction
      rcases letterSubtraction with rfl | rfl <;> rfl
    rw [letterSource] at boundaryMembership
    have prefixClassification := corePrefix_to_handoff_classifies
      primeProperty primeBound layout handoffBound handoffNotActive
      boundaryMembership initialOver initialLocal (SameLine.refl _)
    have tailOver : WordOver
        (singleAlphabet source handoff output guessPhase firstPhase secondPhase
          thirdPhase fourthPhase fifthPhase markerTwoPhase) (letter :: suffix) := by
      intro candidate candidateMem
      simp only [List.mem_cons] at candidateMem
      rcases candidateMem with rfl | candidateMem
      · exact List.mem_append_right _ letterSubtraction
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
        acceptedHandoff_inPhaseAt (handoff := handoff) (first := inputFirst)
          primeProperty
      have canonicalTailLocal : AllStatesLocal prime (letter :: suffix)
          (phaseAffine handoff (acceptedHandoffState prime inputFirst)) :=
        boundaryLocal.of_sameLine (by omega) handoffMembership.local.1
          handoffSame
      have canonicalTailRun : SameLine
          (physicalWordAction prime (letter :: suffix)
            (phaseAffine handoff (acceptedHandoffState prime inputFirst)))
          endpoint :=
        (physicalWordAction_preserves_sameLine prime (letter :: suffix)
          handoffSame).trans tailRun
      exact acceptedHandoff_full_union_cannot_reach_foreign_phase
        primeProperty primeBound layout handoffBound outputBound endpointBound
        handoffNotActive outputNotActive handoffOutputDistinct
        handoffEndpointDistinct outputEndpointDistinct endpointMembership
        tailOver canonicalTailLocal canonicalTailRun
    · rcases falseSurvivor with
        ⟨first, guess, _, QBelowGuess, guessBelowTwoQ, _, handoffSame⟩
      obtain ⟨handoffDigit, handoffMembership⟩ := falseHandoff_inPhaseAt
        (handoff := handoff) primeProperty QBelowGuess guessBelowTwoQ
      have canonicalTailLocal : AllStatesLocal prime (letter :: suffix)
          (phaseAffine handoff (falseHandoffState prime first guess 0)) :=
        boundaryLocal.of_sameLine (by omega) handoffMembership.local.1
          handoffSame
      have canonicalTailRun : SameLine
          (physicalWordAction prime (letter :: suffix)
            (phaseAffine handoff (falseHandoffState prime first guess 0)))
          endpoint :=
        (physicalWordAction_preserves_sameLine prime (letter :: suffix)
          handoffSame).trans tailRun
      exact falseHandoff_full_union_cannot_reach_foreign_phase primeProperty
        primeBound layout handoffBound endpointBound handoffNotActive
        handoffEndpointDistinct endpointMembership QBelowGuess guessBelowTwoQ
        tailOver canonicalTailLocal canonicalTailRun

/-- General positive-input version of
`singleWord_cannot_reach_foreign_phase_of_nonempty`. -/
theorem singleWord_cannot_reach_foreign_phase_general_of_nonempty
    {prime phaseCount source handoff output guessPhase firstPhase secondPhase
      thirdPhase fourthPhase fifthPhase markerTwoPhase endpointPhase counter :
      Nat}
    {endpointDigit : Int} {endpoint : Vec2}
    (primeProperty : IsPrime prime) (primeBound : 6 * phaseCount < prime)
    (layout : FivefoldFrontModule.PhaseLayout phaseCount source guessPhase
      firstPhase secondPhase thirdPhase fourthPhase fifthPhase markerTwoPhase)
    (handoffBound : handoff < phaseCount) (outputBound : output < phaseCount)
    (endpointBound : endpointPhase < phaseCount)
    (handoffNotActive : handoff ∉
      [source, guessPhase, firstPhase, secondPhase, thirdPhase, fourthPhase,
        fifthPhase, markerTwoPhase])
    (outputNotActive : output ∉
      [source, guessPhase, firstPhase, secondPhase, thirdPhase, fourthPhase,
        fifthPhase, markerTwoPhase])
    (endpointNotInternal : endpointPhase ∉
      [guessPhase, firstPhase, secondPhase, thirdPhase, fourthPhase,
        fifthPhase, markerTwoPhase])
    (handoffOutputDistinct : handoff ≠ output)
    (handoffEndpointDistinct : handoff ≠ endpointPhase)
    (outputEndpointDistinct : output ≠ endpointPhase)
    (endpointMembership : InPhaseAt prime endpointPhase endpointDigit endpoint)
    (counterPositive : 0 < counter)
    {word : List PhysicalTemplate}
    (wordOver : WordOver
      (singleAlphabet source handoff output guessPhase firstPhase secondPhase
        thirdPhase fourthPhase fifthPhase markerTwoPhase) word)
    (wordNonempty : word ≠ [])
    (allLocal : AllStatesLocal prime word
      (phaseAffine source (unaryCode prime counter)))
    (completeRun : SameLine
      (physicalWordAction prime word
        (phaseAffine source (unaryCode prime counter))) endpoint) : False := by
  have unionOver : WordOver
      (FivefoldFrontModule.alphabet source handoff guessPhase firstPhase
          secondPhase thirdPhase fourthPhase fifthPhase markerTwoPhase ++
        subtractionAlphabet handoff output) word := by
    simpa [singleAlphabet] using wordOver
  rcases wordOver_append_first_right unionOver with coreOnly |
      ⟨initial, letter, suffix, wordEq, initialOver, letterSubtraction,
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
        (subtractionLetter_reserved letterSubtraction) boundaryLocal.1
      simpa [PhysicalTemplate.act, PhysicalTemplate.matrix] using
        boundaryLocal.2.start
    have letterSource : letter.sourcePhase = handoff := by
      simp [subtractionAlphabet] at letterSubtraction
      rcases letterSubtraction with rfl | rfl <;> rfl
    rw [letterSource] at boundaryMembership
    have prefixClassification := corePrefix_to_handoff_classifies_general
      primeProperty primeBound layout handoffBound handoffNotActive
      boundaryMembership counterPositive initialOver initialLocal
      (SameLine.refl _)
    have tailOver : WordOver
        (singleAlphabet source handoff output guessPhase firstPhase secondPhase
          thirdPhase fourthPhase fifthPhase markerTwoPhase) (letter :: suffix) := by
      intro candidate candidateMem
      simp only [List.mem_cons] at candidateMem
      rcases candidateMem with rfl | candidateMem
      · exact List.mem_append_right _ letterSubtraction
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
      exact acceptedHandoff_full_union_cannot_reach_foreign_phase
        primeProperty primeBound layout handoffBound outputBound endpointBound
        handoffNotActive outputNotActive handoffOutputDistinct
        handoffEndpointDistinct outputEndpointDistinct endpointMembership
        tailOver canonicalTailLocal canonicalTailRun
    · rcases falseSurvivor with
        ⟨first, guess, _, QBelowGuess, guessBelowTwoQ, _, handoffSame⟩
      obtain ⟨handoffDigit, handoffMembership⟩ := falseHandoff_inPhaseAt
        (handoff := handoff) primeProperty QBelowGuess guessBelowTwoQ
      have canonicalTailLocal : AllStatesLocal prime (letter :: suffix)
          (phaseAffine handoff (falseHandoffState prime first guess 0)) :=
        boundaryLocal.of_sameLine (by omega) handoffMembership.local.1
          handoffSame
      have canonicalTailRun : SameLine
          (physicalWordAction prime (letter :: suffix)
            (phaseAffine handoff (falseHandoffState prime first guess 0)))
          endpoint :=
        (physicalWordAction_preserves_sameLine prime (letter :: suffix)
          handoffSame).trans tailRun
      exact falseHandoff_full_union_cannot_reach_foreign_phase primeProperty
        primeBound layout handoffBound endpointBound handoffNotActive
        handoffEndpointDistinct endpointMembership QBelowGuess guessBelowTwoQ
        tailOver canonicalTailLocal canonicalTailRun

/-- A word over the complete eighteen-letter front cannot stop in a guarded
phase foreign to both the front controls and its declared output. -/
theorem singleWord_cannot_reach_foreign_phase
    {prime phaseCount source handoff output guessPhase firstPhase secondPhase
      thirdPhase fourthPhase fifthPhase markerTwoPhase endpointPhase inputFirst :
      Nat}
    {endpointDigit : Int} {endpoint : Vec2}
    (primeProperty : IsPrime prime) (primeBound : 6 * phaseCount < prime)
    (layout : FivefoldFrontModule.PhaseLayout phaseCount source guessPhase
      firstPhase secondPhase thirdPhase fourthPhase fifthPhase markerTwoPhase)
    (handoffBound : handoff < phaseCount) (outputBound : output < phaseCount)
    (endpointBound : endpointPhase < phaseCount)
    (handoffNotActive : handoff ∉
      [source, guessPhase, firstPhase, secondPhase, thirdPhase, fourthPhase,
        fifthPhase, markerTwoPhase])
    (outputNotActive : output ∉
      [source, guessPhase, firstPhase, secondPhase, thirdPhase, fourthPhase,
        fifthPhase, markerTwoPhase])
    (endpointNotActive : endpointPhase ∉
      [source, guessPhase, firstPhase, secondPhase, thirdPhase, fourthPhase,
        fifthPhase, markerTwoPhase])
    (handoffOutputDistinct : handoff ≠ output)
    (handoffEndpointDistinct : handoff ≠ endpointPhase)
    (outputEndpointDistinct : output ≠ endpointPhase)
    (endpointMembership : InPhaseAt prime endpointPhase endpointDigit endpoint)
    {word : List PhysicalTemplate}
    (wordOver : WordOver
      (singleAlphabet source handoff output guessPhase firstPhase secondPhase
        thirdPhase fourthPhase fifthPhase markerTwoPhase) word)
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
  apply singleWord_cannot_reach_foreign_phase_of_nonempty primeProperty
    primeBound layout handoffBound outputBound endpointBound handoffNotActive
    outputNotActive
  · intro internalMem
    apply endpointNotActive
    simp at internalMem ⊢
    grind
  · exact handoffOutputDistinct
  · exact handoffEndpointDistinct
  · exact outputEndpointDistinct
  · exact endpointMembership
  · exact wordOver
  · exact wordNonempty
  · exact allLocal
  · exact completeRun

end Mortality.Compiler.ValidatedFivefoldFrontModule
