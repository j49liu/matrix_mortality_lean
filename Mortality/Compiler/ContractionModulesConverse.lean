import Mortality.Compiler.ContractionModules
import Mortality.Compiler.DoubleValidatedFivefoldConverse

/-!
# Unrestricted-word converses for the contraction modules

The front and projection alphabets use disjoint source-phase sets.  Cutting
at the first letter from the other module then turns arbitrary interleavings
into the already checked module converses.
-/

namespace Mortality.Compiler.ContractionModules

open Mortality.Compiler
open Mortality.PeriodicCode
open Mortality.Compiler.UnaryArithmetic
open Mortality.Compiler.ValidatedFivefoldFrontModule

def PhaseDisjoint (first second : List Nat) : Prop :=
  ∀ {phase : Nat}, phase ∈ first → phase ∈ second → False

theorem PhaseDisjoint.not_second
    {first second : List Nat} (disjoint : PhaseDisjoint first second)
    {phase : Nat} (phaseFirst : phase ∈ first) : phase ∉ second :=
  fun phaseSecond => disjoint phaseFirst phaseSecond

theorem PhaseDisjoint.not_first
    {first second : List Nat} (disjoint : PhaseDisjoint first second)
    {phase : Nat} (phaseSecond : phase ∈ second) : phase ∉ first :=
  fun phaseFirst => disjoint phaseFirst phaseSecond

def threeProjectionSourcePhases (source firstGuess secondGuess negativePhase
    firstValidator secondValidator thirdValidator : Nat) : List Nat :=
  [source, firstGuess, secondGuess, negativePhase, firstValidator,
    secondValidator, thirdValidator]

theorem threeProjectionLetter_source_mem
    {source target firstGuess secondGuess negativePhase firstValidator
      secondValidator thirdValidator : Nat} {letter : PhysicalTemplate}
    (letterMem : letter ∈ ThreeProjectionModule.alphabet source target
      firstGuess secondGuess negativePhase firstValidator secondValidator
      thirdValidator) :
    letter.sourcePhase ∈ threeProjectionSourcePhases source firstGuess
      secondGuess negativePhase firstValidator secondValidator
      thirdValidator := by
  simpa [threeProjectionSourcePhases] using
    (ThreeProjectionModule.letter_source_mem_active letterMem)

def twoProjectionSourcePhases (source guessPhase negativePhase firstValidator
    secondValidator : Nat) : List Nat :=
  [source, guessPhase, negativePhase, firstValidator, secondValidator]

theorem twoProjectionLetter_source_mem
    {source target guessPhase negativePhase firstValidator secondValidator : Nat}
    {letter : PhysicalTemplate}
    (letterMem : letter ∈ TwoProjectionModule.alphabet source target
      guessPhase negativePhase firstValidator secondValidator) :
    letter.sourcePhase ∈ twoProjectionSourcePhases source guessPhase
      negativePhase firstValidator secondValidator := by
  simpa [twoProjectionSourcePhases] using
    (TwoProjectionModule.letter_source_mem_active letterMem)

/-- A nonempty path through the three-to-one contraction forces the complete
canonical block and returns the unconsumed suffix at the declared target. -/
theorem threeWord_forces_prefix_general_to_endpoint_of_nonempty
    {prime phaseCount source frontHandoff projectionInput target frontGuess
      frontFirst frontSecond frontThird frontFourth frontFifth frontMarker
      firstGuess secondGuess negativePhase firstValidator secondValidator
      thirdValidator endpointPhase counter : Nat}
    {endpointDigit : Int} {endpoint : Vec2}
    (primeProperty : IsPrime prime) (primeBound : 6 * phaseCount < prime)
    (frontLayout : FivefoldFrontModule.PhaseLayout phaseCount source frontGuess
      frontFirst frontSecond frontThird frontFourth frontFifth frontMarker)
    (projectionLayout : ThreeProjectionModule.PhaseLayout phaseCount
      projectionInput firstGuess secondGuess negativePhase firstValidator
      secondValidator thirdValidator)
    (frontHandoffBound : frontHandoff < phaseCount)
    (targetBound : target < phaseCount)
    (endpointBound : endpointPhase < phaseCount)
    (frontHandoffNotCore : frontHandoff ∉
      [source, frontGuess, frontFirst, frontSecond, frontThird, frontFourth,
        frontFifth, frontMarker])
    (frontProjectionDisjoint : PhaseDisjoint
      (singleSourcePhases source frontHandoff frontGuess frontFirst frontSecond
        frontThird frontFourth frontFifth frontMarker)
      (threeProjectionSourcePhases projectionInput firstGuess secondGuess
        negativePhase firstValidator secondValidator thirdValidator))
    (targetNotFront : target ∉
      singleSourcePhases source frontHandoff frontGuess frontFirst frontSecond
        frontThird frontFourth frontFifth frontMarker)
    (targetNotProjection : target ∉
      threeProjectionSourcePhases projectionInput firstGuess secondGuess
        negativePhase firstValidator secondValidator thirdValidator)
    (endpointNotFrontInternal : endpointPhase ∉
      [frontHandoff, frontGuess, frontFirst, frontSecond, frontThird,
        frontFourth, frontFifth, frontMarker])
    (endpointNotProjection : endpointPhase ∉
      threeProjectionSourcePhases projectionInput firstGuess secondGuess
        negativePhase firstValidator secondValidator thirdValidator)
    (endpointMembership : InPhaseAt prime endpointPhase endpointDigit endpoint)
    (counterPositive : 0 < counter)
    {word : List PhysicalTemplate}
    (wordOver : WordOver
      (threeAlphabet source frontHandoff projectionInput target frontGuess
        frontFirst frontSecond frontThird frontFourth frontFifth frontMarker
        firstGuess secondGuess negativePhase firstValidator secondValidator
        thirdValidator) word)
    (wordNonempty : word ≠ [])
    (allLocal : AllStatesLocal prime word
      (phaseAffine source (unaryCode prime counter)))
    (completeRun : SameLine
      (physicalWordAction prime word
        (phaseAffine source (unaryCode prime counter)))
      endpoint) :
    ∃ first residual,
      counter = 5 * first + 4 ∧
      word = threeWord source frontHandoff projectionInput target frontGuess
          frontFirst frontSecond frontThird frontFourth frontFifth frontMarker
          firstGuess secondGuess negativePhase firstValidator secondValidator
          thirdValidator first ++ residual ∧
      WordOver
        (threeAlphabet source frontHandoff projectionInput target frontGuess
          frontFirst frontSecond frontThird frontFourth frontFifth frontMarker
          firstGuess secondGuess negativePhase firstValidator secondValidator
          thirdValidator) residual ∧
      AllStatesLocal prime residual
        (phaseAffine target (unaryCode prime (3 * first + 2))) ∧
      SameLine
        (physicalWordAction prime residual
          (phaseAffine target (unaryCode prime (3 * first + 2))))
        endpoint := by
  let frontAlphabet := singleAlphabet source frontHandoff projectionInput
    frontGuess frontFirst frontSecond frontThird frontFourth frontFifth
    frontMarker
  let projectionAlphabet := ThreeProjectionModule.alphabet projectionInput
    target firstGuess secondGuess negativePhase firstValidator secondValidator
    thirdValidator
  have unionOver : WordOver (frontAlphabet ++ projectionAlphabet) word := by
    simpa [frontAlphabet, projectionAlphabet, threeAlphabet] using wordOver
  have projectionInputActive : projectionInput ∈
      threeProjectionSourcePhases projectionInput firstGuess secondGuess
        negativePhase firstValidator secondValidator thirdValidator := by
    simp [threeProjectionSourcePhases]
  have projectionInputNotFront :=
    frontProjectionDisjoint.not_first projectionInputActive
  have projectionInputNotCore : projectionInput ∉
      [source, frontGuess, frontFirst, frontSecond, frontThird, frontFourth,
        frontFifth, frontMarker] := by
    intro coreMem
    apply projectionInputNotFront
    simp [singleSourcePhases] at coreMem ⊢
    grind
  have handoffProjectionInputDistinct : frontHandoff ≠ projectionInput := by
    intro phaseEq
    apply projectionInputNotFront
    simp [singleSourcePhases, phaseEq]
  have targetNotCore : target ∉
      [source, frontGuess, frontFirst, frontSecond, frontThird, frontFourth,
        frontFifth, frontMarker] := by
    intro coreMem
    apply targetNotFront
    simp [singleSourcePhases] at coreMem ⊢
    grind
  have handoffTargetDistinct : frontHandoff ≠ target := by
    intro phaseEq
    apply targetNotFront
    simp [singleSourcePhases, ← phaseEq]
  have projectionInputTargetDistinct : projectionInput ≠ target := by
    intro phaseEq
    apply targetNotProjection
    simp [threeProjectionSourcePhases, phaseEq]
  have endpointNotCore : endpointPhase ∉
      [frontGuess, frontFirst, frontSecond, frontThird, frontFourth,
        frontFifth, frontMarker] := by
    intro coreMem
    apply endpointNotFrontInternal
    simp at coreMem ⊢
    grind
  have handoffEndpointDistinct : frontHandoff ≠ endpointPhase := by
    intro phaseEq
    apply endpointNotFrontInternal
    simp [phaseEq]
  have projectionInputEndpointDistinct : projectionInput ≠ endpointPhase := by
    intro phaseEq
    apply endpointNotProjection
    simp [threeProjectionSourcePhases, phaseEq]
  have projectionEndpointNe {phase : Nat}
      (phaseMem : phase ∈ threeProjectionSourcePhases projectionInput
        firstGuess secondGuess negativePhase firstValidator secondValidator
        thirdValidator) : phase ≠ endpointPhase := by
    intro phaseEq
    apply endpointNotProjection
    simpa [phaseEq] using phaseMem
  rcases wordOver_append_first_right unionOver with frontOnly |
      ⟨initial, letter, suffix, wordEq, initialOver, letterProjection,
        suffixOver⟩
  · exact False.elim
      (singleWord_cannot_reach_foreign_phase_general_of_nonempty primeProperty
        primeBound frontLayout frontHandoffBound projectionLayout.sourceBound
        endpointBound frontHandoffNotCore projectionInputNotCore endpointNotCore
        handoffProjectionInputDistinct handoffEndpointDistinct
        projectionInputEndpointDistinct endpointMembership counterPositive
        frontOnly wordNonempty allLocal completeRun)
  · obtain ⟨initialLocal, boundaryLocal⟩ :=
      allLocal.split_append_cons wordEq
    have boundaryMembership : InPhaseAt prime letter.sourcePhase letter.digit
        (physicalWordAction prime initial
          (phaseAffine source (unaryCode prime counter))) := by
      apply physicalLetter_input_inPhaseAt primeProperty
        (ThreeProjectionModule.letter_reserved letterProjection)
        boundaryLocal.1
      simpa [PhysicalTemplate.act, PhysicalTemplate.matrix] using
        boundaryLocal.2.start
    have letterProjectionActive :=
      threeProjectionLetter_source_mem letterProjection
    by_cases sourceAtBoundary : letter.sourcePhase = projectionInput
    · rw [sourceAtBoundary] at boundaryMembership
      obtain ⟨first, counterEq, initialEq⟩ := singleWord_unique_general
        primeProperty primeBound frontLayout
        frontHandoffBound projectionLayout.sourceBound frontHandoffNotCore
        projectionInputNotCore handoffProjectionInputDistinct
        boundaryMembership counterPositive initialOver initialLocal
        (SameLine.refl _)
      have frontRun := singleWord_correct prime source frontHandoff
        projectionInput frontGuess frontFirst frontSecond frontThird
        frontFourth frontFifth frontMarker first primeProperty.1
      have boundarySame : SameLine
          (phaseAffine projectionInput
            (twoFieldCode prime first (3 * first + 2)))
          (physicalWordAction prime initial
            (phaseAffine source (unaryCode prime counter))) := by
        rw [counterEq, initialEq]
        exact frontRun.symm
      obtain ⟨inputDigit, inputMembership⟩ := twoFieldCode_inPhaseAt
        (phase := projectionInput) (first := first)
        (second := 3 * first + 2) primeProperty
      have tailOver : WordOver (frontAlphabet ++ projectionAlphabet)
          (letter :: suffix) := by
        intro candidate candidateMem
        simp only [List.mem_cons] at candidateMem
        rcases candidateMem with rfl | candidateMem
        · exact List.mem_append_right _ letterProjection
        · exact suffixOver candidate candidateMem
      have tailRun : SameLine
          (physicalWordAction prime (letter :: suffix)
            (physicalWordAction prime initial
              (phaseAffine source (unaryCode prime counter))))
          endpoint := by
        rw [wordEq, physicalWordAction_append] at completeRun
        exact completeRun
      have canonicalTailLocal : AllStatesLocal prime (letter :: suffix)
          (phaseAffine projectionInput
            (twoFieldCode prime first (3 * first + 2))) :=
        boundaryLocal.of_sameLine (by omega) inputMembership.local.1
          boundarySame
      have canonicalTailRun : SameLine
          (physicalWordAction prime (letter :: suffix)
            (phaseAffine projectionInput
              (twoFieldCode prime first (3 * first + 2))))
          endpoint :=
        (physicalWordAction_preserves_sameLine prime (letter :: suffix)
          boundarySame).trans tailRun
      have reordered : WordOver (projectionAlphabet ++ frontAlphabet)
          (letter :: suffix) := by
        intro candidate candidateMem
        have membership := tailOver candidate candidateMem
        simp only [List.mem_append] at membership ⊢
        exact membership.symm
      obtain ⟨residual, tailEq, residualProjectionOver, residualLocal,
          residualRun⟩ :
          ∃ residual,
            letter :: suffix =
                ThreeProjectionModule.acceptedWord projectionInput target
                    firstGuess secondGuess negativePhase firstValidator
                    secondValidator thirdValidator first ++ residual ∧
              WordOver projectionAlphabet residual ∧
              AllStatesLocal prime residual
                (phaseAffine target
                  (unaryCode prime (3 * first + 2))) ∧
              SameLine
                (physicalWordAction prime residual
                  (phaseAffine target
                    (unaryCode prime (3 * first + 2)))) endpoint := by
        rcases wordOver_append_first_right reordered with projectionOnly |
            ⟨projectionPrefix, frontLetter, rest, tailWordEq,
              projectionPrefixOver, frontLetterMem, _⟩
        · exact ThreeProjectionModule.completedPath_forces_accepted_prefix
            primeProperty primeBound projectionLayout endpointBound
            (projectionEndpointNe (by simp [threeProjectionSourcePhases]))
            (projectionEndpointNe (by simp [threeProjectionSourcePhases]))
            (projectionEndpointNe (by simp [threeProjectionSourcePhases]))
            (projectionEndpointNe (by simp [threeProjectionSourcePhases]))
            (projectionEndpointNe (by simp [threeProjectionSourcePhases]))
            (projectionEndpointNe (by simp [threeProjectionSourcePhases]))
            (projectionEndpointNe (by simp [threeProjectionSourcePhases]))
            endpointMembership projectionOnly canonicalTailLocal
            canonicalTailRun
        · obtain ⟨projectionPrefixLocal, frontBoundaryLocal⟩ :=
            canonicalTailLocal.split_append_cons tailWordEq
          have frontBoundaryMembership : InPhaseAt prime
              frontLetter.sourcePhase frontLetter.digit
              (physicalWordAction prime projectionPrefix
                (phaseAffine projectionInput
                  (twoFieldCode prime first
                    (3 * first + 2)))) := by
            apply physicalLetter_input_inPhaseAt primeProperty
              (singleLetter_reserved frontLetterMem)
              frontBoundaryLocal.1
            simpa [PhysicalTemplate.act, PhysicalTemplate.matrix] using
              frontBoundaryLocal.2.start
          have frontSourceActive := singleLetter_source_mem frontLetterMem
          have frontSourceNotProjection :=
            frontProjectionDisjoint.not_second frontSourceActive
          have targetFrontDistinct : target ≠ frontLetter.sourcePhase := by
            intro phaseEq
            apply targetNotFront
            simpa [phaseEq] using frontSourceActive
          exact False.elim
            (ThreeProjectionModule.completedPath_cannot_reach_foreign_phase
              primeProperty primeBound projectionLayout targetBound
              (singleLetter_source_bound frontLayout frontHandoffBound
                frontLetterMem)
              targetNotProjection frontSourceNotProjection
              targetFrontDistinct frontBoundaryMembership
              projectionPrefixOver projectionPrefixLocal (SameLine.refl _))
      refine ⟨first, residual, counterEq, ?_, ?_, residualLocal, residualRun⟩
      · rw [wordEq, initialEq, tailEq]
        simp [threeWord, List.append_assoc]
      · intro candidate candidateMem
        exact List.mem_append_right frontAlphabet
          (residualProjectionOver candidate candidateMem)
    · have boundaryNotCore : letter.sourcePhase ∉
          [source, frontGuess, frontFirst, frontSecond, frontThird,
            frontFourth, frontFifth, frontMarker] := by
        intro coreMem
        have frontMem : letter.sourcePhase ∈
            singleSourcePhases source frontHandoff frontGuess frontFirst
              frontSecond frontThird frontFourth frontFifth frontMarker := by
          simp [singleSourcePhases] at coreMem ⊢
          grind
        exact frontProjectionDisjoint frontMem letterProjectionActive
      have handoffBoundaryDistinct : frontHandoff ≠ letter.sourcePhase := by
        intro phaseEq
        apply frontProjectionDisjoint
          (show frontHandoff ∈ singleSourcePhases source frontHandoff
            frontGuess frontFirst frontSecond frontThird frontFourth
            frontFifth frontMarker by simp [singleSourcePhases])
          (by simpa [phaseEq] using letterProjectionActive)
      have outputBoundaryDistinct : projectionInput ≠ letter.sourcePhase := by
        exact fun phaseEq => sourceAtBoundary phaseEq.symm
      obtain ⟨sourceDigit, sourceMembership⟩ := unaryCode_inPhaseAt
        (base := prime) (phase := source) (counter := counter) primeProperty.1
      have initialNonempty : initial ≠ [] := by
        intro initialEmpty
        subst initial
        have sourceBoundaryDistinct : source ≠ letter.sourcePhase := by
          intro phaseEq
          exact boundaryNotCore (by simp [← phaseEq])
        have phaseEq := (sourceMembership.unique primeProperty primeBound
          frontLayout.sourceBound
          (ThreeProjectionModule.letter_source_bound projectionLayout
            letterProjection)
          boundaryMembership (SameLine.refl _)).1
        exact sourceBoundaryDistinct phaseEq
      exact False.elim
        (singleWord_cannot_reach_foreign_phase_general_of_nonempty
          primeProperty primeBound
          frontLayout frontHandoffBound projectionLayout.sourceBound
          (ThreeProjectionModule.letter_source_bound projectionLayout
            letterProjection)
          frontHandoffNotCore projectionInputNotCore
          (by
            intro internalMem
            apply boundaryNotCore
            simp at internalMem ⊢
            grind)
          handoffProjectionInputDistinct handoffBoundaryDistinct
          outputBoundaryDistinct boundaryMembership counterPositive initialOver
          initialNonempty initialLocal (SameLine.refl _))

/-- A nonempty path through the two-to-one contraction forces the complete
canonical block and returns the unconsumed suffix at the declared target. -/
theorem twoWord_forces_prefix_general_to_endpoint_of_nonempty
    {prime phaseCount source frontHandoff subtractionIntermediate
      projectionInput target frontGuess frontFirst frontSecond frontThird
      frontFourth frontFifth frontMarker projectionGuess projectionNegative
      projectionFirstValidator projectionSecondValidator endpointPhase
      counter : Nat}
    {endpointDigit : Int} {endpoint : Vec2}
    (primeProperty : IsPrime prime) (primeBound : 6 * phaseCount < prime)
    (frontLayout : FivefoldFrontModule.PhaseLayout phaseCount source frontGuess
      frontFirst frontSecond frontThird frontFourth frontFifth frontMarker)
    (projectionLayout : TwoProjectionModule.PhaseLayout phaseCount
      projectionInput projectionGuess projectionNegative
      projectionFirstValidator projectionSecondValidator)
    (frontHandoffBound : frontHandoff < phaseCount)
    (subtractionIntermediateBound : subtractionIntermediate < phaseCount)
    (targetBound : target < phaseCount)
    (endpointBound : endpointPhase < phaseCount)
    (frontHandoffNotCore : frontHandoff ∉
      [source, frontGuess, frontFirst, frontSecond, frontThird, frontFourth,
        frontFifth, frontMarker])
    (subtractionIntermediateNotCore : subtractionIntermediate ∉
      [source, frontGuess, frontFirst, frontSecond, frontThird, frontFourth,
        frontFifth, frontMarker])
    (frontInternalDistinct : frontHandoff ≠ subtractionIntermediate)
    (frontProjectionDisjoint : PhaseDisjoint
      (doubleSourcePhases source frontHandoff subtractionIntermediate
        frontGuess frontFirst frontSecond frontThird frontFourth frontFifth
        frontMarker)
      (twoProjectionSourcePhases projectionInput projectionGuess
        projectionNegative projectionFirstValidator projectionSecondValidator))
    (targetNotFront : target ∉
      doubleSourcePhases source frontHandoff subtractionIntermediate frontGuess
        frontFirst frontSecond frontThird frontFourth frontFifth frontMarker)
    (targetNotProjection : target ∉
      twoProjectionSourcePhases projectionInput projectionGuess
        projectionNegative projectionFirstValidator projectionSecondValidator)
    (endpointNotFrontInternal : endpointPhase ∉
      [frontHandoff, subtractionIntermediate, frontGuess, frontFirst,
        frontSecond, frontThird, frontFourth, frontFifth, frontMarker])
    (endpointNotProjection : endpointPhase ∉
      twoProjectionSourcePhases projectionInput projectionGuess
        projectionNegative projectionFirstValidator projectionSecondValidator)
    (endpointMembership : InPhaseAt prime endpointPhase endpointDigit endpoint)
    (counterPositive : 0 < counter)
    {word : List PhysicalTemplate}
    (wordOver : WordOver
      (twoAlphabet source frontHandoff subtractionIntermediate projectionInput
        target frontGuess frontFirst frontSecond frontThird frontFourth
        frontFifth frontMarker projectionGuess projectionNegative
        projectionFirstValidator projectionSecondValidator) word)
    (wordNonempty : word ≠ [])
    (allLocal : AllStatesLocal prime word
      (phaseAffine source (unaryCode prime counter)))
    (completeRun : SameLine
      (physicalWordAction prime word
        (phaseAffine source (unaryCode prime counter)))
      endpoint) :
    ∃ first residual,
      counter = 5 * first + 4 ∧
      word = twoWord source frontHandoff subtractionIntermediate
          projectionInput target frontGuess frontFirst frontSecond frontThird
          frontFourth frontFifth frontMarker projectionGuess projectionNegative
          projectionFirstValidator projectionSecondValidator first ++
        residual ∧
      WordOver
        (twoAlphabet source frontHandoff subtractionIntermediate projectionInput
          target frontGuess frontFirst frontSecond frontThird frontFourth
          frontFifth frontMarker projectionGuess projectionNegative
          projectionFirstValidator projectionSecondValidator) residual ∧
      AllStatesLocal prime residual
        (phaseAffine target (unaryCode prime (2 * first + 1))) ∧
      SameLine
        (physicalWordAction prime residual
          (phaseAffine target (unaryCode prime (2 * first + 1))))
        endpoint := by
  let frontAlphabet := doubleAlphabet source frontHandoff
    subtractionIntermediate projectionInput frontGuess frontFirst frontSecond
    frontThird frontFourth frontFifth frontMarker
  let projectionAlphabet := TwoProjectionModule.alphabet projectionInput target
    projectionGuess projectionNegative projectionFirstValidator
    projectionSecondValidator
  have unionOver : WordOver (frontAlphabet ++ projectionAlphabet) word := by
    simpa [frontAlphabet, projectionAlphabet, twoAlphabet] using wordOver
  have projectionInputActive : projectionInput ∈
      twoProjectionSourcePhases projectionInput projectionGuess
        projectionNegative projectionFirstValidator projectionSecondValidator := by
    simp [twoProjectionSourcePhases]
  have projectionInputNotFront :=
    frontProjectionDisjoint.not_first projectionInputActive
  have projectionInputNotCore : projectionInput ∉
      [source, frontGuess, frontFirst, frontSecond, frontThird, frontFourth,
        frontFifth, frontMarker] := by
    intro coreMem
    apply projectionInputNotFront
    simp [doubleSourcePhases] at coreMem ⊢
    grind
  have handoffProjectionInputDistinct : frontHandoff ≠ projectionInput := by
    intro phaseEq
    apply projectionInputNotFront
    simp [doubleSourcePhases, phaseEq]
  have intermediateProjectionInputDistinct :
      subtractionIntermediate ≠ projectionInput := by
    intro phaseEq
    apply projectionInputNotFront
    simp [doubleSourcePhases, phaseEq]
  have targetNotCore : target ∉
      [source, frontGuess, frontFirst, frontSecond, frontThird, frontFourth,
        frontFifth, frontMarker] := by
    intro coreMem
    apply targetNotFront
    simp [doubleSourcePhases] at coreMem ⊢
    grind
  have handoffTargetDistinct : frontHandoff ≠ target := by
    intro phaseEq
    apply targetNotFront
    simp [doubleSourcePhases, ← phaseEq]
  have intermediateTargetDistinct : subtractionIntermediate ≠ target := by
    intro phaseEq
    apply targetNotFront
    simp [doubleSourcePhases, ← phaseEq]
  have projectionInputTargetDistinct : projectionInput ≠ target := by
    intro phaseEq
    apply targetNotProjection
    simp [twoProjectionSourcePhases, phaseEq]
  have endpointNotCore : endpointPhase ∉
      [frontGuess, frontFirst, frontSecond, frontThird, frontFourth,
        frontFifth, frontMarker] := by
    intro coreMem
    apply endpointNotFrontInternal
    simp at coreMem ⊢
    grind
  have handoffEndpointDistinct : frontHandoff ≠ endpointPhase := by
    intro phaseEq
    apply endpointNotFrontInternal
    simp [phaseEq]
  have intermediateEndpointDistinct :
      subtractionIntermediate ≠ endpointPhase := by
    intro phaseEq
    apply endpointNotFrontInternal
    simp [phaseEq]
  have projectionInputEndpointDistinct : projectionInput ≠ endpointPhase := by
    intro phaseEq
    apply endpointNotProjection
    simp [twoProjectionSourcePhases, phaseEq]
  have projectionEndpointNe {phase : Nat}
      (phaseMem : phase ∈ twoProjectionSourcePhases projectionInput
        projectionGuess projectionNegative projectionFirstValidator
        projectionSecondValidator) : phase ≠ endpointPhase := by
    intro phaseEq
    apply endpointNotProjection
    simpa [phaseEq] using phaseMem
  rcases wordOver_append_first_right unionOver with frontOnly |
      ⟨initial, letter, suffix, wordEq, initialOver, letterProjection,
        suffixOver⟩
  · exact False.elim
      (doubleWord_cannot_reach_foreign_phase_general_of_nonempty
        primeProperty primeBound
        frontLayout frontHandoffBound subtractionIntermediateBound
        projectionLayout.sourceBound endpointBound frontHandoffNotCore
        subtractionIntermediateNotCore projectionInputNotCore endpointNotCore
        frontInternalDistinct handoffProjectionInputDistinct
        intermediateProjectionInputDistinct handoffEndpointDistinct
        intermediateEndpointDistinct projectionInputEndpointDistinct
        endpointMembership counterPositive frontOnly wordNonempty allLocal
        completeRun)
  · obtain ⟨initialLocal, boundaryLocal⟩ :=
      allLocal.split_append_cons wordEq
    have boundaryMembership : InPhaseAt prime letter.sourcePhase letter.digit
        (physicalWordAction prime initial
          (phaseAffine source (unaryCode prime counter))) := by
      apply physicalLetter_input_inPhaseAt primeProperty
        (TwoProjectionModule.public_letter_reserved letterProjection)
        boundaryLocal.1
      simpa [PhysicalTemplate.act, PhysicalTemplate.matrix] using
        boundaryLocal.2.start
    have letterProjectionActive :=
      twoProjectionLetter_source_mem letterProjection
    by_cases sourceAtBoundary : letter.sourcePhase = projectionInput
    · rw [sourceAtBoundary] at boundaryMembership
      obtain ⟨first, counterEq, initialEq⟩ := doubleWord_unique_general
        primeProperty primeBound frontLayout
        frontHandoffBound subtractionIntermediateBound
        projectionLayout.sourceBound frontHandoffNotCore
        subtractionIntermediateNotCore projectionInputNotCore
        frontInternalDistinct handoffProjectionInputDistinct
        intermediateProjectionInputDistinct boundaryMembership counterPositive
        initialOver initialLocal (SameLine.refl _)
      have frontRun := doubleWord_correct prime source frontHandoff
        subtractionIntermediate projectionInput frontGuess frontFirst
        frontSecond frontThird frontFourth frontFifth frontMarker first
        primeProperty.1
      have boundarySame : SameLine
          (phaseAffine projectionInput
            (twoFieldCode prime first (2 * first + 1)))
          (physicalWordAction prime initial
            (phaseAffine source (unaryCode prime counter))) := by
        rw [counterEq, initialEq]
        exact frontRun.symm
      obtain ⟨inputDigit, inputMembership⟩ := twoFieldCode_inPhaseAt
        (phase := projectionInput) (first := first)
        (second := 2 * first + 1) primeProperty
      have tailOver : WordOver (frontAlphabet ++ projectionAlphabet)
          (letter :: suffix) := by
        intro candidate candidateMem
        simp only [List.mem_cons] at candidateMem
        rcases candidateMem with rfl | candidateMem
        · exact List.mem_append_right _ letterProjection
        · exact suffixOver candidate candidateMem
      have tailRun : SameLine
          (physicalWordAction prime (letter :: suffix)
            (physicalWordAction prime initial
              (phaseAffine source (unaryCode prime counter))))
          endpoint := by
        rw [wordEq, physicalWordAction_append] at completeRun
        exact completeRun
      have canonicalTailLocal : AllStatesLocal prime (letter :: suffix)
          (phaseAffine projectionInput
            (twoFieldCode prime first (2 * first + 1))) :=
        boundaryLocal.of_sameLine (by omega) inputMembership.local.1
          boundarySame
      have canonicalTailRun : SameLine
          (physicalWordAction prime (letter :: suffix)
            (phaseAffine projectionInput
              (twoFieldCode prime first (2 * first + 1))))
          endpoint :=
        (physicalWordAction_preserves_sameLine prime (letter :: suffix)
          boundarySame).trans tailRun
      have reordered : WordOver (projectionAlphabet ++ frontAlphabet)
          (letter :: suffix) := by
        intro candidate candidateMem
        have membership := tailOver candidate candidateMem
        simp only [List.mem_append] at membership ⊢
        exact membership.symm
      obtain ⟨residual, tailEq, residualProjectionOver, residualLocal,
          residualRun⟩ :
          ∃ residual,
            letter :: suffix =
                TwoProjectionModule.acceptedWord projectionInput target
                    projectionGuess projectionNegative
                    projectionFirstValidator projectionSecondValidator
                    first ++ residual ∧
              WordOver projectionAlphabet residual ∧
              AllStatesLocal prime residual
                (phaseAffine target
                  (unaryCode prime (2 * first + 1))) ∧
              SameLine
                (physicalWordAction prime residual
                  (phaseAffine target
                    (unaryCode prime (2 * first + 1)))) endpoint := by
        rcases wordOver_append_first_right reordered with projectionOnly |
            ⟨projectionPrefix, frontLetter, rest, tailWordEq,
              projectionPrefixOver, frontLetterMem, _⟩
        · exact TwoProjectionModule.completedPath_forces_accepted_prefix
            primeProperty primeBound projectionLayout endpointBound
            (projectionEndpointNe (by simp [twoProjectionSourcePhases]))
            (projectionEndpointNe (by simp [twoProjectionSourcePhases]))
            (projectionEndpointNe (by simp [twoProjectionSourcePhases]))
            (projectionEndpointNe (by simp [twoProjectionSourcePhases]))
            (projectionEndpointNe (by simp [twoProjectionSourcePhases]))
            endpointMembership projectionOnly canonicalTailLocal
            canonicalTailRun
        · obtain ⟨projectionPrefixLocal, frontBoundaryLocal⟩ :=
            canonicalTailLocal.split_append_cons tailWordEq
          have frontBoundaryMembership : InPhaseAt prime
              frontLetter.sourcePhase frontLetter.digit
              (physicalWordAction prime projectionPrefix
                (phaseAffine projectionInput
                  (twoFieldCode prime first
                    (2 * first + 1)))) := by
            apply physicalLetter_input_inPhaseAt primeProperty
              (doubleLetter_reserved frontLetterMem)
              frontBoundaryLocal.1
            simpa [PhysicalTemplate.act, PhysicalTemplate.matrix] using
              frontBoundaryLocal.2.start
          have frontSourceActive := doubleLetter_source_mem frontLetterMem
          have frontSourceNotProjection :=
            frontProjectionDisjoint.not_second frontSourceActive
          have targetFrontDistinct : target ≠ frontLetter.sourcePhase := by
            intro phaseEq
            apply targetNotFront
            simpa [phaseEq] using frontSourceActive
          exact False.elim
            (TwoProjectionModule.completedPath_cannot_reach_foreign_phase
              primeProperty primeBound projectionLayout targetBound
              (doubleLetter_source_bound frontLayout frontHandoffBound
                subtractionIntermediateBound frontLetterMem)
              targetNotProjection frontSourceNotProjection
              targetFrontDistinct frontBoundaryMembership
              projectionPrefixOver projectionPrefixLocal (SameLine.refl _))
      refine ⟨first, residual, counterEq, ?_, ?_, residualLocal, residualRun⟩
      · rw [wordEq, initialEq, tailEq]
        simp [twoWord, List.append_assoc]
      · intro candidate candidateMem
        exact List.mem_append_right frontAlphabet
          (residualProjectionOver candidate candidateMem)
    · have boundaryNotCore : letter.sourcePhase ∉
          [source, frontGuess, frontFirst, frontSecond, frontThird,
            frontFourth, frontFifth, frontMarker] := by
        intro coreMem
        have frontMem : letter.sourcePhase ∈
            doubleSourcePhases source frontHandoff subtractionIntermediate
              frontGuess frontFirst frontSecond frontThird frontFourth
              frontFifth frontMarker := by
          simp [doubleSourcePhases] at coreMem ⊢
          grind
        exact frontProjectionDisjoint frontMem letterProjectionActive
      have handoffBoundaryDistinct : frontHandoff ≠ letter.sourcePhase := by
        intro phaseEq
        apply frontProjectionDisjoint
          (show frontHandoff ∈ doubleSourcePhases source frontHandoff
            subtractionIntermediate frontGuess frontFirst frontSecond
            frontThird frontFourth frontFifth frontMarker by
              simp [doubleSourcePhases])
          (by simpa [phaseEq] using letterProjectionActive)
      have intermediateBoundaryDistinct :
          subtractionIntermediate ≠ letter.sourcePhase := by
        intro phaseEq
        apply frontProjectionDisjoint
          (show subtractionIntermediate ∈ doubleSourcePhases source
            frontHandoff subtractionIntermediate frontGuess frontFirst
            frontSecond frontThird frontFourth frontFifth frontMarker by
              simp [doubleSourcePhases])
          (by simpa [phaseEq] using letterProjectionActive)
      have outputBoundaryDistinct : projectionInput ≠ letter.sourcePhase :=
        fun phaseEq => sourceAtBoundary phaseEq.symm
      obtain ⟨sourceDigit, sourceMembership⟩ := unaryCode_inPhaseAt
        (base := prime) (phase := source) (counter := counter) primeProperty.1
      have initialNonempty : initial ≠ [] := by
        intro initialEmpty
        subst initial
        have sourceBoundaryDistinct : source ≠ letter.sourcePhase := by
          intro phaseEq
          exact boundaryNotCore (by simp [← phaseEq])
        have phaseEq := (sourceMembership.unique primeProperty primeBound
          frontLayout.sourceBound
          (TwoProjectionModule.public_letter_source_bound projectionLayout
            letterProjection)
          boundaryMembership (SameLine.refl _)).1
        exact sourceBoundaryDistinct phaseEq
      exact False.elim
        (doubleWord_cannot_reach_foreign_phase_general_of_nonempty
          primeProperty primeBound
          frontLayout frontHandoffBound subtractionIntermediateBound
          projectionLayout.sourceBound
          (TwoProjectionModule.public_letter_source_bound projectionLayout
            letterProjection)
          frontHandoffNotCore subtractionIntermediateNotCore
          projectionInputNotCore
          (by
            intro internalMem
            apply boundaryNotCore
            simp at internalMem ⊢
            grind)
          frontInternalDistinct
          handoffProjectionInputDistinct intermediateProjectionInputDistinct
          handoffBoundaryDistinct intermediateBoundaryDistinct
          outputBoundaryDistinct boundaryMembership counterPositive initialOver
          initialNonempty initialLocal (SameLine.refl _))

end Mortality.Compiler.ContractionModules
