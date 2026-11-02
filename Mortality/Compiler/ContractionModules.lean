import Mortality.Compiler.ValidatedFivefoldFrontModule
import Mortality.Compiler.TwoProjectionModule
import Mortality.Compiler.ThreeProjectionModule

/-!
# The thirty- and thirty-two-letter contraction modules

This file composes the validated fivefold fronts with the two checked typed
projections.  The unrestricted-word converses are developed separately; the
theorems here close the exact alphabets, lengths, actions, and prefix locality
of both accepted executions.
-/

namespace Mortality.Compiler.ContractionModules

open Mortality.Compiler
open Mortality.PeriodicCode
open Mortality.Compiler.UnaryArithmetic
open Mortality.Compiler.IncrementModule
open Mortality.Compiler.ValidatedFivefoldFrontModule

def twoAlphabet
    (source frontHandoff subtractionIntermediate projectionInput target
      frontGuess frontFirst frontSecond frontThird frontFourth frontFifth
      frontMarker projectionGuess projectionNegative projectionFirstValidator
      projectionSecondValidator : Nat) : List PhysicalTemplate :=
  doubleAlphabet source frontHandoff subtractionIntermediate projectionInput
      frontGuess frontFirst frontSecond frontThird frontFourth frontFifth
      frontMarker ++
    TwoProjectionModule.alphabet projectionInput target projectionGuess
      projectionNegative projectionFirstValidator projectionSecondValidator

def twoWord
    (source frontHandoff subtractionIntermediate projectionInput target
      frontGuess frontFirst frontSecond frontThird frontFourth frontFifth
      frontMarker projectionGuess projectionNegative projectionFirstValidator
      projectionSecondValidator first : Nat) : List PhysicalTemplate :=
  doubleWord source frontHandoff subtractionIntermediate projectionInput
      frontGuess frontFirst frontSecond frontThird frontFourth frontFifth
      frontMarker first ++
    TwoProjectionModule.acceptedWord projectionInput target projectionGuess
      projectionNegative projectionFirstValidator projectionSecondValidator
      first

@[simp] theorem twoAlphabet_length
    (source frontHandoff subtractionIntermediate projectionInput target
      frontGuess frontFirst frontSecond frontThird frontFourth frontFifth
      frontMarker projectionGuess projectionNegative projectionFirstValidator
      projectionSecondValidator : Nat) :
    (twoAlphabet source frontHandoff subtractionIntermediate projectionInput
      target frontGuess frontFirst frontSecond frontThird frontFourth
      frontFifth frontMarker projectionGuess projectionNegative
      projectionFirstValidator projectionSecondValidator).length = 30 := by
  simp [twoAlphabet]

@[simp] theorem twoWord_length
    (source frontHandoff subtractionIntermediate projectionInput target
      frontGuess frontFirst frontSecond frontThird frontFourth frontFifth
      frontMarker projectionGuess projectionNegative projectionFirstValidator
      projectionSecondValidator first : Nat) :
    (twoWord source frontHandoff subtractionIntermediate projectionInput target
      frontGuess frontFirst frontSecond frontThird frontFourth frontFifth
      frontMarker projectionGuess projectionNegative projectionFirstValidator
      projectionSecondValidator first).length = 19 * first + 19 := by
  simp [twoWord]
  omega

theorem twoWord_wordOver
    (source frontHandoff subtractionIntermediate projectionInput target
      frontGuess frontFirst frontSecond frontThird frontFourth frontFifth
      frontMarker projectionGuess projectionNegative projectionFirstValidator
      projectionSecondValidator first : Nat) :
    WordOver
      (twoAlphabet source frontHandoff subtractionIntermediate projectionInput
        target frontGuess frontFirst frontSecond frontThird frontFourth
        frontFifth frontMarker projectionGuess projectionNegative
        projectionFirstValidator projectionSecondValidator)
      (twoWord source frontHandoff subtractionIntermediate projectionInput
        target frontGuess frontFirst frontSecond frontThird frontFourth
        frontFifth frontMarker projectionGuess projectionNegative
        projectionFirstValidator projectionSecondValidator first) := by
  intro letter letterMem
  simp only [twoWord, List.mem_append] at letterMem
  rcases letterMem with frontMem | projectionMem
  · exact List.mem_append_left _
      (doubleWord_wordOver source frontHandoff subtractionIntermediate
        projectionInput frontGuess frontFirst frontSecond frontThird
        frontFourth frontFifth frontMarker first letter frontMem)
  · exact List.mem_append_right _
      (TwoProjectionModule.acceptedWord_wordOver projectionInput target
        projectionGuess projectionNegative projectionFirstValidator
        projectionSecondValidator first letter projectionMem)

theorem twoWord_correct
    (base source frontHandoff subtractionIntermediate projectionInput target
      frontGuess frontFirst frontSecond frontThird frontFourth frontFifth
      frontMarker projectionGuess projectionNegative projectionFirstValidator
      projectionSecondValidator first : Nat)
    (baseAtLeastTwo : 2 ≤ base) :
    SameLine
      (physicalWordAction base
        (twoWord source frontHandoff subtractionIntermediate projectionInput
          target frontGuess frontFirst frontSecond frontThird frontFourth
          frontFifth frontMarker projectionGuess projectionNegative
          projectionFirstValidator projectionSecondValidator first)
        (phaseAffine source (unaryCode base (5 * first + 4))))
      (phaseAffine target (unaryCode base (2 * first + 1))) := by
  have frontRun := doubleWord_correct base source frontHandoff
    subtractionIntermediate projectionInput frontGuess frontFirst frontSecond
    frontThird frontFourth frontFifth frontMarker first baseAtLeastTwo
  have projectionRun := TwoProjectionModule.acceptedWord_correct base
    projectionInput target projectionGuess projectionNegative
    projectionFirstValidator projectionSecondValidator first baseAtLeastTwo
  have combined := physicalWordAction_append_sameLine base
    (doubleWord source frontHandoff subtractionIntermediate projectionInput
      frontGuess frontFirst frontSecond frontThird frontFourth frontFifth
      frontMarker first)
    (TwoProjectionModule.acceptedWord projectionInput target projectionGuess
      projectionNegative projectionFirstValidator projectionSecondValidator
      first) frontRun projectionRun
  simpa [twoWord] using combined

theorem two_execution
    (base source frontHandoff subtractionIntermediate projectionInput target
      frontGuess frontFirst frontSecond frontThird frontFourth frontFifth
      frontMarker projectionGuess projectionNegative projectionFirstValidator
      projectionSecondValidator first : Nat)
    (baseAtLeastTwo : 2 ≤ base) :
    let word := twoWord source frontHandoff subtractionIntermediate
      projectionInput target frontGuess frontFirst frontSecond frontThird
      frontFourth frontFifth frontMarker projectionGuess projectionNegative
      projectionFirstValidator projectionSecondValidator first
    WordOver
        (twoAlphabet source frontHandoff subtractionIntermediate projectionInput
          target frontGuess frontFirst frontSecond frontThird frontFourth
          frontFifth frontMarker projectionGuess projectionNegative
          projectionFirstValidator projectionSecondValidator) word ∧
      word.length = 19 * first + 19 ∧
      SameLine
        (physicalWordAction base word
          (phaseAffine source (unaryCode base (5 * first + 4))))
        (phaseAffine target (unaryCode base (2 * first + 1))) ∧
      AllStatesLocal base word
        (phaseAffine source (unaryCode base (5 * first + 4))) := by
  dsimp
  have action := twoWord_correct base source frontHandoff
    subtractionIntermediate projectionInput target frontGuess frontFirst
    frontSecond frontThird frontFourth frontFifth frontMarker projectionGuess
    projectionNegative projectionFirstValidator projectionSecondValidator
    first baseAtLeastTwo
  have inputLocal := phaseUnaryCode_local base source (5 * first + 4)
    baseAtLeastTwo
  have outputLocal := phaseUnaryCode_local base target (2 * first + 1)
    baseAtLeastTwo
  have outputNonzero := physicalWordAction_nonzero (prime := base) (by omega)
    (twoWord source frontHandoff subtractionIntermediate projectionInput target
      frontGuess frontFirst frontSecond frontThird frontFourth frontFifth
      frontMarker projectionGuess projectionNegative projectionFirstValidator
      projectionSecondValidator first) inputLocal.1
  have actualFinalLocal := LocalAt.of_sameLine outputLocal outputNonzero action
  exact ⟨twoWord_wordOver source frontHandoff subtractionIntermediate
      projectionInput target frontGuess frontFirst frontSecond frontThird
      frontFourth frontFifth frontMarker projectionGuess projectionNegative
      projectionFirstValidator projectionSecondValidator first,
    twoWord_length source frontHandoff subtractionIntermediate projectionInput
      target frontGuess frontFirst frontSecond frontThird frontFourth
      frontFifth frontMarker projectionGuess projectionNegative
      projectionFirstValidator projectionSecondValidator first,
    action, allStatesLocal_of_final_local (by omega) _ inputLocal.1
      actualFinalLocal⟩

def threeAlphabet
    (source frontHandoff projectionInput target frontGuess frontFirst
      frontSecond frontThird frontFourth frontFifth frontMarker firstGuess
      secondGuess negativePhase firstValidator secondValidator thirdValidator :
      Nat) : List PhysicalTemplate :=
  singleAlphabet source frontHandoff projectionInput frontGuess frontFirst
      frontSecond frontThird frontFourth frontFifth frontMarker ++
    ThreeProjectionModule.alphabet projectionInput target firstGuess secondGuess
      negativePhase firstValidator secondValidator thirdValidator

def threeWord
    (source frontHandoff projectionInput target frontGuess frontFirst
      frontSecond frontThird frontFourth frontFifth frontMarker firstGuess
      secondGuess negativePhase firstValidator secondValidator thirdValidator
      first : Nat) : List PhysicalTemplate :=
  singleWord source frontHandoff projectionInput frontGuess frontFirst
      frontSecond frontThird frontFourth frontFifth frontMarker first ++
    ThreeProjectionModule.acceptedWord projectionInput target firstGuess
      secondGuess negativePhase firstValidator secondValidator thirdValidator
      first

@[simp] theorem threeAlphabet_length
    (source frontHandoff projectionInput target frontGuess frontFirst
      frontSecond frontThird frontFourth frontFifth frontMarker firstGuess
      secondGuess negativePhase firstValidator secondValidator thirdValidator :
      Nat) :
    (threeAlphabet source frontHandoff projectionInput target frontGuess
      frontFirst frontSecond frontThird frontFourth frontFifth frontMarker
      firstGuess secondGuess negativePhase firstValidator secondValidator
      thirdValidator).length = 32 := by
  simp [threeAlphabet]

@[simp] theorem threeWord_length
    (source frontHandoff projectionInput target frontGuess frontFirst
      frontSecond frontThird frontFourth frontFifth frontMarker firstGuess
      secondGuess negativePhase firstValidator secondValidator thirdValidator
      first : Nat) :
    (threeWord source frontHandoff projectionInput target frontGuess frontFirst
      frontSecond frontThird frontFourth frontFifth frontMarker firstGuess
      secondGuess negativePhase firstValidator secondValidator thirdValidator
      first).length = 24 * first + 24 := by
  simp [threeWord]
  omega

theorem threeWord_wordOver
    (source frontHandoff projectionInput target frontGuess frontFirst
      frontSecond frontThird frontFourth frontFifth frontMarker firstGuess
      secondGuess negativePhase firstValidator secondValidator thirdValidator
      first : Nat) :
    WordOver
      (threeAlphabet source frontHandoff projectionInput target frontGuess
        frontFirst frontSecond frontThird frontFourth frontFifth frontMarker
        firstGuess secondGuess negativePhase firstValidator secondValidator
        thirdValidator)
      (threeWord source frontHandoff projectionInput target frontGuess
        frontFirst frontSecond frontThird frontFourth frontFifth frontMarker
        firstGuess secondGuess negativePhase firstValidator secondValidator
        thirdValidator first) := by
  intro letter letterMem
  simp only [threeWord, List.mem_append] at letterMem
  rcases letterMem with frontMem | projectionMem
  · exact List.mem_append_left _
      (singleWord_wordOver source frontHandoff projectionInput frontGuess
        frontFirst frontSecond frontThird frontFourth frontFifth frontMarker
        first letter frontMem)
  · exact List.mem_append_right _
      (ThreeProjectionModule.acceptedWord_wordOver projectionInput target
        firstGuess secondGuess negativePhase firstValidator secondValidator
        thirdValidator first letter projectionMem)

theorem threeWord_correct
    (base source frontHandoff projectionInput target frontGuess frontFirst
      frontSecond frontThird frontFourth frontFifth frontMarker firstGuess
      secondGuess negativePhase firstValidator secondValidator thirdValidator
      first : Nat) (baseAtLeastTwo : 2 ≤ base) :
    SameLine
      (physicalWordAction base
        (threeWord source frontHandoff projectionInput target frontGuess
          frontFirst frontSecond frontThird frontFourth frontFifth frontMarker
          firstGuess secondGuess negativePhase firstValidator secondValidator
          thirdValidator first)
        (phaseAffine source (unaryCode base (5 * first + 4))))
      (phaseAffine target (unaryCode base (3 * first + 2))) := by
  have frontRun := singleWord_correct base source frontHandoff projectionInput
    frontGuess frontFirst frontSecond frontThird frontFourth frontFifth
    frontMarker first baseAtLeastTwo
  have projectionRun := ThreeProjectionModule.acceptedWord_correct base
    projectionInput target firstGuess secondGuess negativePhase firstValidator
    secondValidator thirdValidator first baseAtLeastTwo
  have combined := physicalWordAction_append_sameLine base
    (singleWord source frontHandoff projectionInput frontGuess frontFirst
      frontSecond frontThird frontFourth frontFifth frontMarker first)
    (ThreeProjectionModule.acceptedWord projectionInput target firstGuess
      secondGuess negativePhase firstValidator secondValidator thirdValidator
      first) frontRun projectionRun
  simpa [threeWord] using combined

theorem three_execution
    (base source frontHandoff projectionInput target frontGuess frontFirst
      frontSecond frontThird frontFourth frontFifth frontMarker firstGuess
      secondGuess negativePhase firstValidator secondValidator thirdValidator
      first : Nat) (baseAtLeastTwo : 2 ≤ base) :
    let word := threeWord source frontHandoff projectionInput target frontGuess
      frontFirst frontSecond frontThird frontFourth frontFifth frontMarker
      firstGuess secondGuess negativePhase firstValidator secondValidator
      thirdValidator first
    WordOver
        (threeAlphabet source frontHandoff projectionInput target frontGuess
          frontFirst frontSecond frontThird frontFourth frontFifth frontMarker
          firstGuess secondGuess negativePhase firstValidator secondValidator
          thirdValidator) word ∧
      word.length = 24 * first + 24 ∧
      SameLine
        (physicalWordAction base word
          (phaseAffine source (unaryCode base (5 * first + 4))))
        (phaseAffine target (unaryCode base (3 * first + 2))) ∧
      AllStatesLocal base word
        (phaseAffine source (unaryCode base (5 * first + 4))) := by
  dsimp
  have action := threeWord_correct base source frontHandoff projectionInput
    target frontGuess frontFirst frontSecond frontThird frontFourth frontFifth
    frontMarker firstGuess secondGuess negativePhase firstValidator
    secondValidator thirdValidator first baseAtLeastTwo
  have inputLocal := phaseUnaryCode_local base source (5 * first + 4)
    baseAtLeastTwo
  have outputLocal := phaseUnaryCode_local base target (3 * first + 2)
    baseAtLeastTwo
  have outputNonzero := physicalWordAction_nonzero (prime := base) (by omega)
    (threeWord source frontHandoff projectionInput target frontGuess frontFirst
      frontSecond frontThird frontFourth frontFifth frontMarker firstGuess
      secondGuess negativePhase firstValidator secondValidator thirdValidator
      first) inputLocal.1
  have actualFinalLocal := LocalAt.of_sameLine outputLocal outputNonzero action
  exact ⟨threeWord_wordOver source frontHandoff projectionInput target
      frontGuess frontFirst frontSecond frontThird frontFourth frontFifth
      frontMarker firstGuess secondGuess negativePhase firstValidator
      secondValidator thirdValidator first,
    threeWord_length source frontHandoff projectionInput target frontGuess
      frontFirst frontSecond frontThird frontFourth frontFifth frontMarker
      firstGuess secondGuess negativePhase firstValidator secondValidator
      thirdValidator first,
    action, allStatesLocal_of_final_local (by omega) _ inputLocal.1
      actualFinalLocal⟩

end Mortality.Compiler.ContractionModules
