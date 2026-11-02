import Mortality.Compiler.BoundaryParser
import Mortality.Compiler.FivefoldFrontClassification
import Mortality.Compiler.TernaryFrontModule

/-!
# The sixteen-letter fivefold front

This file realizes the optimized fivefold front from the manuscript.  The
marker-two exit fuses negation with `T`, so its output is the input expected
by the first positive subtraction scan.
-/

namespace Mortality.Compiler.FivefoldFrontModule

open Mortality.Compiler
open Mortality.PeriodicCode
open Mortality.Compiler.UnaryArithmetic
open Mortality.Compiler.IncrementModule
open Mortality.Compiler.PrefixGuessModule
open Mortality.Compiler.OddHalvingArithmetic
open Mortality.Compiler.OddHalvingModule
open Mortality.Compiler.TernaryFrontArithmetic
open Mortality.Compiler.TernaryFrontModule
open Mortality.Compiler.FivefoldFrontClassification
open Mortality.Compiler.IntegerFraction

def negatingTMarker (source target : Nat) : PhysicalTemplate :=
  { sourcePhase := source
    targetPhase := target
    digit := 2
    preCoefficient := 0
    postSign := .negative
    postCoefficient := 1 }

def alphabet (source target guessPhase firstPhase secondPhase thirdPhase
    fourthPhase fifthPhase markerTwoPhase : Nat) : List PhysicalTemplate :=
  prefixAlphabet source guessPhase firstPhase ++
    [identityZero firstPhase, identityMarker firstPhase secondPhase,
      identityZero secondPhase, identityMarker secondPhase thirdPhase,
      identityZero thirdPhase, identityMarker thirdPhase fourthPhase,
      identityZero fourthPhase, identityMarker fourthPhase fifthPhase,
      identityZero fifthPhase, inverseTMarker fifthPhase markerTwoPhase,
      identityZero markerTwoPhase,
      negatingTMarker markerTwoPhase target]

def fifthScanWord (source target zeros : Nat) : List PhysicalTemplate :=
  List.replicate zeros (identityZero source) ++
    [inverseTMarker source target]

def markerTwoWord (source target zeros : Nat) : List PhysicalTemplate :=
  List.replicate zeros (identityZero source) ++
    [negatingTMarker source target]

def acceptedWord (source target guessPhase firstPhase secondPhase thirdPhase
    fourthPhase fifthPhase markerTwoPhase first : Nat) :
    List PhysicalTemplate :=
  let guess := 4 * (first + 1)
  prefixWord source guessPhase firstPhase guess ++
    plainScanWord firstPhase secondPhase first ++
    plainScanWord secondPhase thirdPhase first ++
    plainScanWord thirdPhase fourthPhase first ++
    plainScanWord fourthPhase fifthPhase first ++
    fifthScanWord fifthPhase markerTwoPhase first ++
    markerTwoWord markerTwoPhase target first

def automaticAcceptedWord
    (target firstPhase secondPhase thirdPhase fourthPhase fifthPhase
      markerTwoPhase first : Nat) : List PhysicalTemplate :=
  plainScanWord firstPhase secondPhase first ++
    plainScanWord secondPhase thirdPhase first ++
    plainScanWord thirdPhase fourthPhase first ++
    plainScanWord fourthPhase fifthPhase first ++
    fifthScanWord fifthPhase markerTwoPhase first ++
    markerTwoWord markerTwoPhase target first

def falseSurvivorAutomaticWord
    (target firstPhase secondPhase thirdPhase fourthPhase fifthPhase
      markerTwoPhase first guess : Nat) : List PhysicalTemplate :=
  plainScanWord firstPhase secondPhase first ++
    plainScanWord secondPhase thirdPhase first ++
    plainScanWord thirdPhase fourthPhase (thirdScanLength first guess) ++
    plainScanWord fourthPhase fifthPhase (fourthZeroCount first guess) ++
    fifthScanWord fifthPhase markerTwoPhase
      (middleFifthZeroCount first guess) ++
    markerTwoWord markerTwoPhase target
      (falseMarkerTwoZeroCount first guess)

def falseSurvivorWord
    (source target guessPhase firstPhase secondPhase thirdPhase fourthPhase
      fifthPhase markerTwoPhase first guess : Nat) : List PhysicalTemplate :=
  prefixWord source guessPhase firstPhase guess ++
    falseSurvivorAutomaticWord target firstPhase secondPhase thirdPhase
      fourthPhase fifthPhase markerTwoPhase first guess

@[simp] theorem alphabet_length
    (source target guessPhase firstPhase secondPhase thirdPhase fourthPhase
      fifthPhase markerTwoPhase : Nat) :
    (alphabet source target guessPhase firstPhase secondPhase thirdPhase
      fourthPhase fifthPhase markerTwoPhase).length = 16 := by
  simp [alphabet]

@[simp] theorem fifthScanWord_length (source target zeros : Nat) :
    (fifthScanWord source target zeros).length = zeros + 1 := by
  simp [fifthScanWord]

@[simp] theorem markerTwoWord_length (source target zeros : Nat) :
    (markerTwoWord source target zeros).length = zeros + 1 := by
  simp [markerTwoWord]

@[simp] theorem acceptedWord_length
    (source target guessPhase firstPhase secondPhase thirdPhase fourthPhase
      fifthPhase markerTwoPhase first : Nat) :
    (acceptedWord source target guessPhase firstPhase secondPhase thirdPhase
      fourthPhase fifthPhase markerTwoPhase first).length =
        10 * first + 10 := by
  simp [acceptedWord, prefixWord_length
    (by omega : 0 < 4 * (first + 1)), plainScanWord]
  omega

theorem acceptedWord_wordOver
    (source target guessPhase firstPhase secondPhase thirdPhase fourthPhase
      fifthPhase markerTwoPhase first : Nat) :
    WordOver
      (alphabet source target guessPhase firstPhase secondPhase thirdPhase
        fourthPhase fifthPhase markerTwoPhase)
      (acceptedWord source target guessPhase firstPhase secondPhase thirdPhase
        fourthPhase fifthPhase markerTwoPhase first) := by
  intro letter letterMem
  simp [acceptedWord, plainScanWord, fifthScanWord, markerTwoWord] at letterMem
  rcases letterMem with prefixMem | ⟨_, rfl⟩ | rfl | ⟨_, rfl⟩ | rfl |
      ⟨_, rfl⟩ | rfl | ⟨_, rfl⟩ | rfl | ⟨_, rfl⟩ | rfl |
      ⟨_, rfl⟩ | rfl
  · exact List.mem_append_left _
      ((prefixWord_wordOver source guessPhase firstPhase
        (4 * (first + 1))) letter prefixMem)
  all_goals simp [alphabet]

theorem thirdPlainMarker_step
    (base thirdPhase fourthPhase first guess : Nat)
    (baseAtLeastTwo : 2 ≤ base) (guessPositive : 0 < guess)
    (thirdAccepted : first ≠ guess - 1) :
    SameLine
      ((identityMarker thirdPhase fourthPhase).act base
        (phaseAffine thirdPhase
          (thirdAutomaticState base first guess
            (thirdScanLength first guess))))
      (phaseAffine fourthPhase (fourthState base first guess 0)) := by
  have deletedEq := thirdAutomaticState_delete_marker base first guess
    baseAtLeastTwo guessPositive thirdAccepted
  rw [fourthState_zero]
  have outputLocal := thirdScanOutput_local base first guess baseAtLeastTwo
  have step := marker_step (source := thirdPhase) (target := fourthPhase)
    (digit := 1) (coefficient := 0) (sign := .positive)
    (value := thirdAutomaticState base first guess
      (thirdScanLength first guess))
    (deleted := thirdScanOutput base first guess)
    (output := thirdScanOutput base first guess) (by omega)
    (thirdAutomaticState_local base first guess
      (thirdScanLength first guess) baseAtLeastTwo)
    outputLocal deletedEq (by simp)
  simpa [identityMarker, PhysicalTemplate.act, PhysicalTemplate.matrix]
    using step

theorem fourthZero_step
    (base fourthPhase first guess deleted : Nat)
    (baseAtLeastTwo : 2 ≤ base)
    (deletedBelow : deleted < fourthZeroCount first guess) :
    SameLine
      ((identityZero fourthPhase).act base
        (phaseAffine fourthPhase (fourthState base first guess deleted)))
      (phaseAffine fourthPhase
        (fourthState base first guess (deleted + 1))) := by
  exact identityZero_step (by omega)
    (fourthState_local base first guess deleted baseAtLeastTwo)
    (fourthState_local base first guess (deleted + 1) baseAtLeastTwo)
    (fourthState_delete_zero base first guess deleted baseAtLeastTwo
      deletedBelow)

theorem fourthAcceptedMarker_step
    (base fourthPhase fifthPhase first : Nat)
    (baseAtLeastTwo : 2 ≤ base) :
    SameLine
      ((identityMarker fourthPhase fifthPhase).act base
        (phaseAffine fourthPhase
          (fourthState base first (4 * (first + 1)) first)))
      (phaseAffine fifthPhase
        (largeFifthState base first (4 * (first + 1)) 0)) := by
  have countEq : fourthZeroCount first (4 * (first + 1)) = first := by
    unfold fourthZeroCount ternaryValidatorLength
    rw [if_pos (by omega)]
    exact Nat.min_eq_left (by omega)
  have deletedEq := fourth_large_delete_marker base first
    (4 * (first + 1)) baseAtLeastTwo (by omega)
  rw [countEq] at deletedEq
  rw [largeFifthState_zero]
  have outputLocal := largeFifthState_local base first
    (4 * (first + 1)) 0 baseAtLeastTwo
  rw [largeFifthState_zero] at outputLocal
  have step := marker_step (source := fourthPhase) (target := fifthPhase)
    (digit := 1) (coefficient := 0) (sign := .positive)
    (value := fourthState base first (4 * (first + 1)) first)
    (deleted := largeFourthOutput base first (4 * (first + 1)))
    (output := largeFourthOutput base first (4 * (first + 1))) (by omega)
    (fourthState_local base first (4 * (first + 1)) first
      baseAtLeastTwo) outputLocal deletedEq (by simp)
  simpa [identityMarker, PhysicalTemplate.act, PhysicalTemplate.matrix]
    using step

theorem fifthZero_step
    (base fifthPhase first guess deleted : Nat)
    (baseAtLeastTwo : 2 ≤ base)
    (twoQBelowGuess : 2 * (first + 1) < guess)
    (deletedBelow : deleted < largeFifthZeroCount first guess) :
    SameLine
      ((identityZero fifthPhase).act base
        (phaseAffine fifthPhase
          (largeFifthState base first guess deleted)))
      (phaseAffine fifthPhase
        (largeFifthState base first guess (deleted + 1))) := by
  exact identityZero_step (by omega)
    (largeFifthState_local base first guess deleted baseAtLeastTwo)
    (largeFifthState_local base first guess (deleted + 1) baseAtLeastTwo)
    (largeFifthState_delete_zero base first guess deleted baseAtLeastTwo
      twoQBelowGuess deletedBelow)

theorem fifthAcceptedMarker_step
    (base fifthPhase markerTwoPhase first : Nat)
    (baseAtLeastTwo : 2 ≤ base) :
    SameLine
      ((inverseTMarker fifthPhase markerTwoPhase).act base
        (phaseAffine fifthPhase
          (largeFifthState base first (4 * (first + 1)) first)))
      (phaseAffine markerTwoPhase
        (aboveThreeMarkerTwoState base first (4 * (first + 1)) 0)) := by
  have countEq : largeFifthZeroCount first (4 * (first + 1)) = first := by
    simp [largeFifthZeroCount]
    omega
  have deletedEq := aboveThreeFifth_delete_marker base first
    (4 * (first + 1)) baseAtLeastTwo (by omega)
  rw [countEq] at deletedEq
  have outputEq := aboveThreeMarkerTwoState_zero base first
    (4 * (first + 1)) baseAtLeastTwo (by omega)
  rw [Tinv_eq_mutationMap] at outputEq
  have deletedLocal := state_local
    (numerator := aboveThreeFifthOutputNumerator base first
      (4 * (first + 1)))
    (halfIntegerDenominator_not_dvd base first (4 * (first + 1))
      baseAtLeastTwo)
  have outputLocal := aboveThreeMarkerTwoState_local base first
    (4 * (first + 1)) 0 baseAtLeastTwo
  have step := marker_step (source := fifthPhase) (target := markerTwoPhase)
    (digit := 1) (coefficient := 1) (sign := .positive)
    (value := largeFifthState base first (4 * (first + 1)) first)
    (deleted := aboveThreeFifthOutput base first (4 * (first + 1)))
    (output := aboveThreeMarkerTwoState base first
      (4 * (first + 1)) 0) (by omega)
    (largeFifthState_local base first (4 * (first + 1)) first
      baseAtLeastTwo) deletedLocal deletedEq outputEq
  simpa [inverseTMarker, PhysicalTemplate.act, PhysicalTemplate.matrix]
    using step

theorem markerTwoZero_step
    (base markerTwoPhase first deleted : Nat)
    (baseAtLeastTwo : 2 ≤ base) (deletedBelow : deleted < first) :
    SameLine
      ((identityZero markerTwoPhase).act base
        (phaseAffine markerTwoPhase
          (aboveThreeMarkerTwoState base first (4 * (first + 1)) deleted)))
      (phaseAffine markerTwoPhase
        (aboveThreeMarkerTwoState base first (4 * (first + 1))
          (deleted + 1))) := by
  have countEq : aboveThreeMarkerTwoZeroCount first
      (4 * (first + 1)) = first := by
    simp [aboveThreeMarkerTwoZeroCount]
    omega
  exact identityZero_step (by omega)
    (aboveThreeMarkerTwoState_local base first (4 * (first + 1)) deleted
      baseAtLeastTwo)
    (aboveThreeMarkerTwoState_local base first (4 * (first + 1))
      (deleted + 1) baseAtLeastTwo)
    (aboveThreeMarkerTwoState_delete_zero base first (4 * (first + 1))
      deleted baseAtLeastTwo (by omega) (by simpa [countEq]))

theorem markerTwoAcceptedMarker_step
    (base markerTwoPhase target first : Nat)
    (baseAtLeastTwo : 2 ≤ base) :
    SameLine
      ((negatingTMarker markerTwoPhase target).act base
        (phaseAffine markerTwoPhase
          (aboveThreeMarkerTwoState base first (4 * (first + 1)) first)))
      (phaseAffine target (acceptedHandoffState base first)) := by
  let markerDenominator := acceptedMarkerDenominator base first
  let handoffNumerator := acceptedHandoffNumerator base first
  have deletedEq := deleteDigit_eq base 2
    (aboveThreeMarkerTwoNumerator base first (4 * (first + 1)) first)
    markerDenominator (-handoffNumerator) (by omega)
    (denominator_nonzero_of_not_dvd
      (markerTwoDenominator_not_dvd base first (4 * (first + 1))
        (aboveThreeMarkerTwoNumerator base first (4 * (first + 1)))
        baseAtLeastTwo)) (by
      simpa [markerDenominator, handoffNumerator,
        acceptedMarkerDenominator] using
        (accepted_markerTwo_difference base first))
  have deletedLocal := state_local (numerator := -handoffNumerator)
    (markerTwoDenominator_not_dvd base first (4 * (first + 1))
      (aboveThreeMarkerTwoNumerator base first (4 * (first + 1)))
      baseAtLeastTwo)
  have outputEq := accepted_markerTwo_to_handoff base first baseAtLeastTwo
  have outputEq' := outputEq
  change mutationMap base .negative 1
      (deleteDigit (base : Rat) 2
        (state
          (aboveThreeMarkerTwoNumerator base first (4 * (first + 1)) first)
          markerDenominator)) = acceptedHandoffState base first at outputEq'
  rw [deletedEq] at outputEq'
  have step := marker_step (source := markerTwoPhase) (target := target)
    (digit := 2) (coefficient := 1) (sign := .negative)
    (value := aboveThreeMarkerTwoState base first (4 * (first + 1)) first)
    (deleted := state (-handoffNumerator) markerDenominator)
    (output := acceptedHandoffState base first) (by omega)
    (aboveThreeMarkerTwoState_local base first (4 * (first + 1)) first
      baseAtLeastTwo) deletedLocal (by
        simpa [aboveThreeMarkerTwoState, markerDenominator,
          acceptedMarkerDenominator] using deletedEq)
      outputEq'
  simpa [negatingTMarker, PhysicalTemplate.act, PhysicalTemplate.matrix]
    using step

theorem thirdAcceptedTail_correct
    (base thirdPhase fourthPhase first deleted remaining : Nat)
    (baseAtLeastTwo : 2 ≤ base) (sumEq : deleted + remaining = first) :
    SameLine
      (physicalWordAction base
        (List.replicate remaining (identityZero thirdPhase) ++
          [identityMarker thirdPhase fourthPhase])
        (phaseAffine thirdPhase
          (thirdAutomaticState base first (4 * (first + 1)) deleted)))
      (phaseAffine fourthPhase
        (fourthState base first (4 * (first + 1)) 0)) := by
  have scanLengthEq : thirdScanLength first (4 * (first + 1)) = first := by
    simp [thirdScanLength]
    omega
  induction remaining generalizing deleted with
  | zero =>
      simpa [physicalWordAction, show deleted = first by omega,
        scanLengthEq] using
        (thirdPlainMarker_step base thirdPhase fourthPhase first
          (4 * (first + 1)) baseAtLeastTwo (by omega) (by omega))
  | succ remaining inductionHypothesis =>
      have firstStep := TernaryFrontModule.thirdZero_step base thirdPhase
        first (4 * (first + 1)) deleted baseAtLeastTwo (by
          rw [scanLengthEq]
          omega)
      have tailRun := inductionHypothesis (deleted := deleted + 1) (by omega)
      have combined := physicalWordAction_cons_sameLine base
        (identityZero thirdPhase)
        (List.replicate remaining (identityZero thirdPhase) ++
          [identityMarker thirdPhase fourthPhase]) firstStep tailRun
      simpa [List.replicate_succ, physicalWordAction] using combined

theorem fourthAcceptedTail_correct
    (base fourthPhase fifthPhase first deleted remaining : Nat)
    (baseAtLeastTwo : 2 ≤ base) (sumEq : deleted + remaining = first) :
    SameLine
      (physicalWordAction base
        (List.replicate remaining (identityZero fourthPhase) ++
          [identityMarker fourthPhase fifthPhase])
        (phaseAffine fourthPhase
          (fourthState base first (4 * (first + 1)) deleted)))
      (phaseAffine fifthPhase
        (largeFifthState base first (4 * (first + 1)) 0)) := by
  have countEq : fourthZeroCount first (4 * (first + 1)) = first := by
    unfold fourthZeroCount ternaryValidatorLength
    rw [if_pos (by omega)]
    exact Nat.min_eq_left (by omega)
  induction remaining generalizing deleted with
  | zero =>
      simpa [physicalWordAction, show deleted = first by omega] using
        (fourthAcceptedMarker_step base fourthPhase fifthPhase first
          baseAtLeastTwo)
  | succ remaining inductionHypothesis =>
      have firstStep := fourthZero_step base fourthPhase first
        (4 * (first + 1)) deleted baseAtLeastTwo (by
          rw [countEq]
          omega)
      have tailRun := inductionHypothesis (deleted := deleted + 1) (by omega)
      have combined := physicalWordAction_cons_sameLine base
        (identityZero fourthPhase)
        (List.replicate remaining (identityZero fourthPhase) ++
          [identityMarker fourthPhase fifthPhase]) firstStep tailRun
      simpa [List.replicate_succ, physicalWordAction] using combined

theorem fifthAcceptedTail_correct
    (base fifthPhase markerTwoPhase first deleted remaining : Nat)
    (baseAtLeastTwo : 2 ≤ base) (sumEq : deleted + remaining = first) :
    SameLine
      (physicalWordAction base
        (List.replicate remaining (identityZero fifthPhase) ++
          [inverseTMarker fifthPhase markerTwoPhase])
        (phaseAffine fifthPhase
          (largeFifthState base first (4 * (first + 1)) deleted)))
      (phaseAffine markerTwoPhase
        (aboveThreeMarkerTwoState base first (4 * (first + 1)) 0)) := by
  have countEq : largeFifthZeroCount first (4 * (first + 1)) = first := by
    simp [largeFifthZeroCount]
    omega
  induction remaining generalizing deleted with
  | zero =>
      simpa [physicalWordAction, show deleted = first by omega] using
        (fifthAcceptedMarker_step base fifthPhase markerTwoPhase first
          baseAtLeastTwo)
  | succ remaining inductionHypothesis =>
      have firstStep := fifthZero_step base fifthPhase first
        (4 * (first + 1)) deleted baseAtLeastTwo (by omega) (by
          rw [countEq]
          omega)
      have tailRun := inductionHypothesis (deleted := deleted + 1) (by omega)
      have combined := physicalWordAction_cons_sameLine base
        (identityZero fifthPhase)
        (List.replicate remaining (identityZero fifthPhase) ++
          [inverseTMarker fifthPhase markerTwoPhase]) firstStep tailRun
      simpa [List.replicate_succ, physicalWordAction] using combined

theorem markerTwoAcceptedTail_correct
    (base markerTwoPhase target first deleted remaining : Nat)
    (baseAtLeastTwo : 2 ≤ base) (sumEq : deleted + remaining = first) :
    SameLine
      (physicalWordAction base
        (List.replicate remaining (identityZero markerTwoPhase) ++
          [negatingTMarker markerTwoPhase target])
        (phaseAffine markerTwoPhase
          (aboveThreeMarkerTwoState base first (4 * (first + 1)) deleted)))
      (phaseAffine target (acceptedHandoffState base first)) := by
  induction remaining generalizing deleted with
  | zero =>
      simpa [physicalWordAction, show deleted = first by omega] using
        (markerTwoAcceptedMarker_step base markerTwoPhase target first
          baseAtLeastTwo)
  | succ remaining inductionHypothesis =>
      have firstStep := markerTwoZero_step base markerTwoPhase first deleted
        baseAtLeastTwo (by omega)
      have tailRun := inductionHypothesis (deleted := deleted + 1) (by omega)
      have combined := physicalWordAction_cons_sameLine base
        (identityZero markerTwoPhase)
        (List.replicate remaining (identityZero markerTwoPhase) ++
          [negatingTMarker markerTwoPhase target]) firstStep tailRun
      simpa [List.replicate_succ, physicalWordAction] using combined

theorem acceptedWord_correct
    (base source target guessPhase firstPhase secondPhase thirdPhase
      fourthPhase fifthPhase markerTwoPhase first : Nat)
    (baseAtLeastTwo : 2 ≤ base) :
    SameLine
      (physicalWordAction base
        (acceptedWord source target guessPhase firstPhase secondPhase
          thirdPhase fourthPhase fifthPhase markerTwoPhase first)
        (phaseAffine source (unaryCode base (5 * first + 4))))
      (phaseAffine target
        (T base (twoFieldCode base first (4 * first + 3)))) := by
  let guess := 4 * (first + 1)
  have inputEq : 5 * first + 4 = first + guess := by
    dsimp [guess]
    omega
  have prefixRun := prefixWord_correct base source guessPhase firstPhase
    (5 * first + 4) guess baseAtLeastTwo (by dsimp [guess]; omega)
      (by dsimp [guess]; omega)
  have prefixRun' : SameLine
      (physicalWordAction base
        (prefixWord source guessPhase firstPhase guess)
        (phaseAffine source (unaryCode base (5 * first + 4))))
      (phaseAffine firstPhase
        (firstAutomaticState base first guess 0)) := by
    rw [firstAutomaticState_zero base first guess baseAtLeastTwo]
    simpa only [inputEq] using prefixRun
  have firstRun := firstScanWord_correct base firstPhase secondPhase first
    guess baseAtLeastTwo
  have firstRun' : SameLine
      (physicalWordAction base
        (plainScanWord firstPhase secondPhase first)
        (phaseAffine firstPhase (firstAutomaticState base first guess 0)))
      (phaseAffine secondPhase (firstScanOutput base first guess)) := by
    simpa [plainScanWord, firstScanWord] using firstRun
  have throughFirst := physicalWordAction_append_sameLine base
    (prefixWord source guessPhase firstPhase guess)
    (plainScanWord firstPhase secondPhase first) prefixRun' firstRun'
  have secondRun := secondPlainScanWord_correct base secondPhase thirdPhase
    first guess baseAtLeastTwo (by dsimp [guess]; omega)
  have throughSecond := physicalWordAction_append_sameLine base
    (prefixWord source guessPhase firstPhase guess ++
      plainScanWord firstPhase secondPhase first)
    (plainScanWord secondPhase thirdPhase first) throughFirst secondRun
  have thirdStart : thirdAutomaticState base first guess 0 =
      secondScanOutput base first guess := thirdAutomaticState_zero _ _ _
  rw [← thirdStart] at throughSecond
  have thirdRun := thirdAcceptedTail_correct base thirdPhase fourthPhase
    first 0 first baseAtLeastTwo (by omega)
  have throughThird := physicalWordAction_append_sameLine base
    (prefixWord source guessPhase firstPhase guess ++
      plainScanWord firstPhase secondPhase first ++
      plainScanWord secondPhase thirdPhase first)
    (plainScanWord thirdPhase fourthPhase first) throughSecond
    (by simpa [plainScanWord, guess] using thirdRun)
  have fourthRun := fourthAcceptedTail_correct base fourthPhase fifthPhase
    first 0 first baseAtLeastTwo (by omega)
  have throughFourth := physicalWordAction_append_sameLine base
    (prefixWord source guessPhase firstPhase guess ++
      plainScanWord firstPhase secondPhase first ++
      plainScanWord secondPhase thirdPhase first ++
      plainScanWord thirdPhase fourthPhase first)
    (plainScanWord fourthPhase fifthPhase first) throughThird
    (by simpa [plainScanWord, guess] using fourthRun)
  have fifthRun := fifthAcceptedTail_correct base fifthPhase markerTwoPhase
    first 0 first baseAtLeastTwo (by omega)
  have throughFifth := physicalWordAction_append_sameLine base
    (prefixWord source guessPhase firstPhase guess ++
      plainScanWord firstPhase secondPhase first ++
      plainScanWord secondPhase thirdPhase first ++
      plainScanWord thirdPhase fourthPhase first ++
      plainScanWord fourthPhase fifthPhase first)
    (fifthScanWord fifthPhase markerTwoPhase first) throughFourth
    (by simpa [fifthScanWord, guess] using fifthRun)
  have markerRun := markerTwoAcceptedTail_correct base markerTwoPhase target
    first 0 first baseAtLeastTwo (by omega)
  have complete := physicalWordAction_append_sameLine base
    (prefixWord source guessPhase firstPhase guess ++
      plainScanWord firstPhase secondPhase first ++
      plainScanWord secondPhase thirdPhase first ++
      plainScanWord thirdPhase fourthPhase first ++
      plainScanWord fourthPhase fifthPhase first ++
      fifthScanWord fifthPhase markerTwoPhase first)
    (markerTwoWord markerTwoPhase target first) throughFifth
    (by simpa [markerTwoWord, guess] using markerRun)
  rw [acceptedHandoffState_eq base first baseAtLeastTwo] at complete
  simpa [acceptedWord, guess, List.append_assoc] using complete

theorem accepted_execution
    (base source target guessPhase firstPhase secondPhase thirdPhase
      fourthPhase fifthPhase markerTwoPhase first : Nat)
    (baseAtLeastTwo : 2 ≤ base) :
    let word := acceptedWord source target guessPhase firstPhase secondPhase
      thirdPhase fourthPhase fifthPhase markerTwoPhase first
    WordOver
        (alphabet source target guessPhase firstPhase secondPhase thirdPhase
          fourthPhase fifthPhase markerTwoPhase) word ∧
      word.length = 10 * first + 10 ∧
      SameLine
        (physicalWordAction base word
          (phaseAffine source (unaryCode base (5 * first + 4))))
        (phaseAffine target
          (T base (twoFieldCode base first (4 * first + 3)))) ∧
      AllStatesLocal base word
        (phaseAffine source (unaryCode base (5 * first + 4))) := by
  dsimp
  have action := acceptedWord_correct base source target guessPhase firstPhase
    secondPhase thirdPhase fourthPhase fifthPhase markerTwoPhase first
    baseAtLeastTwo
  have inputLocal := phaseUnaryCode_local base source (5 * first + 4)
    baseAtLeastTwo
  have outputNonzero := physicalWordAction_nonzero (prime := base) (by omega)
    (acceptedWord source target guessPhase firstPhase secondPhase thirdPhase
      fourthPhase fifthPhase markerTwoPhase first) inputLocal.1
  have outputLocal : LocalAt base
      (phaseAffine target
        (T base (twoFieldCode base first (4 * first + 3)))) := by
    rw [← acceptedHandoffState_eq base first baseAtLeastTwo]
    exact phaseLocal (acceptedHandoffState_local base first baseAtLeastTwo)
  have finalLocal := LocalAt.of_sameLine outputLocal outputNonzero action
  exact ⟨acceptedWord_wordOver source target guessPhase firstPhase secondPhase
      thirdPhase fourthPhase fifthPhase markerTwoPhase first,
    acceptedWord_length source target guessPhase firstPhase secondPhase
      thirdPhase fourthPhase fifthPhase markerTwoPhase first,
    action, allStatesLocal_of_final_local (by omega) _ inputLocal.1
      finalLocal⟩

structure PhaseLayout (phaseCount source guessPhase firstPhase secondPhase
    thirdPhase fourthPhase fifthPhase markerTwoPhase : Nat) : Prop where
  sourceBound : source < phaseCount
  guessBound : guessPhase < phaseCount
  firstBound : firstPhase < phaseCount
  secondBound : secondPhase < phaseCount
  thirdBound : thirdPhase < phaseCount
  fourthBound : fourthPhase < phaseCount
  fifthBound : fifthPhase < phaseCount
  markerTwoBound : markerTwoPhase < phaseCount
  distinct : [source, guessPhase, firstPhase, secondPhase, thirdPhase,
    fourthPhase, fifthPhase, markerTwoPhase].Nodup

theorem letter_source_bound
    {phaseCount source target guessPhase firstPhase secondPhase thirdPhase
      fourthPhase fifthPhase markerTwoPhase : Nat}
    (layout : PhaseLayout phaseCount source guessPhase firstPhase secondPhase
      thirdPhase fourthPhase fifthPhase markerTwoPhase)
    {letter : PhysicalTemplate}
    (letterMem : letter ∈ alphabet source target guessPhase firstPhase
      secondPhase thirdPhase fourthPhase fifthPhase markerTwoPhase) :
    letter.sourcePhase < phaseCount := by
  simp [alphabet, prefixAlphabet] at letterMem
  rcases letterMem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp [startContinue, startExit, privateLoop, privateExit, identityZero,
      identityMarker, inverseTMarker, negatingTMarker, layout.sourceBound,
      layout.guessBound, layout.firstBound, layout.secondBound,
      layout.thirdBound, layout.fourthBound, layout.fifthBound,
      layout.markerTwoBound]

/-- Every core letter starts in one of the eight active core phases. -/
theorem letter_source_mem_active
    {source target guessPhase firstPhase secondPhase thirdPhase fourthPhase
      fifthPhase markerTwoPhase : Nat} {letter : PhysicalTemplate}
    (letterMem : letter ∈ alphabet source target guessPhase firstPhase
      secondPhase thirdPhase fourthPhase fifthPhase markerTwoPhase) :
    letter.sourcePhase ∈ [source, guessPhase, firstPhase, secondPhase,
      thirdPhase, fourthPhase, fifthPhase, markerTwoPhase] := by
  simp [alphabet, prefixAlphabet] at letterMem
  rcases letterMem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp [startContinue, startExit, privateLoop, privateExit, identityZero,
      identityMarker, inverseTMarker, negatingTMarker]

theorem letter_reserved
    {source target guessPhase firstPhase secondPhase thirdPhase fourthPhase
      fifthPhase markerTwoPhase : Nat} {letter : PhysicalTemplate}
    (letterMem : letter ∈ alphabet source target guessPhase firstPhase
      secondPhase thirdPhase fourthPhase fifthPhase markerTwoPhase) :
    ReservedDigit letter.digit := by
  simp [alphabet, prefixAlphabet] at letterMem
  rcases letterMem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp [startContinue, startExit, privateLoop, privateExit, identityZero,
      identityMarker, inverseTMarker, negatingTMarker, ReservedDigit]

theorem force_metadata
    {prime phaseCount source target guessPhase firstPhase secondPhase
      thirdPhase fourthPhase fifthPhase markerTwoPhase actualPhase : Nat}
    {actualDigit : Int} {numerator denominator : Int}
    (primeProperty : IsPrime prime) (primeBound : 6 * phaseCount < prime)
    (layout : PhaseLayout phaseCount source guessPhase firstPhase secondPhase
      thirdPhase fourthPhase fifthPhase markerTwoPhase)
    (actualBound : actualPhase < phaseCount)
    (actualReserved : ReservedDigit actualDigit)
    (denominatorNotDivisible : ¬(prime : Int) ∣ denominator)
    (residue : (prime : Int) ∣ numerator - actualDigit * denominator)
    (representation : SameLine
      (Vec2.affine ((numerator : Rat) / (denominator : Rat)))
      (integerVector numerator denominator))
    {letter : PhysicalTemplate}
    (letterMem : letter ∈ alphabet source target guessPhase firstPhase
      secondPhase thirdPhase fourthPhase fifthPhase markerTwoPhase)
    (outputLocal : LocalAt prime
      (letter.act prime
        (phaseAffine actualPhase
          ((numerator : Rat) / (denominator : Rat))))) :
    letter.sourcePhase = actualPhase ∧ letter.digit = actualDigit := by
  have h := physicalLetter_affine_integer_source_digit_unique
    (prime := prime) (phaseCount := phaseCount)
    (actualPhase := actualPhase) (sourcePhase := letter.sourcePhase)
    (targetPhase := letter.targetPhase) (actualDigit := actualDigit)
    (letterDigit := letter.digit)
    (preCoefficient := letter.preCoefficient)
    (postCoefficient := letter.postCoefficient)
    (postSign := letter.postSign) primeProperty primeBound actualBound
    (letter_source_bound layout letterMem) actualReserved
    (letter_reserved letterMem) denominatorNotDivisible residue representation
    (by simpa [PhysicalTemplate.act, PhysicalTemplate.matrix, phaseAffine]
      using outputLocal)
  exact ⟨h.1.symm, h.2.symm⟩

theorem source_letter_choices
    {phaseCount source target guessPhase firstPhase secondPhase thirdPhase
      fourthPhase fifthPhase markerTwoPhase : Nat}
    (layout : PhaseLayout phaseCount source guessPhase firstPhase secondPhase
      thirdPhase fourthPhase fifthPhase markerTwoPhase)
    {letter : PhysicalTemplate}
    (letterMem : letter ∈ alphabet source target guessPhase firstPhase
      secondPhase thirdPhase fourthPhase fifthPhase markerTwoPhase)
    (sourceEq : letter.sourcePhase = source) :
    letter = startContinue source guessPhase ∨
      letter = startExit source firstPhase := by
  have distinct := layout.distinct
  simp at distinct
  simp [alphabet, prefixAlphabet] at letterMem
  rcases letterMem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp_all [startContinue, startExit, privateLoop, privateExit,
      identityZero, identityMarker, inverseTMarker, negatingTMarker]

theorem guess_letter_choices
    {phaseCount source target guessPhase firstPhase secondPhase thirdPhase
      fourthPhase fifthPhase markerTwoPhase : Nat}
    (layout : PhaseLayout phaseCount source guessPhase firstPhase secondPhase
      thirdPhase fourthPhase fifthPhase markerTwoPhase)
    {letter : PhysicalTemplate}
    (letterMem : letter ∈ alphabet source target guessPhase firstPhase
      secondPhase thirdPhase fourthPhase fifthPhase markerTwoPhase)
    (sourceEq : letter.sourcePhase = guessPhase) :
    letter = privateLoop guessPhase ∨
      letter = privateExit guessPhase firstPhase := by
  have distinct := layout.distinct
  simp at distinct
  simp [alphabet, prefixAlphabet] at letterMem
  rcases letterMem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp_all [startContinue, startExit, privateLoop, privateExit,
      identityZero, identityMarker, inverseTMarker, negatingTMarker]

theorem first_letter_choices
    {phaseCount source target guessPhase firstPhase secondPhase thirdPhase
      fourthPhase fifthPhase markerTwoPhase : Nat}
    (layout : PhaseLayout phaseCount source guessPhase firstPhase secondPhase
      thirdPhase fourthPhase fifthPhase markerTwoPhase)
    {letter : PhysicalTemplate}
    (letterMem : letter ∈ alphabet source target guessPhase firstPhase
      secondPhase thirdPhase fourthPhase fifthPhase markerTwoPhase)
    (sourceEq : letter.sourcePhase = firstPhase) :
    letter = identityZero firstPhase ∨
      letter = identityMarker firstPhase secondPhase := by
  have distinct := layout.distinct
  simp at distinct
  simp [alphabet, prefixAlphabet] at letterMem
  rcases letterMem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp_all [startContinue, startExit, privateLoop, privateExit,
      identityZero, identityMarker, inverseTMarker, negatingTMarker]

theorem second_letter_choices
    {phaseCount source target guessPhase firstPhase secondPhase thirdPhase
      fourthPhase fifthPhase markerTwoPhase : Nat}
    (layout : PhaseLayout phaseCount source guessPhase firstPhase secondPhase
      thirdPhase fourthPhase fifthPhase markerTwoPhase)
    {letter : PhysicalTemplate}
    (letterMem : letter ∈ alphabet source target guessPhase firstPhase
      secondPhase thirdPhase fourthPhase fifthPhase markerTwoPhase)
    (sourceEq : letter.sourcePhase = secondPhase) :
    letter = identityZero secondPhase ∨
      letter = identityMarker secondPhase thirdPhase := by
  have distinct := layout.distinct
  simp at distinct
  simp [alphabet, prefixAlphabet] at letterMem
  rcases letterMem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp_all [startContinue, startExit, privateLoop, privateExit,
      identityZero, identityMarker, inverseTMarker, negatingTMarker]

theorem third_letter_choices
    {phaseCount source target guessPhase firstPhase secondPhase thirdPhase
      fourthPhase fifthPhase markerTwoPhase : Nat}
    (layout : PhaseLayout phaseCount source guessPhase firstPhase secondPhase
      thirdPhase fourthPhase fifthPhase markerTwoPhase)
    {letter : PhysicalTemplate}
    (letterMem : letter ∈ alphabet source target guessPhase firstPhase
      secondPhase thirdPhase fourthPhase fifthPhase markerTwoPhase)
    (sourceEq : letter.sourcePhase = thirdPhase) :
    letter = identityZero thirdPhase ∨
      letter = identityMarker thirdPhase fourthPhase := by
  have distinct := layout.distinct
  simp at distinct
  simp [alphabet, prefixAlphabet] at letterMem
  rcases letterMem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp_all [startContinue, startExit, privateLoop, privateExit,
      identityZero, identityMarker, inverseTMarker, negatingTMarker]

theorem fourth_letter_choices
    {phaseCount source target guessPhase firstPhase secondPhase thirdPhase
      fourthPhase fifthPhase markerTwoPhase : Nat}
    (layout : PhaseLayout phaseCount source guessPhase firstPhase secondPhase
      thirdPhase fourthPhase fifthPhase markerTwoPhase)
    {letter : PhysicalTemplate}
    (letterMem : letter ∈ alphabet source target guessPhase firstPhase
      secondPhase thirdPhase fourthPhase fifthPhase markerTwoPhase)
    (sourceEq : letter.sourcePhase = fourthPhase) :
    letter = identityZero fourthPhase ∨
      letter = identityMarker fourthPhase fifthPhase := by
  have distinct := layout.distinct
  simp at distinct
  simp [alphabet, prefixAlphabet] at letterMem
  rcases letterMem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp_all [startContinue, startExit, privateLoop, privateExit,
      identityZero, identityMarker, inverseTMarker, negatingTMarker]

theorem fifth_letter_choices
    {phaseCount source target guessPhase firstPhase secondPhase thirdPhase
      fourthPhase fifthPhase markerTwoPhase : Nat}
    (layout : PhaseLayout phaseCount source guessPhase firstPhase secondPhase
      thirdPhase fourthPhase fifthPhase markerTwoPhase)
    {letter : PhysicalTemplate}
    (letterMem : letter ∈ alphabet source target guessPhase firstPhase
      secondPhase thirdPhase fourthPhase fifthPhase markerTwoPhase)
    (sourceEq : letter.sourcePhase = fifthPhase) :
    letter = identityZero fifthPhase ∨
      letter = inverseTMarker fifthPhase markerTwoPhase := by
  have distinct := layout.distinct
  simp at distinct
  simp [alphabet, prefixAlphabet] at letterMem
  rcases letterMem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp_all [startContinue, startExit, privateLoop, privateExit,
      identityZero, identityMarker, inverseTMarker, negatingTMarker]

theorem markerTwo_letter_choices
    {phaseCount source target guessPhase firstPhase secondPhase thirdPhase
      fourthPhase fifthPhase markerTwoPhase : Nat}
    (layout : PhaseLayout phaseCount source guessPhase firstPhase secondPhase
      thirdPhase fourthPhase fifthPhase markerTwoPhase)
    {letter : PhysicalTemplate}
    (letterMem : letter ∈ alphabet source target guessPhase firstPhase
      secondPhase thirdPhase fourthPhase fifthPhase markerTwoPhase)
    (sourceEq : letter.sourcePhase = markerTwoPhase) :
    letter = identityZero markerTwoPhase ∨
      letter = negatingTMarker markerTwoPhase target := by
  have distinct := layout.distinct
  simp at distinct
  simp [alphabet, prefixAlphabet] at letterMem
  rcases letterMem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp_all [startContinue, startExit, privateLoop, privateExit,
      identityZero, identityMarker, inverseTMarker, negatingTMarker]

/-- Phase and digit metadata are forced by guarded locality.  This form is
convenient once an arithmetic state has already been packaged as an
`InPhaseAt` fact. -/
theorem force_inPhase_metadata
    {prime phaseCount source target guessPhase firstPhase secondPhase
      thirdPhase fourthPhase fifthPhase markerTwoPhase actualPhase : Nat}
    {actualDigit : Int} {state : Vec2} {letter : PhysicalTemplate}
    (primeProperty : IsPrime prime) (primeBound : 6 * phaseCount < prime)
    (layout : PhaseLayout phaseCount source guessPhase firstPhase secondPhase
      thirdPhase fourthPhase fifthPhase markerTwoPhase)
    (actualBound : actualPhase < phaseCount)
    (membership : InPhaseAt prime actualPhase actualDigit state)
    (letterMem : letter ∈ alphabet source target guessPhase firstPhase
      secondPhase thirdPhase fourthPhase fifthPhase markerTwoPhase)
    (outputLocal : LocalAt prime (letter.act prime state)) :
    letter.sourcePhase = actualPhase ∧ letter.digit = actualDigit := by
  have h := membership.physicalLetter_source_digit_unique primeProperty
    primeBound actualBound (letter_source_bound layout letterMem)
    (letter_reserved letterMem)
    (by simpa [PhysicalTemplate.act, PhysicalTemplate.matrix] using outputLocal)
  exact ⟨h.1.symm, h.2.symm⟩

theorem source_letter
    {prime phaseCount source target guessPhase firstPhase secondPhase
      thirdPhase fourthPhase fifthPhase markerTwoPhase : Nat}
    {digit : Int} {state : Vec2} {letter : PhysicalTemplate}
    (primeProperty : IsPrime prime) (primeBound : 6 * phaseCount < prime)
    (layout : PhaseLayout phaseCount source guessPhase firstPhase secondPhase
      thirdPhase fourthPhase fifthPhase markerTwoPhase)
    (membership : InPhaseAt prime source digit state)
    (letterMem : letter ∈ alphabet source target guessPhase firstPhase
      secondPhase thirdPhase fourthPhase fifthPhase markerTwoPhase)
    (outputLocal : LocalAt prime (letter.act prime state)) :
    digit = 0 ∧
      (letter = startContinue source guessPhase ∨
        letter = startExit source firstPhase) := by
  have forced := force_inPhase_metadata primeProperty primeBound layout
    layout.sourceBound membership letterMem outputLocal
  rcases source_letter_choices layout letterMem forced.1 with h | h
  · subst letter
    exact ⟨by simpa [startContinue] using forced.2.symm, .inl rfl⟩
  · subst letter
    exact ⟨by simpa [startExit] using forced.2.symm, .inr rfl⟩

theorem guess_letter
    {prime phaseCount source target guessPhase firstPhase secondPhase
      thirdPhase fourthPhase fifthPhase markerTwoPhase : Nat}
    {digit : Int} {state : Vec2} {letter : PhysicalTemplate}
    (primeProperty : IsPrime prime) (primeBound : 6 * phaseCount < prime)
    (layout : PhaseLayout phaseCount source guessPhase firstPhase secondPhase
      thirdPhase fourthPhase fifthPhase markerTwoPhase)
    (membership : InPhaseAt prime guessPhase digit state)
    (letterMem : letter ∈ alphabet source target guessPhase firstPhase
      secondPhase thirdPhase fourthPhase fifthPhase markerTwoPhase)
    (outputLocal : LocalAt prime (letter.act prime state)) :
    digit = 0 ∧
      (letter = privateLoop guessPhase ∨
        letter = privateExit guessPhase firstPhase) := by
  have forced := force_inPhase_metadata primeProperty primeBound layout
    layout.guessBound membership letterMem outputLocal
  rcases guess_letter_choices layout letterMem forced.1 with h | h
  · subst letter
    exact ⟨by simpa [privateLoop] using forced.2.symm, .inl rfl⟩
  · subst letter
    exact ⟨by simpa [privateExit] using forced.2.symm, .inr rfl⟩

theorem first_letter
    {prime phaseCount source target guessPhase firstPhase secondPhase
      thirdPhase fourthPhase fifthPhase markerTwoPhase : Nat}
    {digit : Int} {state : Vec2} {letter : PhysicalTemplate}
    (primeProperty : IsPrime prime) (primeBound : 6 * phaseCount < prime)
    (layout : PhaseLayout phaseCount source guessPhase firstPhase secondPhase
      thirdPhase fourthPhase fifthPhase markerTwoPhase)
    (membership : InPhaseAt prime firstPhase digit state)
    (letterMem : letter ∈ alphabet source target guessPhase firstPhase
      secondPhase thirdPhase fourthPhase fifthPhase markerTwoPhase)
    (outputLocal : LocalAt prime (letter.act prime state)) :
    (digit = 0 ∧ letter = identityZero firstPhase) ∨
      (digit = 1 ∧ letter = identityMarker firstPhase secondPhase) := by
  have forced := force_inPhase_metadata primeProperty primeBound layout
    layout.firstBound membership letterMem outputLocal
  rcases first_letter_choices layout letterMem forced.1 with h | h
  · subst letter
    exact .inl ⟨by simpa [identityZero] using forced.2.symm, rfl⟩
  · subst letter
    exact .inr ⟨by simpa [identityMarker] using forced.2.symm, rfl⟩

theorem second_letter
    {prime phaseCount source target guessPhase firstPhase secondPhase
      thirdPhase fourthPhase fifthPhase markerTwoPhase : Nat}
    {digit : Int} {state : Vec2} {letter : PhysicalTemplate}
    (primeProperty : IsPrime prime) (primeBound : 6 * phaseCount < prime)
    (layout : PhaseLayout phaseCount source guessPhase firstPhase secondPhase
      thirdPhase fourthPhase fifthPhase markerTwoPhase)
    (membership : InPhaseAt prime secondPhase digit state)
    (letterMem : letter ∈ alphabet source target guessPhase firstPhase
      secondPhase thirdPhase fourthPhase fifthPhase markerTwoPhase)
    (outputLocal : LocalAt prime (letter.act prime state)) :
    (digit = 0 ∧ letter = identityZero secondPhase) ∨
      (digit = 1 ∧ letter = identityMarker secondPhase thirdPhase) := by
  have forced := force_inPhase_metadata primeProperty primeBound layout
    layout.secondBound membership letterMem outputLocal
  rcases second_letter_choices layout letterMem forced.1 with h | h
  · subst letter
    exact .inl ⟨by simpa [identityZero] using forced.2.symm, rfl⟩
  · subst letter
    exact .inr ⟨by simpa [identityMarker] using forced.2.symm, rfl⟩

theorem third_letter
    {prime phaseCount source target guessPhase firstPhase secondPhase
      thirdPhase fourthPhase fifthPhase markerTwoPhase : Nat}
    {digit : Int} {state : Vec2} {letter : PhysicalTemplate}
    (primeProperty : IsPrime prime) (primeBound : 6 * phaseCount < prime)
    (layout : PhaseLayout phaseCount source guessPhase firstPhase secondPhase
      thirdPhase fourthPhase fifthPhase markerTwoPhase)
    (membership : InPhaseAt prime thirdPhase digit state)
    (letterMem : letter ∈ alphabet source target guessPhase firstPhase
      secondPhase thirdPhase fourthPhase fifthPhase markerTwoPhase)
    (outputLocal : LocalAt prime (letter.act prime state)) :
    (digit = 0 ∧ letter = identityZero thirdPhase) ∨
      (digit = 1 ∧ letter = identityMarker thirdPhase fourthPhase) := by
  have forced := force_inPhase_metadata primeProperty primeBound layout
    layout.thirdBound membership letterMem outputLocal
  rcases third_letter_choices layout letterMem forced.1 with h | h
  · subst letter
    exact .inl ⟨by simpa [identityZero] using forced.2.symm, rfl⟩
  · subst letter
    exact .inr ⟨by simpa [identityMarker] using forced.2.symm, rfl⟩

theorem fourth_letter
    {prime phaseCount source target guessPhase firstPhase secondPhase
      thirdPhase fourthPhase fifthPhase markerTwoPhase : Nat}
    {digit : Int} {state : Vec2} {letter : PhysicalTemplate}
    (primeProperty : IsPrime prime) (primeBound : 6 * phaseCount < prime)
    (layout : PhaseLayout phaseCount source guessPhase firstPhase secondPhase
      thirdPhase fourthPhase fifthPhase markerTwoPhase)
    (membership : InPhaseAt prime fourthPhase digit state)
    (letterMem : letter ∈ alphabet source target guessPhase firstPhase
      secondPhase thirdPhase fourthPhase fifthPhase markerTwoPhase)
    (outputLocal : LocalAt prime (letter.act prime state)) :
    (digit = 0 ∧ letter = identityZero fourthPhase) ∨
      (digit = 1 ∧ letter = identityMarker fourthPhase fifthPhase) := by
  have forced := force_inPhase_metadata primeProperty primeBound layout
    layout.fourthBound membership letterMem outputLocal
  rcases fourth_letter_choices layout letterMem forced.1 with h | h
  · subst letter
    exact .inl ⟨by simpa [identityZero] using forced.2.symm, rfl⟩
  · subst letter
    exact .inr ⟨by simpa [identityMarker] using forced.2.symm, rfl⟩

theorem fifth_letter
    {prime phaseCount source target guessPhase firstPhase secondPhase
      thirdPhase fourthPhase fifthPhase markerTwoPhase : Nat}
    {digit : Int} {state : Vec2} {letter : PhysicalTemplate}
    (primeProperty : IsPrime prime) (primeBound : 6 * phaseCount < prime)
    (layout : PhaseLayout phaseCount source guessPhase firstPhase secondPhase
      thirdPhase fourthPhase fifthPhase markerTwoPhase)
    (membership : InPhaseAt prime fifthPhase digit state)
    (letterMem : letter ∈ alphabet source target guessPhase firstPhase
      secondPhase thirdPhase fourthPhase fifthPhase markerTwoPhase)
    (outputLocal : LocalAt prime (letter.act prime state)) :
    (digit = 0 ∧ letter = identityZero fifthPhase) ∨
      (digit = 1 ∧ letter = inverseTMarker fifthPhase markerTwoPhase) := by
  have forced := force_inPhase_metadata primeProperty primeBound layout
    layout.fifthBound membership letterMem outputLocal
  rcases fifth_letter_choices layout letterMem forced.1 with h | h
  · subst letter
    exact .inl ⟨by simpa [identityZero] using forced.2.symm, rfl⟩
  · subst letter
    exact .inr ⟨by simpa [inverseTMarker] using forced.2.symm, rfl⟩

theorem markerTwo_letter
    {prime phaseCount source target guessPhase firstPhase secondPhase
      thirdPhase fourthPhase fifthPhase markerTwoPhase : Nat}
    {digit : Int} {state : Vec2} {letter : PhysicalTemplate}
    (primeProperty : IsPrime prime) (primeBound : 6 * phaseCount < prime)
    (layout : PhaseLayout phaseCount source guessPhase firstPhase secondPhase
      thirdPhase fourthPhase fifthPhase markerTwoPhase)
    (membership : InPhaseAt prime markerTwoPhase digit state)
    (letterMem : letter ∈ alphabet source target guessPhase firstPhase
      secondPhase thirdPhase fourthPhase fifthPhase markerTwoPhase)
    (outputLocal : LocalAt prime (letter.act prime state)) :
    (digit = 0 ∧ letter = identityZero markerTwoPhase) ∨
      (digit = 2 ∧ letter = negatingTMarker markerTwoPhase target) := by
  have forced := force_inPhase_metadata primeProperty primeBound layout
    layout.markerTwoBound membership letterMem outputLocal
  rcases markerTwo_letter_choices layout letterMem forced.1 with h | h
  · subst letter
    exact .inl ⟨by simpa [identityZero] using forced.2.symm, rfl⟩
  · subst letter
    exact .inr ⟨by simpa [negatingTMarker] using forced.2.symm, rfl⟩

private theorem word_nonempty_of_endpoint_phase_ne
    {prime phaseCount currentPhase endpointPhase : Nat}
    {currentDigit endpointDigit : Int} {current endpoint : Vec2}
    (primeProperty : IsPrime prime) (primeBound : 6 * phaseCount < prime)
    (currentBound : currentPhase < phaseCount)
    (endpointBound : endpointPhase < phaseCount)
    (phaseNe : currentPhase ≠ endpointPhase)
    (currentMembership : InPhaseAt prime currentPhase currentDigit current)
    (endpointMembership : InPhaseAt prime endpointPhase endpointDigit endpoint)
    {word : List PhysicalTemplate}
    (completeRun : SameLine (physicalWordAction prime word current) endpoint) :
    word ≠ [] := by
  intro wordEmpty
  subst word
  have phasesEq := (currentMembership.unique primeProperty primeBound
    currentBound endpointBound endpointMembership (by
      simpa [physicalWordAction] using completeRun)).1
  exact phaseNe phasesEq

/-- A completed path in the private prefix phase must choose its exit before
the unary marker. -/
theorem guessTail_forced_exit_to_endpoint
    {prime phaseCount source target guessPhase firstPhase secondPhase
      thirdPhase fourthPhase fifthPhase markerTwoPhase endpointPhase : Nat}
    {endpointDigit : Int} {endpoint : Vec2}
    (primeProperty : IsPrime prime) (primeBound : 6 * phaseCount < prime)
    (layout : PhaseLayout phaseCount source guessPhase firstPhase secondPhase
      thirdPhase fourthPhase fifthPhase markerTwoPhase)
    (endpointBound : endpointPhase < phaseCount)
    (guessEndpointDistinct : guessPhase ≠ endpointPhase)
    (endpointMembership : InPhaseAt prime endpointPhase endpointDigit endpoint)
    {counter deleted remaining : Nat} (sumEq : deleted + remaining = counter)
    {word : List PhysicalTemplate}
    (wordOver : WordOver
      (alphabet source target guessPhase firstPhase secondPhase thirdPhase
        fourthPhase fifthPhase markerTwoPhase) word)
    (allLocal : AllStatesLocal prime word
      (phaseAffine guessPhase (prefixState prime counter deleted)))
    (completeRun : SameLine
      (physicalWordAction prime word
        (phaseAffine guessPhase (prefixState prime counter deleted))) endpoint) :
    ∃ loops suffix,
      loops < remaining ∧
      word = prefixTail guessPhase firstPhase loops ++ suffix ∧
      WordOver
        (alphabet source target guessPhase firstPhase secondPhase thirdPhase
          fourthPhase fifthPhase markerTwoPhase) suffix ∧
      AllStatesLocal prime suffix
        (phaseAffine firstPhase
          (T prime (prefixState prime counter (deleted + loops + 1)))) ∧
      SameLine
        (physicalWordAction prime suffix
          (phaseAffine firstPhase
            (T prime (prefixState prime counter (deleted + loops + 1)))))
        endpoint := by
  induction remaining generalizing deleted word with
  | zero =>
      have deletedEq : deleted = counter := by omega
      have currentMembership := TernaryFrontModule.guessState_inPhaseAt_marker
        (guessPhase := guessPhase) (counter := counter) primeProperty
      have wordNonempty := word_nonempty_of_endpoint_phase_ne primeProperty
        primeBound layout.guessBound endpointBound guessEndpointDistinct
        currentMembership endpointMembership (word := word) (by
          simpa only [deletedEq] using completeRun)
      cases word with
      | nil => exact False.elim (wordNonempty rfl)
      | cons letter tail =>
          have letterMem := wordOver letter (by simp)
          rcases guess_letter primeProperty primeBound layout
              (by simpa only [deletedEq] using currentMembership) letterMem
              (by simpa only [deletedEq] using allLocal.2.start) with
            ⟨digitEq, _⟩
          omega
  | succ remaining inductionHypothesis =>
      have deletedBelow : deleted < counter := by omega
      have currentMembership := TernaryFrontModule.guessState_inPhaseAt_before
        (guessPhase := guessPhase) (counter := counter) (deleted := deleted)
        primeProperty deletedBelow
      have wordNonempty := word_nonempty_of_endpoint_phase_ne primeProperty
        primeBound layout.guessBound endpointBound guessEndpointDistinct
        currentMembership endpointMembership completeRun
      cases word with
      | nil => exact False.elim (wordNonempty rfl)
      | cons letter tail =>
          have letterMem := wordOver letter (by simp)
          have tailOver : WordOver
              (alphabet source target guessPhase firstPhase secondPhase
                thirdPhase fourthPhase fifthPhase markerTwoPhase) tail := by
            intro candidate candidateMem
            exact wordOver candidate (by simp [candidateMem])
          obtain ⟨_, letterEq | letterEq⟩ :=
            guess_letter primeProperty primeBound layout currentMembership
              letterMem allLocal.2.start
          · subst letter
            have firstStep := privateLoop_step prime guessPhase counter deleted
              primeProperty.1 deletedBelow
            have canonicalLocal := phasePrefixState_local prime guessPhase
              counter (deleted + 1) primeProperty.1
            have tailLocal : AllStatesLocal prime tail
                (phaseAffine guessPhase
                  (prefixState prime counter (deleted + 1))) := by
              apply AllStatesLocal.of_sameLine
                (primePositive := by have := primeProperty.1; omega)
                allLocal.2 canonicalLocal.1 firstStep.symm
            have tailRun : SameLine
                (physicalWordAction prime tail
                  (phaseAffine guessPhase
                    (prefixState prime counter (deleted + 1)))) endpoint :=
              physicalWordAction_tail_sameLine prime
                (privateLoop guessPhase) tail firstStep completeRun
            obtain ⟨loops, suffix, loopsBound, tailEq, suffixOver,
                suffixLocal, suffixRun⟩ :=
              inductionHypothesis (deleted := deleted + 1) (by omega)
                tailOver tailLocal tailRun
            refine ⟨loops + 1, suffix, by omega, ?_, suffixOver, ?_, ?_⟩
            · rw [tailEq]
              simp [prefixTail, List.replicate_succ]
            · simpa only [show deleted + 1 + loops + 1 =
                  deleted + (loops + 1) + 1 by omega] using suffixLocal
            · simpa only [show deleted + 1 + loops + 1 =
                  deleted + (loops + 1) + 1 by omega] using suffixRun
          · subst letter
            have firstStep := privateExit_step prime guessPhase firstPhase
              counter deleted primeProperty.1 deletedBelow
            have canonicalLocal := phaseTPrefixState_local prime firstPhase
              counter (deleted + 1) primeProperty.1
            have tailLocal : AllStatesLocal prime tail
                (phaseAffine firstPhase
                  (T prime (prefixState prime counter (deleted + 1)))) := by
              apply AllStatesLocal.of_sameLine
                (primePositive := by have := primeProperty.1; omega)
                allLocal.2 canonicalLocal.1 firstStep.symm
            have tailRun : SameLine
                (physicalWordAction prime tail
                  (phaseAffine firstPhase
                    (T prime (prefixState prime counter (deleted + 1)))))
                  endpoint :=
              physicalWordAction_tail_sameLine prime
                (privateExit guessPhase firstPhase) tail firstStep completeRun
            exact ⟨0, tail, by omega, by simp [prefixTail], tailOver,
              by simpa using tailLocal, by simpa using tailRun⟩

/-- Boundary-aware parser for a nonempty nondeterministic unary split.
The explicit nonemptiness hypothesis permits the guarded endpoint to be the
source phase; the first surviving letter immediately leaves that phase. -/
theorem prefix_choice_forced_to_endpoint_of_nonempty
    {prime phaseCount source target guessPhase firstPhase secondPhase
      thirdPhase fourthPhase fifthPhase markerTwoPhase endpointPhase : Nat}
    {endpointDigit : Int} {endpoint : Vec2}
    (primeProperty : IsPrime prime) (primeBound : 6 * phaseCount < prime)
    (layout : PhaseLayout phaseCount source guessPhase firstPhase secondPhase
      thirdPhase fourthPhase fifthPhase markerTwoPhase)
    (endpointBound : endpointPhase < phaseCount)
    (guessEndpointDistinct : guessPhase ≠ endpointPhase)
    (endpointMembership : InPhaseAt prime endpointPhase endpointDigit endpoint)
    {counter : Nat} (counterPositive : 0 < counter)
    {word : List PhysicalTemplate}
    (wordOver : WordOver
      (alphabet source target guessPhase firstPhase secondPhase thirdPhase
        fourthPhase fifthPhase markerTwoPhase) word)
    (wordNonempty : word ≠ [])
    (allLocal : AllStatesLocal prime word
      (phaseAffine source (unaryCode prime counter)))
    (completeRun : SameLine
      (physicalWordAction prime word
        (phaseAffine source (unaryCode prime counter))) endpoint) :
    ∃ first guess suffix,
      0 < guess ∧ first + guess = counter ∧
      word = prefixWord source guessPhase firstPhase guess ++ suffix ∧
      WordOver
        (alphabet source target guessPhase firstPhase secondPhase thirdPhase
          fourthPhase fifthPhase markerTwoPhase) suffix ∧
      AllStatesLocal prime suffix
        (phaseAffine firstPhase (firstAutomaticState prime first guess 0)) ∧
      SameLine
        (physicalWordAction prime suffix
          (phaseAffine firstPhase
            (firstAutomaticState prime first guess 0))) endpoint := by
  obtain ⟨previous, counterEq⟩ :=
    Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt counterPositive)
  subst counter
  have sourceMembership := TernaryFrontModule.sourceState_inPhaseAt_positive
    (prime := prime) (source := source) (counter := previous + 1)
    primeProperty (by omega)
  cases word with
  | nil => exact False.elim (wordNonempty rfl)
  | cons letter tail =>
      have letterMem := wordOver letter (by simp)
      have tailOver : WordOver
          (alphabet source target guessPhase firstPhase secondPhase thirdPhase
            fourthPhase fifthPhase markerTwoPhase) tail := by
        intro candidate candidateMem
        exact wordOver candidate (by simp [candidateMem])
      obtain ⟨_, letterEq | letterEq⟩ :=
        source_letter primeProperty primeBound layout sourceMembership
          letterMem allLocal.2.start
      · subst letter
        have firstStep := startContinue_step prime source guessPhase
          (previous + 1) primeProperty.1 (by omega)
        have canonicalLocal := phasePrefixState_local prime guessPhase
          (previous + 1) 1 primeProperty.1
        have tailLocal : AllStatesLocal prime tail
            (phaseAffine guessPhase
              (prefixState prime (previous + 1) 1)) := by
          apply AllStatesLocal.of_sameLine
            (primePositive := by have := primeProperty.1; omega)
            allLocal.2 canonicalLocal.1 firstStep.symm
        have tailRun : SameLine
            (physicalWordAction prime tail
              (phaseAffine guessPhase
                (prefixState prime (previous + 1) 1))) endpoint :=
          physicalWordAction_tail_sameLine prime
            (startContinue source guessPhase) tail firstStep completeRun
        obtain ⟨loops, suffix, loopsBound, tailEq, suffixOver,
            suffixLocal, suffixRun⟩ := guessTail_forced_exit_to_endpoint
          primeProperty primeBound layout endpointBound guessEndpointDistinct
          endpointMembership (counter := previous + 1) (deleted := 1)
          (remaining := previous) (by omega) tailOver tailLocal tailRun
        have splitEq :
            (previous - (loops + 1)) + (loops + 2) = previous + 1 := by
          omega
        refine ⟨previous - (loops + 1), loops + 2, suffix, by omega,
          splitEq, ?_, suffixOver, ?_, ?_⟩
        · rw [tailEq]
          simp [prefixWord, prefixTail]
        · rw [firstAutomaticState_zero prime
              (previous - (loops + 1)) (loops + 2) primeProperty.1]
          rw [splitEq]
          simpa only [show 1 + loops + 1 = loops + 2 by omega] using
            suffixLocal
        · rw [firstAutomaticState_zero prime
              (previous - (loops + 1)) (loops + 2) primeProperty.1]
          rw [splitEq]
          simpa only [show 1 + loops + 1 = loops + 2 by omega] using
            suffixRun
      · subst letter
        have firstStep := startExit_step prime source firstPhase
          (previous + 1) primeProperty.1 (by omega)
        have canonicalLocal := phaseTPrefixState_local prime firstPhase
          (previous + 1) 1 primeProperty.1
        have tailLocal : AllStatesLocal prime tail
            (phaseAffine firstPhase
              (T prime (prefixState prime (previous + 1) 1))) := by
          apply AllStatesLocal.of_sameLine
            (primePositive := by have := primeProperty.1; omega)
            allLocal.2 canonicalLocal.1 firstStep.symm
        have tailRun : SameLine
            (physicalWordAction prime tail
              (phaseAffine firstPhase
                (T prime (prefixState prime (previous + 1) 1)))) endpoint :=
          physicalWordAction_tail_sameLine prime
            (startExit source firstPhase) tail firstStep completeRun
        refine ⟨previous, 1, tail, by omega, by omega, by simp [prefixWord],
          tailOver, ?_, ?_⟩
        · rw [firstAutomaticState_zero prime previous 1 primeProperty.1]
          simpa using tailLocal
        · rw [firstAutomaticState_zero prime previous 1 primeProperty.1]
          simpa using tailRun

/-- Boundary-aware parser for the nondeterministic unary split. -/
theorem prefix_choice_forced_to_endpoint
    {prime phaseCount source target guessPhase firstPhase secondPhase
      thirdPhase fourthPhase fifthPhase markerTwoPhase endpointPhase : Nat}
    {endpointDigit : Int} {endpoint : Vec2}
    (primeProperty : IsPrime prime) (primeBound : 6 * phaseCount < prime)
    (layout : PhaseLayout phaseCount source guessPhase firstPhase secondPhase
      thirdPhase fourthPhase fifthPhase markerTwoPhase)
    (endpointBound : endpointPhase < phaseCount)
    (sourceEndpointDistinct : source ≠ endpointPhase)
    (guessEndpointDistinct : guessPhase ≠ endpointPhase)
    (endpointMembership : InPhaseAt prime endpointPhase endpointDigit endpoint)
    {counter : Nat} (counterPositive : 0 < counter)
    {word : List PhysicalTemplate}
    (wordOver : WordOver
      (alphabet source target guessPhase firstPhase secondPhase thirdPhase
        fourthPhase fifthPhase markerTwoPhase) word)
    (allLocal : AllStatesLocal prime word
      (phaseAffine source (unaryCode prime counter)))
    (completeRun : SameLine
      (physicalWordAction prime word
        (phaseAffine source (unaryCode prime counter))) endpoint) :
    ∃ first guess suffix,
      0 < guess ∧ first + guess = counter ∧
      word = prefixWord source guessPhase firstPhase guess ++ suffix ∧
      WordOver
        (alphabet source target guessPhase firstPhase secondPhase thirdPhase
          fourthPhase fifthPhase markerTwoPhase) suffix ∧
      AllStatesLocal prime suffix
        (phaseAffine firstPhase (firstAutomaticState prime first guess 0)) ∧
      SameLine
        (physicalWordAction prime suffix
          (phaseAffine firstPhase
            (firstAutomaticState prime first guess 0))) endpoint := by
  obtain ⟨sourceDigit, sourceMembership⟩ := unaryCode_inPhaseAt
    (base := prime) (phase := source) (counter := counter) primeProperty.1
  have wordNonempty := word_nonempty_of_endpoint_phase_ne primeProperty
    primeBound layout.sourceBound endpointBound sourceEndpointDistinct
    sourceMembership endpointMembership completeRun
  exact prefix_choice_forced_to_endpoint_of_nonempty primeProperty primeBound
    layout endpointBound guessEndpointDistinct endpointMembership
    counterPositive wordOver wordNonempty allLocal completeRun

/-- Boundary-aware parser for the first plain marker-one scan. -/
theorem firstScanTail_forced_prefix_to_endpoint
    {prime phaseCount source target guessPhase firstPhase secondPhase
      thirdPhase fourthPhase fifthPhase markerTwoPhase endpointPhase : Nat}
    {endpointDigit : Int} {endpoint : Vec2}
    (primeProperty : IsPrime prime) (primeBound : 6 * phaseCount < prime)
    (layout : PhaseLayout phaseCount source guessPhase firstPhase secondPhase
      thirdPhase fourthPhase fifthPhase markerTwoPhase)
    (endpointBound : endpointPhase < phaseCount)
    (firstEndpointDistinct : firstPhase ≠ endpointPhase)
    (endpointMembership : InPhaseAt prime endpointPhase endpointDigit endpoint)
    {first guess deleted remaining : Nat}
    (sumEq : deleted + remaining = first)
    {word : List PhysicalTemplate}
    (wordOver : WordOver
      (alphabet source target guessPhase firstPhase secondPhase thirdPhase
        fourthPhase fifthPhase markerTwoPhase) word)
    (allLocal : AllStatesLocal prime word
      (phaseAffine firstPhase
        (firstAutomaticState prime first guess deleted)))
    (completeRun : SameLine
      (physicalWordAction prime word
        (phaseAffine firstPhase
          (firstAutomaticState prime first guess deleted))) endpoint) :
    ∃ suffix,
      word = List.replicate remaining (identityZero firstPhase) ++
          [identityMarker firstPhase secondPhase] ++ suffix ∧
      WordOver
        (alphabet source target guessPhase firstPhase secondPhase thirdPhase
          fourthPhase fifthPhase markerTwoPhase) suffix ∧
      AllStatesLocal prime suffix
        (phaseAffine secondPhase
          (secondAutomaticState prime first guess 0)) ∧
      SameLine
        (physicalWordAction prime suffix
          (phaseAffine secondPhase
            (secondAutomaticState prime first guess 0))) endpoint := by
  have nextLocal : LocalAt prime
      (phaseAffine secondPhase
        (secondAutomaticState prime first guess 0)) :=
    phaseLocal (secondAutomaticState_local prime first guess 0
      primeProperty.1)
  have parsed := forcedScanPrefixToEndpoint
    (Certificate := True) (primeProperty := primeProperty)
    (primeBound := primeBound) (currentBound := layout.firstBound)
    (endpointBound := endpointBound) (phaseDistinct := firstEndpointDistinct)
    (endpointMembership := endpointMembership)
    (beforeMembership := fun position positionBelow =>
      TernaryFrontModule.firstState_inPhaseAt_before
        (firstPhase := firstPhase) (first := first) (guess := guess)
        (deleted := position) primeProperty positionBelow)
    (markerMembership := TernaryFrontModule.firstState_inPhaseAt_marker
      (firstPhase := firstPhase) (first := first) (guess := guess)
      primeProperty)
    (stateLocal := fun position _ =>
      phaseLocal (firstAutomaticState_local prime first guess position
        primeProperty.1))
    (nextLocal := nextLocal)
    (forceLoop := fun position positionBelow {letter} letterMem outputLocal =>
      by
        rcases first_letter primeProperty primeBound layout
            (TernaryFrontModule.firstState_inPhaseAt_before
              (firstPhase := firstPhase) (first := first) (guess := guess)
              (deleted := position) primeProperty positionBelow)
            letterMem outputLocal with
          ⟨_, letterEq⟩ | ⟨digitEq, _⟩
        · exact letterEq
        · omega)
    (forceExit := fun {letter} letterMem outputLocal => by
      rcases first_letter primeProperty primeBound layout
          (TernaryFrontModule.firstState_inPhaseAt_marker
            (firstPhase := firstPhase) (first := first) (guess := guess)
            primeProperty) letterMem outputLocal with
        ⟨digitEq, _⟩ | ⟨_, letterEq⟩
      · omega
      · exact ⟨True.intro, letterEq⟩)
    (loopStep := fun position positionBelow =>
      firstZero_step prime firstPhase first guess position primeProperty.1
        positionBelow)
    (exitStep := fun _ => by
      rw [secondAutomaticState_zero]
      exact firstMarker_step prime firstPhase secondPhase first guess
        primeProperty.1)
    sumEq wordOver allLocal completeRun
  rcases parsed with ⟨suffix, _, wordEq, suffixOver, suffixLocal, suffixRun⟩
  exact ⟨suffix, wordEq, suffixOver, suffixLocal, suffixRun⟩

/-- Boundary-aware parser for the second plain marker-one scan. -/
theorem secondScanTail_forced_prefix_to_endpoint
    {prime phaseCount source target guessPhase firstPhase secondPhase
      thirdPhase fourthPhase fifthPhase markerTwoPhase endpointPhase : Nat}
    {endpointDigit : Int} {endpoint : Vec2}
    (primeProperty : IsPrime prime) (primeBound : 6 * phaseCount < prime)
    (layout : PhaseLayout phaseCount source guessPhase firstPhase secondPhase
      thirdPhase fourthPhase fifthPhase markerTwoPhase)
    (endpointBound : endpointPhase < phaseCount)
    (secondEndpointDistinct : secondPhase ≠ endpointPhase)
    (endpointMembership : InPhaseAt prime endpointPhase endpointDigit endpoint)
    {first guess deleted remaining : Nat} (guessPositive : 0 < guess)
    (sumEq : deleted + remaining = first)
    {word : List PhysicalTemplate}
    (wordOver : WordOver
      (alphabet source target guessPhase firstPhase secondPhase thirdPhase
        fourthPhase fifthPhase markerTwoPhase) word)
    (allLocal : AllStatesLocal prime word
      (phaseAffine secondPhase
        (secondAutomaticState prime first guess deleted)))
    (completeRun : SameLine
      (physicalWordAction prime word
        (phaseAffine secondPhase
          (secondAutomaticState prime first guess deleted))) endpoint) :
    ∃ suffix,
      word = List.replicate remaining (identityZero secondPhase) ++
          [identityMarker secondPhase thirdPhase] ++ suffix ∧
      WordOver
        (alphabet source target guessPhase firstPhase secondPhase thirdPhase
          fourthPhase fifthPhase markerTwoPhase) suffix ∧
      AllStatesLocal prime suffix
        (phaseAffine thirdPhase
          (thirdAutomaticState prime first guess 0)) ∧
      SameLine
        (physicalWordAction prime suffix
          (phaseAffine thirdPhase
            (thirdAutomaticState prime first guess 0))) endpoint := by
  have nextLocal : LocalAt prime
      (phaseAffine thirdPhase
        (thirdAutomaticState prime first guess 0)) :=
    phaseLocal (thirdAutomaticState_local prime first guess 0 primeProperty.1)
  have parsed := forcedScanPrefixToEndpoint
    (Certificate := True) (primeProperty := primeProperty)
    (primeBound := primeBound) (currentBound := layout.secondBound)
    (endpointBound := endpointBound) (phaseDistinct := secondEndpointDistinct)
    (endpointMembership := endpointMembership)
    (beforeMembership := fun position positionBelow =>
      TernaryFrontModule.secondState_inPhaseAt_before
        (secondPhase := secondPhase) (first := first) (guess := guess)
        (deleted := position) primeProperty positionBelow)
    (markerMembership := TernaryFrontModule.secondState_inPhaseAt_marker
      (secondPhase := secondPhase) (first := first) (guess := guess)
      primeProperty guessPositive)
    (stateLocal := fun position _ =>
      phaseLocal (secondAutomaticState_local prime first guess position
        primeProperty.1))
    (nextLocal := nextLocal)
    (forceLoop := fun position positionBelow {letter} letterMem outputLocal =>
      by
        rcases second_letter primeProperty primeBound layout
            (TernaryFrontModule.secondState_inPhaseAt_before
              (secondPhase := secondPhase) (first := first) (guess := guess)
              (deleted := position) primeProperty positionBelow)
            letterMem outputLocal with
          ⟨_, letterEq⟩ | ⟨digitEq, _⟩
        · exact letterEq
        · omega)
    (forceExit := fun {letter} letterMem outputLocal => by
      rcases second_letter primeProperty primeBound layout
          (TernaryFrontModule.secondState_inPhaseAt_marker
            (secondPhase := secondPhase) (first := first) (guess := guess)
            primeProperty guessPositive) letterMem outputLocal with
        ⟨digitEq, _⟩ | ⟨_, letterEq⟩
      · omega
      · exact ⟨True.intro, letterEq⟩)
    (loopStep := fun position positionBelow =>
      secondZero_step prime secondPhase first guess position primeProperty.1
        positionBelow)
    (exitStep := fun _ => by
      rw [thirdAutomaticState_zero]
      exact TernaryFrontModule.secondPlainMarker_step prime secondPhase
        thirdPhase first guess primeProperty.1 guessPositive)
    sumEq wordOver allLocal completeRun
  rcases parsed with ⟨suffix, _, wordEq, suffixOver, suffixLocal, suffixRun⟩
  exact ⟨suffix, wordEq, suffixOver, suffixLocal, suffixRun⟩

/-- Boundary-aware parser for the third scan.  Its marker-one exit also
certifies that the equality `guess = first + 1` was not guessed. -/
theorem thirdScanTail_forced_prefix_to_endpoint
    {prime phaseCount source target guessPhase firstPhase secondPhase
      thirdPhase fourthPhase fifthPhase markerTwoPhase endpointPhase : Nat}
    {endpointDigit : Int} {endpoint : Vec2}
    (primeProperty : IsPrime prime) (primeBound : 6 * phaseCount < prime)
    (layout : PhaseLayout phaseCount source guessPhase firstPhase secondPhase
      thirdPhase fourthPhase fifthPhase markerTwoPhase)
    (endpointBound : endpointPhase < phaseCount)
    (thirdEndpointDistinct : thirdPhase ≠ endpointPhase)
    (endpointMembership : InPhaseAt prime endpointPhase endpointDigit endpoint)
    {first guess deleted remaining : Nat} (guessPositive : 0 < guess)
    (sumEq : deleted + remaining = thirdScanLength first guess)
    {word : List PhysicalTemplate}
    (wordOver : WordOver
      (alphabet source target guessPhase firstPhase secondPhase thirdPhase
        fourthPhase fifthPhase markerTwoPhase) word)
    (allLocal : AllStatesLocal prime word
      (phaseAffine thirdPhase
        (thirdAutomaticState prime first guess deleted)))
    (completeRun : SameLine
      (physicalWordAction prime word
        (phaseAffine thirdPhase
          (thirdAutomaticState prime first guess deleted))) endpoint) :
    ∃ suffix,
      first ≠ guess - 1 ∧
      word = List.replicate remaining (identityZero thirdPhase) ++
          [identityMarker thirdPhase fourthPhase] ++ suffix ∧
      WordOver
        (alphabet source target guessPhase firstPhase secondPhase thirdPhase
          fourthPhase fifthPhase markerTwoPhase) suffix ∧
      AllStatesLocal prime suffix
        (phaseAffine fourthPhase (fourthState prime first guess 0)) ∧
      SameLine
        (physicalWordAction prime suffix
          (phaseAffine fourthPhase (fourthState prime first guess 0)))
        endpoint := by
  have nextLocal : LocalAt prime
      (phaseAffine fourthPhase (fourthState prime first guess 0)) :=
    phaseLocal (fourthState_local prime first guess 0 primeProperty.1)
  have parsed := forcedScanPrefixToEndpoint
    (Certificate := first ≠ guess - 1) (primeProperty := primeProperty)
    (primeBound := primeBound) (currentBound := layout.thirdBound)
    (endpointBound := endpointBound) (phaseDistinct := thirdEndpointDistinct)
    (endpointMembership := endpointMembership)
    (beforeMembership := fun position positionBelow =>
      TernaryFrontModule.thirdState_inPhaseAt_before
        (thirdPhase := thirdPhase) (first := first) (guess := guess)
        (deleted := position) primeProperty positionBelow)
    (markerMembership := TernaryFrontModule.thirdState_inPhaseAt_marker
      (thirdPhase := thirdPhase) (first := first) (guess := guess)
      primeProperty guessPositive)
    (stateLocal := fun position _ =>
      phaseLocal (thirdAutomaticState_local prime first guess position
        primeProperty.1))
    (nextLocal := nextLocal)
    (forceLoop := fun position positionBelow {letter} letterMem outputLocal =>
      by
        rcases third_letter primeProperty primeBound layout
            (TernaryFrontModule.thirdState_inPhaseAt_before
              (thirdPhase := thirdPhase) (first := first) (guess := guess)
              (deleted := position) primeProperty positionBelow)
            letterMem outputLocal with
          ⟨_, letterEq⟩ | ⟨digitEq, _⟩
        · exact letterEq
        · omega)
    (forceExit := fun {letter} letterMem outputLocal => by
      rcases third_letter primeProperty primeBound layout
          (TernaryFrontModule.thirdState_inPhaseAt_marker
            (thirdPhase := thirdPhase) (first := first) (guess := guess)
            primeProperty guessPositive) letterMem outputLocal with
        ⟨digitEq, _⟩ | ⟨digitEq, letterEq⟩
      · unfold thirdMarkerDigit at digitEq
        split at digitEq <;> omega
      · have accepted : first ≠ guess - 1 := by
          unfold thirdMarkerDigit at digitEq
          split at digitEq
          · omega
          · assumption
        exact ⟨accepted, letterEq⟩)
    (loopStep := fun position positionBelow =>
      TernaryFrontModule.thirdZero_step prime thirdPhase first guess position
        primeProperty.1 positionBelow)
    (exitStep := fun accepted =>
      thirdPlainMarker_step prime thirdPhase fourthPhase first guess
        primeProperty.1 guessPositive accepted)
    sumEq wordOver allLocal completeRun
  exact parsed

theorem fourthState_inPhaseAt_before
    {prime fourthPhase first guess deleted : Nat}
    (primeProperty : IsPrime prime)
    (deletedBelow : deleted < fourthZeroCount first guess) :
    InPhaseAt prime fourthPhase 0
      (phaseAffine fourthPhase (fourthState prime first guess deleted)) := by
  apply inPhaseAt_phaseAffine_integer (by simp [ReservedDigit])
    (halfIntegerDenominator_not_dvd prime first guess primeProperty.1)
    (by simpa using
      (fourthState_zero_residue prime first guess deleted deletedBelow))
  exact fourthState_sameLine_integer prime first guess deleted primeProperty.1

theorem fourthState_inPhaseAt_marker
    {prime fourthPhase first guess : Nat}
    (primeProperty : IsPrime prime) (guessPositive : 0 < guess)
    (thirdAccepted : first ≠ guess - 1) :
    InPhaseAt prime fourthPhase (fourthMarkerDigit first guess)
      (phaseAffine fourthPhase
        (fourthState prime first guess (fourthZeroCount first guess))) := by
  apply inPhaseAt_phaseAffine_integer
    (by unfold fourthMarkerDigit ternaryValidatorMarkerDigit
        split <;> simp [ReservedDigit])
    (halfIntegerDenominator_not_dvd prime first guess primeProperty.1)
    (fourthState_marker_residue prime first guess guessPositive thirdAccepted)
  exact fourthState_sameLine_integer prime first guess
    (fourthZeroCount first guess) primeProperty.1

theorem fourthMarker_step
    (base fourthPhase fifthPhase first guess : Nat)
    (baseAtLeastTwo : 2 ≤ base)
    {next : Rat}
    (nextLocal : LocalAt base (Vec2.affine next))
    (deletedEq : deleteDigit (base : Rat) 1
        (fourthState base first guess (fourthZeroCount first guess)) = next) :
    SameLine
      ((identityMarker fourthPhase fifthPhase).act base
        (phaseAffine fourthPhase
          (fourthState base first guess (fourthZeroCount first guess))))
      (phaseAffine fifthPhase next) := by
  have step := marker_step (source := fourthPhase) (target := fifthPhase)
    (digit := 1) (coefficient := 0) (sign := .positive)
    (value := fourthState base first guess (fourthZeroCount first guess))
    (deleted := next) (output := next) (by omega)
    (fourthState_local base first guess (fourthZeroCount first guess)
      baseAtLeastTwo) nextLocal deletedEq (by simp)
  simpa [identityMarker, PhysicalTemplate.act, PhysicalTemplate.matrix]
    using step

/-- Parser for the fourth scan in any branch where its marker has digit one.
The caller supplies the branch-specific arithmetic normal form `next`. -/
theorem fourthScanTail_forced_prefix_to_endpoint
    {prime phaseCount source target guessPhase firstPhase secondPhase
      thirdPhase fourthPhase fifthPhase markerTwoPhase endpointPhase : Nat}
    {endpointDigit : Int} {endpoint : Vec2}
    (primeProperty : IsPrime prime) (primeBound : 6 * phaseCount < prime)
    (layout : PhaseLayout phaseCount source guessPhase firstPhase secondPhase
      thirdPhase fourthPhase fifthPhase markerTwoPhase)
    (endpointBound : endpointPhase < phaseCount)
    (fourthEndpointDistinct : fourthPhase ≠ endpointPhase)
    (endpointMembership : InPhaseAt prime endpointPhase endpointDigit endpoint)
    {first guess deleted remaining : Nat} (guessPositive : 0 < guess)
    (thirdAccepted : first ≠ guess - 1)
    (markerOne : fourthMarkerDigit first guess = 1)
    {next : Rat} (nextLocalAffine : LocalAt prime (Vec2.affine next))
    (deletedEq : deleteDigit (prime : Rat) 1
        (fourthState prime first guess (fourthZeroCount first guess)) = next)
    (sumEq : deleted + remaining = fourthZeroCount first guess)
    {word : List PhysicalTemplate}
    (wordOver : WordOver
      (alphabet source target guessPhase firstPhase secondPhase thirdPhase
        fourthPhase fifthPhase markerTwoPhase) word)
    (allLocal : AllStatesLocal prime word
      (phaseAffine fourthPhase (fourthState prime first guess deleted)))
    (completeRun : SameLine
      (physicalWordAction prime word
        (phaseAffine fourthPhase (fourthState prime first guess deleted)))
      endpoint) :
    ∃ suffix,
      word = List.replicate remaining (identityZero fourthPhase) ++
          [identityMarker fourthPhase fifthPhase] ++ suffix ∧
      WordOver
        (alphabet source target guessPhase firstPhase secondPhase thirdPhase
          fourthPhase fifthPhase markerTwoPhase) suffix ∧
      AllStatesLocal prime suffix (phaseAffine fifthPhase next) ∧
      SameLine (physicalWordAction prime suffix
        (phaseAffine fifthPhase next)) endpoint := by
  have parsed := forcedScanPrefixToEndpoint
    (Certificate := True) (primeProperty := primeProperty)
    (primeBound := primeBound) (currentBound := layout.fourthBound)
    (endpointBound := endpointBound) (phaseDistinct := fourthEndpointDistinct)
    (endpointMembership := endpointMembership)
    (beforeMembership := fun position positionBelow =>
      fourthState_inPhaseAt_before (fourthPhase := fourthPhase)
        (first := first) (guess := guess) (deleted := position)
        primeProperty positionBelow)
    (markerMembership := fourthState_inPhaseAt_marker
      (fourthPhase := fourthPhase) (first := first) (guess := guess)
      primeProperty guessPositive thirdAccepted)
    (stateLocal := fun position _ =>
      phaseLocal (fourthState_local prime first guess position
        primeProperty.1))
    (nextLocal := phaseLocal nextLocalAffine)
    (forceLoop := fun position positionBelow {letter} letterMem outputLocal =>
      by
        rcases fourth_letter primeProperty primeBound layout
            (fourthState_inPhaseAt_before (fourthPhase := fourthPhase)
              (first := first) (guess := guess) (deleted := position)
              primeProperty positionBelow)
            letterMem outputLocal with
          ⟨_, letterEq⟩ | ⟨digitEq, _⟩
        · exact letterEq
        · omega)
    (forceExit := fun {letter} letterMem outputLocal => by
      rcases fourth_letter primeProperty primeBound layout
          (fourthState_inPhaseAt_marker (fourthPhase := fourthPhase)
            (first := first) (guess := guess) primeProperty guessPositive
            thirdAccepted) letterMem outputLocal with
        ⟨digitEq, _⟩ | ⟨_, letterEq⟩
      · rw [markerOne] at digitEq
        omega
      · exact ⟨True.intro, letterEq⟩)
    (loopStep := fun position positionBelow =>
      fourthZero_step prime fourthPhase first guess position primeProperty.1
        positionBelow)
    (exitStep := fun _ => fourthMarker_step prime fourthPhase fifthPhase
      first guess primeProperty.1 nextLocalAffine deletedEq)
    sumEq wordOver allLocal completeRun
  rcases parsed with ⟨suffix, _, wordEq, suffixOver, suffixLocal, suffixRun⟩
  exact ⟨suffix, wordEq, suffixOver, suffixLocal, suffixRun⟩

/-- If `guess = 2(first+1)`, the fourth scan exposes digit two, while the
alphabet offers only marker one.  Thus no completed path can cross it. -/
theorem fourthScan_rejects_twoQ
    {prime phaseCount source target guessPhase firstPhase secondPhase
      thirdPhase fourthPhase fifthPhase markerTwoPhase endpointPhase : Nat}
    {endpointDigit : Int} {endpoint : Vec2}
    (primeProperty : IsPrime prime) (primeBound : 6 * phaseCount < prime)
    (layout : PhaseLayout phaseCount source guessPhase firstPhase secondPhase
      thirdPhase fourthPhase fifthPhase markerTwoPhase)
    (endpointBound : endpointPhase < phaseCount)
    (fourthEndpointDistinct : fourthPhase ≠ endpointPhase)
    (endpointMembership : InPhaseAt prime endpointPhase endpointDigit endpoint)
    {first guess deleted remaining : Nat} (guessPositive : 0 < guess)
    (thirdAccepted : first ≠ guess - 1)
    (guessEqTwoQ : guess = 2 * (first + 1))
    (sumEq : deleted + remaining = fourthZeroCount first guess)
    {word : List PhysicalTemplate}
    (wordOver : WordOver
      (alphabet source target guessPhase firstPhase secondPhase thirdPhase
        fourthPhase fifthPhase markerTwoPhase) word)
    (allLocal : AllStatesLocal prime word
      (phaseAffine fourthPhase (fourthState prime first guess deleted)))
    (completeRun : SameLine
      (physicalWordAction prime word
        (phaseAffine fourthPhase (fourthState prime first guess deleted)))
      endpoint) : False := by
  apply forcedScanRejectsAtMarker
    (markerDigit := 2)
    (primeProperty := primeProperty) (primeBound := primeBound)
    (currentBound := layout.fourthBound) (endpointBound := endpointBound)
    (phaseDistinct := fourthEndpointDistinct)
    (endpointMembership := endpointMembership)
    (beforeMembership := fun position positionBelow =>
      fourthState_inPhaseAt_before (fourthPhase := fourthPhase)
        (first := first) (guess := guess) (deleted := position)
        primeProperty positionBelow)
    (markerMembership := by
      simpa [(fourthMarkerDigit_eq_two_iff first guess).2 guessEqTwoQ] using
        (fourthState_inPhaseAt_marker (fourthPhase := fourthPhase)
          (first := first) (guess := guess) primeProperty guessPositive
          thirdAccepted))
    (stateLocal := fun position _ =>
      phaseLocal (fourthState_local prime first guess position
        primeProperty.1))
    (forceLoop := fun position positionBelow {letter} letterMem outputLocal =>
      by
        rcases fourth_letter primeProperty primeBound layout
            (fourthState_inPhaseAt_before (fourthPhase := fourthPhase)
              (first := first) (guess := guess) (deleted := position)
              primeProperty positionBelow)
            letterMem outputLocal with
          ⟨_, letterEq⟩ | ⟨digitEq, _⟩
        · exact letterEq
        · omega)
    (rejectMarker := fun {letter} letterMem outputLocal => by
      rcases fourth_letter primeProperty primeBound layout
          (fourthState_inPhaseAt_marker (fourthPhase := fourthPhase)
            (first := first) (guess := guess) primeProperty guessPositive
            thirdAccepted) letterMem outputLocal with
        ⟨digitEq, _⟩ | ⟨digitEq, _⟩
      · rw [(fourthMarkerDigit_eq_two_iff first guess).2 guessEqTwoQ]
          at digitEq
        omega
      · rw [(fourthMarkerDigit_eq_two_iff first guess).2 guessEqTwoQ]
          at digitEq
        omega)
    (loopStep := fun position positionBelow =>
      fourthZero_step prime fourthPhase first guess position primeProperty.1
        positionBelow)
    sumEq wordOver allLocal completeRun

theorem smallFifthState_inPhaseAt_before
    {prime fifthPhase first guess deleted : Nat}
    (primeProperty : IsPrime prime) (guessPositive : 0 < guess)
    (guessBelowQ : guess < first + 1)
    (deletedBelow : deleted < smallFifthZeroCount first guess) :
    InPhaseAt prime fifthPhase 0
      (phaseAffine fifthPhase (smallFifthState prime first guess deleted)) := by
  apply inPhaseAt_phaseAffine_integer (by simp [ReservedDigit])
    (halfIntegerDenominator_not_dvd prime first guess primeProperty.1)
    (by
      simpa using (show (prime : Int) ∣
          smallFifthNumerator prime first guess deleted from
        ⟨smallFifthNumerator prime first guess (deleted + 1),
          smallFifthNumerator_step prime first guess deleted guessPositive
            guessBelowQ deletedBelow⟩))
  exact smallFifthState_sameLine_integer prime first guess deleted
    primeProperty.1

theorem smallFifthState_inPhaseAt_marker
    {prime fifthPhase first guess : Nat}
    (primeProperty : IsPrime prime) (guessPositive : 0 < guess)
    (guessBelowQ : guess < first + 1) :
    InPhaseAt prime fifthPhase 2
      (phaseAffine fifthPhase
        (smallFifthState prime first guess
          (smallFifthZeroCount first guess))) := by
  apply inPhaseAt_phaseAffine_integer (by simp [ReservedDigit])
    (halfIntegerDenominator_not_dvd prime first guess primeProperty.1)
    (smallFifth_marker_residue_two prime first guess guessPositive
      guessBelowQ)
  exact smallFifthState_sameLine_integer prime first guess
    (smallFifthZeroCount first guess) primeProperty.1

theorem middleFifthState_inPhaseAt_before
    {prime fifthPhase first guess deleted : Nat}
    (primeProperty : IsPrime prime) (QBelowGuess : first + 1 < guess)
    (guessBelowTwoQ : guess < 2 * (first + 1))
    (deletedBelow : deleted < middleFifthZeroCount first guess) :
    InPhaseAt prime fifthPhase 0
      (phaseAffine fifthPhase (middleFifthState prime first guess deleted)) := by
  apply inPhaseAt_phaseAffine_integer (by simp [ReservedDigit])
    (halfIntegerDenominator_not_dvd prime first guess primeProperty.1)
    (by
      simpa using (show (prime : Int) ∣
          middleFifthNumerator prime first guess deleted from
        ⟨middleFifthNumerator prime first guess (deleted + 1),
          middleFifthNumerator_step prime first guess deleted QBelowGuess
            guessBelowTwoQ deletedBelow⟩))
  exact middleFifthState_sameLine_integer prime first guess deleted
    primeProperty.1

theorem middleFifthState_inPhaseAt_marker
    {prime fifthPhase first guess : Nat}
    (primeProperty : IsPrime prime) (QBelowGuess : first + 1 < guess)
    (guessBelowTwoQ : guess < 2 * (first + 1)) :
    InPhaseAt prime fifthPhase 1
      (phaseAffine fifthPhase
        (middleFifthState prime first guess
          (middleFifthZeroCount first guess))) := by
  apply inPhaseAt_phaseAffine_integer (by simp [ReservedDigit])
    (halfIntegerDenominator_not_dvd prime first guess primeProperty.1)
    (by simpa using
      (middleFifth_marker_residue_one prime first guess QBelowGuess
        guessBelowTwoQ))
  exact middleFifthState_sameLine_integer prime first guess
    (middleFifthZeroCount first guess) primeProperty.1

theorem largeFifthState_inPhaseAt_before
    {prime fifthPhase first guess deleted : Nat}
    (primeProperty : IsPrime prime)
    (twoQBelowGuess : 2 * (first + 1) < guess)
    (deletedBelow : deleted < largeFifthZeroCount first guess) :
    InPhaseAt prime fifthPhase 0
      (phaseAffine fifthPhase (largeFifthState prime first guess deleted)) := by
  apply inPhaseAt_phaseAffine_integer (by simp [ReservedDigit])
    (halfIntegerDenominator_not_dvd prime first guess primeProperty.1)
    (by
      simpa using (show (prime : Int) ∣
          largeFifthNumerator prime first guess deleted from
        ⟨largeFifthNumerator prime first guess (deleted + 1),
          largeFifthNumerator_step prime first guess deleted twoQBelowGuess
            deletedBelow⟩))
  exact largeFifthState_sameLine_integer prime first guess deleted
    primeProperty.1

theorem largeFifthState_inPhaseAt_marker
    {prime fifthPhase first guess : Nat}
    (primeProperty : IsPrime prime)
    (twoQBelowGuess : 2 * (first + 1) < guess) :
    InPhaseAt prime fifthPhase (largeFifthMarkerDigit first guess)
      (phaseAffine fifthPhase
        (largeFifthState prime first guess
          (largeFifthZeroCount first guess))) := by
  apply inPhaseAt_phaseAffine_integer
    (by unfold largeFifthMarkerDigit; split <;> simp [ReservedDigit])
    (halfIntegerDenominator_not_dvd prime first guess primeProperty.1)
    (largeFifth_marker_residue prime first guess twoQBelowGuess)
  exact largeFifthState_sameLine_integer prime first guess
    (largeFifthZeroCount first guess) primeProperty.1

theorem fifthMarker_step
    (base fifthPhase markerTwoPhase : Nat) {value deleted output : Rat}
    (baseAtLeastTwo : 2 ≤ base)
    (valueLocal : LocalAt base (Vec2.affine value))
    (deletedLocal : LocalAt base (Vec2.affine deleted))
    (deletedEq : deleteDigit (base : Rat) 1 value = deleted)
    (outputEq : Tinv base deleted = output) :
    SameLine
      ((inverseTMarker fifthPhase markerTwoPhase).act base
        (phaseAffine fifthPhase value))
      (phaseAffine markerTwoPhase output) := by
  have transformed := outputEq
  rw [Tinv_eq_mutationMap] at transformed
  have step := marker_step (source := fifthPhase) (target := markerTwoPhase)
    (digit := 1) (coefficient := 1) (sign := .positive)
    (value := value) (deleted := deleted) (output := output) (by omega)
    valueLocal deletedLocal deletedEq transformed
  simpa [inverseTMarker, PhysicalTemplate.act, PhysicalTemplate.matrix]
    using step

theorem smallFifthZero_step
    (base fifthPhase first guess deleted : Nat)
    (baseAtLeastTwo : 2 ≤ base) (guessPositive : 0 < guess)
    (guessBelowQ : guess < first + 1)
    (deletedBelow : deleted < smallFifthZeroCount first guess) :
    SameLine
      ((identityZero fifthPhase).act base
        (phaseAffine fifthPhase (smallFifthState base first guess deleted)))
      (phaseAffine fifthPhase
        (smallFifthState base first guess (deleted + 1))) := by
  exact identityZero_step (by omega)
    (smallFifthState_local base first guess deleted baseAtLeastTwo)
    (smallFifthState_local base first guess (deleted + 1) baseAtLeastTwo)
    (smallFifthState_delete_zero base first guess deleted baseAtLeastTwo
      guessPositive guessBelowQ deletedBelow)

theorem middleFifthZero_step
    (base fifthPhase first guess deleted : Nat)
    (baseAtLeastTwo : 2 ≤ base) (QBelowGuess : first + 1 < guess)
    (guessBelowTwoQ : guess < 2 * (first + 1))
    (deletedBelow : deleted < middleFifthZeroCount first guess) :
    SameLine
      ((identityZero fifthPhase).act base
        (phaseAffine fifthPhase (middleFifthState base first guess deleted)))
      (phaseAffine fifthPhase
        (middleFifthState base first guess (deleted + 1))) := by
  exact identityZero_step (by omega)
    (middleFifthState_local base first guess deleted baseAtLeastTwo)
    (middleFifthState_local base first guess (deleted + 1) baseAtLeastTwo)
    (middleFifthState_delete_zero base first guess deleted baseAtLeastTwo
      QBelowGuess guessBelowTwoQ deletedBelow)

theorem middleFifthMarker_step
    (base fifthPhase markerTwoPhase first guess : Nat)
    (baseAtLeastTwo : 2 ≤ base) (QBelowGuess : first + 1 < guess)
    (guessBelowTwoQ : guess < 2 * (first + 1)) :
    SameLine
      ((inverseTMarker fifthPhase markerTwoPhase).act base
        (phaseAffine fifthPhase
          (middleFifthState base first guess
            (middleFifthZeroCount first guess))))
      (phaseAffine markerTwoPhase
        (falseMarkerTwoState base first guess 0)) := by
  apply fifthMarker_step base fifthPhase markerTwoPhase baseAtLeastTwo
    (middleFifthState_local base first guess
      (middleFifthZeroCount first guess) baseAtLeastTwo)
    (state_local
      (halfIntegerDenominator_not_dvd base first guess baseAtLeastTwo))
    (middleFifth_delete_marker base first guess baseAtLeastTwo QBelowGuess
      guessBelowTwoQ)
    (falseMarkerTwoState_zero base first guess baseAtLeastTwo QBelowGuess
      guessBelowTwoQ)

theorem belowThreeFifthMarker_step
    (base fifthPhase markerTwoPhase first guess : Nat)
    (baseAtLeastTwo : 2 ≤ base)
    (twoQBelowGuess : 2 * (first + 1) < guess)
    (guessBelowThreeQ : guess < 3 * (first + 1)) :
    SameLine
      ((inverseTMarker fifthPhase markerTwoPhase).act base
        (phaseAffine fifthPhase
          (largeFifthState base first guess
            (largeFifthZeroCount first guess))))
      (phaseAffine markerTwoPhase
        (belowThreeMarkerTwoState base first guess 0)) := by
  apply fifthMarker_step base fifthPhase markerTwoPhase baseAtLeastTwo
    (largeFifthState_local base first guess
      (largeFifthZeroCount first guess) baseAtLeastTwo)
    (state_local
      (halfIntegerDenominator_not_dvd base first guess baseAtLeastTwo))
    (belowThreeFifth_delete_marker base first guess baseAtLeastTwo
      twoQBelowGuess guessBelowThreeQ)
    (belowThreeMarkerTwoState_zero base first guess baseAtLeastTwo
      twoQBelowGuess guessBelowThreeQ)

theorem aboveThreeFifthMarker_step
    (base fifthPhase markerTwoPhase first guess : Nat)
    (baseAtLeastTwo : 2 ≤ base)
    (threeQBelowGuess : 3 * (first + 1) < guess) :
    SameLine
      ((inverseTMarker fifthPhase markerTwoPhase).act base
        (phaseAffine fifthPhase
          (largeFifthState base first guess
            (largeFifthZeroCount first guess))))
      (phaseAffine markerTwoPhase
        (aboveThreeMarkerTwoState base first guess 0)) := by
  apply fifthMarker_step base fifthPhase markerTwoPhase baseAtLeastTwo
    (largeFifthState_local base first guess
      (largeFifthZeroCount first guess) baseAtLeastTwo)
    (state_local
      (halfIntegerDenominator_not_dvd base first guess baseAtLeastTwo))
    (aboveThreeFifth_delete_marker base first guess baseAtLeastTwo
      threeQBelowGuess)
    (aboveThreeMarkerTwoState_zero base first guess baseAtLeastTwo
      threeQBelowGuess)

/-- Generic boundary parser for a fifth-phase state family whose terminal
digit is one. -/
theorem fifthScanTail_forced_prefix_to_endpoint
    {prime phaseCount source target guessPhase firstPhase secondPhase
      thirdPhase fourthPhase fifthPhase markerTwoPhase endpointPhase : Nat}
    {endpointDigit : Int} {endpoint next : Vec2}
    (primeProperty : IsPrime prime) (primeBound : 6 * phaseCount < prime)
    (layout : PhaseLayout phaseCount source guessPhase firstPhase secondPhase
      thirdPhase fourthPhase fifthPhase markerTwoPhase)
    (endpointBound : endpointPhase < phaseCount)
    (fifthEndpointDistinct : fifthPhase ≠ endpointPhase)
    (endpointMembership : InPhaseAt prime endpointPhase endpointDigit endpoint)
    {limit deleted remaining : Nat} {state : Nat → Vec2}
    (beforeMembership : ∀ position, position < limit →
      InPhaseAt prime fifthPhase 0 (state position))
    (markerMembership : InPhaseAt prime fifthPhase 1 (state limit))
    (stateLocal : ∀ position, position ≤ limit → LocalAt prime (state position))
    (nextLocal : LocalAt prime next)
    (loopStep : ∀ position, position < limit →
      SameLine ((identityZero fifthPhase).act prime (state position))
        (state (position + 1)))
    (exitStep : SameLine
      ((inverseTMarker fifthPhase markerTwoPhase).act prime (state limit)) next)
    (sumEq : deleted + remaining = limit)
    {word : List PhysicalTemplate}
    (wordOver : WordOver
      (alphabet source target guessPhase firstPhase secondPhase thirdPhase
        fourthPhase fifthPhase markerTwoPhase) word)
    (allLocal : AllStatesLocal prime word (state deleted))
    (completeRun : SameLine
      (physicalWordAction prime word (state deleted)) endpoint) :
    ∃ suffix,
      word = List.replicate remaining (identityZero fifthPhase) ++
          [inverseTMarker fifthPhase markerTwoPhase] ++ suffix ∧
      WordOver
        (alphabet source target guessPhase firstPhase secondPhase thirdPhase
          fourthPhase fifthPhase markerTwoPhase) suffix ∧
      AllStatesLocal prime suffix next ∧
      SameLine (physicalWordAction prime suffix next) endpoint := by
  have parsed := forcedScanPrefixToEndpoint
    (Certificate := True) (primeProperty := primeProperty)
    (primeBound := primeBound) (currentBound := layout.fifthBound)
    (endpointBound := endpointBound) (phaseDistinct := fifthEndpointDistinct)
    (endpointMembership := endpointMembership)
    (beforeMembership := beforeMembership)
    (markerMembership := markerMembership) (stateLocal := stateLocal)
    (nextLocal := nextLocal)
    (forceLoop := fun position positionBelow {letter} letterMem outputLocal =>
      by
        rcases fifth_letter primeProperty primeBound layout
            (beforeMembership position positionBelow) letterMem outputLocal with
          ⟨_, letterEq⟩ | ⟨digitEq, _⟩
        · exact letterEq
        · omega)
    (forceExit := fun {letter} letterMem outputLocal => by
      rcases fifth_letter primeProperty primeBound layout markerMembership
          letterMem outputLocal with
        ⟨digitEq, _⟩ | ⟨_, letterEq⟩
      · omega
      · exact ⟨True.intro, letterEq⟩)
    (loopStep := loopStep) (exitStep := fun _ => exitStep)
    sumEq wordOver allLocal completeRun
  rcases parsed with ⟨suffix, _, wordEq, suffixOver, suffixLocal, suffixRun⟩
  exact ⟨suffix, wordEq, suffixOver, suffixLocal, suffixRun⟩

/-- Generic rejection parser for a fifth-phase state family whose terminal
digit is two. -/
theorem fifthScan_rejects_digit_two
    {prime phaseCount source target guessPhase firstPhase secondPhase
      thirdPhase fourthPhase fifthPhase markerTwoPhase endpointPhase : Nat}
    {endpointDigit : Int} {endpoint : Vec2}
    (primeProperty : IsPrime prime) (primeBound : 6 * phaseCount < prime)
    (layout : PhaseLayout phaseCount source guessPhase firstPhase secondPhase
      thirdPhase fourthPhase fifthPhase markerTwoPhase)
    (endpointBound : endpointPhase < phaseCount)
    (fifthEndpointDistinct : fifthPhase ≠ endpointPhase)
    (endpointMembership : InPhaseAt prime endpointPhase endpointDigit endpoint)
    {limit deleted remaining : Nat} {state : Nat → Vec2}
    (beforeMembership : ∀ position, position < limit →
      InPhaseAt prime fifthPhase 0 (state position))
    (markerMembership : InPhaseAt prime fifthPhase 2 (state limit))
    (stateLocal : ∀ position, position ≤ limit → LocalAt prime (state position))
    (loopStep : ∀ position, position < limit →
      SameLine ((identityZero fifthPhase).act prime (state position))
        (state (position + 1)))
    (sumEq : deleted + remaining = limit)
    {word : List PhysicalTemplate}
    (wordOver : WordOver
      (alphabet source target guessPhase firstPhase secondPhase thirdPhase
        fourthPhase fifthPhase markerTwoPhase) word)
    (allLocal : AllStatesLocal prime word (state deleted))
    (completeRun : SameLine
      (physicalWordAction prime word (state deleted)) endpoint) : False := by
  apply forcedScanRejectsAtMarker
    (primeProperty := primeProperty) (primeBound := primeBound)
    (currentBound := layout.fifthBound) (endpointBound := endpointBound)
    (phaseDistinct := fifthEndpointDistinct)
    (endpointMembership := endpointMembership)
    (beforeMembership := beforeMembership) (markerMembership := markerMembership)
    (stateLocal := stateLocal)
    (forceLoop := fun position positionBelow {letter} letterMem outputLocal =>
      by
        rcases fifth_letter primeProperty primeBound layout
            (beforeMembership position positionBelow) letterMem outputLocal with
          ⟨_, letterEq⟩ | ⟨digitEq, _⟩
        · exact letterEq
        · omega)
    (rejectMarker := fun {letter} letterMem outputLocal => by
      rcases fifth_letter primeProperty primeBound layout markerMembership
          letterMem outputLocal with
        ⟨digitEq, _⟩ | ⟨digitEq, _⟩ <;> omega)
    (loopStep := loopStep) sumEq wordOver allLocal completeRun

theorem falseMarkerTwoState_inPhaseAt_before
    {prime markerTwoPhase first guess deleted : Nat}
    (primeProperty : IsPrime prime) (QBelowGuess : first + 1 < guess)
    (guessBelowTwoQ : guess < 2 * (first + 1))
    (deletedBelow : deleted < falseMarkerTwoZeroCount first guess) :
    InPhaseAt prime markerTwoPhase 0
      (phaseAffine markerTwoPhase
        (falseMarkerTwoState prime first guess deleted)) := by
  apply inPhaseAt_phaseAffine_integer (by simp [ReservedDigit])
    (markerTwoDenominator_not_dvd prime first guess _ primeProperty.1)
    (by
      simpa using (show (prime : Int) ∣
          falseMarkerTwoNumerator prime first guess deleted from
        ⟨falseMarkerTwoNumerator prime first guess (deleted + 1),
          falseMarkerTwoNumerator_step prime first guess deleted QBelowGuess
            guessBelowTwoQ deletedBelow⟩))
  exact falseMarkerTwoState_sameLine_integer prime first guess deleted
    primeProperty.1

theorem falseMarkerTwoState_inPhaseAt_marker
    {prime markerTwoPhase first guess : Nat}
    (primeProperty : IsPrime prime) (QBelowGuess : first + 1 < guess)
    (guessBelowTwoQ : guess < 2 * (first + 1)) :
    InPhaseAt prime markerTwoPhase 2
      (phaseAffine markerTwoPhase
        (falseMarkerTwoState prime first guess
          (falseMarkerTwoZeroCount first guess))) := by
  apply inPhaseAt_phaseAffine_integer (by simp [ReservedDigit])
    (markerTwoDenominator_not_dvd prime first guess _ primeProperty.1)
    (falseMarkerTwo_marker_residue_two prime first guess QBelowGuess
      guessBelowTwoQ)
  exact falseMarkerTwoState_sameLine_integer prime first guess
    (falseMarkerTwoZeroCount first guess) primeProperty.1

theorem belowThreeMarkerTwoState_inPhaseAt_before
    {prime markerTwoPhase first guess deleted : Nat}
    (primeProperty : IsPrime prime)
    (twoQBelowGuess : 2 * (first + 1) < guess)
    (guessBelowThreeQ : guess < 3 * (first + 1))
    (deletedBelow : deleted < belowThreeMarkerTwoZeroCount first guess) :
    InPhaseAt prime markerTwoPhase 0
      (phaseAffine markerTwoPhase
        (belowThreeMarkerTwoState prime first guess deleted)) := by
  apply inPhaseAt_phaseAffine_integer (by simp [ReservedDigit])
    (markerTwoDenominator_not_dvd prime first guess _ primeProperty.1)
    (by
      simpa using (show (prime : Int) ∣
          belowThreeMarkerTwoNumerator prime first guess deleted from
        ⟨belowThreeMarkerTwoNumerator prime first guess (deleted + 1),
          belowThreeMarkerTwoNumerator_step prime first guess deleted
            twoQBelowGuess guessBelowThreeQ deletedBelow⟩))
  exact belowThreeMarkerTwoState_sameLine_integer prime first guess deleted
    primeProperty.1

theorem belowThreeMarkerTwoState_inPhaseAt_marker
    {prime markerTwoPhase first guess : Nat}
    (primeProperty : IsPrime prime)
    (twoQBelowGuess : 2 * (first + 1) < guess)
    (guessBelowThreeQ : guess < 3 * (first + 1)) :
    InPhaseAt prime markerTwoPhase 1
      (phaseAffine markerTwoPhase
        (belowThreeMarkerTwoState prime first guess
          (belowThreeMarkerTwoZeroCount first guess))) := by
  apply inPhaseAt_phaseAffine_integer (by simp [ReservedDigit])
    (markerTwoDenominator_not_dvd prime first guess _ primeProperty.1)
    (by simpa using
      (belowThreeMarkerTwo_marker_residue_one prime first guess
        twoQBelowGuess guessBelowThreeQ))
  exact belowThreeMarkerTwoState_sameLine_integer prime first guess
    (belowThreeMarkerTwoZeroCount first guess) primeProperty.1

theorem aboveThreeMarkerTwoState_inPhaseAt_before
    {prime markerTwoPhase first guess deleted : Nat}
    (primeProperty : IsPrime prime)
    (threeQBelowGuess : 3 * (first + 1) < guess)
    (deletedBelow : deleted < aboveThreeMarkerTwoZeroCount first guess) :
    InPhaseAt prime markerTwoPhase 0
      (phaseAffine markerTwoPhase
        (aboveThreeMarkerTwoState prime first guess deleted)) := by
  apply inPhaseAt_phaseAffine_integer (by simp [ReservedDigit])
    (markerTwoDenominator_not_dvd prime first guess _ primeProperty.1)
    (by
      simpa using (show (prime : Int) ∣
          aboveThreeMarkerTwoNumerator prime first guess deleted from
        ⟨aboveThreeMarkerTwoNumerator prime first guess (deleted + 1),
          aboveThreeMarkerTwoNumerator_step prime first guess deleted
            threeQBelowGuess deletedBelow⟩))
  exact aboveThreeMarkerTwoState_sameLine_integer prime first guess deleted
    primeProperty.1

theorem aboveThreeMarkerTwoState_inPhaseAt_marker
    {prime markerTwoPhase first guess : Nat}
    (primeProperty : IsPrime prime)
    (threeQBelowGuess : 3 * (first + 1) < guess) :
    InPhaseAt prime markerTwoPhase (aboveThreeMarkerTwoDigit first guess)
      (phaseAffine markerTwoPhase
        (aboveThreeMarkerTwoState prime first guess
          (aboveThreeMarkerTwoZeroCount first guess))) := by
  apply inPhaseAt_phaseAffine_integer
    (by unfold aboveThreeMarkerTwoDigit; split <;> simp [ReservedDigit])
    (markerTwoDenominator_not_dvd prime first guess _ primeProperty.1)
    (aboveThreeMarkerTwo_marker_residue prime first guess threeQBelowGuess)
  exact aboveThreeMarkerTwoState_sameLine_integer prime first guess
    (aboveThreeMarkerTwoZeroCount first guess) primeProperty.1

theorem falseMarkerTwoZero_step
    (base markerTwoPhase first guess deleted : Nat)
    (baseAtLeastTwo : 2 ≤ base) (QBelowGuess : first + 1 < guess)
    (guessBelowTwoQ : guess < 2 * (first + 1))
    (deletedBelow : deleted < falseMarkerTwoZeroCount first guess) :
    SameLine
      ((identityZero markerTwoPhase).act base
        (phaseAffine markerTwoPhase
          (falseMarkerTwoState base first guess deleted)))
      (phaseAffine markerTwoPhase
        (falseMarkerTwoState base first guess (deleted + 1))) := by
  exact identityZero_step (by omega)
    (falseMarkerTwoState_local base first guess deleted baseAtLeastTwo)
    (falseMarkerTwoState_local base first guess (deleted + 1) baseAtLeastTwo)
    (falseMarkerTwoState_delete_zero base first guess deleted baseAtLeastTwo
      QBelowGuess guessBelowTwoQ deletedBelow)

theorem belowThreeMarkerTwoZero_step
    (base markerTwoPhase first guess deleted : Nat)
    (baseAtLeastTwo : 2 ≤ base)
    (twoQBelowGuess : 2 * (first + 1) < guess)
    (guessBelowThreeQ : guess < 3 * (first + 1))
    (deletedBelow : deleted < belowThreeMarkerTwoZeroCount first guess) :
    SameLine
      ((identityZero markerTwoPhase).act base
        (phaseAffine markerTwoPhase
          (belowThreeMarkerTwoState base first guess deleted)))
      (phaseAffine markerTwoPhase
        (belowThreeMarkerTwoState base first guess (deleted + 1))) := by
  exact identityZero_step (by omega)
    (belowThreeMarkerTwoState_local base first guess deleted baseAtLeastTwo)
    (belowThreeMarkerTwoState_local base first guess (deleted + 1)
      baseAtLeastTwo)
    (belowThreeMarkerTwoState_delete_zero base first guess deleted
      baseAtLeastTwo twoQBelowGuess guessBelowThreeQ deletedBelow)

theorem aboveThreeMarkerTwoZero_step
    (base markerTwoPhase first guess deleted : Nat)
    (baseAtLeastTwo : 2 ≤ base)
    (threeQBelowGuess : 3 * (first + 1) < guess)
    (deletedBelow : deleted < aboveThreeMarkerTwoZeroCount first guess) :
    SameLine
      ((identityZero markerTwoPhase).act base
        (phaseAffine markerTwoPhase
          (aboveThreeMarkerTwoState base first guess deleted)))
      (phaseAffine markerTwoPhase
        (aboveThreeMarkerTwoState base first guess (deleted + 1))) := by
  exact identityZero_step (by omega)
    (aboveThreeMarkerTwoState_local base first guess deleted baseAtLeastTwo)
    (aboveThreeMarkerTwoState_local base first guess (deleted + 1)
      baseAtLeastTwo)
    (aboveThreeMarkerTwoState_delete_zero base first guess deleted
      baseAtLeastTwo threeQBelowGuess deletedBelow)

theorem falseMarkerTwoMarker_step
    (base markerTwoPhase target first guess : Nat)
    (baseAtLeastTwo : 2 ≤ base) (QBelowGuess : first + 1 < guess)
    (guessBelowTwoQ : guess < 2 * (first + 1)) :
    SameLine
      ((negatingTMarker markerTwoPhase target).act base
        (phaseAffine markerTwoPhase
          (falseMarkerTwoState base first guess
            (falseMarkerTwoZeroCount first guess))))
      (phaseAffine target (falseHandoffState base first guess 0)) := by
  let markerDenominator := markerTwoDenominator base first guess
    (falseMarkerTwoNumerator base first guess)
  let handoffNumerator := falseHandoffNumerator base first guess 0
  have denominatorNotDivisible := markerTwoDenominator_not_dvd base first guess
    (falseMarkerTwoNumerator base first guess) baseAtLeastTwo
  have deletedEq := deleteDigit_eq base 2
    (falseMarkerTwoNumerator base first guess
      (falseMarkerTwoZeroCount first guess)) markerDenominator
    (-handoffNumerator) (by omega)
    (denominator_nonzero_of_not_dvd denominatorNotDivisible) (by
      simpa [markerDenominator, handoffNumerator] using
        (false_markerTwo_difference base first guess QBelowGuess
          guessBelowTwoQ))
  have deletedLocal := state_local (numerator := -handoffNumerator)
    denominatorNotDivisible
  have outputEq := false_markerTwo_to_handoff base first guess baseAtLeastTwo
    QBelowGuess guessBelowTwoQ
  have outputEq' := outputEq
  change mutationMap base .negative 1
      (deleteDigit (base : Rat) 2
        (state
          (falseMarkerTwoNumerator base first guess
            (falseMarkerTwoZeroCount first guess)) markerDenominator)) =
        falseHandoffState base first guess 0 at outputEq'
  rw [deletedEq] at outputEq'
  have step := marker_step (source := markerTwoPhase) (target := target)
    (digit := 2) (coefficient := 1) (sign := .negative)
    (value := falseMarkerTwoState base first guess
      (falseMarkerTwoZeroCount first guess))
    (deleted := state (-handoffNumerator) markerDenominator)
    (output := falseHandoffState base first guess 0) (by omega)
    (falseMarkerTwoState_local base first guess
      (falseMarkerTwoZeroCount first guess) baseAtLeastTwo)
    deletedLocal (by
      simpa [falseMarkerTwoState, markerDenominator] using deletedEq) outputEq'
  simpa [negatingTMarker, PhysicalTemplate.act, PhysicalTemplate.matrix]
    using step

/-- Generic boundary parser for a marker-two state family whose terminal
digit is two. -/
theorem markerTwoTail_forced_prefix_to_endpoint
    {prime phaseCount source target guessPhase firstPhase secondPhase
      thirdPhase fourthPhase fifthPhase markerTwoPhase endpointPhase : Nat}
    {endpointDigit : Int} {endpoint next : Vec2}
    (primeProperty : IsPrime prime) (primeBound : 6 * phaseCount < prime)
    (layout : PhaseLayout phaseCount source guessPhase firstPhase secondPhase
      thirdPhase fourthPhase fifthPhase markerTwoPhase)
    (endpointBound : endpointPhase < phaseCount)
    (markerTwoEndpointDistinct : markerTwoPhase ≠ endpointPhase)
    (endpointMembership : InPhaseAt prime endpointPhase endpointDigit endpoint)
    {limit deleted remaining : Nat} {state : Nat → Vec2}
    (beforeMembership : ∀ position, position < limit →
      InPhaseAt prime markerTwoPhase 0 (state position))
    (markerMembership : InPhaseAt prime markerTwoPhase 2 (state limit))
    (stateLocal : ∀ position, position ≤ limit → LocalAt prime (state position))
    (nextLocal : LocalAt prime next)
    (loopStep : ∀ position, position < limit →
      SameLine ((identityZero markerTwoPhase).act prime (state position))
        (state (position + 1)))
    (exitStep : SameLine
      ((negatingTMarker markerTwoPhase target).act prime (state limit)) next)
    (sumEq : deleted + remaining = limit)
    {word : List PhysicalTemplate}
    (wordOver : WordOver
      (alphabet source target guessPhase firstPhase secondPhase thirdPhase
        fourthPhase fifthPhase markerTwoPhase) word)
    (allLocal : AllStatesLocal prime word (state deleted))
    (completeRun : SameLine
      (physicalWordAction prime word (state deleted)) endpoint) :
    ∃ suffix,
      word = List.replicate remaining (identityZero markerTwoPhase) ++
          [negatingTMarker markerTwoPhase target] ++ suffix ∧
      WordOver
        (alphabet source target guessPhase firstPhase secondPhase thirdPhase
          fourthPhase fifthPhase markerTwoPhase) suffix ∧
      AllStatesLocal prime suffix next ∧
      SameLine (physicalWordAction prime suffix next) endpoint := by
  have parsed := forcedScanPrefixToEndpoint
    (Certificate := True) (primeProperty := primeProperty)
    (primeBound := primeBound) (currentBound := layout.markerTwoBound)
    (endpointBound := endpointBound)
    (phaseDistinct := markerTwoEndpointDistinct)
    (endpointMembership := endpointMembership)
    (beforeMembership := beforeMembership)
    (markerMembership := markerMembership) (stateLocal := stateLocal)
    (nextLocal := nextLocal)
    (forceLoop := fun position positionBelow {letter} letterMem outputLocal =>
      by
        rcases markerTwo_letter primeProperty primeBound layout
            (beforeMembership position positionBelow) letterMem outputLocal with
          ⟨_, letterEq⟩ | ⟨digitEq, _⟩
        · exact letterEq
        · omega)
    (forceExit := fun {letter} letterMem outputLocal => by
      rcases markerTwo_letter primeProperty primeBound layout markerMembership
          letterMem outputLocal with
        ⟨digitEq, _⟩ | ⟨_, letterEq⟩
      · omega
      · exact ⟨True.intro, letterEq⟩)
    (loopStep := loopStep) (exitStep := fun _ => exitStep)
    sumEq wordOver allLocal completeRun
  rcases parsed with ⟨suffix, _, wordEq, suffixOver, suffixLocal, suffixRun⟩
  exact ⟨suffix, wordEq, suffixOver, suffixLocal, suffixRun⟩

/-- Generic rejection parser for a marker-two state family whose terminal
digit is one. -/
theorem markerTwo_rejects_digit_one
    {prime phaseCount source target guessPhase firstPhase secondPhase
      thirdPhase fourthPhase fifthPhase markerTwoPhase endpointPhase : Nat}
    {endpointDigit : Int} {endpoint : Vec2}
    (primeProperty : IsPrime prime) (primeBound : 6 * phaseCount < prime)
    (layout : PhaseLayout phaseCount source guessPhase firstPhase secondPhase
      thirdPhase fourthPhase fifthPhase markerTwoPhase)
    (endpointBound : endpointPhase < phaseCount)
    (markerTwoEndpointDistinct : markerTwoPhase ≠ endpointPhase)
    (endpointMembership : InPhaseAt prime endpointPhase endpointDigit endpoint)
    {limit deleted remaining : Nat} {state : Nat → Vec2}
    (beforeMembership : ∀ position, position < limit →
      InPhaseAt prime markerTwoPhase 0 (state position))
    (markerMembership : InPhaseAt prime markerTwoPhase 1 (state limit))
    (stateLocal : ∀ position, position ≤ limit → LocalAt prime (state position))
    (loopStep : ∀ position, position < limit →
      SameLine ((identityZero markerTwoPhase).act prime (state position))
        (state (position + 1)))
    (sumEq : deleted + remaining = limit)
    {word : List PhysicalTemplate}
    (wordOver : WordOver
      (alphabet source target guessPhase firstPhase secondPhase thirdPhase
        fourthPhase fifthPhase markerTwoPhase) word)
    (allLocal : AllStatesLocal prime word (state deleted))
    (completeRun : SameLine
      (physicalWordAction prime word (state deleted)) endpoint) : False := by
  apply forcedScanRejectsAtMarker
    (primeProperty := primeProperty) (primeBound := primeBound)
    (currentBound := layout.markerTwoBound) (endpointBound := endpointBound)
    (phaseDistinct := markerTwoEndpointDistinct)
    (endpointMembership := endpointMembership)
    (beforeMembership := beforeMembership) (markerMembership := markerMembership)
    (stateLocal := stateLocal)
    (forceLoop := fun position positionBelow {letter} letterMem outputLocal =>
      by
        rcases markerTwo_letter primeProperty primeBound layout
            (beforeMembership position positionBelow) letterMem outputLocal with
          ⟨_, letterEq⟩ | ⟨digitEq, _⟩
        · exact letterEq
        · omega)
    (rejectMarker := fun {letter} letterMem outputLocal => by
      rcases markerTwo_letter primeProperty primeBound layout markerMembership
          letterMem outputLocal with
        ⟨digitEq, _⟩ | ⟨digitEq, _⟩ <;> omega)
    (loopStep := loopStep) sumEq wordOver allLocal completeRun

theorem smallFifthScan_rejects
    {prime phaseCount source target guessPhase firstPhase secondPhase
      thirdPhase fourthPhase fifthPhase markerTwoPhase endpointPhase : Nat}
    {endpointDigit : Int} {endpoint : Vec2}
    (primeProperty : IsPrime prime) (primeBound : 6 * phaseCount < prime)
    (layout : PhaseLayout phaseCount source guessPhase firstPhase secondPhase
      thirdPhase fourthPhase fifthPhase markerTwoPhase)
    (endpointBound : endpointPhase < phaseCount)
    (fifthEndpointDistinct : fifthPhase ≠ endpointPhase)
    (endpointMembership : InPhaseAt prime endpointPhase endpointDigit endpoint)
    {first guess deleted remaining : Nat} (guessPositive : 0 < guess)
    (guessBelowQ : guess < first + 1)
    (sumEq : deleted + remaining = smallFifthZeroCount first guess)
    {word : List PhysicalTemplate}
    (wordOver : WordOver
      (alphabet source target guessPhase firstPhase secondPhase thirdPhase
        fourthPhase fifthPhase markerTwoPhase) word)
    (allLocal : AllStatesLocal prime word
      (phaseAffine fifthPhase (smallFifthState prime first guess deleted)))
    (completeRun : SameLine
      (physicalWordAction prime word
        (phaseAffine fifthPhase (smallFifthState prime first guess deleted)))
      endpoint) : False := by
  exact fifthScan_rejects_digit_two primeProperty primeBound layout
    endpointBound fifthEndpointDistinct endpointMembership
    (beforeMembership := fun position positionBelow =>
      smallFifthState_inPhaseAt_before (fifthPhase := fifthPhase)
        primeProperty guessPositive guessBelowQ positionBelow)
    (markerMembership := smallFifthState_inPhaseAt_marker
      (fifthPhase := fifthPhase) primeProperty guessPositive guessBelowQ)
    (stateLocal := fun position _ =>
      phaseLocal (smallFifthState_local prime first guess position
        primeProperty.1))
    (loopStep := fun position positionBelow =>
      smallFifthZero_step prime fifthPhase first guess position primeProperty.1
        guessPositive guessBelowQ positionBelow)
    sumEq wordOver allLocal completeRun

theorem middleFifthScan_forced_prefix_to_endpoint
    {prime phaseCount source target guessPhase firstPhase secondPhase
      thirdPhase fourthPhase fifthPhase markerTwoPhase endpointPhase : Nat}
    {endpointDigit : Int} {endpoint : Vec2}
    (primeProperty : IsPrime prime) (primeBound : 6 * phaseCount < prime)
    (layout : PhaseLayout phaseCount source guessPhase firstPhase secondPhase
      thirdPhase fourthPhase fifthPhase markerTwoPhase)
    (endpointBound : endpointPhase < phaseCount)
    (fifthEndpointDistinct : fifthPhase ≠ endpointPhase)
    (endpointMembership : InPhaseAt prime endpointPhase endpointDigit endpoint)
    {first guess deleted remaining : Nat} (QBelowGuess : first + 1 < guess)
    (guessBelowTwoQ : guess < 2 * (first + 1))
    (sumEq : deleted + remaining = middleFifthZeroCount first guess)
    {word : List PhysicalTemplate}
    (wordOver : WordOver
      (alphabet source target guessPhase firstPhase secondPhase thirdPhase
        fourthPhase fifthPhase markerTwoPhase) word)
    (allLocal : AllStatesLocal prime word
      (phaseAffine fifthPhase (middleFifthState prime first guess deleted)))
    (completeRun : SameLine
      (physicalWordAction prime word
        (phaseAffine fifthPhase (middleFifthState prime first guess deleted)))
      endpoint) :
    ∃ suffix,
      word = List.replicate remaining (identityZero fifthPhase) ++
          [inverseTMarker fifthPhase markerTwoPhase] ++ suffix ∧
      WordOver
        (alphabet source target guessPhase firstPhase secondPhase thirdPhase
          fourthPhase fifthPhase markerTwoPhase) suffix ∧
      AllStatesLocal prime suffix
        (phaseAffine markerTwoPhase
          (falseMarkerTwoState prime first guess 0)) ∧
      SameLine
        (physicalWordAction prime suffix
          (phaseAffine markerTwoPhase
            (falseMarkerTwoState prime first guess 0))) endpoint := by
  apply fifthScanTail_forced_prefix_to_endpoint primeProperty primeBound
    layout endpointBound fifthEndpointDistinct endpointMembership
    (beforeMembership := fun position positionBelow =>
      middleFifthState_inPhaseAt_before (fifthPhase := fifthPhase)
        primeProperty QBelowGuess guessBelowTwoQ positionBelow)
    (markerMembership := middleFifthState_inPhaseAt_marker
      (fifthPhase := fifthPhase) primeProperty QBelowGuess guessBelowTwoQ)
    (stateLocal := fun position _ =>
      phaseLocal (middleFifthState_local prime first guess position
        primeProperty.1))
    (nextLocal := phaseLocal
      (falseMarkerTwoState_local prime first guess 0 primeProperty.1))
    (loopStep := fun position positionBelow =>
      middleFifthZero_step prime fifthPhase first guess position primeProperty.1
        QBelowGuess guessBelowTwoQ positionBelow)
    (exitStep := middleFifthMarker_step prime fifthPhase markerTwoPhase first
      guess primeProperty.1 QBelowGuess guessBelowTwoQ)
    sumEq wordOver allLocal completeRun

theorem largeFifthScan_forced_prefix_to_endpoint
    {prime phaseCount source target guessPhase firstPhase secondPhase
      thirdPhase fourthPhase fifthPhase markerTwoPhase endpointPhase : Nat}
    {endpointDigit : Int} {endpoint next : Vec2}
    (primeProperty : IsPrime prime) (primeBound : 6 * phaseCount < prime)
    (layout : PhaseLayout phaseCount source guessPhase firstPhase secondPhase
      thirdPhase fourthPhase fifthPhase markerTwoPhase)
    (endpointBound : endpointPhase < phaseCount)
    (fifthEndpointDistinct : fifthPhase ≠ endpointPhase)
    (endpointMembership : InPhaseAt prime endpointPhase endpointDigit endpoint)
    {first guess deleted remaining : Nat}
    (twoQBelowGuess : 2 * (first + 1) < guess)
    (markerOne : largeFifthMarkerDigit first guess = 1)
    (nextLocal : LocalAt prime next)
    (exitStep : SameLine
      ((inverseTMarker fifthPhase markerTwoPhase).act prime
        (phaseAffine fifthPhase
          (largeFifthState prime first guess
            (largeFifthZeroCount first guess)))) next)
    (sumEq : deleted + remaining = largeFifthZeroCount first guess)
    {word : List PhysicalTemplate}
    (wordOver : WordOver
      (alphabet source target guessPhase firstPhase secondPhase thirdPhase
        fourthPhase fifthPhase markerTwoPhase) word)
    (allLocal : AllStatesLocal prime word
      (phaseAffine fifthPhase (largeFifthState prime first guess deleted)))
    (completeRun : SameLine
      (physicalWordAction prime word
        (phaseAffine fifthPhase (largeFifthState prime first guess deleted)))
      endpoint) :
    ∃ suffix,
      word = List.replicate remaining (identityZero fifthPhase) ++
          [inverseTMarker fifthPhase markerTwoPhase] ++ suffix ∧
      WordOver
        (alphabet source target guessPhase firstPhase secondPhase thirdPhase
          fourthPhase fifthPhase markerTwoPhase) suffix ∧
      AllStatesLocal prime suffix next ∧
      SameLine (physicalWordAction prime suffix next) endpoint := by
  apply fifthScanTail_forced_prefix_to_endpoint primeProperty primeBound
    layout endpointBound fifthEndpointDistinct endpointMembership
    (beforeMembership := fun position positionBelow =>
      largeFifthState_inPhaseAt_before (fifthPhase := fifthPhase)
        primeProperty twoQBelowGuess positionBelow)
    (markerMembership := by
      simpa [markerOne] using
        (largeFifthState_inPhaseAt_marker (fifthPhase := fifthPhase)
          primeProperty twoQBelowGuess))
    (stateLocal := fun position _ =>
      phaseLocal (largeFifthState_local prime first guess position
        primeProperty.1))
    (nextLocal := nextLocal)
    (loopStep := fun position positionBelow =>
      fifthZero_step prime fifthPhase first guess position primeProperty.1
        twoQBelowGuess positionBelow)
    (exitStep := exitStep) sumEq wordOver allLocal completeRun

theorem largeFifthScan_rejects_threeQ
    {prime phaseCount source target guessPhase firstPhase secondPhase
      thirdPhase fourthPhase fifthPhase markerTwoPhase endpointPhase : Nat}
    {endpointDigit : Int} {endpoint : Vec2}
    (primeProperty : IsPrime prime) (primeBound : 6 * phaseCount < prime)
    (layout : PhaseLayout phaseCount source guessPhase firstPhase secondPhase
      thirdPhase fourthPhase fifthPhase markerTwoPhase)
    (endpointBound : endpointPhase < phaseCount)
    (fifthEndpointDistinct : fifthPhase ≠ endpointPhase)
    (endpointMembership : InPhaseAt prime endpointPhase endpointDigit endpoint)
    {first guess deleted remaining : Nat}
    (twoQBelowGuess : 2 * (first + 1) < guess)
    (guessEqThreeQ : guess = 3 * (first + 1))
    (sumEq : deleted + remaining = largeFifthZeroCount first guess)
    {word : List PhysicalTemplate}
    (wordOver : WordOver
      (alphabet source target guessPhase firstPhase secondPhase thirdPhase
        fourthPhase fifthPhase markerTwoPhase) word)
    (allLocal : AllStatesLocal prime word
      (phaseAffine fifthPhase (largeFifthState prime first guess deleted)))
    (completeRun : SameLine
      (physicalWordAction prime word
        (phaseAffine fifthPhase (largeFifthState prime first guess deleted)))
      endpoint) : False := by
  apply fifthScan_rejects_digit_two primeProperty primeBound layout
    endpointBound fifthEndpointDistinct endpointMembership
    (beforeMembership := fun position positionBelow =>
      largeFifthState_inPhaseAt_before (fifthPhase := fifthPhase)
        primeProperty twoQBelowGuess positionBelow)
    (markerMembership := by
      simpa [(largeFifthMarkerDigit_eq_two_iff first guess).2 guessEqThreeQ]
        using (largeFifthState_inPhaseAt_marker (fifthPhase := fifthPhase)
          primeProperty twoQBelowGuess))
    (stateLocal := fun position _ =>
      phaseLocal (largeFifthState_local prime first guess position
        primeProperty.1))
    (loopStep := fun position positionBelow =>
      fifthZero_step prime fifthPhase first guess position primeProperty.1
        twoQBelowGuess positionBelow)
    sumEq wordOver allLocal completeRun

theorem falseMarkerTwoTail_forced_prefix_to_endpoint
    {prime phaseCount source target guessPhase firstPhase secondPhase
      thirdPhase fourthPhase fifthPhase markerTwoPhase endpointPhase : Nat}
    {endpointDigit : Int} {endpoint : Vec2}
    (primeProperty : IsPrime prime) (primeBound : 6 * phaseCount < prime)
    (layout : PhaseLayout phaseCount source guessPhase firstPhase secondPhase
      thirdPhase fourthPhase fifthPhase markerTwoPhase)
    (endpointBound : endpointPhase < phaseCount)
    (markerTwoEndpointDistinct : markerTwoPhase ≠ endpointPhase)
    (endpointMembership : InPhaseAt prime endpointPhase endpointDigit endpoint)
    {first guess deleted remaining : Nat} (QBelowGuess : first + 1 < guess)
    (guessBelowTwoQ : guess < 2 * (first + 1))
    (sumEq : deleted + remaining = falseMarkerTwoZeroCount first guess)
    {word : List PhysicalTemplate}
    (wordOver : WordOver
      (alphabet source target guessPhase firstPhase secondPhase thirdPhase
        fourthPhase fifthPhase markerTwoPhase) word)
    (allLocal : AllStatesLocal prime word
      (phaseAffine markerTwoPhase
        (falseMarkerTwoState prime first guess deleted)))
    (completeRun : SameLine
      (physicalWordAction prime word
        (phaseAffine markerTwoPhase
          (falseMarkerTwoState prime first guess deleted))) endpoint) :
    ∃ suffix,
      word = List.replicate remaining (identityZero markerTwoPhase) ++
          [negatingTMarker markerTwoPhase target] ++ suffix ∧
      WordOver
        (alphabet source target guessPhase firstPhase secondPhase thirdPhase
          fourthPhase fifthPhase markerTwoPhase) suffix ∧
      AllStatesLocal prime suffix
        (phaseAffine target (falseHandoffState prime first guess 0)) ∧
      SameLine
        (physicalWordAction prime suffix
          (phaseAffine target (falseHandoffState prime first guess 0)))
        endpoint := by
  apply markerTwoTail_forced_prefix_to_endpoint primeProperty primeBound
    layout endpointBound markerTwoEndpointDistinct endpointMembership
    (beforeMembership := fun position positionBelow =>
      falseMarkerTwoState_inPhaseAt_before (markerTwoPhase := markerTwoPhase)
        primeProperty QBelowGuess guessBelowTwoQ positionBelow)
    (markerMembership := falseMarkerTwoState_inPhaseAt_marker
      (markerTwoPhase := markerTwoPhase) primeProperty QBelowGuess
      guessBelowTwoQ)
    (stateLocal := fun position _ =>
      phaseLocal (falseMarkerTwoState_local prime first guess position
        primeProperty.1))
    (nextLocal := phaseLocal
      (falseHandoffState_local prime first guess 0 primeProperty.1))
    (loopStep := fun position positionBelow =>
      falseMarkerTwoZero_step prime markerTwoPhase first guess position
        primeProperty.1 QBelowGuess guessBelowTwoQ positionBelow)
    (exitStep := falseMarkerTwoMarker_step prime markerTwoPhase target first
      guess primeProperty.1 QBelowGuess guessBelowTwoQ)
    sumEq wordOver allLocal completeRun

theorem belowThreeMarkerTwo_rejects
    {prime phaseCount source target guessPhase firstPhase secondPhase
      thirdPhase fourthPhase fifthPhase markerTwoPhase endpointPhase : Nat}
    {endpointDigit : Int} {endpoint : Vec2}
    (primeProperty : IsPrime prime) (primeBound : 6 * phaseCount < prime)
    (layout : PhaseLayout phaseCount source guessPhase firstPhase secondPhase
      thirdPhase fourthPhase fifthPhase markerTwoPhase)
    (endpointBound : endpointPhase < phaseCount)
    (markerTwoEndpointDistinct : markerTwoPhase ≠ endpointPhase)
    (endpointMembership : InPhaseAt prime endpointPhase endpointDigit endpoint)
    {first guess deleted remaining : Nat}
    (twoQBelowGuess : 2 * (first + 1) < guess)
    (guessBelowThreeQ : guess < 3 * (first + 1))
    (sumEq : deleted + remaining = belowThreeMarkerTwoZeroCount first guess)
    {word : List PhysicalTemplate}
    (wordOver : WordOver
      (alphabet source target guessPhase firstPhase secondPhase thirdPhase
        fourthPhase fifthPhase markerTwoPhase) word)
    (allLocal : AllStatesLocal prime word
      (phaseAffine markerTwoPhase
        (belowThreeMarkerTwoState prime first guess deleted)))
    (completeRun : SameLine
      (physicalWordAction prime word
        (phaseAffine markerTwoPhase
          (belowThreeMarkerTwoState prime first guess deleted))) endpoint) :
    False := by
  apply markerTwo_rejects_digit_one primeProperty primeBound layout
    endpointBound markerTwoEndpointDistinct endpointMembership
    (beforeMembership := fun position positionBelow =>
      belowThreeMarkerTwoState_inPhaseAt_before
        (markerTwoPhase := markerTwoPhase) primeProperty twoQBelowGuess
        guessBelowThreeQ positionBelow)
    (markerMembership := belowThreeMarkerTwoState_inPhaseAt_marker
      (markerTwoPhase := markerTwoPhase) primeProperty twoQBelowGuess
      guessBelowThreeQ)
    (stateLocal := fun position _ =>
      phaseLocal (belowThreeMarkerTwoState_local prime first guess position
        primeProperty.1))
    (loopStep := fun position positionBelow =>
      belowThreeMarkerTwoZero_step prime markerTwoPhase first guess position
        primeProperty.1 twoQBelowGuess guessBelowThreeQ positionBelow)
    sumEq wordOver allLocal completeRun

theorem aboveThreeMarkerTwoTail_forced_prefix_to_endpoint
    {prime phaseCount source target guessPhase firstPhase secondPhase
      thirdPhase fourthPhase fifthPhase markerTwoPhase endpointPhase : Nat}
    {endpointDigit : Int} {endpoint : Vec2}
    (primeProperty : IsPrime prime) (primeBound : 6 * phaseCount < prime)
    (layout : PhaseLayout phaseCount source guessPhase firstPhase secondPhase
      thirdPhase fourthPhase fifthPhase markerTwoPhase)
    (endpointBound : endpointPhase < phaseCount)
    (markerTwoEndpointDistinct : markerTwoPhase ≠ endpointPhase)
    (endpointMembership : InPhaseAt prime endpointPhase endpointDigit endpoint)
    {first guess deleted remaining : Nat}
    (threeQBelowGuess : 3 * (first + 1) < guess)
    (guessEqFourQ : guess = 4 * (first + 1))
    (sumEq : deleted + remaining = aboveThreeMarkerTwoZeroCount first guess)
    {word : List PhysicalTemplate}
    (wordOver : WordOver
      (alphabet source target guessPhase firstPhase secondPhase thirdPhase
        fourthPhase fifthPhase markerTwoPhase) word)
    (allLocal : AllStatesLocal prime word
      (phaseAffine markerTwoPhase
        (aboveThreeMarkerTwoState prime first guess deleted)))
    (completeRun : SameLine
      (physicalWordAction prime word
        (phaseAffine markerTwoPhase
          (aboveThreeMarkerTwoState prime first guess deleted))) endpoint) :
    ∃ suffix,
      word = List.replicate remaining (identityZero markerTwoPhase) ++
          [negatingTMarker markerTwoPhase target] ++ suffix ∧
      WordOver
        (alphabet source target guessPhase firstPhase secondPhase thirdPhase
          fourthPhase fifthPhase markerTwoPhase) suffix ∧
      AllStatesLocal prime suffix
        (phaseAffine target (acceptedHandoffState prime first)) ∧
      SameLine
        (physicalWordAction prime suffix
          (phaseAffine target (acceptedHandoffState prime first))) endpoint := by
  subst guess
  have countEq : aboveThreeMarkerTwoZeroCount first (4 * (first + 1)) =
      first := by
    simp [aboveThreeMarkerTwoZeroCount]
    omega
  apply markerTwoTail_forced_prefix_to_endpoint primeProperty primeBound
    layout endpointBound markerTwoEndpointDistinct endpointMembership
    (beforeMembership := fun position positionBelow =>
      aboveThreeMarkerTwoState_inPhaseAt_before
        (markerTwoPhase := markerTwoPhase) primeProperty (by omega)
        (by simpa [countEq] using positionBelow))
    (markerMembership := by
      simpa [countEq, aboveThreeMarkerTwoDigit] using
        (aboveThreeMarkerTwoState_inPhaseAt_marker
          (markerTwoPhase := markerTwoPhase) (first := first)
          (guess := 4 * (first + 1)) primeProperty (by omega)))
    (stateLocal := fun position _ =>
      phaseLocal (aboveThreeMarkerTwoState_local prime first
        (4 * (first + 1)) position primeProperty.1))
    (nextLocal := phaseLocal
      (acceptedHandoffState_local prime first primeProperty.1))
    (loopStep := fun position positionBelow => by
      rw [countEq] at positionBelow
      exact markerTwoZero_step prime markerTwoPhase first position
        primeProperty.1 positionBelow)
    (exitStep := by
      rw [countEq]
      exact markerTwoAcceptedMarker_step prime markerTwoPhase target first
        primeProperty.1)
    sumEq wordOver allLocal completeRun

theorem aboveThreeMarkerTwo_rejects_wrong_guess
    {prime phaseCount source target guessPhase firstPhase secondPhase
      thirdPhase fourthPhase fifthPhase markerTwoPhase endpointPhase : Nat}
    {endpointDigit : Int} {endpoint : Vec2}
    (primeProperty : IsPrime prime) (primeBound : 6 * phaseCount < prime)
    (layout : PhaseLayout phaseCount source guessPhase firstPhase secondPhase
      thirdPhase fourthPhase fifthPhase markerTwoPhase)
    (endpointBound : endpointPhase < phaseCount)
    (markerTwoEndpointDistinct : markerTwoPhase ≠ endpointPhase)
    (endpointMembership : InPhaseAt prime endpointPhase endpointDigit endpoint)
    {first guess deleted remaining : Nat}
    (threeQBelowGuess : 3 * (first + 1) < guess)
    (guessNeFourQ : guess ≠ 4 * (first + 1))
    (sumEq : deleted + remaining = aboveThreeMarkerTwoZeroCount first guess)
    {word : List PhysicalTemplate}
    (wordOver : WordOver
      (alphabet source target guessPhase firstPhase secondPhase thirdPhase
        fourthPhase fifthPhase markerTwoPhase) word)
    (allLocal : AllStatesLocal prime word
      (phaseAffine markerTwoPhase
        (aboveThreeMarkerTwoState prime first guess deleted)))
    (completeRun : SameLine
      (physicalWordAction prime word
        (phaseAffine markerTwoPhase
          (aboveThreeMarkerTwoState prime first guess deleted))) endpoint) :
    False := by
  apply markerTwo_rejects_digit_one primeProperty primeBound layout
    endpointBound markerTwoEndpointDistinct endpointMembership
    (beforeMembership := fun position positionBelow =>
      aboveThreeMarkerTwoState_inPhaseAt_before
        (markerTwoPhase := markerTwoPhase) primeProperty threeQBelowGuess
        positionBelow)
    (markerMembership := by
      have digitOne : aboveThreeMarkerTwoDigit first guess = 1 := by
        simp [aboveThreeMarkerTwoDigit, guessNeFourQ]
      simpa [digitOne] using
        (aboveThreeMarkerTwoState_inPhaseAt_marker
          (markerTwoPhase := markerTwoPhase) primeProperty threeQBelowGuess))
    (stateLocal := fun position _ =>
      phaseLocal (aboveThreeMarkerTwoState_local prime first guess position
        primeProperty.1))
    (loopStep := fun position positionBelow =>
      aboveThreeMarkerTwoZero_step prime markerTwoPhase first guess position
        primeProperty.1 threeQBelowGuess positionBelow)
    sumEq wordOver allLocal completeRun

/-- Exhaustive converse for the deterministic part of the fivefold front.
Only the intended guess reaches the accepted handoff.  The sole other
survivor is the deliberate false interval `Q < guess < 2Q`; its exact word
and handoff state are returned for the following subtraction validator. -/
theorem automaticSuffix_classifies
    {prime phaseCount source target guessPhase firstPhase secondPhase
      thirdPhase fourthPhase fifthPhase markerTwoPhase endpointPhase : Nat}
    {endpointDigit : Int} {endpoint : Vec2}
    (primeProperty : IsPrime prime) (primeBound : 6 * phaseCount < prime)
    (layout : PhaseLayout phaseCount source guessPhase firstPhase secondPhase
      thirdPhase fourthPhase fifthPhase markerTwoPhase)
    (endpointBound : endpointPhase < phaseCount)
    (firstTargetDistinct : firstPhase ≠ endpointPhase)
    (secondTargetDistinct : secondPhase ≠ endpointPhase)
    (thirdTargetDistinct : thirdPhase ≠ endpointPhase)
    (fourthTargetDistinct : fourthPhase ≠ endpointPhase)
    (fifthTargetDistinct : fifthPhase ≠ endpointPhase)
    (markerTwoTargetDistinct : markerTwoPhase ≠ endpointPhase)
    (endpointMembership : InPhaseAt prime endpointPhase endpointDigit endpoint)
    {first guess : Nat} (guessPositive : 0 < guess)
    {word : List PhysicalTemplate}
    (wordOver : WordOver
      (alphabet source target guessPhase firstPhase secondPhase thirdPhase
        fourthPhase fifthPhase markerTwoPhase) word)
    (allLocal : AllStatesLocal prime word
      (phaseAffine firstPhase (firstAutomaticState prime first guess 0)))
    (completeRun : SameLine
      (physicalWordAction prime word
        (phaseAffine firstPhase (firstAutomaticState prime first guess 0)))
      endpoint) :
    ∃ suffix,
      (guess = 4 * (first + 1) ∧
        word = automaticAcceptedWord target firstPhase secondPhase thirdPhase
            fourthPhase fifthPhase markerTwoPhase first ++ suffix ∧
        WordOver
          (alphabet source target guessPhase firstPhase secondPhase thirdPhase
            fourthPhase fifthPhase markerTwoPhase) suffix ∧
        AllStatesLocal prime suffix
          (phaseAffine target (acceptedHandoffState prime first)) ∧
        SameLine
          (physicalWordAction prime suffix
            (phaseAffine target (acceptedHandoffState prime first)))
          endpoint) ∨
      (first + 1 < guess ∧ guess < 2 * (first + 1) ∧
        word = falseSurvivorAutomaticWord target firstPhase secondPhase
            thirdPhase fourthPhase fifthPhase markerTwoPhase first guess ++
          suffix ∧
        WordOver
          (alphabet source target guessPhase firstPhase secondPhase thirdPhase
            fourthPhase fifthPhase markerTwoPhase) suffix ∧
        AllStatesLocal prime suffix
          (phaseAffine target (falseHandoffState prime first guess 0)) ∧
        SameLine
          (physicalWordAction prime suffix
            (phaseAffine target (falseHandoffState prime first guess 0)))
          endpoint) := by
  obtain ⟨afterFirst, firstEq, afterFirstOver, afterFirstLocal,
      afterFirstRun⟩ := firstScanTail_forced_prefix_to_endpoint
    primeProperty primeBound layout endpointBound firstTargetDistinct
    endpointMembership (first := first) (guess := guess) (deleted := 0)
    (remaining := first) (by omega) wordOver allLocal completeRun
  obtain ⟨afterSecond, secondEq, afterSecondOver, afterSecondLocal,
      afterSecondRun⟩ := secondScanTail_forced_prefix_to_endpoint
    primeProperty primeBound layout endpointBound secondTargetDistinct
    endpointMembership guessPositive (deleted := 0) (remaining := first)
    (by omega) afterFirstOver afterFirstLocal afterFirstRun
  obtain ⟨afterThird, thirdAccepted, thirdEq, afterThirdOver,
      afterThirdLocal, afterThirdRun⟩ :=
    thirdScanTail_forced_prefix_to_endpoint primeProperty primeBound layout
      endpointBound thirdTargetDistinct endpointMembership guessPositive
      (deleted := 0) (remaining := thirdScanLength first guess) (by omega)
      afterSecondOver afterSecondLocal afterSecondRun
  cases exhaustive_fivefold_outcome first guess guessPositive with
  | fifthRejectSmall guessBelowQ =>
      have markerOne : fourthMarkerDigit first guess = 1 := by
        simp [fourthMarkerDigit, ternaryValidatorMarkerDigit]
        omega
      obtain ⟨afterFourth, fourthEq, afterFourthOver, afterFourthLocal,
          afterFourthRun⟩ := fourthScanTail_forced_prefix_to_endpoint
        primeProperty primeBound layout endpointBound fourthTargetDistinct
        endpointMembership guessPositive thirdAccepted markerOne
        (next := smallFifthState prime first guess 0)
        (smallFifthState_local prime first guess 0 primeProperty.1)
        (by rw [smallFifthState_zero]
            exact fourth_small_delete_marker prime first guess
              primeProperty.1 guessPositive guessBelowQ)
        (deleted := 0) (remaining := fourthZeroCount first guess) (by omega)
        afterThirdOver afterThirdLocal afterThirdRun
      exact False.elim (smallFifthScan_rejects primeProperty primeBound
        layout endpointBound fifthTargetDistinct endpointMembership guessPositive
        guessBelowQ (deleted := 0)
        (remaining := smallFifthZeroCount first guess) (by omega)
        afterFourthOver afterFourthLocal afterFourthRun)
  | thirdRejectAtQ guessEqQ =>
      exact False.elim (thirdAccepted (by omega))
  | falseSurvivor QBelowGuess guessBelowTwoQ =>
      have markerOne : fourthMarkerDigit first guess = 1 := by
        simp [fourthMarkerDigit, ternaryValidatorMarkerDigit]
        omega
      obtain ⟨afterFourth, fourthEq, afterFourthOver, afterFourthLocal,
          afterFourthRun⟩ := fourthScanTail_forced_prefix_to_endpoint
        primeProperty primeBound layout endpointBound fourthTargetDistinct
        endpointMembership guessPositive thirdAccepted markerOne
        (next := middleFifthState prime first guess 0)
        (middleFifthState_local prime first guess 0 primeProperty.1)
        (by rw [middleFifthState_zero]
            exact fourth_middle_delete_marker prime first guess
              primeProperty.1 QBelowGuess guessBelowTwoQ)
        (deleted := 0) (remaining := fourthZeroCount first guess) (by omega)
        afterThirdOver afterThirdLocal afterThirdRun
      obtain ⟨afterFifth, fifthEq, afterFifthOver, afterFifthLocal,
          afterFifthRun⟩ := middleFifthScan_forced_prefix_to_endpoint
        primeProperty primeBound layout endpointBound fifthTargetDistinct
        endpointMembership QBelowGuess guessBelowTwoQ (deleted := 0)
        (remaining := middleFifthZeroCount first guess) (by omega)
        afterFourthOver afterFourthLocal afterFourthRun
      obtain ⟨suffix, markerEq, suffixOver, suffixLocal, suffixRun⟩ :=
        falseMarkerTwoTail_forced_prefix_to_endpoint primeProperty primeBound
          layout endpointBound markerTwoTargetDistinct endpointMembership
          QBelowGuess guessBelowTwoQ (deleted := 0)
          (remaining := falseMarkerTwoZeroCount first guess) (by omega)
          afterFifthOver afterFifthLocal afterFifthRun
      rw [markerEq] at fifthEq
      rw [fifthEq] at fourthEq
      rw [fourthEq] at thirdEq
      rw [thirdEq] at secondEq
      rw [secondEq] at firstEq
      refine ⟨suffix, .inr ⟨QBelowGuess, guessBelowTwoQ, ?_, suffixOver,
        suffixLocal, suffixRun⟩⟩
      simpa [falseSurvivorAutomaticWord, plainScanWord, fifthScanWord,
        markerTwoWord, List.append_assoc] using firstEq
  | fourthRejectAtTwoQ guessEqTwoQ =>
      exact False.elim (fourthScan_rejects_twoQ primeProperty primeBound
        layout endpointBound fourthTargetDistinct endpointMembership
        guessPositive thirdAccepted guessEqTwoQ (deleted := 0)
        (remaining := fourthZeroCount first guess) (by omega)
        afterThirdOver afterThirdLocal afterThirdRun)
  | markerTwoRejectMiddle twoQBelowGuess guessBelowThreeQ =>
      have markerOne : fourthMarkerDigit first guess = 1 := by
        simp [fourthMarkerDigit, ternaryValidatorMarkerDigit]
        omega
      obtain ⟨afterFourth, _, afterFourthOver, afterFourthLocal,
          afterFourthRun⟩ := fourthScanTail_forced_prefix_to_endpoint
        primeProperty primeBound layout endpointBound fourthTargetDistinct
        endpointMembership guessPositive thirdAccepted markerOne
        (next := largeFifthState prime first guess 0)
        (largeFifthState_local prime first guess 0 primeProperty.1)
        (by rw [largeFifthState_zero]
            exact fourth_large_delete_marker prime first guess
              primeProperty.1 twoQBelowGuess)
        (deleted := 0) (remaining := fourthZeroCount first guess) (by omega)
        afterThirdOver afterThirdLocal afterThirdRun
      have fifthMarkerOne : largeFifthMarkerDigit first guess = 1 := by
        simp [largeFifthMarkerDigit]
        omega
      obtain ⟨afterFifth, _, afterFifthOver, afterFifthLocal,
          afterFifthRun⟩ := largeFifthScan_forced_prefix_to_endpoint
        primeProperty primeBound layout endpointBound fifthTargetDistinct
        endpointMembership twoQBelowGuess fifthMarkerOne
        (next := phaseAffine markerTwoPhase
          (belowThreeMarkerTwoState prime first guess 0))
        (phaseLocal (belowThreeMarkerTwoState_local prime first guess 0
          primeProperty.1))
        (belowThreeFifthMarker_step prime fifthPhase markerTwoPhase first guess
          primeProperty.1 twoQBelowGuess guessBelowThreeQ)
        (deleted := 0) (remaining := largeFifthZeroCount first guess)
        (by omega) afterFourthOver afterFourthLocal afterFourthRun
      exact False.elim (belowThreeMarkerTwo_rejects primeProperty primeBound
        layout endpointBound markerTwoTargetDistinct endpointMembership
        twoQBelowGuess guessBelowThreeQ (deleted := 0)
        (remaining := belowThreeMarkerTwoZeroCount first guess) (by omega)
        afterFifthOver afterFifthLocal afterFifthRun)
  | fifthRejectAtThreeQ guessEqThreeQ =>
      have twoQBelowGuess : 2 * (first + 1) < guess := by omega
      have markerOne : fourthMarkerDigit first guess = 1 := by
        simp [fourthMarkerDigit, ternaryValidatorMarkerDigit]
        omega
      obtain ⟨afterFourth, _, afterFourthOver, afterFourthLocal,
          afterFourthRun⟩ := fourthScanTail_forced_prefix_to_endpoint
        primeProperty primeBound layout endpointBound fourthTargetDistinct
        endpointMembership guessPositive thirdAccepted markerOne
        (next := largeFifthState prime first guess 0)
        (largeFifthState_local prime first guess 0 primeProperty.1)
        (by rw [largeFifthState_zero]
            exact fourth_large_delete_marker prime first guess
              primeProperty.1 twoQBelowGuess)
        (deleted := 0) (remaining := fourthZeroCount first guess) (by omega)
        afterThirdOver afterThirdLocal afterThirdRun
      exact False.elim (largeFifthScan_rejects_threeQ primeProperty primeBound
        layout endpointBound fifthTargetDistinct endpointMembership
        twoQBelowGuess guessEqThreeQ (deleted := 0)
        (remaining := largeFifthZeroCount first guess) (by omega)
        afterFourthOver afterFourthLocal afterFourthRun)
  | accepted guessEqFourQ =>
      have twoQBelowGuess : 2 * (first + 1) < guess := by omega
      have threeQBelowGuess : 3 * (first + 1) < guess := by omega
      have markerOne : fourthMarkerDigit first guess = 1 := by
        simp [fourthMarkerDigit, ternaryValidatorMarkerDigit]
        omega
      obtain ⟨afterFourth, fourthEq, afterFourthOver, afterFourthLocal,
          afterFourthRun⟩ := fourthScanTail_forced_prefix_to_endpoint
        primeProperty primeBound layout endpointBound fourthTargetDistinct
        endpointMembership guessPositive thirdAccepted markerOne
        (next := largeFifthState prime first guess 0)
        (largeFifthState_local prime first guess 0 primeProperty.1)
        (by rw [largeFifthState_zero]
            exact fourth_large_delete_marker prime first guess
              primeProperty.1 twoQBelowGuess)
        (deleted := 0) (remaining := fourthZeroCount first guess) (by omega)
        afterThirdOver afterThirdLocal afterThirdRun
      have fifthMarkerOne : largeFifthMarkerDigit first guess = 1 := by
        simp [largeFifthMarkerDigit]
        omega
      obtain ⟨afterFifth, fifthEq, afterFifthOver, afterFifthLocal,
          afterFifthRun⟩ := largeFifthScan_forced_prefix_to_endpoint
        primeProperty primeBound layout endpointBound fifthTargetDistinct
        endpointMembership twoQBelowGuess fifthMarkerOne
        (next := phaseAffine markerTwoPhase
          (aboveThreeMarkerTwoState prime first guess 0))
        (phaseLocal (aboveThreeMarkerTwoState_local prime first guess 0
          primeProperty.1))
        (aboveThreeFifthMarker_step prime fifthPhase markerTwoPhase first guess
          primeProperty.1 threeQBelowGuess)
        (deleted := 0) (remaining := largeFifthZeroCount first guess)
        (by omega) afterFourthOver afterFourthLocal afterFourthRun
      obtain ⟨suffix, markerEq, suffixOver, suffixLocal, suffixRun⟩ :=
        aboveThreeMarkerTwoTail_forced_prefix_to_endpoint primeProperty
          primeBound layout endpointBound markerTwoTargetDistinct
          endpointMembership threeQBelowGuess guessEqFourQ (deleted := 0)
          (remaining := aboveThreeMarkerTwoZeroCount first guess) (by omega)
          afterFifthOver afterFifthLocal afterFifthRun
      rw [markerEq] at fifthEq
      rw [fifthEq] at fourthEq
      rw [fourthEq] at thirdEq
      rw [thirdEq] at secondEq
      rw [secondEq] at firstEq
      have thirdCount : thirdScanLength first guess = first := by
        simp [thirdScanLength]
        omega
      have fourthCount : fourthZeroCount first guess = first := by
        unfold fourthZeroCount ternaryValidatorLength
        rw [if_pos (by omega)]
        exact Nat.min_eq_left (by omega)
      have fifthCount : largeFifthZeroCount first guess = first := by
        simp [largeFifthZeroCount]
        omega
      have markerCount : aboveThreeMarkerTwoZeroCount first guess = first := by
        simp [aboveThreeMarkerTwoZeroCount]
        omega
      refine ⟨suffix, .inl ⟨guessEqFourQ, ?_, suffixOver, suffixLocal,
        suffixRun⟩⟩
      simpa [automaticAcceptedWord, plainScanWord, fifthScanWord,
        markerTwoWord, thirdCount, fourthCount, fifthCount, markerCount,
        List.append_assoc] using firstEq
  | markerTwoRejectHigh threeQBelowGuess guessNeFourQ =>
      have twoQBelowGuess : 2 * (first + 1) < guess := by omega
      have markerOne : fourthMarkerDigit first guess = 1 := by
        simp [fourthMarkerDigit, ternaryValidatorMarkerDigit]
        omega
      obtain ⟨afterFourth, _, afterFourthOver, afterFourthLocal,
          afterFourthRun⟩ := fourthScanTail_forced_prefix_to_endpoint
        primeProperty primeBound layout endpointBound fourthTargetDistinct
        endpointMembership guessPositive thirdAccepted markerOne
        (next := largeFifthState prime first guess 0)
        (largeFifthState_local prime first guess 0 primeProperty.1)
        (by rw [largeFifthState_zero]
            exact fourth_large_delete_marker prime first guess
              primeProperty.1 twoQBelowGuess)
        (deleted := 0) (remaining := fourthZeroCount first guess) (by omega)
        afterThirdOver afterThirdLocal afterThirdRun
      have fifthMarkerOne : largeFifthMarkerDigit first guess = 1 := by
        simp [largeFifthMarkerDigit]
        omega
      obtain ⟨afterFifth, _, afterFifthOver, afterFifthLocal,
          afterFifthRun⟩ := largeFifthScan_forced_prefix_to_endpoint
        primeProperty primeBound layout endpointBound fifthTargetDistinct
        endpointMembership twoQBelowGuess fifthMarkerOne
        (next := phaseAffine markerTwoPhase
          (aboveThreeMarkerTwoState prime first guess 0))
        (phaseLocal (aboveThreeMarkerTwoState_local prime first guess 0
          primeProperty.1))
        (aboveThreeFifthMarker_step prime fifthPhase markerTwoPhase first guess
          primeProperty.1 threeQBelowGuess)
        (deleted := 0) (remaining := largeFifthZeroCount first guess)
        (by omega) afterFourthOver afterFourthLocal afterFourthRun
      exact False.elim (aboveThreeMarkerTwo_rejects_wrong_guess
        primeProperty primeBound layout endpointBound markerTwoTargetDistinct
        endpointMembership threeQBelowGuess guessNeFourQ (deleted := 0)
        (remaining := aboveThreeMarkerTwoZeroCount first guess) (by omega)
        afterFifthOver afterFifthLocal afterFifthRun)

/-- Full classification of a nonempty path through the sixteen-letter core.
The endpoint may equal the source phase because nonemptiness removes the
otherwise possible empty execution. -/
theorem completedPath_classifies_of_nonempty
    {prime phaseCount source target guessPhase firstPhase secondPhase
      thirdPhase fourthPhase fifthPhase markerTwoPhase endpointPhase inputFirst :
      Nat}
    {endpointDigit : Int} {endpoint : Vec2}
    (primeProperty : IsPrime prime) (primeBound : 6 * phaseCount < prime)
    (layout : PhaseLayout phaseCount source guessPhase firstPhase secondPhase
      thirdPhase fourthPhase fifthPhase markerTwoPhase)
    (endpointBound : endpointPhase < phaseCount)
    (guessTargetDistinct : guessPhase ≠ endpointPhase)
    (firstTargetDistinct : firstPhase ≠ endpointPhase)
    (secondTargetDistinct : secondPhase ≠ endpointPhase)
    (thirdTargetDistinct : thirdPhase ≠ endpointPhase)
    (fourthTargetDistinct : fourthPhase ≠ endpointPhase)
    (fifthTargetDistinct : fifthPhase ≠ endpointPhase)
    (markerTwoTargetDistinct : markerTwoPhase ≠ endpointPhase)
    (endpointMembership : InPhaseAt prime endpointPhase endpointDigit endpoint)
    {word : List PhysicalTemplate}
    (wordOver : WordOver
      (alphabet source target guessPhase firstPhase secondPhase thirdPhase
        fourthPhase fifthPhase markerTwoPhase) word)
    (wordNonempty : word ≠ [])
    (allLocal : AllStatesLocal prime word
      (phaseAffine source (unaryCode prime (5 * inputFirst + 4))))
    (completeRun : SameLine
      (physicalWordAction prime word
        (phaseAffine source (unaryCode prime (5 * inputFirst + 4))))
      endpoint) :
    ∃ suffix,
      (word = acceptedWord source target guessPhase firstPhase secondPhase
            thirdPhase fourthPhase fifthPhase markerTwoPhase inputFirst ++
          suffix ∧
        WordOver
          (alphabet source target guessPhase firstPhase secondPhase thirdPhase
            fourthPhase fifthPhase markerTwoPhase) suffix ∧
        AllStatesLocal prime suffix
          (phaseAffine target (acceptedHandoffState prime inputFirst)) ∧
        SameLine
          (physicalWordAction prime suffix
            (phaseAffine target (acceptedHandoffState prime inputFirst)))
          endpoint) ∨
      (∃ first guess,
        first + guess = 5 * inputFirst + 4 ∧
        first + 1 < guess ∧ guess < 2 * (first + 1) ∧
        word = falseSurvivorWord source target guessPhase firstPhase
            secondPhase thirdPhase fourthPhase fifthPhase markerTwoPhase
            first guess ++ suffix ∧
        WordOver
          (alphabet source target guessPhase firstPhase secondPhase thirdPhase
            fourthPhase fifthPhase markerTwoPhase) suffix ∧
        AllStatesLocal prime suffix
          (phaseAffine target (falseHandoffState prime first guess 0)) ∧
        SameLine
          (physicalWordAction prime suffix
            (phaseAffine target (falseHandoffState prime first guess 0)))
          endpoint) := by
  obtain ⟨first, guess, afterPrefix, guessPositive, splitEq, prefixEq,
      afterPrefixOver, afterPrefixLocal, afterPrefixRun⟩ :=
    prefix_choice_forced_to_endpoint_of_nonempty primeProperty primeBound
      layout endpointBound guessTargetDistinct endpointMembership
      (counter := 5 * inputFirst + 4) (by omega) wordOver wordNonempty allLocal
      completeRun
  obtain ⟨suffix, accepted | falseSurvivor⟩ := automaticSuffix_classifies
    primeProperty primeBound layout endpointBound firstTargetDistinct
    secondTargetDistinct thirdTargetDistinct fourthTargetDistinct
    fifthTargetDistinct markerTwoTargetDistinct endpointMembership
    guessPositive afterPrefixOver afterPrefixLocal afterPrefixRun
  · rcases accepted with ⟨guessEq, automaticEq, suffixOver, suffixLocal,
      suffixRun⟩
    have firstEq : first = inputFirst := by omega
    subst first
    rw [automaticEq] at prefixEq
    refine ⟨suffix, .inl ⟨?_, suffixOver, suffixLocal, suffixRun⟩⟩
    simpa [guessEq, acceptedWord, automaticAcceptedWord, List.append_assoc] using
      prefixEq
  · rcases falseSurvivor with ⟨QBelowGuess, guessBelowTwoQ, automaticEq,
      suffixOver, suffixLocal, suffixRun⟩
    rw [automaticEq] at prefixEq
    refine ⟨suffix, .inr ⟨first, guess, splitEq, QBelowGuess,
      guessBelowTwoQ, ?_, suffixOver, suffixLocal, suffixRun⟩⟩
    simpa [falseSurvivorWord, List.append_assoc] using prefixEq

/-- General positive-input classification of a nonempty core path.  In the
accepted branch the parser derives, rather than assumes, the equation
`counter = 5 * first + 4`. -/
theorem completedPath_classifies_general_of_nonempty
    {prime phaseCount source target guessPhase firstPhase secondPhase
      thirdPhase fourthPhase fifthPhase markerTwoPhase endpointPhase counter :
      Nat}
    {endpointDigit : Int} {endpoint : Vec2}
    (primeProperty : IsPrime prime) (primeBound : 6 * phaseCount < prime)
    (layout : PhaseLayout phaseCount source guessPhase firstPhase secondPhase
      thirdPhase fourthPhase fifthPhase markerTwoPhase)
    (endpointBound : endpointPhase < phaseCount)
    (guessTargetDistinct : guessPhase ≠ endpointPhase)
    (firstTargetDistinct : firstPhase ≠ endpointPhase)
    (secondTargetDistinct : secondPhase ≠ endpointPhase)
    (thirdTargetDistinct : thirdPhase ≠ endpointPhase)
    (fourthTargetDistinct : fourthPhase ≠ endpointPhase)
    (fifthTargetDistinct : fifthPhase ≠ endpointPhase)
    (markerTwoTargetDistinct : markerTwoPhase ≠ endpointPhase)
    (endpointMembership : InPhaseAt prime endpointPhase endpointDigit endpoint)
    (counterPositive : 0 < counter)
    {word : List PhysicalTemplate}
    (wordOver : WordOver
      (alphabet source target guessPhase firstPhase secondPhase thirdPhase
        fourthPhase fifthPhase markerTwoPhase) word)
    (wordNonempty : word ≠ [])
    (allLocal : AllStatesLocal prime word
      (phaseAffine source (unaryCode prime counter)))
    (completeRun : SameLine
      (physicalWordAction prime word
        (phaseAffine source (unaryCode prime counter))) endpoint) :
    ∃ suffix,
      ((∃ first,
        counter = 5 * first + 4 ∧
        word = acceptedWord source target guessPhase firstPhase secondPhase
              thirdPhase fourthPhase fifthPhase markerTwoPhase first ++
            suffix ∧
        WordOver
          (alphabet source target guessPhase firstPhase secondPhase thirdPhase
            fourthPhase fifthPhase markerTwoPhase) suffix ∧
        AllStatesLocal prime suffix
          (phaseAffine target (acceptedHandoffState prime first)) ∧
        SameLine
          (physicalWordAction prime suffix
            (phaseAffine target (acceptedHandoffState prime first)))
          endpoint) ∨
      (∃ first guess,
        first + guess = counter ∧
        first + 1 < guess ∧ guess < 2 * (first + 1) ∧
        word = falseSurvivorWord source target guessPhase firstPhase
            secondPhase thirdPhase fourthPhase fifthPhase markerTwoPhase
            first guess ++ suffix ∧
        WordOver
          (alphabet source target guessPhase firstPhase secondPhase thirdPhase
            fourthPhase fifthPhase markerTwoPhase) suffix ∧
        AllStatesLocal prime suffix
          (phaseAffine target (falseHandoffState prime first guess 0)) ∧
        SameLine
          (physicalWordAction prime suffix
            (phaseAffine target (falseHandoffState prime first guess 0)))
          endpoint)) := by
  obtain ⟨first, guess, afterPrefix, guessPositive, splitEq, prefixEq,
      afterPrefixOver, afterPrefixLocal, afterPrefixRun⟩ :=
    prefix_choice_forced_to_endpoint_of_nonempty primeProperty primeBound
      layout endpointBound guessTargetDistinct endpointMembership
      counterPositive wordOver wordNonempty allLocal completeRun
  obtain ⟨suffix, accepted | falseSurvivor⟩ := automaticSuffix_classifies
    primeProperty primeBound layout endpointBound firstTargetDistinct
    secondTargetDistinct thirdTargetDistinct fourthTargetDistinct
    fifthTargetDistinct markerTwoTargetDistinct endpointMembership
    guessPositive afterPrefixOver afterPrefixLocal afterPrefixRun
  · rcases accepted with ⟨guessEq, automaticEq, suffixOver, suffixLocal,
      suffixRun⟩
    rw [automaticEq] at prefixEq
    refine ⟨suffix, .inl ⟨first, ?_, ?_, suffixOver, suffixLocal,
      suffixRun⟩⟩
    · omega
    · simpa [guessEq, acceptedWord, automaticAcceptedWord,
        List.append_assoc] using prefixEq
  · rcases falseSurvivor with ⟨QBelowGuess, guessBelowTwoQ, automaticEq,
      suffixOver, suffixLocal, suffixRun⟩
    rw [automaticEq] at prefixEq
    refine ⟨suffix, .inr ⟨first, guess, splitEq, QBelowGuess,
      guessBelowTwoQ, ?_, suffixOver, suffixLocal, suffixRun⟩⟩
    simpa [falseSurvivorWord, List.append_assoc] using prefixEq

/-- Full boundary-to-boundary classification for the sixteen-letter core.
The accepted branch forces the unique split `first + 4(first+1)`, while the
only other branch is the explicit false survivor passed to the next
subtraction scan. -/
theorem completedPath_classifies
    {prime phaseCount source target guessPhase firstPhase secondPhase
      thirdPhase fourthPhase fifthPhase markerTwoPhase endpointPhase inputFirst :
      Nat}
    {endpointDigit : Int} {endpoint : Vec2}
    (primeProperty : IsPrime prime) (primeBound : 6 * phaseCount < prime)
    (layout : PhaseLayout phaseCount source guessPhase firstPhase secondPhase
      thirdPhase fourthPhase fifthPhase markerTwoPhase)
    (endpointBound : endpointPhase < phaseCount)
    (sourceTargetDistinct : source ≠ endpointPhase)
    (guessTargetDistinct : guessPhase ≠ endpointPhase)
    (firstTargetDistinct : firstPhase ≠ endpointPhase)
    (secondTargetDistinct : secondPhase ≠ endpointPhase)
    (thirdTargetDistinct : thirdPhase ≠ endpointPhase)
    (fourthTargetDistinct : fourthPhase ≠ endpointPhase)
    (fifthTargetDistinct : fifthPhase ≠ endpointPhase)
    (markerTwoTargetDistinct : markerTwoPhase ≠ endpointPhase)
    (endpointMembership : InPhaseAt prime endpointPhase endpointDigit endpoint)
    {word : List PhysicalTemplate}
    (wordOver : WordOver
      (alphabet source target guessPhase firstPhase secondPhase thirdPhase
        fourthPhase fifthPhase markerTwoPhase) word)
    (allLocal : AllStatesLocal prime word
      (phaseAffine source (unaryCode prime (5 * inputFirst + 4))))
    (completeRun : SameLine
      (physicalWordAction prime word
        (phaseAffine source (unaryCode prime (5 * inputFirst + 4))))
      endpoint) :
    ∃ suffix,
      (word = acceptedWord source target guessPhase firstPhase secondPhase
            thirdPhase fourthPhase fifthPhase markerTwoPhase inputFirst ++
          suffix ∧
        WordOver
          (alphabet source target guessPhase firstPhase secondPhase thirdPhase
            fourthPhase fifthPhase markerTwoPhase) suffix ∧
        AllStatesLocal prime suffix
          (phaseAffine target (acceptedHandoffState prime inputFirst)) ∧
        SameLine
          (physicalWordAction prime suffix
            (phaseAffine target (acceptedHandoffState prime inputFirst)))
          endpoint) ∨
      (∃ first guess,
        first + guess = 5 * inputFirst + 4 ∧
        first + 1 < guess ∧ guess < 2 * (first + 1) ∧
        word = falseSurvivorWord source target guessPhase firstPhase
            secondPhase thirdPhase fourthPhase fifthPhase markerTwoPhase
            first guess ++ suffix ∧
        WordOver
          (alphabet source target guessPhase firstPhase secondPhase thirdPhase
            fourthPhase fifthPhase markerTwoPhase) suffix ∧
        AllStatesLocal prime suffix
          (phaseAffine target (falseHandoffState prime first guess 0)) ∧
        SameLine
          (physicalWordAction prime suffix
            (phaseAffine target (falseHandoffState prime first guess 0)))
          endpoint) := by
  obtain ⟨sourceDigit, sourceMembership⟩ := unaryCode_inPhaseAt
    (base := prime) (phase := source) (counter := 5 * inputFirst + 4)
    primeProperty.1
  have wordNonempty := word_nonempty_of_endpoint_phase_ne primeProperty
    primeBound layout.sourceBound endpointBound sourceTargetDistinct
    sourceMembership endpointMembership completeRun
  exact completedPath_classifies_of_nonempty primeProperty primeBound layout
    endpointBound guessTargetDistinct firstTargetDistinct secondTargetDistinct
    thirdTargetDistinct fourthTargetDistinct fifthTargetDistinct
    markerTwoTargetDistinct endpointMembership wordOver wordNonempty allLocal
    completeRun

/-- No core letter leaves the handoff phase, provided that phase is not one
of the eight active source phases. -/
theorem no_core_letter_from_target
    {prime phaseCount source target guessPhase firstPhase secondPhase
      thirdPhase fourthPhase fifthPhase markerTwoPhase : Nat}
    {digit : Int} {state : Vec2} {letter : PhysicalTemplate}
    (primeProperty : IsPrime prime) (primeBound : 6 * phaseCount < prime)
    (layout : PhaseLayout phaseCount source guessPhase firstPhase secondPhase
      thirdPhase fourthPhase fifthPhase markerTwoPhase)
    (targetBound : target < phaseCount)
    (targetNotActive : target ∉ [source, guessPhase, firstPhase, secondPhase,
      thirdPhase, fourthPhase, fifthPhase, markerTwoPhase])
    (membership : InPhaseAt prime target digit state)
    (letterMem : letter ∈ alphabet source target guessPhase firstPhase
      secondPhase thirdPhase fourthPhase fifthPhase markerTwoPhase)
    (outputLocal : LocalAt prime (letter.act prime state)) : False := by
  have forced := membership.physicalLetter_source_digit_unique primeProperty
    primeBound targetBound (letter_source_bound layout letterMem)
    (letter_reserved letterMem)
    (by simpa [PhysicalTemplate.act, PhysicalTemplate.matrix] using outputLocal)
  have notActive := targetNotActive
  simp only [List.mem_cons, not_or] at notActive
  rcases notActive with ⟨targetNeSource, targetNeGuess, targetNeFirst,
    targetNeSecond, targetNeThird, targetNeFourth, targetNeFifth,
    targetNeMarkerTwo, _⟩
  simp [alphabet, prefixAlphabet] at letterMem
  rcases letterMem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp only [startContinue, startExit, privateLoop, privateExit,
      identityZero, identityMarker, inverseTMarker, negatingTMarker] at forced <;>
    first
    | exact targetNeSource forced.1
    | exact targetNeGuess forced.1
    | exact targetNeFirst forced.1
    | exact targetNeSecond forced.1
    | exact targetNeThird forced.1
    | exact targetNeFourth forced.1
    | exact targetNeFifth forced.1
    | exact targetNeMarkerTwo forced.1

/-- Consequently every local word over the core alphabet that starts at the
handoff is empty. -/
theorem core_word_from_target_eq_nil
    {prime phaseCount source target guessPhase firstPhase secondPhase
      thirdPhase fourthPhase fifthPhase markerTwoPhase : Nat}
    {digit : Int} {state : Vec2}
    (primeProperty : IsPrime prime) (primeBound : 6 * phaseCount < prime)
    (layout : PhaseLayout phaseCount source guessPhase firstPhase secondPhase
      thirdPhase fourthPhase fifthPhase markerTwoPhase)
    (targetBound : target < phaseCount)
    (targetNotActive : target ∉ [source, guessPhase, firstPhase, secondPhase,
      thirdPhase, fourthPhase, fifthPhase, markerTwoPhase])
    (membership : InPhaseAt prime target digit state)
    {word : List PhysicalTemplate}
    (wordOver : WordOver
      (alphabet source target guessPhase firstPhase secondPhase thirdPhase
        fourthPhase fifthPhase markerTwoPhase) word)
    (allLocal : AllStatesLocal prime word state) : word = [] := by
  cases word with
  | nil => rfl
  | cons letter tail =>
      exact False.elim (no_core_letter_from_target primeProperty primeBound
        layout targetBound targetNotActive membership (wordOver letter (by
          simp)) allLocal.2.start)

end Mortality.Compiler.FivefoldFrontModule
