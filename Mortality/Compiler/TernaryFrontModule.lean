import Mortality.Compiler.OddHalvingModule
import Mortality.Compiler.TernaryFrontArithmetic

/-!
# The twelve-letter ternary front end

This file realizes the table in the ternary-front lemma.  It proves the
complete accepted execution from `z_(3a+2)` to `X_(a,2a+1)` in `6a+6`
physical letters.  The converse is developed from the arithmetic split
classification in `TernaryFrontArithmetic`.
-/

namespace Mortality.Compiler.TernaryFrontModule

open Mortality.PeriodicCode
open Mortality.Compiler.UnaryArithmetic
open Mortality.Compiler.IncrementModule
open Mortality.Compiler.PrefixGuessModule
open Mortality.Compiler.OddHalvingArithmetic
open Mortality.Compiler.OddHalvingModule
open Mortality.Compiler.TernaryFrontArithmetic

def negatingValidatorMarker (source target : Nat) : PhysicalTemplate :=
  { sourcePhase := source
    targetPhase := target
    digit := 2
    preCoefficient := 0
    postSign := .negative
    postCoefficient := 0 }

def ternaryFrontAlphabet (source target guessPhase firstPhase secondPhase
    thirdPhase validatorPhase : Nat) : List PhysicalTemplate :=
  prefixAlphabet source guessPhase firstPhase ++
    [identityZero firstPhase, identityMarker firstPhase secondPhase,
      identityZero secondPhase, identityMarker secondPhase thirdPhase,
      identityZero thirdPhase, inverseTMarker thirdPhase validatorPhase,
      identityZero validatorPhase,
      negatingValidatorMarker validatorPhase target]

structure PhaseLayout (phaseCount source guessPhase firstPhase secondPhase
    thirdPhase validatorPhase : Nat) : Prop where
  core : OddHalvingModule.PhaseLayout phaseCount source guessPhase firstPhase
    secondPhase thirdPhase
  validatorBound : validatorPhase < phaseCount
  sourceValidatorDistinct : source ≠ validatorPhase
  guessValidatorDistinct : guessPhase ≠ validatorPhase
  firstValidatorDistinct : firstPhase ≠ validatorPhase
  secondValidatorDistinct : secondPhase ≠ validatorPhase
  thirdValidatorDistinct : thirdPhase ≠ validatorPhase

@[simp] theorem ternaryFrontAlphabet_length
    (source target guessPhase firstPhase secondPhase thirdPhase
      validatorPhase : Nat) :
    (ternaryFrontAlphabet source target guessPhase firstPhase secondPhase
      thirdPhase validatorPhase).length = 12 := by
  simp [ternaryFrontAlphabet]

def plainScanWord (source target zeros : Nat) : List PhysicalTemplate :=
  List.replicate zeros (identityZero source) ++
    [identityMarker source target]

def thirdScanWord (source target zeros : Nat) : List PhysicalTemplate :=
  List.replicate zeros (identityZero source) ++
    [inverseTMarker source target]

def frontValidatorWord (source target zeros : Nat) :
    List PhysicalTemplate :=
  List.replicate zeros (identityZero source) ++
    [negatingValidatorMarker source target]

def ternaryFrontWord (source target guessPhase firstPhase secondPhase
    thirdPhase validatorPhase first : Nat) : List PhysicalTemplate :=
  prefixWord source guessPhase firstPhase (2 * first + 2) ++
    plainScanWord firstPhase secondPhase first ++
    plainScanWord secondPhase thirdPhase first ++
    thirdScanWord thirdPhase validatorPhase first ++
    frontValidatorWord validatorPhase target first

@[simp] theorem plainScanWord_length (source target zeros : Nat) :
    (plainScanWord source target zeros).length = zeros + 1 := by
  simp [plainScanWord]

@[simp] theorem thirdScanWord_length (source target zeros : Nat) :
    (thirdScanWord source target zeros).length = zeros + 1 := by
  simp [thirdScanWord]

@[simp] theorem frontValidatorWord_length (source target zeros : Nat) :
    (frontValidatorWord source target zeros).length = zeros + 1 := by
  simp [frontValidatorWord]

@[simp] theorem ternaryFrontWord_length
    (source target guessPhase firstPhase secondPhase thirdPhase
      validatorPhase first : Nat) :
    (ternaryFrontWord source target guessPhase firstPhase secondPhase
      thirdPhase validatorPhase first).length = 6 * first + 6 := by
  simp [ternaryFrontWord, prefixWord_length (by omega : 0 < 2 * first + 2)]
  omega

theorem secondPlainMarker_step
    (base secondPhase thirdPhase first guess : Nat)
    (baseAtLeastTwo : 2 ≤ base) (guessPositive : 0 < guess) :
    SameLine
      ((identityMarker secondPhase thirdPhase).act base
        (phaseAffine secondPhase
          (secondAutomaticState base first guess first)))
      (phaseAffine thirdPhase (secondScanOutput base first guess)) := by
  have deletedEq := secondAutomaticState_delete_marker base first guess
    baseAtLeastTwo guessPositive
  have step := marker_step (source := secondPhase) (target := thirdPhase)
    (digit := 1) (coefficient := 0) (sign := .positive)
    (value := secondAutomaticState base first guess first)
    (deleted := secondScanOutput base first guess)
    (output := secondScanOutput base first guess) (by omega)
    (secondAutomaticState_local base first guess first baseAtLeastTwo)
    (secondScanOutput_local base first guess baseAtLeastTwo) deletedEq
    (by simp)
  simpa [identityMarker, PhysicalTemplate.act, PhysicalTemplate.matrix]
    using step

theorem thirdZero_step
    (base thirdPhase first guess deleted : Nat)
    (baseAtLeastTwo : 2 ≤ base)
    (deletedBelow : deleted < thirdScanLength first guess) :
    SameLine
      ((identityZero thirdPhase).act base
        (phaseAffine thirdPhase
          (thirdAutomaticState base first guess deleted)))
      (phaseAffine thirdPhase
        (thirdAutomaticState base first guess (deleted + 1))) := by
  exact identityZero_step (by omega)
    (thirdAutomaticState_local base first guess deleted baseAtLeastTwo)
    (thirdAutomaticState_local base first guess (deleted + 1)
      baseAtLeastTwo)
    (thirdAutomaticState_delete_zero base first guess deleted baseAtLeastTwo
      deletedBelow)

theorem thirdMarker_step
    (base thirdPhase validatorPhase first guess : Nat)
    (baseAtLeastTwo : 2 ≤ base) (guessPositive : 0 < guess)
    (middleRejected : first ≠ guess - 1) :
    SameLine
      ((inverseTMarker thirdPhase validatorPhase).act base
        (phaseAffine thirdPhase
          (thirdAutomaticState base first guess
            (thirdScanLength first guess))))
      (phaseAffine validatorPhase
        (ternaryValidatorState base first guess 0)) := by
  have deletedEq := thirdAutomaticState_delete_marker base first guess
    baseAtLeastTwo guessPositive middleRejected
  have outputEq := Tinv_thirdScanOutput base first guess baseAtLeastTwo
    guessPositive middleRejected
  rw [Tinv_eq_mutationMap] at outputEq
  have step := marker_step (source := thirdPhase) (target := validatorPhase)
    (digit := 1) (coefficient := 1) (sign := .positive)
    (value := thirdAutomaticState base first guess
      (thirdScanLength first guess))
    (deleted := thirdScanOutput base first guess)
    (output := ternaryValidatorState base first guess 0) (by omega)
    (thirdAutomaticState_local base first guess
      (thirdScanLength first guess) baseAtLeastTwo)
    (thirdScanOutput_local base first guess baseAtLeastTwo) deletedEq outputEq
  simpa [inverseTMarker, PhysicalTemplate.act, PhysicalTemplate.matrix]
    using step

theorem frontValidatorZero_step
    (base validatorPhase first guess deleted : Nat)
    (baseAtLeastTwo : 2 ≤ base)
    (deletedBelow : deleted < ternaryValidatorLength first guess) :
    SameLine
      ((identityZero validatorPhase).act base
        (phaseAffine validatorPhase
          (ternaryValidatorState base first guess deleted)))
      (phaseAffine validatorPhase
        (ternaryValidatorState base first guess (deleted + 1))) := by
  exact identityZero_step (by omega)
    (ternaryValidatorState_local base first guess deleted baseAtLeastTwo)
    (ternaryValidatorState_local base first guess (deleted + 1)
      baseAtLeastTwo)
    (ternaryValidatorState_delete_zero base first guess deleted
      baseAtLeastTwo deletedBelow)

theorem frontValidatorMarker_step
    (base validatorPhase target first : Nat)
    (baseAtLeastTwo : 2 ≤ base) :
    SameLine
      ((negatingValidatorMarker validatorPhase target).act base
        (phaseAffine validatorPhase
          (ternaryValidatorState base first (2 * first + 2) first)))
      (phaseAffine target (twoFieldCode base first (2 * first + 1))) := by
  have deletedEq := accepted_ternary_validator_delete_marker base first
    baseAtLeastTwo
  have outputEq := accepted_ternary_front_output base first baseAtLeastTwo
  have twoFieldLocal := periodicCode_local_affine base
    (twoFieldDigits first (2 * first + 1)) baseAtLeastTwo (by
      simp [twoFieldDigits])
  have negativeLocal := mutationMap_local_of_local .negative 0 twoFieldLocal
  have negativeEq : mutationMap base .negative 0
        (twoFieldCode base first (2 * first + 1)) =
      -(twoFieldCode base first (2 * first + 1)) := by
    simp [mutationMap, mutationDenominator, Sign.value, Rat.div_def]
    grind
  have deletedLocal : LocalAt base
      (Vec2.affine (-(twoFieldCode base first (2 * first + 1)))) := by
    rw [← negativeEq]
    exact negativeLocal
  have outputEq' : mutationMap base .negative 0
        (-(twoFieldCode base first (2 * first + 1))) =
      twoFieldCode base first (2 * first + 1) := by
    rw [← deletedEq]
    exact outputEq
  have step := marker_step (source := validatorPhase) (target := target)
    (digit := 2) (coefficient := 0) (sign := .negative)
    (value := ternaryValidatorState base first (2 * first + 2) first)
    (deleted := -(twoFieldCode base first (2 * first + 1)))
    (output := twoFieldCode base first (2 * first + 1)) (by omega)
    (ternaryValidatorState_local base first (2 * first + 2) first
      baseAtLeastTwo) deletedLocal deletedEq outputEq'
  simpa [negatingValidatorMarker, PhysicalTemplate.act,
    PhysicalTemplate.matrix] using step

theorem secondPlainScanTail_correct
    (base secondPhase thirdPhase first guess deleted remaining : Nat)
    (baseAtLeastTwo : 2 ≤ base) (guessPositive : 0 < guess)
    (sumEq : deleted + remaining = first) :
    SameLine
      (physicalWordAction base
        (List.replicate remaining (identityZero secondPhase) ++
          [identityMarker secondPhase thirdPhase])
        (phaseAffine secondPhase
          (secondAutomaticState base first guess deleted)))
      (phaseAffine thirdPhase (secondScanOutput base first guess)) := by
  induction remaining generalizing deleted with
  | zero =>
      simpa [physicalWordAction, show deleted = first by omega] using
        secondPlainMarker_step base secondPhase thirdPhase first guess
          baseAtLeastTwo guessPositive
  | succ remaining inductionHypothesis =>
      have firstStep := secondZero_step base secondPhase first guess deleted
        baseAtLeastTwo (by omega)
      have tailRun := inductionHypothesis (deleted := deleted + 1) (by omega)
      have combined := physicalWordAction_cons_sameLine base
        (identityZero secondPhase)
        (List.replicate remaining (identityZero secondPhase) ++
          [identityMarker secondPhase thirdPhase]) firstStep tailRun
      simpa [List.replicate_succ, physicalWordAction] using combined

theorem secondPlainScanWord_correct
    (base secondPhase thirdPhase first guess : Nat)
    (baseAtLeastTwo : 2 ≤ base) (guessPositive : 0 < guess) :
    SameLine
      (physicalWordAction base
        (plainScanWord secondPhase thirdPhase first)
        (phaseAffine secondPhase
          (secondAutomaticState base first guess 0)))
      (phaseAffine thirdPhase (secondScanOutput base first guess)) := by
  simpa [plainScanWord] using
    secondPlainScanTail_correct base secondPhase thirdPhase first guess 0
      first baseAtLeastTwo guessPositive (by omega)

theorem thirdScanTail_correct
    (base thirdPhase validatorPhase first guess deleted remaining : Nat)
    (baseAtLeastTwo : 2 ≤ base) (guessPositive : 0 < guess)
    (middleRejected : first ≠ guess - 1)
    (sumEq : deleted + remaining = thirdScanLength first guess) :
    SameLine
      (physicalWordAction base
        (List.replicate remaining (identityZero thirdPhase) ++
          [inverseTMarker thirdPhase validatorPhase])
        (phaseAffine thirdPhase
          (thirdAutomaticState base first guess deleted)))
      (phaseAffine validatorPhase
        (ternaryValidatorState base first guess 0)) := by
  induction remaining generalizing deleted with
  | zero =>
      simpa [physicalWordAction,
        show deleted = thirdScanLength first guess by omega] using
        thirdMarker_step base thirdPhase validatorPhase first guess
          baseAtLeastTwo guessPositive middleRejected
  | succ remaining inductionHypothesis =>
      have firstStep := thirdZero_step base thirdPhase first guess deleted
        baseAtLeastTwo (by omega)
      have tailRun := inductionHypothesis (deleted := deleted + 1) (by omega)
      have combined := physicalWordAction_cons_sameLine base
        (identityZero thirdPhase)
        (List.replicate remaining (identityZero thirdPhase) ++
          [inverseTMarker thirdPhase validatorPhase]) firstStep tailRun
      simpa [List.replicate_succ, physicalWordAction] using combined

theorem thirdScanWord_correct
    (base thirdPhase validatorPhase first guess : Nat)
    (baseAtLeastTwo : 2 ≤ base) (guessPositive : 0 < guess)
    (middleRejected : first ≠ guess - 1) :
    SameLine
      (physicalWordAction base
        (thirdScanWord thirdPhase validatorPhase
          (thirdScanLength first guess))
        (phaseAffine thirdPhase
          (thirdAutomaticState base first guess 0)))
      (phaseAffine validatorPhase
        (ternaryValidatorState base first guess 0)) := by
  simpa [thirdScanWord] using
    thirdScanTail_correct base thirdPhase validatorPhase first guess 0
      (thirdScanLength first guess) baseAtLeastTwo guessPositive
      middleRejected (by omega)

theorem frontValidatorTail_correct
    (base validatorPhase target first deleted remaining : Nat)
    (baseAtLeastTwo : 2 ≤ base) (sumEq : deleted + remaining = first) :
    SameLine
      (physicalWordAction base
        (List.replicate remaining (identityZero validatorPhase) ++
          [negatingValidatorMarker validatorPhase target])
        (phaseAffine validatorPhase
          (ternaryValidatorState base first (2 * first + 2) deleted)))
      (phaseAffine target (twoFieldCode base first (2 * first + 1))) := by
  induction remaining generalizing deleted with
  | zero =>
      simpa [physicalWordAction, show deleted = first by omega] using
        frontValidatorMarker_step base validatorPhase target first
          baseAtLeastTwo
  | succ remaining inductionHypothesis =>
      have validatorLengthEq :
          ternaryValidatorLength first (2 * first + 2) = first := by
        unfold ternaryValidatorLength
        rw [if_pos (by omega)]
        exact Nat.min_eq_left (by omega)
      have firstStep := frontValidatorZero_step base validatorPhase first
        (2 * first + 2) deleted baseAtLeastTwo (by
          rw [validatorLengthEq]
          omega)
      have tailRun := inductionHypothesis (deleted := deleted + 1) (by omega)
      have combined := physicalWordAction_cons_sameLine base
        (identityZero validatorPhase)
        (List.replicate remaining (identityZero validatorPhase) ++
          [negatingValidatorMarker validatorPhase target]) firstStep tailRun
      simpa [List.replicate_succ, physicalWordAction] using combined

theorem frontValidatorWord_correct
    (base validatorPhase target first : Nat) (baseAtLeastTwo : 2 ≤ base) :
    SameLine
      (physicalWordAction base
        (frontValidatorWord validatorPhase target first)
        (phaseAffine validatorPhase
          (ternaryValidatorState base first (2 * first + 2) 0)))
      (phaseAffine target (twoFieldCode base first (2 * first + 1))) := by
  simpa [frontValidatorWord] using
    frontValidatorTail_correct base validatorPhase target first 0 first
      baseAtLeastTwo (by omega)

theorem ternaryFrontWord_correct
    (base source target guessPhase firstPhase secondPhase thirdPhase
      validatorPhase first : Nat) (baseAtLeastTwo : 2 ≤ base) :
    SameLine
      (physicalWordAction base
        (ternaryFrontWord source target guessPhase firstPhase secondPhase
          thirdPhase validatorPhase first)
        (phaseAffine source (unaryCode base (3 * first + 2))))
      (phaseAffine target (twoFieldCode base first (2 * first + 1))) := by
  have counterSplit : 3 * first + 2 = first + (2 * first + 2) := by omega
  have prefixRun := prefixWord_correct base source guessPhase firstPhase
    (3 * first + 2) (2 * first + 2) baseAtLeastTwo (by omega) (by omega)
  have prefixRun' : SameLine
      (physicalWordAction base
        (prefixWord source guessPhase firstPhase (2 * first + 2))
        (phaseAffine source (unaryCode base (3 * first + 2))))
      (phaseAffine firstPhase
        (firstAutomaticState base first (2 * first + 2) 0)) := by
    rw [firstAutomaticState_zero base first (2 * first + 2)
      baseAtLeastTwo]
    simpa only [counterSplit] using prefixRun
  have firstRun : SameLine
      (physicalWordAction base
        (plainScanWord firstPhase secondPhase first)
        (phaseAffine firstPhase
          (firstAutomaticState base first (2 * first + 2) 0)))
      (phaseAffine secondPhase
        (firstScanOutput base first (2 * first + 2))) := by
    simpa [plainScanWord, firstScanWord] using
      firstScanWord_correct base firstPhase secondPhase first
        (2 * first + 2) baseAtLeastTwo
  have throughFirst := physicalWordAction_append_sameLine base
    (prefixWord source guessPhase firstPhase (2 * first + 2))
    (plainScanWord firstPhase secondPhase first) prefixRun' firstRun
  have secondRun := secondPlainScanWord_correct base secondPhase thirdPhase
    first (2 * first + 2) baseAtLeastTwo (by omega)
  have secondRun' : SameLine
      (physicalWordAction base
        (plainScanWord secondPhase thirdPhase first)
        (phaseAffine secondPhase
          (firstScanOutput base first (2 * first + 2))))
      (phaseAffine thirdPhase
        (thirdAutomaticState base first (2 * first + 2) 0)) := by
    rw [thirdAutomaticState_zero]
    rw [← secondAutomaticState_zero]
    exact secondRun
  have throughSecond := physicalWordAction_append_sameLine base
    (prefixWord source guessPhase firstPhase (2 * first + 2) ++
      plainScanWord firstPhase secondPhase first)
    (plainScanWord secondPhase thirdPhase first) throughFirst secondRun'
  have thirdLengthEq : thirdScanLength first (2 * first + 2) = first := by
    exact Nat.min_eq_left (by omega)
  have thirdRunRaw := thirdScanWord_correct base thirdPhase validatorPhase
    first (2 * first + 2) baseAtLeastTwo (by omega) (by omega)
  have thirdRun : SameLine
      (physicalWordAction base
        (thirdScanWord thirdPhase validatorPhase first)
        (phaseAffine thirdPhase
          (thirdAutomaticState base first (2 * first + 2) 0)))
      (phaseAffine validatorPhase
        (ternaryValidatorState base first (2 * first + 2) 0)) := by
    simpa only [thirdLengthEq] using thirdRunRaw
  have throughThird := physicalWordAction_append_sameLine base
    (prefixWord source guessPhase firstPhase (2 * first + 2) ++
      plainScanWord firstPhase secondPhase first ++
      plainScanWord secondPhase thirdPhase first)
    (thirdScanWord thirdPhase validatorPhase first) throughSecond thirdRun
  have validatorRun := frontValidatorWord_correct base validatorPhase target
    first baseAtLeastTwo
  have complete := physicalWordAction_append_sameLine base
    (prefixWord source guessPhase firstPhase (2 * first + 2) ++
      plainScanWord firstPhase secondPhase first ++
      plainScanWord secondPhase thirdPhase first ++
      thirdScanWord thirdPhase validatorPhase first)
    (frontValidatorWord validatorPhase target first) throughThird validatorRun
  simpa [ternaryFrontWord, List.append_assoc] using complete

theorem ternaryFrontWord_wordOver
    (source target guessPhase firstPhase secondPhase thirdPhase
      validatorPhase first : Nat) :
    WordOver
      (ternaryFrontAlphabet source target guessPhase firstPhase secondPhase
        thirdPhase validatorPhase)
      (ternaryFrontWord source target guessPhase firstPhase secondPhase
        thirdPhase validatorPhase first) := by
  let alphabet := ternaryFrontAlphabet source target guessPhase firstPhase
    secondPhase thirdPhase validatorPhase
  have prefixOver : WordOver alphabet
      (prefixWord source guessPhase firstPhase (2 * first + 2)) := by
    apply (prefixWord_wordOver source guessPhase firstPhase
      (2 * first + 2)).mono
    intro letter letterMem
    simp [alphabet, ternaryFrontAlphabet, letterMem]
  have firstOver : WordOver alphabet
      (plainScanWord firstPhase secondPhase first) := by
    intro letter letterMem
    simp [plainScanWord] at letterMem
    rcases letterMem with ⟨_, rfl⟩ | rfl <;>
      simp [alphabet, ternaryFrontAlphabet]
  have secondOver : WordOver alphabet
      (plainScanWord secondPhase thirdPhase first) := by
    intro letter letterMem
    simp [plainScanWord] at letterMem
    rcases letterMem with ⟨_, rfl⟩ | rfl <;>
      simp [alphabet, ternaryFrontAlphabet]
  have thirdOver : WordOver alphabet
      (thirdScanWord thirdPhase validatorPhase first) := by
    intro letter letterMem
    simp [thirdScanWord] at letterMem
    rcases letterMem with ⟨_, rfl⟩ | rfl <;>
      simp [alphabet, ternaryFrontAlphabet]
  have validatorOver : WordOver alphabet
      (frontValidatorWord validatorPhase target first) := by
    intro letter letterMem
    simp [frontValidatorWord] at letterMem
    rcases letterMem with ⟨_, rfl⟩ | rfl <;>
      simp [alphabet, ternaryFrontAlphabet]
  unfold ternaryFrontWord
  exact wordOver_append
    (wordOver_append
      (wordOver_append (wordOver_append prefixOver firstOver) secondOver)
      thirdOver) validatorOver

/-- Complete forward obligation for the twelve-letter front end. -/
theorem ternaryFront_execution
    (base source target guessPhase firstPhase secondPhase thirdPhase
      validatorPhase first : Nat) (baseAtLeastTwo : 2 ≤ base) :
    let word := ternaryFrontWord source target guessPhase firstPhase
      secondPhase thirdPhase validatorPhase first
    WordOver
        (ternaryFrontAlphabet source target guessPhase firstPhase secondPhase
          thirdPhase validatorPhase) word ∧
      word.length = 6 * first + 6 ∧
      SameLine
        (physicalWordAction base word
          (phaseAffine source (unaryCode base (3 * first + 2))))
        (phaseAffine target (twoFieldCode base first (2 * first + 1))) ∧
      AllStatesLocal base word
        (phaseAffine source (unaryCode base (3 * first + 2))) := by
  dsimp
  have action := ternaryFrontWord_correct base source target guessPhase
    firstPhase secondPhase thirdPhase validatorPhase first baseAtLeastTwo
  have inputLocal := phaseUnaryCode_local base source (3 * first + 2)
    baseAtLeastTwo
  have outputNonzero := physicalWordAction_nonzero (prime := base) (by omega)
    (ternaryFrontWord source target guessPhase firstPhase secondPhase
      thirdPhase validatorPhase first) inputLocal.1
  have outputLocal : LocalAt base
      (phaseAffine target (twoFieldCode base first (2 * first + 1))) :=
    phaseLocal (periodicCode_local_affine base
      (twoFieldDigits first (2 * first + 1)) baseAtLeastTwo (by
        simp [twoFieldDigits]))
  have finalLocal := LocalAt.of_sameLine outputLocal outputNonzero action
  exact ⟨ternaryFrontWord_wordOver source target guessPhase firstPhase
      secondPhase thirdPhase validatorPhase first,
    ternaryFrontWord_length source target guessPhase firstPhase secondPhase
      thirdPhase validatorPhase first,
    action, allStatesLocal_of_final_local (by omega) _ inputLocal.1
      finalLocal⟩

private theorem ternaryFrontLetter_source_bound
    {phaseCount source target guessPhase firstPhase secondPhase thirdPhase
      validatorPhase : Nat} {letter : PhysicalTemplate}
    (layout : PhaseLayout phaseCount source guessPhase firstPhase secondPhase
      thirdPhase validatorPhase)
    (letterMem : letter ∈ ternaryFrontAlphabet source target guessPhase
      firstPhase secondPhase thirdPhase validatorPhase) :
    letter.sourcePhase < phaseCount := by
  simp [ternaryFrontAlphabet, prefixAlphabet] at letterMem
  rcases letterMem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl <;>
    simp [startContinue, startExit, privateLoop, privateExit, identityZero,
      identityMarker, inverseTMarker, negatingValidatorMarker,
      layout.core.sourceBound, layout.core.guessBound,
      layout.core.firstBound, layout.core.secondBound,
      layout.core.validatorBound, layout.validatorBound]

private theorem ternaryFrontLetter_reserved
    {source target guessPhase firstPhase secondPhase thirdPhase
      validatorPhase : Nat} {letter : PhysicalTemplate}
    (letterMem : letter ∈ ternaryFrontAlphabet source target guessPhase
      firstPhase secondPhase thirdPhase validatorPhase) :
    ReservedDigit letter.digit := by
  simp [ternaryFrontAlphabet, prefixAlphabet] at letterMem
  rcases letterMem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl <;>
    simp [startContinue, startExit, privateLoop, privateExit, identityZero,
      identityMarker, inverseTMarker, negatingValidatorMarker,
      ReservedDigit]

theorem third_letter_before_marker
    {prime phaseCount source target guessPhase firstPhase secondPhase
      thirdPhase validatorPhase first guess deleted : Nat}
    (primeProperty : IsPrime prime)
    (primeBound : 6 * phaseCount < prime)
    (layout : PhaseLayout phaseCount source guessPhase firstPhase secondPhase
      thirdPhase validatorPhase)
    (deletedBelow : deleted < thirdScanLength first guess)
    {letter : PhysicalTemplate}
    (letterMem : letter ∈ ternaryFrontAlphabet source target guessPhase
      firstPhase secondPhase thirdPhase validatorPhase)
    (outputLocal : LocalAt prime
      (letter.act prime
        (phaseAffine thirdPhase
          (thirdAutomaticState prime first guess deleted)))) :
    letter = identityZero thirdPhase := by
  have forced := physicalLetter_affine_integer_source_digit_unique
    (prime := prime) (phaseCount := phaseCount)
    (actualPhase := thirdPhase) (sourcePhase := letter.sourcePhase)
    (targetPhase := letter.targetPhase) (actualDigit := 0)
    (letterDigit := letter.digit)
    (preCoefficient := letter.preCoefficient)
    (postCoefficient := letter.postCoefficient)
    (postSign := letter.postSign) primeProperty primeBound
    layout.core.validatorBound
    (ternaryFrontLetter_source_bound layout letterMem)
    (by simp [ReservedDigit]) (ternaryFrontLetter_reserved letterMem)
    (halfIntegerDenominator_not_dvd prime first guess primeProperty.1)
    (by simpa using
      thirdAutomaticState_zero_residue prime first guess deleted deletedBelow)
    (thirdAutomaticState_sameLine_integer prime first guess deleted
      primeProperty.1)
    (by simpa [PhysicalTemplate.act, PhysicalTemplate.matrix, phaseAffine]
      using outputLocal)
  simp [ternaryFrontAlphabet, prefixAlphabet] at letterMem
  rcases letterMem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl
  · exact False.elim (layout.core.sourceValidatorDistinct forced.1.symm)
  · exact False.elim (layout.core.sourceValidatorDistinct forced.1.symm)
  · exact False.elim (layout.core.guessValidatorDistinct forced.1.symm)
  · exact False.elim (layout.core.guessValidatorDistinct forced.1.symm)
  · exact False.elim (layout.core.firstValidatorDistinct forced.1.symm)
  · exact False.elim (layout.core.firstValidatorDistinct forced.1.symm)
  · exact False.elim (layout.core.secondValidatorDistinct forced.1.symm)
  · exact False.elim (layout.core.secondValidatorDistinct forced.1.symm)
  · rfl
  · simp [inverseTMarker] at forced
  · exact False.elim (layout.thirdValidatorDistinct forced.1)
  · exact False.elim (layout.thirdValidatorDistinct forced.1)

/-- The third scan can take its marker-one exit exactly outside the
middle split `first = guess-1`; that equality exposes digit two and is
rejected before the final validator. -/
theorem third_letter_at_marker
    {prime phaseCount source target guessPhase firstPhase secondPhase
      thirdPhase validatorPhase first guess : Nat}
    (primeProperty : IsPrime prime)
    (primeBound : 6 * phaseCount < prime)
    (guessPositive : 0 < guess)
    (layout : PhaseLayout phaseCount source guessPhase firstPhase secondPhase
      thirdPhase validatorPhase)
    {letter : PhysicalTemplate}
    (letterMem : letter ∈ ternaryFrontAlphabet source target guessPhase
      firstPhase secondPhase thirdPhase validatorPhase)
    (outputLocal : LocalAt prime
      (letter.act prime
        (phaseAffine thirdPhase
          (thirdAutomaticState prime first guess
            (thirdScanLength first guess))))) :
    first ≠ guess - 1 ∧
      letter = inverseTMarker thirdPhase validatorPhase := by
  have forced := physicalLetter_affine_integer_source_digit_unique
    (prime := prime) (phaseCount := phaseCount)
    (actualPhase := thirdPhase) (sourcePhase := letter.sourcePhase)
    (targetPhase := letter.targetPhase)
    (actualDigit := thirdMarkerDigit first guess)
    (letterDigit := letter.digit)
    (preCoefficient := letter.preCoefficient)
    (postCoefficient := letter.postCoefficient)
    (postSign := letter.postSign) primeProperty primeBound
    layout.core.validatorBound
    (ternaryFrontLetter_source_bound layout letterMem)
    (by unfold thirdMarkerDigit ReservedDigit; split <;> omega)
    (ternaryFrontLetter_reserved letterMem)
    (halfIntegerDenominator_not_dvd prime first guess primeProperty.1)
    (thirdAutomaticState_marker_residue prime first guess guessPositive)
    (thirdAutomaticState_sameLine_integer prime first guess
      (thirdScanLength first guess) primeProperty.1)
    (by simpa [PhysicalTemplate.act, PhysicalTemplate.matrix, phaseAffine]
      using outputLocal)
  simp [ternaryFrontAlphabet, prefixAlphabet] at letterMem
  rcases letterMem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl
  · exact False.elim (layout.core.sourceValidatorDistinct forced.1.symm)
  · exact False.elim (layout.core.sourceValidatorDistinct forced.1.symm)
  · exact False.elim (layout.core.guessValidatorDistinct forced.1.symm)
  · exact False.elim (layout.core.guessValidatorDistinct forced.1.symm)
  · exact False.elim (layout.core.firstValidatorDistinct forced.1.symm)
  · exact False.elim (layout.core.firstValidatorDistinct forced.1.symm)
  · exact False.elim (layout.core.secondValidatorDistinct forced.1.symm)
  · exact False.elim (layout.core.secondValidatorDistinct forced.1.symm)
  · exfalso
    have digitEq := forced.2
    by_cases middle : first = guess - 1
    · simp [thirdMarkerDigit, middle, identityZero] at digitEq
    · simp [thirdMarkerDigit, middle, identityZero] at digitEq
  · by_cases middle : first = guess - 1
    · exfalso
      have digitEq := forced.2
      simp [thirdMarkerDigit, middle, inverseTMarker] at digitEq
    · exact ⟨middle, rfl⟩
  · exact False.elim (layout.thirdValidatorDistinct forced.1)
  · exact False.elim (layout.thirdValidatorDistinct forced.1)

theorem validator_letter_before_marker
    {prime phaseCount source target guessPhase firstPhase secondPhase
      thirdPhase validatorPhase first guess deleted : Nat}
    (primeProperty : IsPrime prime)
    (primeBound : 6 * phaseCount < prime)
    (layout : PhaseLayout phaseCount source guessPhase firstPhase secondPhase
      thirdPhase validatorPhase)
    (deletedBelow : deleted < ternaryValidatorLength first guess)
    {letter : PhysicalTemplate}
    (letterMem : letter ∈ ternaryFrontAlphabet source target guessPhase
      firstPhase secondPhase thirdPhase validatorPhase)
    (outputLocal : LocalAt prime
      (letter.act prime
        (phaseAffine validatorPhase
          (ternaryValidatorState prime first guess deleted)))) :
    letter = identityZero validatorPhase := by
  have forced := physicalLetter_affine_integer_source_digit_unique
    (prime := prime) (phaseCount := phaseCount)
    (actualPhase := validatorPhase) (sourcePhase := letter.sourcePhase)
    (targetPhase := letter.targetPhase) (actualDigit := 0)
    (letterDigit := letter.digit)
    (preCoefficient := letter.preCoefficient)
    (postCoefficient := letter.postCoefficient)
    (postSign := letter.postSign) primeProperty primeBound
    layout.validatorBound (ternaryFrontLetter_source_bound layout letterMem)
    (by simp [ReservedDigit]) (ternaryFrontLetter_reserved letterMem)
    (ternaryCandidateDenominator_not_dvd prime first guess primeProperty.1)
    (by
      have residue := ternaryValidatorState_zero_residue prime first guess
        deleted deletedBelow
      simpa using residue)
    (ternaryValidatorState_sameLine_integer prime first guess deleted
      primeProperty.1)
    (by simpa [PhysicalTemplate.act, PhysicalTemplate.matrix, phaseAffine]
      using outputLocal)
  simp [ternaryFrontAlphabet, prefixAlphabet] at letterMem
  rcases letterMem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl
  · exact False.elim (layout.sourceValidatorDistinct forced.1.symm)
  · exact False.elim (layout.sourceValidatorDistinct forced.1.symm)
  · exact False.elim (layout.guessValidatorDistinct forced.1.symm)
  · exact False.elim (layout.guessValidatorDistinct forced.1.symm)
  · exact False.elim (layout.firstValidatorDistinct forced.1.symm)
  · exact False.elim (layout.firstValidatorDistinct forced.1.symm)
  · exact False.elim (layout.secondValidatorDistinct forced.1.symm)
  · exact False.elim (layout.secondValidatorDistinct forced.1.symm)
  · exact False.elim (layout.thirdValidatorDistinct forced.1.symm)
  · exact False.elim (layout.thirdValidatorDistinct forced.1.symm)
  · rfl
  · simp [negatingValidatorMarker] at forced

/-- At the final validator marker, locality forces the unique ternary
split and the digit-two negating exit. -/
theorem validator_letter_at_marker
    {prime phaseCount source target guessPhase firstPhase secondPhase
      thirdPhase validatorPhase first guess : Nat}
    (primeProperty : IsPrime prime)
    (primeBound : 6 * phaseCount < prime)
    (guessPositive : 0 < guess)
    (middleRejected : first ≠ guess - 1)
    (layout : PhaseLayout phaseCount source guessPhase firstPhase secondPhase
      thirdPhase validatorPhase)
    {letter : PhysicalTemplate}
    (letterMem : letter ∈ ternaryFrontAlphabet source target guessPhase
      firstPhase secondPhase thirdPhase validatorPhase)
    (outputLocal : LocalAt prime
      (letter.act prime
        (phaseAffine validatorPhase
          (ternaryValidatorState prime first guess
            (ternaryValidatorLength first guess))))) :
    guess = 2 * first + 2 ∧
      letter = negatingValidatorMarker validatorPhase target := by
  have forced := physicalLetter_affine_integer_source_digit_unique
    (prime := prime) (phaseCount := phaseCount)
    (actualPhase := validatorPhase) (sourcePhase := letter.sourcePhase)
    (targetPhase := letter.targetPhase)
    (actualDigit := ternaryValidatorMarkerDigit first guess)
    (letterDigit := letter.digit)
    (preCoefficient := letter.preCoefficient)
    (postCoefficient := letter.postCoefficient)
    (postSign := letter.postSign) primeProperty primeBound
    layout.validatorBound (ternaryFrontLetter_source_bound layout letterMem)
    (by unfold ternaryValidatorMarkerDigit ReservedDigit; split <;> omega)
    (ternaryFrontLetter_reserved letterMem)
    (ternaryCandidateDenominator_not_dvd prime first guess primeProperty.1)
    (ternaryValidatorState_marker_residue prime first guess guessPositive
      middleRejected)
    (ternaryValidatorState_sameLine_integer prime first guess
      (ternaryValidatorLength first guess) primeProperty.1)
    (by simpa [PhysicalTemplate.act, PhysicalTemplate.matrix, phaseAffine]
      using outputLocal)
  simp [ternaryFrontAlphabet, prefixAlphabet] at letterMem
  rcases letterMem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl
  · exact False.elim (layout.sourceValidatorDistinct forced.1.symm)
  · exact False.elim (layout.sourceValidatorDistinct forced.1.symm)
  · exact False.elim (layout.guessValidatorDistinct forced.1.symm)
  · exact False.elim (layout.guessValidatorDistinct forced.1.symm)
  · exact False.elim (layout.firstValidatorDistinct forced.1.symm)
  · exact False.elim (layout.firstValidatorDistinct forced.1.symm)
  · exact False.elim (layout.secondValidatorDistinct forced.1.symm)
  · exact False.elim (layout.secondValidatorDistinct forced.1.symm)
  · exact False.elim (layout.thirdValidatorDistinct forced.1.symm)
  · exact False.elim (layout.thirdValidatorDistinct forced.1.symm)
  · exfalso
    have digitEq := forced.2
    by_cases accepted : guess = 2 * first + 2
    · simp [ternaryValidatorMarkerDigit, accepted, identityZero] at digitEq
    · simp [ternaryValidatorMarkerDigit, accepted, identityZero] at digitEq
  · by_cases accepted : guess = 2 * first + 2
    · exact ⟨accepted, rfl⟩
    · exfalso
      have digitEq := forced.2
      simp [ternaryValidatorMarkerDigit, accepted,
        negatingValidatorMarker] at digitEq

theorem first_letter_before_marker
    {prime phaseCount source target guessPhase firstPhase secondPhase
      thirdPhase validatorPhase first guess deleted : Nat}
    (primeProperty : IsPrime prime) (primeBound : 6 * phaseCount < prime)
    (layout : PhaseLayout phaseCount source guessPhase firstPhase secondPhase
      thirdPhase validatorPhase) (deletedBelow : deleted < first)
    {letter : PhysicalTemplate}
    (letterMem : letter ∈ ternaryFrontAlphabet source target guessPhase
      firstPhase secondPhase thirdPhase validatorPhase)
    (outputLocal : LocalAt prime
      (letter.act prime (phaseAffine firstPhase
        (firstAutomaticState prime first guess deleted)))) :
    letter = identityZero firstPhase := by
  have forced := physicalLetter_affine_integer_source_digit_unique
    (prime := prime) (phaseCount := phaseCount)
    (actualPhase := firstPhase) (sourcePhase := letter.sourcePhase)
    (targetPhase := letter.targetPhase) (actualDigit := 0)
    (letterDigit := letter.digit)
    (preCoefficient := letter.preCoefficient)
    (postCoefficient := letter.postCoefficient)
    (postSign := letter.postSign) primeProperty primeBound
    layout.core.firstBound (ternaryFrontLetter_source_bound layout letterMem)
    (by simp [ReservedDigit]) (ternaryFrontLetter_reserved letterMem)
    (halfIntegerDenominator_not_dvd prime first guess primeProperty.1)
    (firstAutomaticState_zero_residue prime first guess deleted deletedBelow)
    (firstAutomaticState_sameLine_integer prime first guess deleted
      primeProperty.1)
    (by simpa [PhysicalTemplate.act, PhysicalTemplate.matrix, phaseAffine]
      using outputLocal)
  simp [ternaryFrontAlphabet, prefixAlphabet] at letterMem
  rcases letterMem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl
  · exact False.elim (layout.core.sourceFirstDistinct forced.1.symm)
  · exact False.elim (layout.core.sourceFirstDistinct forced.1.symm)
  · exact False.elim (layout.core.guessFirstDistinct forced.1.symm)
  · exact False.elim (layout.core.guessFirstDistinct forced.1.symm)
  · rfl
  · simp [identityMarker] at forced
  · exact False.elim (layout.core.firstSecondDistinct forced.1)
  · exact False.elim (layout.core.firstSecondDistinct forced.1)
  · exact False.elim (layout.core.firstValidatorDistinct forced.1)
  · exact False.elim (layout.core.firstValidatorDistinct forced.1)
  · exact False.elim (layout.firstValidatorDistinct forced.1)
  · exact False.elim (layout.firstValidatorDistinct forced.1)

theorem first_letter_at_marker
    {prime phaseCount source target guessPhase firstPhase secondPhase
      thirdPhase validatorPhase first guess : Nat}
    (primeProperty : IsPrime prime) (primeBound : 6 * phaseCount < prime)
    (layout : PhaseLayout phaseCount source guessPhase firstPhase secondPhase
      thirdPhase validatorPhase) {letter : PhysicalTemplate}
    (letterMem : letter ∈ ternaryFrontAlphabet source target guessPhase
      firstPhase secondPhase thirdPhase validatorPhase)
    (outputLocal : LocalAt prime
      (letter.act prime (phaseAffine firstPhase
        (firstAutomaticState prime first guess first)))) :
    letter = identityMarker firstPhase secondPhase := by
  have forced := physicalLetter_affine_integer_source_digit_unique
    (prime := prime) (phaseCount := phaseCount)
    (actualPhase := firstPhase) (sourcePhase := letter.sourcePhase)
    (targetPhase := letter.targetPhase) (actualDigit := 1)
    (letterDigit := letter.digit)
    (preCoefficient := letter.preCoefficient)
    (postCoefficient := letter.postCoefficient)
    (postSign := letter.postSign) primeProperty primeBound
    layout.core.firstBound (ternaryFrontLetter_source_bound layout letterMem)
    (by simp [ReservedDigit]) (ternaryFrontLetter_reserved letterMem)
    (halfIntegerDenominator_not_dvd prime first guess primeProperty.1)
    (firstAutomaticState_marker_residue prime first guess)
    (firstAutomaticState_sameLine_integer prime first guess first
      primeProperty.1)
    (by simpa [PhysicalTemplate.act, PhysicalTemplate.matrix, phaseAffine]
      using outputLocal)
  simp [ternaryFrontAlphabet, prefixAlphabet] at letterMem
  rcases letterMem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl
  · exact False.elim (layout.core.sourceFirstDistinct forced.1.symm)
  · exact False.elim (layout.core.sourceFirstDistinct forced.1.symm)
  · exact False.elim (layout.core.guessFirstDistinct forced.1.symm)
  · exact False.elim (layout.core.guessFirstDistinct forced.1.symm)
  · simp [identityZero] at forced
  · rfl
  · exact False.elim (layout.core.firstSecondDistinct forced.1)
  · exact False.elim (layout.core.firstSecondDistinct forced.1)
  · exact False.elim (layout.core.firstValidatorDistinct forced.1)
  · exact False.elim (layout.core.firstValidatorDistinct forced.1)
  · exact False.elim (layout.firstValidatorDistinct forced.1)
  · exact False.elim (layout.firstValidatorDistinct forced.1)

theorem second_letter_before_marker
    {prime phaseCount source target guessPhase firstPhase secondPhase
      thirdPhase validatorPhase first guess deleted : Nat}
    (primeProperty : IsPrime prime) (primeBound : 6 * phaseCount < prime)
    (layout : PhaseLayout phaseCount source guessPhase firstPhase secondPhase
      thirdPhase validatorPhase) (deletedBelow : deleted < first)
    {letter : PhysicalTemplate}
    (letterMem : letter ∈ ternaryFrontAlphabet source target guessPhase
      firstPhase secondPhase thirdPhase validatorPhase)
    (outputLocal : LocalAt prime
      (letter.act prime (phaseAffine secondPhase
        (secondAutomaticState prime first guess deleted)))) :
    letter = identityZero secondPhase := by
  have forced := physicalLetter_affine_integer_source_digit_unique
    (prime := prime) (phaseCount := phaseCount)
    (actualPhase := secondPhase) (sourcePhase := letter.sourcePhase)
    (targetPhase := letter.targetPhase) (actualDigit := 0)
    (letterDigit := letter.digit)
    (preCoefficient := letter.preCoefficient)
    (postCoefficient := letter.postCoefficient)
    (postSign := letter.postSign) primeProperty primeBound
    layout.core.secondBound (ternaryFrontLetter_source_bound layout letterMem)
    (by simp [ReservedDigit]) (ternaryFrontLetter_reserved letterMem)
    (halfIntegerDenominator_not_dvd prime first guess primeProperty.1)
    (secondAutomaticState_zero_residue prime first guess deleted deletedBelow)
    (secondAutomaticState_sameLine_integer prime first guess deleted
      primeProperty.1)
    (by simpa [PhysicalTemplate.act, PhysicalTemplate.matrix, phaseAffine]
      using outputLocal)
  simp [ternaryFrontAlphabet, prefixAlphabet] at letterMem
  rcases letterMem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl
  · exact False.elim (layout.core.sourceSecondDistinct forced.1.symm)
  · exact False.elim (layout.core.sourceSecondDistinct forced.1.symm)
  · exact False.elim (layout.core.guessSecondDistinct forced.1.symm)
  · exact False.elim (layout.core.guessSecondDistinct forced.1.symm)
  · exact False.elim (layout.core.firstSecondDistinct forced.1.symm)
  · exact False.elim (layout.core.firstSecondDistinct forced.1.symm)
  · rfl
  · simp [identityMarker] at forced
  · exact False.elim (layout.core.secondValidatorDistinct forced.1)
  · exact False.elim (layout.core.secondValidatorDistinct forced.1)
  · exact False.elim (layout.secondValidatorDistinct forced.1)
  · exact False.elim (layout.secondValidatorDistinct forced.1)

theorem second_letter_at_marker
    {prime phaseCount source target guessPhase firstPhase secondPhase
      thirdPhase validatorPhase first guess : Nat}
    (primeProperty : IsPrime prime) (primeBound : 6 * phaseCount < prime)
    (guessPositive : 0 < guess)
    (layout : PhaseLayout phaseCount source guessPhase firstPhase secondPhase
      thirdPhase validatorPhase) {letter : PhysicalTemplate}
    (letterMem : letter ∈ ternaryFrontAlphabet source target guessPhase
      firstPhase secondPhase thirdPhase validatorPhase)
    (outputLocal : LocalAt prime
      (letter.act prime (phaseAffine secondPhase
        (secondAutomaticState prime first guess first)))) :
    letter = identityMarker secondPhase thirdPhase := by
  have forced := physicalLetter_affine_integer_source_digit_unique
    (prime := prime) (phaseCount := phaseCount)
    (actualPhase := secondPhase) (sourcePhase := letter.sourcePhase)
    (targetPhase := letter.targetPhase) (actualDigit := 1)
    (letterDigit := letter.digit)
    (preCoefficient := letter.preCoefficient)
    (postCoefficient := letter.postCoefficient)
    (postSign := letter.postSign) primeProperty primeBound
    layout.core.secondBound (ternaryFrontLetter_source_bound layout letterMem)
    (by simp [ReservedDigit]) (ternaryFrontLetter_reserved letterMem)
    (halfIntegerDenominator_not_dvd prime first guess primeProperty.1)
    (secondAutomaticState_marker_residue prime first guess guessPositive)
    (secondAutomaticState_sameLine_integer prime first guess first
      primeProperty.1)
    (by simpa [PhysicalTemplate.act, PhysicalTemplate.matrix, phaseAffine]
      using outputLocal)
  simp [ternaryFrontAlphabet, prefixAlphabet] at letterMem
  rcases letterMem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl
  · exact False.elim (layout.core.sourceSecondDistinct forced.1.symm)
  · exact False.elim (layout.core.sourceSecondDistinct forced.1.symm)
  · exact False.elim (layout.core.guessSecondDistinct forced.1.symm)
  · exact False.elim (layout.core.guessSecondDistinct forced.1.symm)
  · exact False.elim (layout.core.firstSecondDistinct forced.1.symm)
  · exact False.elim (layout.core.firstSecondDistinct forced.1.symm)
  · simp [identityZero] at forced
  · rfl
  · exact False.elim (layout.core.secondValidatorDistinct forced.1)
  · exact False.elim (layout.core.secondValidatorDistinct forced.1)
  · exact False.elim (layout.secondValidatorDistinct forced.1)
  · exact False.elim (layout.secondValidatorDistinct forced.1)

theorem source_letter_positive
    {prime phaseCount source target guessPhase firstPhase secondPhase
      thirdPhase validatorPhase counter : Nat}
    (primeProperty : IsPrime prime) (primeBound : 6 * phaseCount < prime)
    (layout : PhaseLayout phaseCount source guessPhase firstPhase secondPhase
      thirdPhase validatorPhase) {letter : PhysicalTemplate}
    (letterMem : letter ∈ ternaryFrontAlphabet source target guessPhase
      firstPhase secondPhase thirdPhase validatorPhase)
    (outputLocal : LocalAt prime
      (letter.act prime
        (phaseAffine source (unaryCode prime (counter + 1))))) :
    letter = startContinue source guessPhase ∨
      letter = startExit source firstPhase := by
  have digitsEq : unaryDigits (counter + 1) = 0 :: unaryDigits counter := by
    simp [unaryDigits, List.replicate_succ]
  have forced := physicalLetter_periodic_affine_source_digit_unique
    (prime := prime) (phaseCount := phaseCount)
    (actualPhase := source) (sourcePhase := letter.sourcePhase)
    (targetPhase := letter.targetPhase) (actualDigit := 0)
    (letterDigit := letter.digit)
    (preCoefficient := letter.preCoefficient)
    (postCoefficient := letter.postCoefficient)
    (postSign := letter.postSign) (unaryDigits counter) primeProperty
    primeBound layout.core.sourceBound
    (ternaryFrontLetter_source_bound layout letterMem)
    (by simp [ReservedDigit]) (ternaryFrontLetter_reserved letterMem)
    (by simpa [PhysicalTemplate.act, PhysicalTemplate.matrix, phaseAffine,
      unaryCode, digitsEq] using outputLocal)
  simp [ternaryFrontAlphabet, prefixAlphabet] at letterMem
  rcases letterMem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl
  · exact Or.inl rfl
  · exact Or.inr rfl
  · exact False.elim (layout.core.sourceGuessDistinct forced.1)
  · exact False.elim (layout.core.sourceGuessDistinct forced.1)
  · exact False.elim (layout.core.sourceFirstDistinct forced.1)
  · exact False.elim (layout.core.sourceFirstDistinct forced.1)
  · exact False.elim (layout.core.sourceSecondDistinct forced.1)
  · exact False.elim (layout.core.sourceSecondDistinct forced.1)
  · exact False.elim (layout.core.sourceValidatorDistinct forced.1)
  · exact False.elim (layout.core.sourceValidatorDistinct forced.1)
  · exact False.elim (layout.sourceValidatorDistinct forced.1)
  · exact False.elim (layout.sourceValidatorDistinct forced.1)

theorem source_rejects_zero
    {prime phaseCount source target guessPhase firstPhase secondPhase
      thirdPhase validatorPhase : Nat}
    (primeProperty : IsPrime prime) (primeBound : 6 * phaseCount < prime)
    (layout : PhaseLayout phaseCount source guessPhase firstPhase secondPhase
      thirdPhase validatorPhase) {letter : PhysicalTemplate}
    (letterMem : letter ∈ ternaryFrontAlphabet source target guessPhase
      firstPhase secondPhase thirdPhase validatorPhase) :
    ¬LocalAt prime
      (letter.act prime (phaseAffine source (unaryCode prime 0))) := by
  intro outputLocal
  have forced := physicalLetter_periodic_affine_source_digit_unique
    (prime := prime) (phaseCount := phaseCount)
    (actualPhase := source) (sourcePhase := letter.sourcePhase)
    (targetPhase := letter.targetPhase) (actualDigit := 1)
    (letterDigit := letter.digit)
    (preCoefficient := letter.preCoefficient)
    (postCoefficient := letter.postCoefficient)
    (postSign := letter.postSign) [] primeProperty primeBound
    layout.core.sourceBound (ternaryFrontLetter_source_bound layout letterMem)
    (by simp [ReservedDigit]) (ternaryFrontLetter_reserved letterMem)
    (by simpa [PhysicalTemplate.act, PhysicalTemplate.matrix, phaseAffine,
      unaryCode, unaryDigits] using outputLocal)
  simp [ternaryFrontAlphabet, prefixAlphabet] at letterMem
  rcases letterMem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl
  · simp [startContinue] at forced
  · simp [startExit] at forced
  · exact layout.core.sourceGuessDistinct forced.1
  · exact layout.core.sourceGuessDistinct forced.1
  · exact layout.core.sourceFirstDistinct forced.1
  · exact layout.core.sourceFirstDistinct forced.1
  · exact layout.core.sourceSecondDistinct forced.1
  · exact layout.core.sourceSecondDistinct forced.1
  · exact layout.core.sourceValidatorDistinct forced.1
  · exact layout.core.sourceValidatorDistinct forced.1
  · exact layout.sourceValidatorDistinct forced.1
  · exact layout.sourceValidatorDistinct forced.1

theorem guess_letter_before_marker
    {prime phaseCount source target guessPhase firstPhase secondPhase
      thirdPhase validatorPhase counter deleted : Nat}
    (primeProperty : IsPrime prime) (primeBound : 6 * phaseCount < prime)
    (layout : PhaseLayout phaseCount source guessPhase firstPhase secondPhase
      thirdPhase validatorPhase) (deletedBelow : deleted < counter)
    {letter : PhysicalTemplate}
    (letterMem : letter ∈ ternaryFrontAlphabet source target guessPhase
      firstPhase secondPhase thirdPhase validatorPhase)
    (outputLocal : LocalAt prime
      (letter.act prime
        (phaseAffine guessPhase (prefixState prime counter deleted)))) :
    letter = privateLoop guessPhase ∨
      letter = privateExit guessPhase firstPhase := by
  have denominatorNotDivisible := one_sub_power_not_dvd prime (counter + 1)
    primeProperty.1 (by omega)
  have actualResidue : (prime : Int) ∣
      (prime : Int) ^ (counter - deleted) -
        0 * (1 - (prime : Int) ^ (counter + 1)) := by
    simpa using base_dvd_positive_power prime (counter - deleted) (by omega)
  have forced := physicalLetter_affine_integer_source_digit_unique
    (prime := prime) (phaseCount := phaseCount)
    (actualPhase := guessPhase) (sourcePhase := letter.sourcePhase)
    (targetPhase := letter.targetPhase) (actualDigit := 0)
    (letterDigit := letter.digit)
    (preCoefficient := letter.preCoefficient)
    (postCoefficient := letter.postCoefficient)
    (postSign := letter.postSign) primeProperty primeBound
    layout.core.guessBound (ternaryFrontLetter_source_bound layout letterMem)
    (by simp [ReservedDigit]) (ternaryFrontLetter_reserved letterMem)
    denominatorNotDivisible actualResidue
    (prefixState_sameLine_integer prime counter deleted primeProperty.1)
    (by simpa [PhysicalTemplate.act, PhysicalTemplate.matrix, phaseAffine]
      using outputLocal)
  simp [ternaryFrontAlphabet, prefixAlphabet] at letterMem
  rcases letterMem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl
  · exact False.elim (layout.core.sourceGuessDistinct forced.1.symm)
  · exact False.elim (layout.core.sourceGuessDistinct forced.1.symm)
  · exact Or.inl rfl
  · exact Or.inr rfl
  · exact False.elim (layout.core.guessFirstDistinct forced.1)
  · exact False.elim (layout.core.guessFirstDistinct forced.1)
  · exact False.elim (layout.core.guessSecondDistinct forced.1)
  · exact False.elim (layout.core.guessSecondDistinct forced.1)
  · exact False.elim (layout.core.guessValidatorDistinct forced.1)
  · exact False.elim (layout.core.guessValidatorDistinct forced.1)
  · exact False.elim (layout.guessValidatorDistinct forced.1)
  · exact False.elim (layout.guessValidatorDistinct forced.1)

theorem guess_rejects_marker
    {prime phaseCount source target guessPhase firstPhase secondPhase
      thirdPhase validatorPhase counter : Nat}
    (primeProperty : IsPrime prime) (primeBound : 6 * phaseCount < prime)
    (layout : PhaseLayout phaseCount source guessPhase firstPhase secondPhase
      thirdPhase validatorPhase) {letter : PhysicalTemplate}
    (letterMem : letter ∈ ternaryFrontAlphabet source target guessPhase
      firstPhase secondPhase thirdPhase validatorPhase) :
    ¬LocalAt prime
      (letter.act prime
        (phaseAffine guessPhase (prefixState prime counter counter))) := by
  intro outputLocal
  have denominatorNotDivisible := one_sub_power_not_dvd prime (counter + 1)
    primeProperty.1 (by omega)
  have actualResidue : (prime : Int) ∣
      (prime : Int) ^ (counter - counter) -
        1 * (1 - (prime : Int) ^ (counter + 1)) := by
    simp only [Nat.sub_self, Int.pow_zero, Int.one_mul]
    have powerDivisible := base_dvd_positive_power prime (counter + 1)
      (by omega)
    rw [show (1 : Int) - (1 - (prime : Int) ^ (counter + 1)) =
      (prime : Int) ^ (counter + 1) by grind]
    exact powerDivisible
  have forced := physicalLetter_affine_integer_source_digit_unique
    (prime := prime) (phaseCount := phaseCount)
    (actualPhase := guessPhase) (sourcePhase := letter.sourcePhase)
    (targetPhase := letter.targetPhase) (actualDigit := 1)
    (letterDigit := letter.digit)
    (preCoefficient := letter.preCoefficient)
    (postCoefficient := letter.postCoefficient)
    (postSign := letter.postSign) primeProperty primeBound
    layout.core.guessBound (ternaryFrontLetter_source_bound layout letterMem)
    (by simp [ReservedDigit]) (ternaryFrontLetter_reserved letterMem)
    denominatorNotDivisible actualResidue
    (prefixState_sameLine_integer prime counter counter primeProperty.1)
    (by simpa [PhysicalTemplate.act, PhysicalTemplate.matrix, phaseAffine]
      using outputLocal)
  simp [ternaryFrontAlphabet, prefixAlphabet] at letterMem
  rcases letterMem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl
  · exact layout.core.sourceGuessDistinct forced.1.symm
  · exact layout.core.sourceGuessDistinct forced.1.symm
  · simp [privateLoop] at forced
  · simp [privateExit] at forced
  · exact layout.core.guessFirstDistinct forced.1
  · exact layout.core.guessFirstDistinct forced.1
  · exact layout.core.guessSecondDistinct forced.1
  · exact layout.core.guessSecondDistinct forced.1
  · exact layout.core.guessValidatorDistinct forced.1
  · exact layout.core.guessValidatorDistinct forced.1
  · exact layout.guessValidatorDistinct forced.1
  · exact layout.guessValidatorDistinct forced.1

/-! ## Boundary-aware converse

The front end has a variable running time on rejected guesses.  Its
converse must therefore use the phase of a completed path, rather than
an externally prescribed clock length.  The following lemmas parse a
surviving path from left to right while carrying its fixed endpoint.
-/

private theorem word_nonempty_of_endpoint_phase_ne
    {prime phaseCount currentPhase endpointPhase : Nat}
    {currentDigit endpointDigit : Int} {current endpoint : Vec2}
    (primeProperty : IsPrime prime)
    (primeBound : 6 * phaseCount < prime)
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

theorem firstState_inPhaseAt_before
    {prime firstPhase first guess deleted : Nat}
    (primeProperty : IsPrime prime) (deletedBelow : deleted < first) :
    InPhaseAt prime firstPhase 0
      (phaseAffine firstPhase
        (firstAutomaticState prime first guess deleted)) := by
  apply inPhaseAt_phaseAffine_integer (by simp [ReservedDigit])
    (halfIntegerDenominator_not_dvd prime first guess primeProperty.1)
    (firstAutomaticState_zero_residue prime first guess deleted deletedBelow)
  exact firstAutomaticState_sameLine_integer prime first guess deleted
    primeProperty.1

theorem firstState_inPhaseAt_marker
    {prime firstPhase first guess : Nat}
    (primeProperty : IsPrime prime) :
    InPhaseAt prime firstPhase 1
      (phaseAffine firstPhase
        (firstAutomaticState prime first guess first)) := by
  apply inPhaseAt_phaseAffine_integer (by simp [ReservedDigit])
    (halfIntegerDenominator_not_dvd prime first guess primeProperty.1)
    (firstAutomaticState_marker_residue prime first guess)
  exact firstAutomaticState_sameLine_integer prime first guess first
    primeProperty.1

/-- A completed path cannot stop inside the first automatic scan.  Its
unique prefix through that scan is the expected zero block and marker.
-/
theorem firstScanTail_forced_prefix_to_endpoint
    {prime phaseCount source target guessPhase firstPhase secondPhase
      thirdPhase validatorPhase endpointPhase : Nat}
    {endpointDigit : Int} {endpoint : Vec2}
    (primeProperty : IsPrime prime)
    (primeBound : 6 * phaseCount < prime)
    (layout : PhaseLayout phaseCount source guessPhase firstPhase secondPhase
      thirdPhase validatorPhase)
    (endpointBound : endpointPhase < phaseCount)
    (firstEndpointDistinct : firstPhase ≠ endpointPhase)
    (endpointMembership : InPhaseAt prime endpointPhase endpointDigit endpoint)
    {first guess deleted remaining : Nat}
    (sumEq : deleted + remaining = first)
    {word : List PhysicalTemplate}
    (wordOver : WordOver
      (ternaryFrontAlphabet source target guessPhase firstPhase secondPhase
        thirdPhase validatorPhase) word)
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
        (ternaryFrontAlphabet source target guessPhase firstPhase secondPhase
          thirdPhase validatorPhase) suffix ∧
      AllStatesLocal prime suffix
        (phaseAffine secondPhase
          (secondAutomaticState prime first guess 0)) ∧
      SameLine
        (physicalWordAction prime suffix
          (phaseAffine secondPhase
            (secondAutomaticState prime first guess 0))) endpoint := by
  induction remaining generalizing deleted word with
  | zero =>
      have deletedEq : deleted = first := by omega
      have currentMembership := firstState_inPhaseAt_marker
        (firstPhase := firstPhase) (first := first) (guess := guess)
        primeProperty
      have wordNonempty := word_nonempty_of_endpoint_phase_ne primeProperty
        primeBound layout.core.firstBound endpointBound firstEndpointDistinct
        currentMembership endpointMembership (word := word) (by
          simpa only [deletedEq] using completeRun)
      cases word with
      | nil => exact False.elim (wordNonempty rfl)
      | cons letter tail =>
          have letterMem := wordOver letter (by simp)
          have tailOver : WordOver
              (ternaryFrontAlphabet source target guessPhase firstPhase
                secondPhase thirdPhase validatorPhase) tail := by
            intro candidate candidateMem
            exact wordOver candidate (by simp [candidateMem])
          have letterEq := first_letter_at_marker
            (first := first) (guess := guess) primeProperty primeBound layout
            letterMem (by simpa only [deletedEq] using allLocal.2.start)
          subst letter
          have firstStep := firstMarker_step prime firstPhase secondPhase first
            guess primeProperty.1
          have canonicalLocal : LocalAt prime
              (phaseAffine secondPhase
                (secondAutomaticState prime first guess 0)) :=
            phaseLocal
              (secondAutomaticState_local prime first guess 0
                primeProperty.1)
          have tailLocal : AllStatesLocal prime tail
              (phaseAffine secondPhase
                (secondAutomaticState prime first guess 0)) := by
            apply AllStatesLocal.of_sameLine
              (primePositive := by have := primeProperty.1; omega)
              allLocal.2 canonicalLocal.1
            rw [secondAutomaticState_zero]
            simpa only [deletedEq] using firstStep.symm
          have tailRun : SameLine
              (physicalWordAction prime tail
                (phaseAffine secondPhase
                  (secondAutomaticState prime first guess 0))) endpoint := by
            apply physicalWordAction_tail_sameLine prime
              (identityMarker firstPhase secondPhase) tail
                (completeRun := by simpa only [deletedEq] using completeRun)
            rw [secondAutomaticState_zero]
            simpa only [deletedEq] using firstStep
          exact ⟨tail, by simp, tailOver, tailLocal, tailRun⟩
  | succ remaining inductionHypothesis =>
      have deletedBelow : deleted < first := by omega
      have currentMembership := firstState_inPhaseAt_before
        (firstPhase := firstPhase) (first := first) (guess := guess)
        (deleted := deleted) primeProperty deletedBelow
      have wordNonempty := word_nonempty_of_endpoint_phase_ne primeProperty
        primeBound layout.core.firstBound endpointBound firstEndpointDistinct
        currentMembership endpointMembership completeRun
      cases word with
      | nil => exact False.elim (wordNonempty rfl)
      | cons letter tail =>
          have letterMem := wordOver letter (by simp)
          have tailOver : WordOver
              (ternaryFrontAlphabet source target guessPhase firstPhase
                secondPhase thirdPhase validatorPhase) tail := by
            intro candidate candidateMem
            exact wordOver candidate (by simp [candidateMem])
          have letterEq := first_letter_before_marker primeProperty primeBound
            layout deletedBelow letterMem allLocal.2.start
          subst letter
          have firstStep := firstZero_step prime firstPhase first guess deleted
            primeProperty.1 deletedBelow
          have canonicalLocal : LocalAt prime
              (phaseAffine firstPhase
                (firstAutomaticState prime first guess (deleted + 1))) :=
            phaseLocal
              (firstAutomaticState_local prime first guess (deleted + 1)
                primeProperty.1)
          have tailLocal : AllStatesLocal prime tail
              (phaseAffine firstPhase
                (firstAutomaticState prime first guess (deleted + 1))) := by
            apply AllStatesLocal.of_sameLine
              (primePositive := by have := primeProperty.1; omega)
              allLocal.2 canonicalLocal.1 firstStep.symm
          have tailRun : SameLine
              (physicalWordAction prime tail
                (phaseAffine firstPhase
                  (firstAutomaticState prime first guess (deleted + 1))))
                endpoint :=
            physicalWordAction_tail_sameLine prime
              (identityZero firstPhase) tail firstStep completeRun
          obtain ⟨suffix, tailEq, suffixOver, suffixLocal, suffixRun⟩ :=
            inductionHypothesis (deleted := deleted + 1) (by omega) tailOver
              tailLocal tailRun
          refine ⟨suffix, ?_, suffixOver, suffixLocal, suffixRun⟩
          rw [tailEq]
          simp [List.replicate_succ]

theorem secondState_inPhaseAt_before
    {prime secondPhase first guess deleted : Nat}
    (primeProperty : IsPrime prime) (deletedBelow : deleted < first) :
    InPhaseAt prime secondPhase 0
      (phaseAffine secondPhase
        (secondAutomaticState prime first guess deleted)) := by
  apply inPhaseAt_phaseAffine_integer (by simp [ReservedDigit])
    (halfIntegerDenominator_not_dvd prime first guess primeProperty.1)
    (secondAutomaticState_zero_residue prime first guess deleted deletedBelow)
  exact secondAutomaticState_sameLine_integer prime first guess deleted
    primeProperty.1

theorem secondState_inPhaseAt_marker
    {prime secondPhase first guess : Nat}
    (primeProperty : IsPrime prime) (guessPositive : 0 < guess) :
    InPhaseAt prime secondPhase 1
      (phaseAffine secondPhase
        (secondAutomaticState prime first guess first)) := by
  apply inPhaseAt_phaseAffine_integer (by simp [ReservedDigit])
    (halfIntegerDenominator_not_dvd prime first guess primeProperty.1)
    (secondAutomaticState_marker_residue prime first guess guessPositive)
  exact secondAutomaticState_sameLine_integer prime first guess first
    primeProperty.1

/-- Boundary-aware parser for the second plain scan. -/
theorem secondScanTail_forced_prefix_to_endpoint
    {prime phaseCount source target guessPhase firstPhase secondPhase
      thirdPhase validatorPhase endpointPhase : Nat}
    {endpointDigit : Int} {endpoint : Vec2}
    (primeProperty : IsPrime prime)
    (primeBound : 6 * phaseCount < prime)
    (layout : PhaseLayout phaseCount source guessPhase firstPhase secondPhase
      thirdPhase validatorPhase)
    (endpointBound : endpointPhase < phaseCount)
    (secondEndpointDistinct : secondPhase ≠ endpointPhase)
    (endpointMembership : InPhaseAt prime endpointPhase endpointDigit endpoint)
    {first guess deleted remaining : Nat}
    (guessPositive : 0 < guess)
    (sumEq : deleted + remaining = first)
    {word : List PhysicalTemplate}
    (wordOver : WordOver
      (ternaryFrontAlphabet source target guessPhase firstPhase secondPhase
        thirdPhase validatorPhase) word)
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
        (ternaryFrontAlphabet source target guessPhase firstPhase secondPhase
          thirdPhase validatorPhase) suffix ∧
      AllStatesLocal prime suffix
        (phaseAffine thirdPhase
          (thirdAutomaticState prime first guess 0)) ∧
      SameLine
        (physicalWordAction prime suffix
          (phaseAffine thirdPhase
            (thirdAutomaticState prime first guess 0))) endpoint := by
  induction remaining generalizing deleted word with
  | zero =>
      have deletedEq : deleted = first := by omega
      have currentMembership := secondState_inPhaseAt_marker
        (secondPhase := secondPhase) (first := first) (guess := guess)
        primeProperty guessPositive
      have wordNonempty := word_nonempty_of_endpoint_phase_ne primeProperty
        primeBound layout.core.secondBound endpointBound secondEndpointDistinct
        currentMembership endpointMembership (word := word) (by
          simpa only [deletedEq] using completeRun)
      cases word with
      | nil => exact False.elim (wordNonempty rfl)
      | cons letter tail =>
          have letterMem := wordOver letter (by simp)
          have tailOver : WordOver
              (ternaryFrontAlphabet source target guessPhase firstPhase
                secondPhase thirdPhase validatorPhase) tail := by
            intro candidate candidateMem
            exact wordOver candidate (by simp [candidateMem])
          have letterEq := second_letter_at_marker
            (first := first) (guess := guess) primeProperty primeBound
            guessPositive layout letterMem
            (by simpa only [deletedEq] using allLocal.2.start)
          subst letter
          have firstStep := secondPlainMarker_step prime secondPhase
            thirdPhase first guess primeProperty.1 guessPositive
          have canonicalLocal : LocalAt prime
              (phaseAffine thirdPhase
                (thirdAutomaticState prime first guess 0)) :=
            phaseLocal
              (thirdAutomaticState_local prime first guess 0
                primeProperty.1)
          have tailLocal : AllStatesLocal prime tail
              (phaseAffine thirdPhase
                (thirdAutomaticState prime first guess 0)) := by
            apply AllStatesLocal.of_sameLine
              (primePositive := by have := primeProperty.1; omega)
              allLocal.2 canonicalLocal.1
            rw [thirdAutomaticState_zero]
            simpa only [deletedEq] using firstStep.symm
          have tailRun : SameLine
              (physicalWordAction prime tail
                (phaseAffine thirdPhase
                  (thirdAutomaticState prime first guess 0))) endpoint := by
            apply physicalWordAction_tail_sameLine prime
              (identityMarker secondPhase thirdPhase) tail
                (completeRun := by simpa only [deletedEq] using completeRun)
            rw [thirdAutomaticState_zero]
            simpa only [deletedEq] using firstStep
          exact ⟨tail, by simp, tailOver, tailLocal, tailRun⟩
  | succ remaining inductionHypothesis =>
      have deletedBelow : deleted < first := by omega
      have currentMembership := secondState_inPhaseAt_before
        (secondPhase := secondPhase) (first := first) (guess := guess)
        (deleted := deleted) primeProperty deletedBelow
      have wordNonempty := word_nonempty_of_endpoint_phase_ne primeProperty
        primeBound layout.core.secondBound endpointBound secondEndpointDistinct
        currentMembership endpointMembership completeRun
      cases word with
      | nil => exact False.elim (wordNonempty rfl)
      | cons letter tail =>
          have letterMem := wordOver letter (by simp)
          have tailOver : WordOver
              (ternaryFrontAlphabet source target guessPhase firstPhase
                secondPhase thirdPhase validatorPhase) tail := by
            intro candidate candidateMem
            exact wordOver candidate (by simp [candidateMem])
          have letterEq := second_letter_before_marker primeProperty
            primeBound layout deletedBelow letterMem allLocal.2.start
          subst letter
          have firstStep := secondZero_step prime secondPhase first guess
            deleted primeProperty.1 deletedBelow
          have canonicalLocal : LocalAt prime
              (phaseAffine secondPhase
                (secondAutomaticState prime first guess (deleted + 1))) :=
            phaseLocal
              (secondAutomaticState_local prime first guess (deleted + 1)
                primeProperty.1)
          have tailLocal : AllStatesLocal prime tail
              (phaseAffine secondPhase
                (secondAutomaticState prime first guess (deleted + 1))) := by
            apply AllStatesLocal.of_sameLine
              (primePositive := by have := primeProperty.1; omega)
              allLocal.2 canonicalLocal.1 firstStep.symm
          have tailRun : SameLine
              (physicalWordAction prime tail
                (phaseAffine secondPhase
                  (secondAutomaticState prime first guess (deleted + 1))))
                endpoint :=
            physicalWordAction_tail_sameLine prime
              (identityZero secondPhase) tail firstStep completeRun
          obtain ⟨suffix, tailEq, suffixOver, suffixLocal, suffixRun⟩ :=
            inductionHypothesis (deleted := deleted + 1) (by omega) tailOver
              tailLocal tailRun
          refine ⟨suffix, ?_, suffixOver, suffixLocal, suffixRun⟩
          rw [tailEq]
          simp [List.replicate_succ]

theorem thirdState_inPhaseAt_before
    {prime thirdPhase first guess deleted : Nat}
    (primeProperty : IsPrime prime)
    (deletedBelow : deleted < thirdScanLength first guess) :
    InPhaseAt prime thirdPhase 0
      (phaseAffine thirdPhase
        (thirdAutomaticState prime first guess deleted)) := by
  apply inPhaseAt_phaseAffine_integer (by simp [ReservedDigit])
    (halfIntegerDenominator_not_dvd prime first guess primeProperty.1)
    (by simpa using
      thirdAutomaticState_zero_residue prime first guess deleted deletedBelow)
  exact thirdAutomaticState_sameLine_integer prime first guess deleted
    primeProperty.1

theorem thirdState_inPhaseAt_marker
    {prime thirdPhase first guess : Nat}
    (primeProperty : IsPrime prime) (guessPositive : 0 < guess) :
    InPhaseAt prime thirdPhase (thirdMarkerDigit first guess)
      (phaseAffine thirdPhase
        (thirdAutomaticState prime first guess
          (thirdScanLength first guess))) := by
  apply inPhaseAt_phaseAffine_integer
    (by unfold thirdMarkerDigit ReservedDigit; split <;> omega)
    (halfIntegerDenominator_not_dvd prime first guess primeProperty.1)
    (thirdAutomaticState_marker_residue prime first guess guessPositive)
  exact thirdAutomaticState_sameLine_integer prime first guess
    (thirdScanLength first guess) primeProperty.1

/-- Boundary-aware parser for the variable third scan.  Reaching its
exit also certifies rejection of the middle split. -/
theorem thirdScanTail_forced_prefix_to_endpoint
    {prime phaseCount source target guessPhase firstPhase secondPhase
      thirdPhase validatorPhase endpointPhase : Nat}
    {endpointDigit : Int} {endpoint : Vec2}
    (primeProperty : IsPrime prime)
    (primeBound : 6 * phaseCount < prime)
    (layout : PhaseLayout phaseCount source guessPhase firstPhase secondPhase
      thirdPhase validatorPhase)
    (endpointBound : endpointPhase < phaseCount)
    (thirdEndpointDistinct : thirdPhase ≠ endpointPhase)
    (endpointMembership : InPhaseAt prime endpointPhase endpointDigit endpoint)
    {first guess deleted remaining : Nat}
    (guessPositive : 0 < guess)
    (sumEq : deleted + remaining = thirdScanLength first guess)
    {word : List PhysicalTemplate}
    (wordOver : WordOver
      (ternaryFrontAlphabet source target guessPhase firstPhase secondPhase
        thirdPhase validatorPhase) word)
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
          [inverseTMarker thirdPhase validatorPhase] ++ suffix ∧
      WordOver
        (ternaryFrontAlphabet source target guessPhase firstPhase secondPhase
          thirdPhase validatorPhase) suffix ∧
      AllStatesLocal prime suffix
        (phaseAffine validatorPhase
          (ternaryValidatorState prime first guess 0)) ∧
      SameLine
        (physicalWordAction prime suffix
          (phaseAffine validatorPhase
            (ternaryValidatorState prime first guess 0))) endpoint := by
  induction remaining generalizing deleted word with
  | zero =>
      have deletedEq : deleted = thirdScanLength first guess := by omega
      have currentMembership := thirdState_inPhaseAt_marker
        (thirdPhase := thirdPhase) (first := first) (guess := guess)
        primeProperty guessPositive
      have wordNonempty := word_nonempty_of_endpoint_phase_ne primeProperty
        primeBound layout.core.validatorBound endpointBound
        thirdEndpointDistinct currentMembership endpointMembership
        (word := word) (by simpa only [deletedEq] using completeRun)
      cases word with
      | nil => exact False.elim (wordNonempty rfl)
      | cons letter tail =>
          have letterMem := wordOver letter (by simp)
          have tailOver : WordOver
              (ternaryFrontAlphabet source target guessPhase firstPhase
                secondPhase thirdPhase validatorPhase) tail := by
            intro candidate candidateMem
            exact wordOver candidate (by simp [candidateMem])
          obtain ⟨middleRejected, letterEq⟩ := third_letter_at_marker
            (first := first) (guess := guess) primeProperty primeBound
            guessPositive layout letterMem
            (by simpa only [deletedEq] using allLocal.2.start)
          subst letter
          have firstStep := thirdMarker_step prime thirdPhase validatorPhase
            first guess primeProperty.1 guessPositive middleRejected
          have canonicalLocal : LocalAt prime
              (phaseAffine validatorPhase
                (ternaryValidatorState prime first guess 0)) :=
            phaseLocal
              (ternaryValidatorState_local prime first guess 0
                primeProperty.1)
          have tailLocal : AllStatesLocal prime tail
              (phaseAffine validatorPhase
                (ternaryValidatorState prime first guess 0)) := by
            apply AllStatesLocal.of_sameLine
              (primePositive := by have := primeProperty.1; omega)
              allLocal.2 canonicalLocal.1
            simpa only [deletedEq] using firstStep.symm
          have tailRun : SameLine
              (physicalWordAction prime tail
                (phaseAffine validatorPhase
                  (ternaryValidatorState prime first guess 0))) endpoint := by
            apply physicalWordAction_tail_sameLine prime
              (inverseTMarker thirdPhase validatorPhase) tail
                (completeRun := by simpa only [deletedEq] using completeRun)
            simpa only [deletedEq] using firstStep
          exact ⟨tail, middleRejected, by simp, tailOver, tailLocal,
            tailRun⟩
  | succ remaining inductionHypothesis =>
      have deletedBelow : deleted < thirdScanLength first guess := by omega
      have currentMembership := thirdState_inPhaseAt_before
        (thirdPhase := thirdPhase) (first := first) (guess := guess)
        (deleted := deleted) primeProperty deletedBelow
      have wordNonempty := word_nonempty_of_endpoint_phase_ne primeProperty
        primeBound layout.core.validatorBound endpointBound
        thirdEndpointDistinct currentMembership endpointMembership completeRun
      cases word with
      | nil => exact False.elim (wordNonempty rfl)
      | cons letter tail =>
          have letterMem := wordOver letter (by simp)
          have tailOver : WordOver
              (ternaryFrontAlphabet source target guessPhase firstPhase
                secondPhase thirdPhase validatorPhase) tail := by
            intro candidate candidateMem
            exact wordOver candidate (by simp [candidateMem])
          have letterEq := third_letter_before_marker primeProperty
            primeBound layout deletedBelow letterMem allLocal.2.start
          subst letter
          have firstStep := thirdZero_step prime thirdPhase first guess deleted
            primeProperty.1 deletedBelow
          have canonicalLocal : LocalAt prime
              (phaseAffine thirdPhase
                (thirdAutomaticState prime first guess (deleted + 1))) :=
            phaseLocal
              (thirdAutomaticState_local prime first guess (deleted + 1)
                primeProperty.1)
          have tailLocal : AllStatesLocal prime tail
              (phaseAffine thirdPhase
                (thirdAutomaticState prime first guess (deleted + 1))) := by
            apply AllStatesLocal.of_sameLine
              (primePositive := by have := primeProperty.1; omega)
              allLocal.2 canonicalLocal.1 firstStep.symm
          have tailRun : SameLine
              (physicalWordAction prime tail
                (phaseAffine thirdPhase
                  (thirdAutomaticState prime first guess (deleted + 1))))
                endpoint :=
            physicalWordAction_tail_sameLine prime
              (identityZero thirdPhase) tail firstStep completeRun
          obtain ⟨suffix, middleRejected, tailEq, suffixOver, suffixLocal,
              suffixRun⟩ :=
            inductionHypothesis (deleted := deleted + 1) (by omega) tailOver
              tailLocal tailRun
          refine ⟨suffix, middleRejected, ?_, suffixOver, suffixLocal,
            suffixRun⟩
          rw [tailEq]
          simp [List.replicate_succ]

theorem validatorState_inPhaseAt_before
    {prime validatorPhase first guess deleted : Nat}
    (primeProperty : IsPrime prime)
    (deletedBelow : deleted < ternaryValidatorLength first guess) :
    InPhaseAt prime validatorPhase 0
      (phaseAffine validatorPhase
        (ternaryValidatorState prime first guess deleted)) := by
  apply inPhaseAt_phaseAffine_integer (by simp [ReservedDigit])
    (ternaryCandidateDenominator_not_dvd prime first guess primeProperty.1)
    (by
      simpa only [Int.zero_mul, Int.sub_zero] using
        (ternaryValidatorState_zero_residue prime first guess deleted
          deletedBelow))
  exact ternaryValidatorState_sameLine_integer prime first guess deleted
    primeProperty.1

theorem validatorState_inPhaseAt_marker
    {prime validatorPhase first guess : Nat}
    (primeProperty : IsPrime prime) (guessPositive : 0 < guess)
    (middleRejected : first ≠ guess - 1) :
    InPhaseAt prime validatorPhase
      (ternaryValidatorMarkerDigit first guess)
      (phaseAffine validatorPhase
        (ternaryValidatorState prime first guess
          (ternaryValidatorLength first guess))) := by
  apply inPhaseAt_phaseAffine_integer
    (by unfold ternaryValidatorMarkerDigit ReservedDigit; split <;> omega)
    (ternaryCandidateDenominator_not_dvd prime first guess primeProperty.1)
    (ternaryValidatorState_marker_residue prime first guess guessPositive
      middleRejected)
  exact ternaryValidatorState_sameLine_integer prime first guess
    (ternaryValidatorLength first guess) primeProperty.1

/-- Boundary-aware parser for the final validator.  Any completed path
through this phase certifies the unique accepted ternary split. -/
theorem validatorTail_forced_prefix_to_endpoint
    {prime phaseCount source target guessPhase firstPhase secondPhase
      thirdPhase validatorPhase endpointPhase : Nat}
    {endpointDigit : Int} {endpoint : Vec2}
    (primeProperty : IsPrime prime)
    (primeBound : 6 * phaseCount < prime)
    (layout : PhaseLayout phaseCount source guessPhase firstPhase secondPhase
      thirdPhase validatorPhase)
    (endpointBound : endpointPhase < phaseCount)
    (validatorEndpointDistinct : validatorPhase ≠ endpointPhase)
    (endpointMembership : InPhaseAt prime endpointPhase endpointDigit endpoint)
    {first guess deleted remaining : Nat}
    (guessPositive : 0 < guess)
    (middleRejected : first ≠ guess - 1)
    (sumEq : deleted + remaining = ternaryValidatorLength first guess)
    {word : List PhysicalTemplate}
    (wordOver : WordOver
      (ternaryFrontAlphabet source target guessPhase firstPhase secondPhase
        thirdPhase validatorPhase) word)
    (allLocal : AllStatesLocal prime word
      (phaseAffine validatorPhase
        (ternaryValidatorState prime first guess deleted)))
    (completeRun : SameLine
      (physicalWordAction prime word
        (phaseAffine validatorPhase
          (ternaryValidatorState prime first guess deleted))) endpoint) :
    ∃ suffix,
      guess = 2 * first + 2 ∧
      word = List.replicate remaining (identityZero validatorPhase) ++
          [negatingValidatorMarker validatorPhase target] ++ suffix ∧
      WordOver
        (ternaryFrontAlphabet source target guessPhase firstPhase secondPhase
          thirdPhase validatorPhase) suffix ∧
      AllStatesLocal prime suffix
        (phaseAffine target (twoFieldCode prime first (2 * first + 1))) ∧
      SameLine
        (physicalWordAction prime suffix
          (phaseAffine target
            (twoFieldCode prime first (2 * first + 1)))) endpoint := by
  induction remaining generalizing deleted word with
  | zero =>
      have deletedEq : deleted = ternaryValidatorLength first guess := by
        omega
      have currentMembership := validatorState_inPhaseAt_marker
        (validatorPhase := validatorPhase) (first := first) (guess := guess)
        primeProperty guessPositive middleRejected
      have wordNonempty := word_nonempty_of_endpoint_phase_ne primeProperty
        primeBound layout.validatorBound endpointBound
        validatorEndpointDistinct currentMembership endpointMembership
        (word := word) (by simpa only [deletedEq] using completeRun)
      cases word with
      | nil => exact False.elim (wordNonempty rfl)
      | cons letter tail =>
          have letterMem := wordOver letter (by simp)
          have tailOver : WordOver
              (ternaryFrontAlphabet source target guessPhase firstPhase
                secondPhase thirdPhase validatorPhase) tail := by
            intro candidate candidateMem
            exact wordOver candidate (by simp [candidateMem])
          obtain ⟨accepted, letterEq⟩ := validator_letter_at_marker
            (first := first) (guess := guess) primeProperty primeBound
            guessPositive middleRejected layout letterMem
            (by simpa only [deletedEq] using allLocal.2.start)
          subst guess
          subst letter
          have validatorLengthEq :
              ternaryValidatorLength first (2 * first + 2) = first := by
            unfold ternaryValidatorLength
            rw [if_pos (by omega)]
            exact Nat.min_eq_left (by omega)
          have deletedFirst : deleted = first := by omega
          have firstStep := frontValidatorMarker_step prime validatorPhase
            target first primeProperty.1
          have canonicalLocal : LocalAt prime
              (phaseAffine target
                (twoFieldCode prime first (2 * first + 1))) :=
            phaseLocal (periodicCode_local_affine prime
              (twoFieldDigits first (2 * first + 1)) primeProperty.1 (by
                simp [twoFieldDigits]))
          have tailLocal : AllStatesLocal prime tail
              (phaseAffine target
                (twoFieldCode prime first (2 * first + 1))) := by
            apply AllStatesLocal.of_sameLine
              (primePositive := by have := primeProperty.1; omega)
              allLocal.2 canonicalLocal.1
            simpa only [deletedFirst] using firstStep.symm
          have tailRun : SameLine
              (physicalWordAction prime tail
                (phaseAffine target
                  (twoFieldCode prime first (2 * first + 1)))) endpoint := by
            apply physicalWordAction_tail_sameLine prime
              (negatingValidatorMarker validatorPhase target) tail
                (completeRun := by simpa only [deletedFirst] using
                  completeRun)
            simpa only [deletedFirst] using firstStep
          exact ⟨tail, rfl, by simp, tailOver, tailLocal, tailRun⟩
  | succ remaining inductionHypothesis =>
      have deletedBelow : deleted < ternaryValidatorLength first guess := by
        omega
      have currentMembership := validatorState_inPhaseAt_before
        (validatorPhase := validatorPhase) (first := first) (guess := guess)
        (deleted := deleted) primeProperty deletedBelow
      have wordNonempty := word_nonempty_of_endpoint_phase_ne primeProperty
        primeBound layout.validatorBound endpointBound
        validatorEndpointDistinct currentMembership endpointMembership
        completeRun
      cases word with
      | nil => exact False.elim (wordNonempty rfl)
      | cons letter tail =>
          have letterMem := wordOver letter (by simp)
          have tailOver : WordOver
              (ternaryFrontAlphabet source target guessPhase firstPhase
                secondPhase thirdPhase validatorPhase) tail := by
            intro candidate candidateMem
            exact wordOver candidate (by simp [candidateMem])
          have letterEq := validator_letter_before_marker primeProperty
            primeBound layout deletedBelow letterMem allLocal.2.start
          subst letter
          have firstStep := frontValidatorZero_step prime validatorPhase
            first guess deleted primeProperty.1 deletedBelow
          have canonicalLocal : LocalAt prime
              (phaseAffine validatorPhase
                (ternaryValidatorState prime first guess (deleted + 1))) :=
            phaseLocal
              (ternaryValidatorState_local prime first guess (deleted + 1)
                primeProperty.1)
          have tailLocal : AllStatesLocal prime tail
              (phaseAffine validatorPhase
                (ternaryValidatorState prime first guess (deleted + 1))) := by
            apply AllStatesLocal.of_sameLine
              (primePositive := by have := primeProperty.1; omega)
              allLocal.2 canonicalLocal.1 firstStep.symm
          have tailRun : SameLine
              (physicalWordAction prime tail
                (phaseAffine validatorPhase
                  (ternaryValidatorState prime first guess (deleted + 1))))
                endpoint :=
            physicalWordAction_tail_sameLine prime
              (identityZero validatorPhase) tail firstStep completeRun
          obtain ⟨suffix, accepted, tailEq, suffixOver, suffixLocal,
              suffixRun⟩ :=
            inductionHypothesis (deleted := deleted + 1) (by omega) tailOver
              tailLocal tailRun
          refine ⟨suffix, accepted, ?_, suffixOver, suffixLocal, suffixRun⟩
          rw [tailEq]
          simp [List.replicate_succ]

/-- The entire deterministic suffix of the ternary front end is forced
on every completed path. -/
theorem automaticSuffix_forced_prefix_to_endpoint
    {prime phaseCount source target guessPhase firstPhase secondPhase
      thirdPhase validatorPhase endpointPhase : Nat}
    {endpointDigit : Int} {endpoint : Vec2}
    (primeProperty : IsPrime prime)
    (primeBound : 6 * phaseCount < prime)
    (layout : PhaseLayout phaseCount source guessPhase firstPhase secondPhase
      thirdPhase validatorPhase)
    (endpointBound : endpointPhase < phaseCount)
    (firstEndpointDistinct : firstPhase ≠ endpointPhase)
    (secondEndpointDistinct : secondPhase ≠ endpointPhase)
    (thirdEndpointDistinct : thirdPhase ≠ endpointPhase)
    (validatorEndpointDistinct : validatorPhase ≠ endpointPhase)
    (endpointMembership : InPhaseAt prime endpointPhase endpointDigit endpoint)
    {first guess : Nat} (guessPositive : 0 < guess)
    {word : List PhysicalTemplate}
    (wordOver : WordOver
      (ternaryFrontAlphabet source target guessPhase firstPhase secondPhase
        thirdPhase validatorPhase) word)
    (allLocal : AllStatesLocal prime word
      (phaseAffine firstPhase
        (firstAutomaticState prime first guess 0)))
    (completeRun : SameLine
      (physicalWordAction prime word
        (phaseAffine firstPhase
          (firstAutomaticState prime first guess 0))) endpoint) :
    ∃ suffix,
      guess = 2 * first + 2 ∧
      word = plainScanWord firstPhase secondPhase first ++
          plainScanWord secondPhase thirdPhase first ++
          thirdScanWord thirdPhase validatorPhase first ++
          frontValidatorWord validatorPhase target first ++ suffix ∧
      WordOver
        (ternaryFrontAlphabet source target guessPhase firstPhase secondPhase
          thirdPhase validatorPhase) suffix ∧
      AllStatesLocal prime suffix
        (phaseAffine target (twoFieldCode prime first (2 * first + 1))) ∧
      SameLine
        (physicalWordAction prime suffix
          (phaseAffine target
            (twoFieldCode prime first (2 * first + 1)))) endpoint := by
  obtain ⟨afterFirst, wordEq, afterFirstOver, afterFirstLocal,
      afterFirstRun⟩ := firstScanTail_forced_prefix_to_endpoint
    primeProperty primeBound layout endpointBound firstEndpointDistinct
    endpointMembership (first := first) (guess := guess) (deleted := 0)
    (remaining := first) (by omega) wordOver allLocal completeRun
  obtain ⟨afterSecond, firstTailEq, afterSecondOver, afterSecondLocal,
      afterSecondRun⟩ := secondScanTail_forced_prefix_to_endpoint
    primeProperty primeBound layout endpointBound secondEndpointDistinct
    endpointMembership guessPositive (deleted := 0) (remaining := first)
    (by omega) afterFirstOver afterFirstLocal afterFirstRun
  obtain ⟨afterThird, middleRejected, secondTailEq, afterThirdOver,
      afterThirdLocal, afterThirdRun⟩ :=
    thirdScanTail_forced_prefix_to_endpoint primeProperty primeBound layout
      endpointBound thirdEndpointDistinct endpointMembership guessPositive
      (deleted := 0) (remaining := thirdScanLength first guess) (by omega)
      afterSecondOver afterSecondLocal afterSecondRun
  obtain ⟨suffix, accepted, thirdTailEq, suffixOver, suffixLocal,
      suffixRun⟩ := validatorTail_forced_prefix_to_endpoint
    primeProperty primeBound layout endpointBound validatorEndpointDistinct
    endpointMembership guessPositive middleRejected (deleted := 0)
    (remaining := ternaryValidatorLength first guess) (by omega)
    afterThirdOver afterThirdLocal afterThirdRun
  have thirdLengthEq : thirdScanLength first guess = first := by
    rw [accepted]
    exact Nat.min_eq_left (by omega)
  have validatorLengthEq : ternaryValidatorLength first guess = first := by
    rw [accepted]
    unfold ternaryValidatorLength
    rw [if_pos (by omega)]
    exact Nat.min_eq_left (by omega)
  refine ⟨suffix, accepted, ?_, suffixOver, suffixLocal, suffixRun⟩
  rw [wordEq, firstTailEq, secondTailEq, thirdTailEq]
  simp only [plainScanWord, thirdScanWord, frontValidatorWord,
    thirdLengthEq, validatorLengthEq, List.append_assoc]

theorem sourceState_inPhaseAt_positive
    {prime source counter : Nat} (primeProperty : IsPrime prime)
    (counterPositive : 0 < counter) :
    InPhaseAt prime source 0
      (phaseAffine source (unaryCode prime counter)) := by
  obtain ⟨previous, rfl⟩ :=
    Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt counterPositive)
  simpa [unaryCode, unaryDigits, List.replicate_succ] using
    (periodicCode_inPhaseAt prime source 0
      (List.replicate previous (0 : Int) ++ [1]) primeProperty.1
      (by simp [ReservedDigit]))

theorem guessState_inPhaseAt_before
    {prime guessPhase counter deleted : Nat}
    (primeProperty : IsPrime prime) (deletedBelow : deleted < counter) :
    InPhaseAt prime guessPhase 0
      (phaseAffine guessPhase (prefixState prime counter deleted)) := by
  have residue : (prime : Int) ∣
      (prime : Int) ^ (counter - deleted) -
        0 * (1 - (prime : Int) ^ (counter + 1)) := by
    simpa using base_dvd_positive_power prime (counter - deleted) (by omega)
  apply inPhaseAt_phaseAffine_integer (by simp [ReservedDigit])
    (one_sub_power_not_dvd prime (counter + 1) primeProperty.1 (by omega))
    residue
  exact prefixState_sameLine_integer prime counter deleted primeProperty.1

theorem guessState_inPhaseAt_marker
    {prime guessPhase counter : Nat} (primeProperty : IsPrime prime) :
    InPhaseAt prime guessPhase 1
      (phaseAffine guessPhase (prefixState prime counter counter)) := by
  have residue : (prime : Int) ∣
      (prime : Int) ^ (counter - counter) -
        1 * (1 - (prime : Int) ^ (counter + 1)) := by
    simp only [Nat.sub_self, Int.pow_zero, Int.one_mul]
    have powerDivisible := base_dvd_positive_power prime (counter + 1)
      (by omega)
    rw [show (1 : Int) - (1 - (prime : Int) ^ (counter + 1)) =
      (prime : Int) ^ (counter + 1) by grind]
    exact powerDivisible
  apply inPhaseAt_phaseAffine_integer (by simp [ReservedDigit])
    (one_sub_power_not_dvd prime (counter + 1) primeProperty.1 (by omega))
    residue
  exact prefixState_sameLine_integer prime counter counter primeProperty.1

/-- A completed path in the private guess phase must take one of the
zero-digit exits before it reaches the unary marker. -/
theorem guessTail_forced_exit_to_endpoint
    {prime phaseCount source target guessPhase firstPhase secondPhase
      thirdPhase validatorPhase endpointPhase : Nat}
    {endpointDigit : Int} {endpoint : Vec2}
    (primeProperty : IsPrime prime)
    (primeBound : 6 * phaseCount < prime)
    (layout : PhaseLayout phaseCount source guessPhase firstPhase secondPhase
      thirdPhase validatorPhase)
    (endpointBound : endpointPhase < phaseCount)
    (guessEndpointDistinct : guessPhase ≠ endpointPhase)
    (endpointMembership : InPhaseAt prime endpointPhase endpointDigit endpoint)
    {counter deleted remaining : Nat} (sumEq : deleted + remaining = counter)
    {word : List PhysicalTemplate}
    (wordOver : WordOver
      (ternaryFrontAlphabet source target guessPhase firstPhase secondPhase
        thirdPhase validatorPhase) word)
    (allLocal : AllStatesLocal prime word
      (phaseAffine guessPhase (prefixState prime counter deleted)))
    (completeRun : SameLine
      (physicalWordAction prime word
        (phaseAffine guessPhase (prefixState prime counter deleted)))
      endpoint) :
    ∃ loops suffix,
      loops < remaining ∧
      word = prefixTail guessPhase firstPhase loops ++ suffix ∧
      WordOver
        (ternaryFrontAlphabet source target guessPhase firstPhase secondPhase
          thirdPhase validatorPhase) suffix ∧
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
      have currentMembership := guessState_inPhaseAt_marker
        (guessPhase := guessPhase) (counter := counter) primeProperty
      have wordNonempty := word_nonempty_of_endpoint_phase_ne primeProperty
        primeBound layout.core.guessBound endpointBound guessEndpointDistinct
        currentMembership endpointMembership (word := word) (by
          simpa only [deletedEq] using completeRun)
      cases word with
      | nil => exact False.elim (wordNonempty rfl)
      | cons letter tail =>
          have letterMem := wordOver letter (by simp)
          have rejected := guess_rejects_marker (counter := counter)
            primeProperty primeBound layout letterMem
          exact False.elim (rejected (by
            simpa only [deletedEq] using allLocal.2.start))
  | succ remaining inductionHypothesis =>
      have deletedBelow : deleted < counter := by omega
      have currentMembership := guessState_inPhaseAt_before
        (guessPhase := guessPhase) (counter := counter) (deleted := deleted)
        primeProperty deletedBelow
      have wordNonempty := word_nonempty_of_endpoint_phase_ne primeProperty
        primeBound layout.core.guessBound endpointBound guessEndpointDistinct
        currentMembership endpointMembership completeRun
      cases word with
      | nil => exact False.elim (wordNonempty rfl)
      | cons letter tail =>
          have letterMem := wordOver letter (by simp)
          have tailOver : WordOver
              (ternaryFrontAlphabet source target guessPhase firstPhase
                secondPhase thirdPhase validatorPhase) tail := by
            intro candidate candidateMem
            exact wordOver candidate (by simp [candidateMem])
          obtain letterEq | letterEq := guess_letter_before_marker
            primeProperty primeBound layout deletedBelow letterMem
              allLocal.2.start
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

/-- Boundary-aware form of the nondeterministic prefix choice.  The
endpoint prevents the word from stopping in either the source or the
private guess phase. -/
theorem prefix_choice_forced_to_endpoint
    {prime phaseCount source target guessPhase firstPhase secondPhase
      thirdPhase validatorPhase endpointPhase : Nat}
    {endpointDigit : Int} {endpoint : Vec2}
    (primeProperty : IsPrime prime)
    (primeBound : 6 * phaseCount < prime)
    (layout : PhaseLayout phaseCount source guessPhase firstPhase secondPhase
      thirdPhase validatorPhase)
    (endpointBound : endpointPhase < phaseCount)
    (sourceEndpointDistinct : source ≠ endpointPhase)
    (guessEndpointDistinct : guessPhase ≠ endpointPhase)
    (endpointMembership : InPhaseAt prime endpointPhase endpointDigit endpoint)
    {counter : Nat} (counterPositive : 0 < counter)
    {word : List PhysicalTemplate}
    (wordOver : WordOver
      (ternaryFrontAlphabet source target guessPhase firstPhase secondPhase
        thirdPhase validatorPhase) word)
    (allLocal : AllStatesLocal prime word
      (phaseAffine source (unaryCode prime counter)))
    (completeRun : SameLine
      (physicalWordAction prime word
        (phaseAffine source (unaryCode prime counter))) endpoint) :
    ∃ first guess suffix,
      0 < guess ∧ first + guess = counter ∧
      word = prefixWord source guessPhase firstPhase guess ++ suffix ∧
      WordOver
        (ternaryFrontAlphabet source target guessPhase firstPhase secondPhase
          thirdPhase validatorPhase) suffix ∧
      AllStatesLocal prime suffix
        (phaseAffine firstPhase
          (firstAutomaticState prime first guess 0)) ∧
      SameLine
        (physicalWordAction prime suffix
          (phaseAffine firstPhase
            (firstAutomaticState prime first guess 0))) endpoint := by
  obtain ⟨previous, counterEq⟩ :=
    Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt counterPositive)
  subst counter
  have sourceMembership := sourceState_inPhaseAt_positive
    (prime := prime) (source := source) (counter := previous + 1)
    primeProperty (by omega)
  have wordNonempty := word_nonempty_of_endpoint_phase_ne primeProperty
    primeBound layout.core.sourceBound endpointBound sourceEndpointDistinct
    sourceMembership endpointMembership completeRun
  cases word with
  | nil => exact False.elim (wordNonempty rfl)
  | cons letter tail =>
      have letterMem := wordOver letter (by simp)
      have tailOver : WordOver
          (ternaryFrontAlphabet source target guessPhase firstPhase
            secondPhase thirdPhase validatorPhase) tail := by
        intro candidate candidateMem
        exact wordOver candidate (by simp [candidateMem])
      obtain letterEq | letterEq := source_letter_positive
        (counter := previous) primeProperty primeBound layout letterMem
          allLocal.2.start
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

/-- Full boundary-to-boundary converse for the twelve-letter ternary
front end.  Every path from its unary source to a guarded endpoint
outside the six active phases begins with the unique accepted block.
The remaining suffix is returned for subsequent module parsing. -/
theorem ternaryFrontWord_forced_prefix_to_endpoint
    {prime phaseCount source target guessPhase firstPhase secondPhase
      thirdPhase validatorPhase endpointPhase counter : Nat}
    {endpointDigit : Int} {endpoint : Vec2}
    (primeProperty : IsPrime prime)
    (primeBound : 6 * phaseCount < prime)
    (layout : PhaseLayout phaseCount source guessPhase firstPhase secondPhase
      thirdPhase validatorPhase)
    (endpointBound : endpointPhase < phaseCount)
    (sourceEndpointDistinct : source ≠ endpointPhase)
    (guessEndpointDistinct : guessPhase ≠ endpointPhase)
    (firstEndpointDistinct : firstPhase ≠ endpointPhase)
    (secondEndpointDistinct : secondPhase ≠ endpointPhase)
    (thirdEndpointDistinct : thirdPhase ≠ endpointPhase)
    (validatorEndpointDistinct : validatorPhase ≠ endpointPhase)
    (endpointMembership : InPhaseAt prime endpointPhase endpointDigit endpoint)
    (counterPositive : 0 < counter)
    {word : List PhysicalTemplate}
    (wordOver : WordOver
      (ternaryFrontAlphabet source target guessPhase firstPhase secondPhase
        thirdPhase validatorPhase) word)
    (completeRun : SameLine
      (physicalWordAction prime word
        (phaseAffine source (unaryCode prime counter))) endpoint) :
    ∃ first suffix,
      counter = 3 * first + 2 ∧
      word = ternaryFrontWord source target guessPhase firstPhase secondPhase
          thirdPhase validatorPhase first ++ suffix ∧
      WordOver
        (ternaryFrontAlphabet source target guessPhase firstPhase secondPhase
          thirdPhase validatorPhase) suffix ∧
      AllStatesLocal prime suffix
        (phaseAffine target (twoFieldCode prime first (2 * first + 1))) ∧
      SameLine
        (physicalWordAction prime suffix
          (phaseAffine target
            (twoFieldCode prime first (2 * first + 1)))) endpoint := by
  have inputLocal := phaseUnaryCode_local prime source counter
    primeProperty.1
  have outputNonzero := physicalWordAction_nonzero
    (prime := prime) (by have := primeProperty.1; omega) word inputLocal.1
  have finalLocal : LocalAt prime
      (physicalWordAction prime word
        (phaseAffine source (unaryCode prime counter))) :=
    LocalAt.of_sameLine endpointMembership.local outputNonzero completeRun
  have allLocal := allStatesLocal_of_final_local
    (by have := primeProperty.1; omega) word inputLocal.1 finalLocal
  obtain ⟨first, guess, afterPrefix, guessPositive, splitEq, wordEq,
      afterPrefixOver, afterPrefixLocal, afterPrefixRun⟩ :=
    prefix_choice_forced_to_endpoint primeProperty primeBound layout
      endpointBound sourceEndpointDistinct guessEndpointDistinct
      endpointMembership counterPositive wordOver allLocal completeRun
  obtain ⟨suffix, accepted, suffixEq, suffixOver, suffixLocal,
      suffixRun⟩ := automaticSuffix_forced_prefix_to_endpoint
    primeProperty primeBound layout endpointBound firstEndpointDistinct
    secondEndpointDistinct thirdEndpointDistinct validatorEndpointDistinct
    endpointMembership guessPositive afterPrefixOver afterPrefixLocal
    afterPrefixRun
  have counterEq : counter = 3 * first + 2 := by omega
  refine ⟨first, suffix, counterEq, ?_, suffixOver, suffixLocal, suffixRun⟩
  rw [wordEq, suffixEq, accepted]
  simp [ternaryFrontWord, List.append_assoc]

end Mortality.Compiler.TernaryFrontModule
