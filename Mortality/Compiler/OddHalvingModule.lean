import Mortality.Compiler.OddHalvingArithmetic

/-!
# The ten-letter odd-halving module

This file packages the checked prefix and scan arithmetic into the physical
table of Lemma 5.5 and proves the complete accepted execution
`z_(2a+1) ↦ z_a` in exactly `4a+4` letters.
-/

namespace Mortality.Compiler.OddHalvingModule

open Mortality.PeriodicCode
open Mortality.Compiler.UnaryArithmetic
open Mortality.Compiler.IncrementModule
open Mortality.Compiler.PrefixGuessModule
open Mortality.Compiler.OddHalvingArithmetic

def identityZero (phase : Nat) : PhysicalTemplate :=
  { sourcePhase := phase
    targetPhase := phase
    digit := 0
    preCoefficient := 0
    postSign := .positive
    postCoefficient := 0 }

def identityMarker (source target : Nat) : PhysicalTemplate :=
  { sourcePhase := source
    targetPhase := target
    digit := 1
    preCoefficient := 0
    postSign := .positive
    postCoefficient := 0 }

def inverseTMarker (source target : Nat) : PhysicalTemplate :=
  { sourcePhase := source
    targetPhase := target
    digit := 1
    preCoefficient := 0
    postSign := .positive
    postCoefficient := 1 }

def validatorMarker (source target : Nat) : PhysicalTemplate :=
  { sourcePhase := source
    targetPhase := target
    digit := 2
    preCoefficient := 0
    postSign := .negative
    postCoefficient := 2 }

def oddHalvingAlphabet (source target guessPhase firstPhase secondPhase
    validatorPhase : Nat) : List PhysicalTemplate :=
  prefixAlphabet source guessPhase firstPhase ++
    [identityZero firstPhase, identityMarker firstPhase secondPhase,
      identityZero secondPhase, inverseTMarker secondPhase validatorPhase,
      identityZero validatorPhase, validatorMarker validatorPhase target]

/-- Bounds and freshness conditions for the five source phases used by
one odd-halving occurrence.  The target is a program boundary and is
not a source phase of this module. -/
structure PhaseLayout (phaseCount source guessPhase firstPhase secondPhase
    validatorPhase : Nat) : Prop where
  sourceBound : source < phaseCount
  guessBound : guessPhase < phaseCount
  firstBound : firstPhase < phaseCount
  secondBound : secondPhase < phaseCount
  validatorBound : validatorPhase < phaseCount
  sourceGuessDistinct : source ≠ guessPhase
  sourceFirstDistinct : source ≠ firstPhase
  sourceSecondDistinct : source ≠ secondPhase
  sourceValidatorDistinct : source ≠ validatorPhase
  guessFirstDistinct : guessPhase ≠ firstPhase
  guessSecondDistinct : guessPhase ≠ secondPhase
  guessValidatorDistinct : guessPhase ≠ validatorPhase
  firstSecondDistinct : firstPhase ≠ secondPhase
  firstValidatorDistinct : firstPhase ≠ validatorPhase
  secondValidatorDistinct : secondPhase ≠ validatorPhase

@[simp] theorem oddHalvingAlphabet_length
    (source target guessPhase firstPhase secondPhase validatorPhase : Nat) :
    (oddHalvingAlphabet source target guessPhase firstPhase secondPhase
      validatorPhase).length = 10 := by
  simp [oddHalvingAlphabet]

def firstScanWord (firstPhase secondPhase zeros : Nat) :
    List PhysicalTemplate :=
  List.replicate zeros (identityZero firstPhase) ++
    [identityMarker firstPhase secondPhase]

def secondScanWord (secondPhase validatorPhase zeros : Nat) :
    List PhysicalTemplate :=
  List.replicate zeros (identityZero secondPhase) ++
    [inverseTMarker secondPhase validatorPhase]

def validatorWord (validatorPhase target zeros : Nat) :
    List PhysicalTemplate :=
  List.replicate zeros (identityZero validatorPhase) ++
    [validatorMarker validatorPhase target]

def oddHalvingWord (source target guessPhase firstPhase secondPhase
    validatorPhase first : Nat) : List PhysicalTemplate :=
  prefixWord source guessPhase firstPhase (first + 1) ++
    firstScanWord firstPhase secondPhase first ++
    secondScanWord secondPhase validatorPhase first ++
    validatorWord validatorPhase target first

@[simp] theorem firstScanWord_length (firstPhase secondPhase zeros : Nat) :
    (firstScanWord firstPhase secondPhase zeros).length = zeros + 1 := by
  simp [firstScanWord]

@[simp] theorem secondScanWord_length
    (secondPhase validatorPhase zeros : Nat) :
    (secondScanWord secondPhase validatorPhase zeros).length = zeros + 1 := by
  simp [secondScanWord]

@[simp] theorem validatorWord_length (validatorPhase target zeros : Nat) :
    (validatorWord validatorPhase target zeros).length = zeros + 1 := by
  simp [validatorWord]

@[simp] theorem oddHalvingWord_length
    (source target guessPhase firstPhase secondPhase validatorPhase first : Nat) :
    (oddHalvingWord source target guessPhase firstPhase secondPhase
      validatorPhase first).length = 4 * first + 4 := by
  simp [oddHalvingWord, prefixWord_length (by omega : 0 < first + 1)]
  omega

theorem phaseLocal {base phase : Nat} {value : Rat}
    (membership : LocalAt base (Vec2.affine value)) :
    LocalAt base (phaseAffine phase value) := by
  rw [show phaseAffine phase value =
      Matrix2.apply (IntMatrix2.cast (chart phase)) (Vec2.affine value) by
    simpa [phaseAffine] using (chart_apply phase value).symm]
  exact (local_chart_iff base phase _).mpr membership

theorem identityZero_step
    {base phase : Nat} {value next : Rat} (basePositive : 0 < base)
    (valueLocal : LocalAt base (Vec2.affine value))
    (nextLocal : LocalAt base (Vec2.affine next))
    (deletedEq : deleteDigit (base : Rat) 0 value = next) :
    SameLine
      ((identityZero phase).act base (phaseAffine phase value))
      (phaseAffine phase next) := by
  have action := physicalLetter_affine_sameLine_of_local
    (sourcePhase := phase) (targetPhase := phase) (digit := 0)
    (preCoefficient := 0) (postCoefficient := 0)
    (postSign := .positive) basePositive valueLocal
    (by
      have deletedActual : LocalAt base
          (Vec2.affine (deleteDigit (base : Rat) 0 value)) := by
        rw [deletedEq]
        exact nextLocal
      simpa [deleteDigit] using deletedActual)
  simp [localLetterMap] at action
  have deletedRaw := deletedEq
  unfold deleteDigit at deletedRaw
  simp only [Rat.intCast_zero] at deletedRaw
  rw [deletedRaw] at action
  exact action

theorem marker_step
    {base source target : Nat} {digit coefficient : Int} {sign : Sign}
    {value deleted output : Rat} (basePositive : 0 < base)
    (valueLocal : LocalAt base (Vec2.affine value))
    (deletedLocal : LocalAt base (Vec2.affine deleted))
    (deletedEq : deleteDigit (base : Rat) digit value = deleted)
    (outputEq : mutationMap base sign coefficient deleted = output) :
    SameLine
      (Matrix2.apply
        (IntMatrix2.cast
          (physicalLetter base source target digit 0 sign coefficient))
        (phaseAffine source value))
      (phaseAffine target output) := by
  have action := physicalLetter_affine_sameLine_of_local
    (sourcePhase := source) (targetPhase := target) (digit := digit)
    (preCoefficient := 0) (postCoefficient := coefficient)
    (postSign := sign) basePositive valueLocal
    (by
      have deletedActual : LocalAt base
          (Vec2.affine (deleteDigit (base : Rat) digit value)) := by
        rw [deletedEq]
        exact deletedLocal
      simpa [deleteDigit] using deletedActual)
  simp [localLetterMap] at action
  have deletedRaw := deletedEq
  unfold deleteDigit at deletedRaw
  rw [deletedRaw, outputEq] at action
  exact action

theorem firstZero_step
    (base firstPhase first guess deleted : Nat)
    (baseAtLeastTwo : 2 ≤ base) (deletedBelow : deleted < first) :
    SameLine
      ((identityZero firstPhase).act base
        (phaseAffine firstPhase
          (firstAutomaticState base first guess deleted)))
      (phaseAffine firstPhase
        (firstAutomaticState base first guess (deleted + 1))) := by
  exact identityZero_step (by omega)
    (firstAutomaticState_local base first guess deleted baseAtLeastTwo)
    (firstAutomaticState_local base first guess (deleted + 1) baseAtLeastTwo)
    (firstAutomaticState_delete_zero base first guess deleted
      baseAtLeastTwo deletedBelow)

theorem firstMarker_step
    (base firstPhase secondPhase first guess : Nat)
    (baseAtLeastTwo : 2 ≤ base) :
    SameLine
      ((identityMarker firstPhase secondPhase).act base
        (phaseAffine firstPhase
          (firstAutomaticState base first guess first)))
      (phaseAffine secondPhase (firstScanOutput base first guess)) := by
  have deletedEq := firstAutomaticState_delete_marker base first guess
    baseAtLeastTwo
  have step := marker_step (source := firstPhase) (target := secondPhase)
    (digit := 1) (coefficient := 0) (sign := .positive)
    (value := firstAutomaticState base first guess first)
    (deleted := firstScanOutput base first guess)
    (output := firstScanOutput base first guess) (by omega)
    (firstAutomaticState_local base first guess first baseAtLeastTwo)
    (firstScanOutput_local base first guess baseAtLeastTwo) deletedEq
    (by simp)
  simpa [identityMarker, PhysicalTemplate.act, PhysicalTemplate.matrix]
    using step

theorem secondZero_step
    (base secondPhase first guess deleted : Nat)
    (baseAtLeastTwo : 2 ≤ base) (deletedBelow : deleted < first) :
    SameLine
      ((identityZero secondPhase).act base
        (phaseAffine secondPhase
          (secondAutomaticState base first guess deleted)))
      (phaseAffine secondPhase
        (secondAutomaticState base first guess (deleted + 1))) := by
  exact identityZero_step (by omega)
    (secondAutomaticState_local base first guess deleted baseAtLeastTwo)
    (secondAutomaticState_local base first guess (deleted + 1) baseAtLeastTwo)
    (secondAutomaticState_delete_zero base first guess deleted
      baseAtLeastTwo deletedBelow)

theorem secondMarker_step
    (base secondPhase validatorPhase first guess : Nat)
    (baseAtLeastTwo : 2 ≤ base) (guessPositive : 0 < guess) :
    SameLine
      ((inverseTMarker secondPhase validatorPhase).act base
        (phaseAffine secondPhase
          (secondAutomaticState base first guess first)))
      (phaseAffine validatorPhase (validatorInput base first guess)) := by
  have deletedEq := secondAutomaticState_delete_marker base first guess
    baseAtLeastTwo guessPositive
  have outputEq := validator_input_formula base first guess baseAtLeastTwo
    guessPositive
  rw [Tinv_eq_mutationMap] at outputEq
  have step := marker_step (source := secondPhase) (target := validatorPhase)
    (digit := 1) (coefficient := 1) (sign := .positive)
    (value := secondAutomaticState base first guess first)
    (deleted := secondScanOutput base first guess)
    (output := validatorInput base first guess) (by omega)
    (secondAutomaticState_local base first guess first baseAtLeastTwo)
    (secondScanOutput_local base first guess baseAtLeastTwo) deletedEq
    outputEq
  simpa [inverseTMarker, PhysicalTemplate.act, PhysicalTemplate.matrix]
    using step

theorem validatorZero_step
    (base validatorPhase first guess deleted : Nat)
    (baseAtLeastTwo : 2 ≤ base) (guessPositive : 0 < guess)
    (deletedBelow : deleted < validatorLength first guess) :
    SameLine
      ((identityZero validatorPhase).act base
        (phaseAffine validatorPhase
          (validatorState base first guess deleted)))
      (phaseAffine validatorPhase
        (validatorState base first guess (deleted + 1))) := by
  exact identityZero_step (by omega)
    (validatorState_local base first guess deleted baseAtLeastTwo guessPositive)
    (validatorState_local base first guess (deleted + 1) baseAtLeastTwo
      guessPositive)
    (validatorState_delete_zero base first guess deleted baseAtLeastTwo
      deletedBelow)

theorem validatorMarker_step
    (base validatorPhase target first : Nat)
    (baseAtLeastTwo : 2 ≤ base) :
    SameLine
      ((validatorMarker validatorPhase target).act base
        (phaseAffine validatorPhase
          (validatorState base first (first + 1) first)))
      (phaseAffine target (unaryCode base first)) := by
  have deletedEq := accepted_validator_delete_marker base first
    baseAtLeastTwo
  have outputEq := K_regenerates_unary base first baseAtLeastTwo
  rw [K_eq_mutationMap] at outputEq
  have step := marker_step (source := validatorPhase) (target := target)
    (digit := 2) (coefficient := 2) (sign := .negative)
    (value := validatorState base first (first + 1) first)
    (deleted := -((base : Rat) ^ first) /
      (1 + (base : Rat) ^ (first + 1)))
    (output := unaryCode base first) (by omega)
    (validatorState_local base first (first + 1) first baseAtLeastTwo
      (by omega))
    (acceptedValidatorDeleted_local base first baseAtLeastTwo) deletedEq
    outputEq
  simpa [validatorMarker, PhysicalTemplate.act, PhysicalTemplate.matrix]
    using step

theorem firstScanTail_correct
    (base firstPhase secondPhase first guess deleted remaining : Nat)
    (baseAtLeastTwo : 2 ≤ base) (sumEq : deleted + remaining = first) :
    SameLine
      (physicalWordAction base
        (List.replicate remaining (identityZero firstPhase) ++
          [identityMarker firstPhase secondPhase])
        (phaseAffine firstPhase
          (firstAutomaticState base first guess deleted)))
      (phaseAffine secondPhase (firstScanOutput base first guess)) := by
  induction remaining generalizing deleted with
  | zero =>
      simpa [physicalWordAction, show deleted = first by omega] using
        firstMarker_step base firstPhase secondPhase first guess baseAtLeastTwo
  | succ remaining inductionHypothesis =>
      have firstStep := firstZero_step base firstPhase first guess deleted
        baseAtLeastTwo (by omega)
      have tailRun := inductionHypothesis (deleted := deleted + 1) (by omega)
      have combined := physicalWordAction_cons_sameLine base
        (identityZero firstPhase)
        (List.replicate remaining (identityZero firstPhase) ++
          [identityMarker firstPhase secondPhase]) firstStep tailRun
      simpa [List.replicate_succ, physicalWordAction]
        using combined

theorem firstScanWord_correct
    (base firstPhase secondPhase first guess : Nat)
    (baseAtLeastTwo : 2 ≤ base) :
    SameLine
      (physicalWordAction base (firstScanWord firstPhase secondPhase first)
        (phaseAffine firstPhase
          (firstAutomaticState base first guess 0)))
      (phaseAffine secondPhase (firstScanOutput base first guess)) := by
  simpa [firstScanWord] using
    firstScanTail_correct base firstPhase secondPhase first guess 0 first
      baseAtLeastTwo (by omega)

theorem secondScanTail_correct
    (base secondPhase validatorPhase first guess deleted remaining : Nat)
    (baseAtLeastTwo : 2 ≤ base) (guessPositive : 0 < guess)
    (sumEq : deleted + remaining = first) :
    SameLine
      (physicalWordAction base
        (List.replicate remaining (identityZero secondPhase) ++
          [inverseTMarker secondPhase validatorPhase])
        (phaseAffine secondPhase
          (secondAutomaticState base first guess deleted)))
      (phaseAffine validatorPhase (validatorInput base first guess)) := by
  induction remaining generalizing deleted with
  | zero =>
      simpa [physicalWordAction, show deleted = first by omega] using
        secondMarker_step base secondPhase validatorPhase first guess
          baseAtLeastTwo guessPositive
  | succ remaining inductionHypothesis =>
      have firstStep := secondZero_step base secondPhase first guess deleted
        baseAtLeastTwo (by omega)
      have tailRun := inductionHypothesis (deleted := deleted + 1) (by omega)
      have combined := physicalWordAction_cons_sameLine base
        (identityZero secondPhase)
        (List.replicate remaining (identityZero secondPhase) ++
          [inverseTMarker secondPhase validatorPhase]) firstStep tailRun
      simpa [List.replicate_succ, physicalWordAction] using combined

theorem secondScanWord_correct
    (base secondPhase validatorPhase first guess : Nat)
    (baseAtLeastTwo : 2 ≤ base) (guessPositive : 0 < guess) :
    SameLine
      (physicalWordAction base
        (secondScanWord secondPhase validatorPhase first)
        (phaseAffine secondPhase
          (secondAutomaticState base first guess 0)))
      (phaseAffine validatorPhase (validatorInput base first guess)) := by
  simpa [secondScanWord] using
    secondScanTail_correct base secondPhase validatorPhase first guess 0 first
      baseAtLeastTwo guessPositive (by omega)

theorem validatorTail_correct
    (base validatorPhase target first deleted remaining : Nat)
    (baseAtLeastTwo : 2 ≤ base) (sumEq : deleted + remaining = first) :
    SameLine
      (physicalWordAction base
        (List.replicate remaining (identityZero validatorPhase) ++
          [validatorMarker validatorPhase target])
        (phaseAffine validatorPhase
          (validatorState base first (first + 1) deleted)))
      (phaseAffine target (unaryCode base first)) := by
  induction remaining generalizing deleted with
  | zero =>
      simpa [physicalWordAction, show deleted = first by omega] using
        validatorMarker_step base validatorPhase target first baseAtLeastTwo
  | succ remaining inductionHypothesis =>
      have firstStep := validatorZero_step base validatorPhase first
        (first + 1) deleted baseAtLeastTwo (by omega) (by
          unfold validatorLength
          simp
          omega)
      have tailRun := inductionHypothesis (deleted := deleted + 1) (by omega)
      have combined := physicalWordAction_cons_sameLine base
        (identityZero validatorPhase)
        (List.replicate remaining (identityZero validatorPhase) ++
          [validatorMarker validatorPhase target]) firstStep tailRun
      simpa [List.replicate_succ, physicalWordAction] using combined

theorem validatorWord_correct
    (base validatorPhase target first : Nat) (baseAtLeastTwo : 2 ≤ base) :
    SameLine
      (physicalWordAction base (validatorWord validatorPhase target first)
        (phaseAffine validatorPhase
          (validatorState base first (first + 1) 0)))
      (phaseAffine target (unaryCode base first)) := by
  simpa [validatorWord] using
    validatorTail_correct base validatorPhase target first 0 first
      baseAtLeastTwo (by omega)

/-- The displayed ten-letter alphabet realizes every accepted odd-halving
execution in the claimed `4a+4` letters. -/
theorem oddHalvingWord_correct
    (base source target guessPhase firstPhase secondPhase validatorPhase
      first : Nat) (baseAtLeastTwo : 2 ≤ base) :
    SameLine
      (physicalWordAction base
        (oddHalvingWord source target guessPhase firstPhase secondPhase
          validatorPhase first)
        (phaseAffine source (unaryCode base (2 * first + 1))))
      (phaseAffine target (unaryCode base first)) := by
  have inputCounterEq : 2 * first + 1 = first + (first + 1) := by omega
  have prefixRun := prefixWord_correct base source guessPhase firstPhase
    (2 * first + 1) (first + 1) baseAtLeastTwo (by omega) (by omega)
  have prefixRun' : SameLine
      (physicalWordAction base
        (prefixWord source guessPhase firstPhase (first + 1))
        (phaseAffine source (unaryCode base (2 * first + 1))))
      (phaseAffine firstPhase
        (firstAutomaticState base first (first + 1) 0)) := by
    rw [firstAutomaticState_zero base first (first + 1) baseAtLeastTwo]
    simpa only [inputCounterEq] using prefixRun
  have firstRun := firstScanWord_correct base firstPhase secondPhase first
    (first + 1) baseAtLeastTwo
  have throughFirst := physicalWordAction_append_sameLine base
    (prefixWord source guessPhase firstPhase (first + 1))
    (firstScanWord firstPhase secondPhase first) prefixRun' firstRun
  have secondRun := secondScanWord_correct base secondPhase validatorPhase
    first (first + 1) baseAtLeastTwo (by omega)
  have secondRun' : SameLine
      (physicalWordAction base
        (secondScanWord secondPhase validatorPhase first)
        (phaseAffine secondPhase (firstScanOutput base first (first + 1))))
      (phaseAffine validatorPhase
        (validatorState base first (first + 1) 0)) := by
    rw [validatorState_zero]
    rw [← secondAutomaticState_zero base first (first + 1)]
    exact secondRun
  have throughSecond := physicalWordAction_append_sameLine base
    (prefixWord source guessPhase firstPhase (first + 1) ++
      firstScanWord firstPhase secondPhase first)
    (secondScanWord secondPhase validatorPhase first) throughFirst secondRun'
  have validatorRun := validatorWord_correct base validatorPhase target first
    baseAtLeastTwo
  have complete := physicalWordAction_append_sameLine base
    (prefixWord source guessPhase firstPhase (first + 1) ++
      firstScanWord firstPhase secondPhase first ++
      secondScanWord secondPhase validatorPhase first)
    (validatorWord validatorPhase target first) throughSecond validatorRun
  simpa [oddHalvingWord, List.append_assoc] using complete

theorem oddHalvingWord_wordOver
    (source target guessPhase firstPhase secondPhase validatorPhase first : Nat) :
    WordOver
      (oddHalvingAlphabet source target guessPhase firstPhase secondPhase
        validatorPhase)
      (oddHalvingWord source target guessPhase firstPhase secondPhase
        validatorPhase first) := by
  let alphabet := oddHalvingAlphabet source target guessPhase firstPhase
    secondPhase validatorPhase
  have prefixOver : WordOver alphabet
      (prefixWord source guessPhase firstPhase (first + 1)) := by
    apply (prefixWord_wordOver source guessPhase firstPhase (first + 1)).mono
    intro letter letterMem
    simp [alphabet, oddHalvingAlphabet, letterMem]
  have firstOver : WordOver alphabet
      (firstScanWord firstPhase secondPhase first) := by
    intro letter letterMem
    simp [firstScanWord] at letterMem
    rcases letterMem with ⟨_, rfl⟩ | rfl <;>
      simp [alphabet, oddHalvingAlphabet]
  have secondOver : WordOver alphabet
      (secondScanWord secondPhase validatorPhase first) := by
    intro letter letterMem
    simp [secondScanWord] at letterMem
    rcases letterMem with ⟨_, rfl⟩ | rfl <;>
      simp [alphabet, oddHalvingAlphabet]
  have validatorOver : WordOver alphabet
      (validatorWord validatorPhase target first) := by
    intro letter letterMem
    simp [validatorWord] at letterMem
    rcases letterMem with ⟨_, rfl⟩ | rfl <;>
      simp [alphabet, oddHalvingAlphabet]
  unfold oddHalvingWord
  exact wordOver_append
    (wordOver_append (wordOver_append prefixOver firstOver) secondOver)
    validatorOver

/-- Complete forward local-module obligation for the accepted odd input. -/
theorem oddHalving_execution
    (base source target guessPhase firstPhase secondPhase validatorPhase
      first : Nat) (baseAtLeastTwo : 2 ≤ base) :
    let word := oddHalvingWord source target guessPhase firstPhase secondPhase
      validatorPhase first
    WordOver
        (oddHalvingAlphabet source target guessPhase firstPhase secondPhase
          validatorPhase) word ∧
      word.length = 4 * first + 4 ∧
      SameLine
        (physicalWordAction base word
          (phaseAffine source (unaryCode base (2 * first + 1))))
        (phaseAffine target (unaryCode base first)) ∧
      AllStatesLocal base word
        (phaseAffine source (unaryCode base (2 * first + 1))) := by
  dsimp
  have action := oddHalvingWord_correct base source target guessPhase
    firstPhase secondPhase validatorPhase first baseAtLeastTwo
  have inputLocal := phaseUnaryCode_local base source (2 * first + 1)
    baseAtLeastTwo
  have outputNonzero := physicalWordAction_nonzero (prime := base) (by omega)
    (oddHalvingWord source target guessPhase firstPhase secondPhase
      validatorPhase first) inputLocal.1
  have finalLocal := LocalAt.of_sameLine
    (phaseUnaryCode_local base target first baseAtLeastTwo) outputNonzero
    action
  exact ⟨oddHalvingWord_wordOver source target guessPhase firstPhase
      secondPhase validatorPhase first,
    oddHalvingWord_length source target guessPhase firstPhase secondPhase
      validatorPhase first,
    action, allStatesLocal_of_final_local (by omega) _ inputLocal.1
      finalLocal⟩

private theorem oddHalvingLetter_source_bound
    {phaseCount source target guessPhase firstPhase secondPhase validatorPhase : Nat}
    {letter : PhysicalTemplate}
    (sourceBound : source < phaseCount)
    (guessBound : guessPhase < phaseCount)
    (firstBound : firstPhase < phaseCount)
    (secondBound : secondPhase < phaseCount)
    (validatorBound : validatorPhase < phaseCount)
    (letterMem : letter ∈
      oddHalvingAlphabet source target guessPhase firstPhase secondPhase
        validatorPhase) :
    letter.sourcePhase < phaseCount := by
  simp [oddHalvingAlphabet, prefixAlphabet] at letterMem
  rcases letterMem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl <;>
    simp [startContinue, startExit, privateLoop, privateExit, identityZero,
      identityMarker, inverseTMarker, validatorMarker, sourceBound,
      guessBound, firstBound, secondBound, validatorBound]

private theorem oddHalvingLetter_reserved
    {source target guessPhase firstPhase secondPhase validatorPhase : Nat}
    {letter : PhysicalTemplate}
    (letterMem : letter ∈
      oddHalvingAlphabet source target guessPhase firstPhase secondPhase
        validatorPhase) :
    ReservedDigit letter.digit := by
  simp [oddHalvingAlphabet, prefixAlphabet] at letterMem
  rcases letterMem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl <;>
    simp [startContinue, startExit, privateLoop, privateExit, identityZero,
      identityMarker, inverseTMarker, validatorMarker, ReservedDigit]

/-- On a positive unary input, the full ten-letter alphabet leaves
exactly the two nondeterministic prefix choices. -/
theorem source_letter_positive
    {prime phaseCount source target guessPhase firstPhase secondPhase
      validatorPhase counter : Nat}
    (primeProperty : IsPrime prime)
    (primeBound : 6 * phaseCount < prime)
    (layout : PhaseLayout phaseCount source guessPhase firstPhase secondPhase
      validatorPhase)
    {letter : PhysicalTemplate}
    (letterMem : letter ∈
      oddHalvingAlphabet source target guessPhase firstPhase secondPhase
        validatorPhase)
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
    primeBound layout.sourceBound
    (oddHalvingLetter_source_bound layout.sourceBound layout.guessBound
      layout.firstBound layout.secondBound layout.validatorBound letterMem)
    (by simp [ReservedDigit]) (oddHalvingLetter_reserved letterMem)
    (by simpa [PhysicalTemplate.act, PhysicalTemplate.matrix, phaseAffine,
      unaryCode, digitsEq] using outputLocal)
  simp [oddHalvingAlphabet, prefixAlphabet] at letterMem
  rcases letterMem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl
  · exact Or.inl rfl
  · exact Or.inr rfl
  · exact False.elim (layout.sourceGuessDistinct forced.1)
  · exact False.elim (layout.sourceGuessDistinct forced.1)
  · exact False.elim (layout.sourceFirstDistinct forced.1)
  · exact False.elim (layout.sourceFirstDistinct forced.1)
  · exact False.elim (layout.sourceSecondDistinct forced.1)
  · exact False.elim (layout.sourceSecondDistinct forced.1)
  · exact False.elim (layout.sourceValidatorDistinct forced.1)
  · exact False.elim (layout.sourceValidatorDistinct forced.1)

/-- No letter of the odd-halving module can start on `z_0`. -/
theorem source_rejects_zero
    {prime phaseCount source target guessPhase firstPhase secondPhase
      validatorPhase : Nat}
    (primeProperty : IsPrime prime)
    (primeBound : 6 * phaseCount < prime)
    (layout : PhaseLayout phaseCount source guessPhase firstPhase secondPhase
      validatorPhase)
    {letter : PhysicalTemplate}
    (letterMem : letter ∈
      oddHalvingAlphabet source target guessPhase firstPhase secondPhase
        validatorPhase) :
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
    layout.sourceBound
    (oddHalvingLetter_source_bound layout.sourceBound layout.guessBound
      layout.firstBound layout.secondBound layout.validatorBound letterMem)
    (by simp [ReservedDigit]) (oddHalvingLetter_reserved letterMem)
    (by simpa [PhysicalTemplate.act, PhysicalTemplate.matrix, phaseAffine,
      unaryCode, unaryDigits] using outputLocal)
  simp [oddHalvingAlphabet, prefixAlphabet] at letterMem
  rcases letterMem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl
  · simp [startContinue] at forced
  · simp [startExit] at forced
  · exact layout.sourceGuessDistinct forced.1
  · exact layout.sourceGuessDistinct forced.1
  · exact layout.sourceFirstDistinct forced.1
  · exact layout.sourceFirstDistinct forced.1
  · exact layout.sourceSecondDistinct forced.1
  · exact layout.sourceSecondDistinct forced.1
  · exact layout.sourceValidatorDistinct forced.1
  · exact layout.sourceValidatorDistinct forced.1

/-- While zeros remain in the private guess phase, precisely its loop
and exit can survive. -/
theorem guess_letter_before_marker
    {prime phaseCount source target guessPhase firstPhase secondPhase
      validatorPhase counter deleted : Nat}
    (primeProperty : IsPrime prime)
    (primeBound : 6 * phaseCount < prime)
    (layout : PhaseLayout phaseCount source guessPhase firstPhase secondPhase
      validatorPhase)
    (deletedBelow : deleted < counter)
    {letter : PhysicalTemplate}
    (letterMem : letter ∈
      oddHalvingAlphabet source target guessPhase firstPhase secondPhase
        validatorPhase)
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
    (postSign := letter.postSign) primeProperty primeBound layout.guessBound
    (oddHalvingLetter_source_bound layout.sourceBound layout.guessBound
      layout.firstBound layout.secondBound layout.validatorBound letterMem)
    (by simp [ReservedDigit]) (oddHalvingLetter_reserved letterMem)
    denominatorNotDivisible actualResidue
    (prefixState_sameLine_integer prime counter deleted primeProperty.1)
    (by simpa [PhysicalTemplate.act, PhysicalTemplate.matrix, phaseAffine]
      using outputLocal)
  simp [oddHalvingAlphabet, prefixAlphabet] at letterMem
  rcases letterMem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl
  · exact False.elim (layout.sourceGuessDistinct forced.1.symm)
  · exact False.elim (layout.sourceGuessDistinct forced.1.symm)
  · exact Or.inl rfl
  · exact Or.inr rfl
  · exact False.elim (layout.guessFirstDistinct forced.1)
  · exact False.elim (layout.guessFirstDistinct forced.1)
  · exact False.elim (layout.guessSecondDistinct forced.1)
  · exact False.elim (layout.guessSecondDistinct forced.1)
  · exact False.elim (layout.guessValidatorDistinct forced.1)
  · exact False.elim (layout.guessValidatorDistinct forced.1)

/-- The private guess phase has no surviving letter after all unary
zeros have been consumed. -/
theorem guess_rejects_marker
    {prime phaseCount source target guessPhase firstPhase secondPhase
      validatorPhase counter : Nat}
    (primeProperty : IsPrime prime)
    (primeBound : 6 * phaseCount < prime)
    (layout : PhaseLayout phaseCount source guessPhase firstPhase secondPhase
      validatorPhase)
    {letter : PhysicalTemplate}
    (letterMem : letter ∈
      oddHalvingAlphabet source target guessPhase firstPhase secondPhase
        validatorPhase) :
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
    (postSign := letter.postSign) primeProperty primeBound layout.guessBound
    (oddHalvingLetter_source_bound layout.sourceBound layout.guessBound
      layout.firstBound layout.secondBound layout.validatorBound letterMem)
    (by simp [ReservedDigit]) (oddHalvingLetter_reserved letterMem)
    denominatorNotDivisible actualResidue
    (prefixState_sameLine_integer prime counter counter primeProperty.1)
    (by simpa [PhysicalTemplate.act, PhysicalTemplate.matrix, phaseAffine]
      using outputLocal)
  simp [oddHalvingAlphabet, prefixAlphabet] at letterMem
  rcases letterMem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl
  · exact layout.sourceGuessDistinct forced.1.symm
  · exact layout.sourceGuessDistinct forced.1.symm
  · simp [privateLoop] at forced
  · simp [privateExit] at forced
  · exact layout.guessFirstDistinct forced.1
  · exact layout.guessFirstDistinct forced.1
  · exact layout.guessSecondDistinct forced.1
  · exact layout.guessSecondDistinct forced.1
  · exact layout.guessValidatorDistinct forced.1
  · exact layout.guessValidatorDistinct forced.1

/-- During the first automatic marker-one scan, every zero before the
marker forces the first-phase zero loop. -/
theorem first_letter_before_marker
    {prime phaseCount source target guessPhase firstPhase secondPhase
      validatorPhase first guess deleted : Nat}
    (primeProperty : IsPrime prime)
    (primeBound : 6 * phaseCount < prime)
    (sourceBound : source < phaseCount)
    (guessBound : guessPhase < phaseCount)
    (firstBound : firstPhase < phaseCount)
    (secondBound : secondPhase < phaseCount)
    (validatorBound : validatorPhase < phaseCount)
    (firstSourceDistinct : firstPhase ≠ source)
    (firstGuessDistinct : firstPhase ≠ guessPhase)
    (firstSecondDistinct : firstPhase ≠ secondPhase)
    (firstValidatorDistinct : firstPhase ≠ validatorPhase)
    (deletedBelow : deleted < first)
    {letter : PhysicalTemplate}
    (letterMem : letter ∈
      oddHalvingAlphabet source target guessPhase firstPhase secondPhase
        validatorPhase)
    (outputLocal : LocalAt prime
      (letter.act prime
        (phaseAffine firstPhase
          (firstAutomaticState prime first guess deleted)))) :
    letter = identityZero firstPhase := by
  have forced := physicalLetter_affine_integer_source_digit_unique
    (prime := prime) (phaseCount := phaseCount)
    (actualPhase := firstPhase) (sourcePhase := letter.sourcePhase)
    (targetPhase := letter.targetPhase) (actualDigit := 0)
    (letterDigit := letter.digit)
    (preCoefficient := letter.preCoefficient)
    (postCoefficient := letter.postCoefficient)
    (postSign := letter.postSign) primeProperty primeBound firstBound
    (oddHalvingLetter_source_bound sourceBound guessBound firstBound
      secondBound validatorBound letterMem)
    (by simp [ReservedDigit]) (oddHalvingLetter_reserved letterMem)
    (halfIntegerDenominator_not_dvd prime first guess primeProperty.1)
    (firstAutomaticState_zero_residue prime first guess deleted deletedBelow)
    (firstAutomaticState_sameLine_integer prime first guess deleted
      primeProperty.1)
    (by simpa [PhysicalTemplate.act, PhysicalTemplate.matrix, phaseAffine]
      using outputLocal)
  simp [oddHalvingAlphabet, prefixAlphabet] at letterMem
  rcases letterMem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl
  · exact False.elim (firstSourceDistinct forced.1)
  · exact False.elim (firstSourceDistinct forced.1)
  · exact False.elim (firstGuessDistinct forced.1)
  · exact False.elim (firstGuessDistinct forced.1)
  · rfl
  · simp [identityMarker] at forced
  · exact False.elim (firstSecondDistinct forced.1)
  · exact False.elim (firstSecondDistinct forced.1)
  · exact False.elim (firstValidatorDistinct forced.1)
  · exact False.elim (firstValidatorDistinct forced.1)

/-- At the first scan's marker, the unique surviving module letter is
its marker-one handoff to the second scan. -/
theorem first_letter_at_marker
    {prime phaseCount source target guessPhase firstPhase secondPhase
      validatorPhase first guess : Nat}
    (primeProperty : IsPrime prime)
    (primeBound : 6 * phaseCount < prime)
    (sourceBound : source < phaseCount)
    (guessBound : guessPhase < phaseCount)
    (firstBound : firstPhase < phaseCount)
    (secondBound : secondPhase < phaseCount)
    (validatorBound : validatorPhase < phaseCount)
    (firstSourceDistinct : firstPhase ≠ source)
    (firstGuessDistinct : firstPhase ≠ guessPhase)
    (firstSecondDistinct : firstPhase ≠ secondPhase)
    (firstValidatorDistinct : firstPhase ≠ validatorPhase)
    {letter : PhysicalTemplate}
    (letterMem : letter ∈
      oddHalvingAlphabet source target guessPhase firstPhase secondPhase
        validatorPhase)
    (outputLocal : LocalAt prime
      (letter.act prime
        (phaseAffine firstPhase
          (firstAutomaticState prime first guess first)))) :
    letter = identityMarker firstPhase secondPhase := by
  have forced := physicalLetter_affine_integer_source_digit_unique
    (prime := prime) (phaseCount := phaseCount)
    (actualPhase := firstPhase) (sourcePhase := letter.sourcePhase)
    (targetPhase := letter.targetPhase) (actualDigit := 1)
    (letterDigit := letter.digit)
    (preCoefficient := letter.preCoefficient)
    (postCoefficient := letter.postCoefficient)
    (postSign := letter.postSign) primeProperty primeBound firstBound
    (oddHalvingLetter_source_bound sourceBound guessBound firstBound
      secondBound validatorBound letterMem)
    (by simp [ReservedDigit]) (oddHalvingLetter_reserved letterMem)
    (halfIntegerDenominator_not_dvd prime first guess primeProperty.1)
    (firstAutomaticState_marker_residue prime first guess)
    (firstAutomaticState_sameLine_integer prime first guess first
      primeProperty.1)
    (by simpa [PhysicalTemplate.act, PhysicalTemplate.matrix, phaseAffine]
      using outputLocal)
  simp [oddHalvingAlphabet, prefixAlphabet] at letterMem
  rcases letterMem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl
  · exact False.elim (firstSourceDistinct forced.1)
  · exact False.elim (firstSourceDistinct forced.1)
  · exact False.elim (firstGuessDistinct forced.1)
  · exact False.elim (firstGuessDistinct forced.1)
  · simp [identityZero] at forced
  · rfl
  · exact False.elim (firstSecondDistinct forced.1)
  · exact False.elim (firstSecondDistinct forced.1)
  · exact False.elim (firstValidatorDistinct forced.1)
  · exact False.elim (firstValidatorDistinct forced.1)

/-- During the second marker-one scan, every zero before the marker
forces the second-phase zero loop. -/
theorem second_letter_before_marker
    {prime phaseCount source target guessPhase firstPhase secondPhase
      validatorPhase first guess deleted : Nat}
    (primeProperty : IsPrime prime)
    (primeBound : 6 * phaseCount < prime)
    (sourceBound : source < phaseCount)
    (guessBound : guessPhase < phaseCount)
    (firstBound : firstPhase < phaseCount)
    (secondBound : secondPhase < phaseCount)
    (validatorBound : validatorPhase < phaseCount)
    (secondSourceDistinct : secondPhase ≠ source)
    (secondGuessDistinct : secondPhase ≠ guessPhase)
    (secondFirstDistinct : secondPhase ≠ firstPhase)
    (secondValidatorDistinct : secondPhase ≠ validatorPhase)
    (deletedBelow : deleted < first)
    {letter : PhysicalTemplate}
    (letterMem : letter ∈
      oddHalvingAlphabet source target guessPhase firstPhase secondPhase
        validatorPhase)
    (outputLocal : LocalAt prime
      (letter.act prime
        (phaseAffine secondPhase
          (secondAutomaticState prime first guess deleted)))) :
    letter = identityZero secondPhase := by
  have forced := physicalLetter_affine_integer_source_digit_unique
    (prime := prime) (phaseCount := phaseCount)
    (actualPhase := secondPhase) (sourcePhase := letter.sourcePhase)
    (targetPhase := letter.targetPhase) (actualDigit := 0)
    (letterDigit := letter.digit)
    (preCoefficient := letter.preCoefficient)
    (postCoefficient := letter.postCoefficient)
    (postSign := letter.postSign) primeProperty primeBound secondBound
    (oddHalvingLetter_source_bound sourceBound guessBound firstBound
      secondBound validatorBound letterMem)
    (by simp [ReservedDigit]) (oddHalvingLetter_reserved letterMem)
    (halfIntegerDenominator_not_dvd prime first guess primeProperty.1)
    (secondAutomaticState_zero_residue prime first guess deleted deletedBelow)
    (secondAutomaticState_sameLine_integer prime first guess deleted
      primeProperty.1)
    (by simpa [PhysicalTemplate.act, PhysicalTemplate.matrix, phaseAffine]
      using outputLocal)
  simp [oddHalvingAlphabet, prefixAlphabet] at letterMem
  rcases letterMem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl
  · exact False.elim (secondSourceDistinct forced.1)
  · exact False.elim (secondSourceDistinct forced.1)
  · exact False.elim (secondGuessDistinct forced.1)
  · exact False.elim (secondGuessDistinct forced.1)
  · exact False.elim (secondFirstDistinct forced.1)
  · exact False.elim (secondFirstDistinct forced.1)
  · rfl
  · simp [inverseTMarker] at forced
  · exact False.elim (secondValidatorDistinct forced.1)
  · exact False.elim (secondValidatorDistinct forced.1)

/-- At the second scan's marker, the unique surviving module letter is
the marker-one handoff carrying `T⁻¹` into the validator. -/
theorem second_letter_at_marker
    {prime phaseCount source target guessPhase firstPhase secondPhase
      validatorPhase first guess : Nat}
    (primeProperty : IsPrime prime)
    (primeBound : 6 * phaseCount < prime)
    (guessPositive : 0 < guess)
    (sourceBound : source < phaseCount)
    (guessBound : guessPhase < phaseCount)
    (firstBound : firstPhase < phaseCount)
    (secondBound : secondPhase < phaseCount)
    (validatorBound : validatorPhase < phaseCount)
    (secondSourceDistinct : secondPhase ≠ source)
    (secondGuessDistinct : secondPhase ≠ guessPhase)
    (secondFirstDistinct : secondPhase ≠ firstPhase)
    (secondValidatorDistinct : secondPhase ≠ validatorPhase)
    {letter : PhysicalTemplate}
    (letterMem : letter ∈
      oddHalvingAlphabet source target guessPhase firstPhase secondPhase
        validatorPhase)
    (outputLocal : LocalAt prime
      (letter.act prime
        (phaseAffine secondPhase
          (secondAutomaticState prime first guess first)))) :
    letter = inverseTMarker secondPhase validatorPhase := by
  have forced := physicalLetter_affine_integer_source_digit_unique
    (prime := prime) (phaseCount := phaseCount)
    (actualPhase := secondPhase) (sourcePhase := letter.sourcePhase)
    (targetPhase := letter.targetPhase) (actualDigit := 1)
    (letterDigit := letter.digit)
    (preCoefficient := letter.preCoefficient)
    (postCoefficient := letter.postCoefficient)
    (postSign := letter.postSign) primeProperty primeBound secondBound
    (oddHalvingLetter_source_bound sourceBound guessBound firstBound
      secondBound validatorBound letterMem)
    (by simp [ReservedDigit]) (oddHalvingLetter_reserved letterMem)
    (halfIntegerDenominator_not_dvd prime first guess primeProperty.1)
    (secondAutomaticState_marker_residue prime first guess guessPositive)
    (secondAutomaticState_sameLine_integer prime first guess first
      primeProperty.1)
    (by simpa [PhysicalTemplate.act, PhysicalTemplate.matrix, phaseAffine]
      using outputLocal)
  simp [oddHalvingAlphabet, prefixAlphabet] at letterMem
  rcases letterMem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl
  · exact False.elim (secondSourceDistinct forced.1)
  · exact False.elim (secondSourceDistinct forced.1)
  · exact False.elim (secondGuessDistinct forced.1)
  · exact False.elim (secondGuessDistinct forced.1)
  · exact False.elim (secondFirstDistinct forced.1)
  · exact False.elim (secondFirstDistinct forced.1)
  · simp [identityZero] at forced
  · rfl
  · exact False.elim (secondValidatorDistinct forced.1)
  · exact False.elim (secondValidatorDistinct forced.1)

/-- Before the validator's first nonzero digit, locality forces its
zero-loop letter. -/
theorem validator_letter_before_marker
    {prime phaseCount source target guessPhase firstPhase secondPhase
      validatorPhase first guess deleted : Nat}
    (primeProperty : IsPrime prime)
    (primeBound : 6 * phaseCount < prime)
    (guessPositive : 0 < guess)
    (sourceBound : source < phaseCount)
    (guessBound : guessPhase < phaseCount)
    (firstBound : firstPhase < phaseCount)
    (secondBound : secondPhase < phaseCount)
    (validatorBound : validatorPhase < phaseCount)
    (validatorSourceDistinct : validatorPhase ≠ source)
    (validatorGuessDistinct : validatorPhase ≠ guessPhase)
    (validatorFirstDistinct : validatorPhase ≠ firstPhase)
    (validatorSecondDistinct : validatorPhase ≠ secondPhase)
    (deletedBelow : deleted < validatorLength first guess)
    {letter : PhysicalTemplate}
    (letterMem : letter ∈
      oddHalvingAlphabet source target guessPhase firstPhase secondPhase
        validatorPhase)
    (outputLocal : LocalAt prime
      (letter.act prime
        (phaseAffine validatorPhase
          (validatorState prime first guess deleted)))) :
    letter = identityZero validatorPhase := by
  have denominatorNotDivisible := one_add_power_not_dvd prime guess
    primeProperty.1 guessPositive
  have forced := physicalLetter_affine_integer_source_digit_unique
    (prime := prime) (phaseCount := phaseCount)
    (actualPhase := validatorPhase) (sourcePhase := letter.sourcePhase)
    (targetPhase := letter.targetPhase) (actualDigit := 0)
    (letterDigit := letter.digit)
    (preCoefficient := letter.preCoefficient)
    (postCoefficient := letter.postCoefficient)
    (postSign := letter.postSign) primeProperty primeBound validatorBound
    (oddHalvingLetter_source_bound sourceBound guessBound firstBound
      secondBound validatorBound letterMem)
    (by simp [ReservedDigit]) (oddHalvingLetter_reserved letterMem)
    denominatorNotDivisible
    (by simpa using
      validatorState_zero_residue prime first guess deleted deletedBelow)
    (validatorState_sameLine_integer prime first guess deleted
      primeProperty.1 guessPositive)
    (by simpa [PhysicalTemplate.act, PhysicalTemplate.matrix, phaseAffine]
      using outputLocal)
  simp [oddHalvingAlphabet, prefixAlphabet] at letterMem
  rcases letterMem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl
  · exact False.elim (validatorSourceDistinct forced.1)
  · exact False.elim (validatorSourceDistinct forced.1)
  · exact False.elim (validatorGuessDistinct forced.1)
  · exact False.elim (validatorGuessDistinct forced.1)
  · exact False.elim (validatorFirstDistinct forced.1)
  · exact False.elim (validatorFirstDistinct forced.1)
  · exact False.elim (validatorSecondDistinct forced.1)
  · exact False.elim (validatorSecondDistinct forced.1)
  · rfl
  · simp [validatorMarker] at forced

/-- At the validator's first nonzero digit, a letter from the entire
ten-letter module can survive only for the accepted equality `a=b-1`,
and that letter is the marker-two exit. -/
theorem validator_letter_at_marker
    {prime phaseCount source target guessPhase firstPhase secondPhase
      validatorPhase first guess : Nat}
    (primeProperty : IsPrime prime)
    (primeBound : 6 * phaseCount < prime)
    (guessPositive : 0 < guess)
    (sourceBound : source < phaseCount)
    (guessBound : guessPhase < phaseCount)
    (firstBound : firstPhase < phaseCount)
    (secondBound : secondPhase < phaseCount)
    (validatorBound : validatorPhase < phaseCount)
    (validatorSourceDistinct : validatorPhase ≠ source)
    (validatorGuessDistinct : validatorPhase ≠ guessPhase)
    (validatorFirstDistinct : validatorPhase ≠ firstPhase)
    (validatorSecondDistinct : validatorPhase ≠ secondPhase)
    {letter : PhysicalTemplate}
    (letterMem : letter ∈
      oddHalvingAlphabet source target guessPhase firstPhase secondPhase
        validatorPhase)
    (outputLocal : LocalAt prime
      (letter.act prime
        (phaseAffine validatorPhase
          (validatorState prime first guess
            (validatorLength first guess))))) :
    first = guess - 1 ∧
      letter = validatorMarker validatorPhase target := by
  have denominatorNotDivisible := one_add_power_not_dvd prime guess
    primeProperty.1 guessPositive
  have markerResidue := validatorState_marker_residue prime first guess
    guessPositive
  have forced := physicalLetter_affine_integer_source_digit_unique
    (prime := prime) (phaseCount := phaseCount)
    (actualPhase := validatorPhase) (sourcePhase := letter.sourcePhase)
    (targetPhase := letter.targetPhase)
    (actualDigit := validatorMarkerDigit first guess)
    (letterDigit := letter.digit)
    (preCoefficient := letter.preCoefficient)
    (postCoefficient := letter.postCoefficient)
    (postSign := letter.postSign) primeProperty primeBound validatorBound
    (oddHalvingLetter_source_bound sourceBound guessBound firstBound
      secondBound validatorBound letterMem)
    (by
      unfold validatorMarkerDigit ReservedDigit
      split <;> omega)
    (oddHalvingLetter_reserved letterMem) denominatorNotDivisible
    markerResidue
    (validatorState_sameLine_integer prime first guess
      (validatorLength first guess) primeProperty.1 guessPositive)
    (by simpa [PhysicalTemplate.act, PhysicalTemplate.matrix, phaseAffine]
      using outputLocal)
  simp [oddHalvingAlphabet, prefixAlphabet] at letterMem
  rcases letterMem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl
  · exact False.elim (validatorSourceDistinct forced.1)
  · exact False.elim (validatorSourceDistinct forced.1)
  · exact False.elim (validatorGuessDistinct forced.1)
  · exact False.elim (validatorGuessDistinct forced.1)
  · exact False.elim (validatorFirstDistinct forced.1)
  · exact False.elim (validatorFirstDistinct forced.1)
  · exact False.elim (validatorSecondDistinct forced.1)
  · exact False.elim (validatorSecondDistinct forced.1)
  · exfalso
    have digitEq := forced.2
    by_cases accepted : first = guess - 1
    · simp [validatorMarkerDigit, accepted, identityZero] at digitEq
    · simp [validatorMarkerDigit, accepted, identityZero] at digitEq
  · by_cases accepted : first = guess - 1
    · exact ⟨accepted, rfl⟩
    · exfalso
      have digitEq := forced.2
      simp [validatorMarkerDigit, accepted, validatorMarker] at digitEq

/-- Exact-length converse for the remainder of the first marker-one
scan. -/
theorem firstScanTail_surviving_unique
    {prime phaseCount source target guessPhase firstPhase secondPhase
      validatorPhase deleted remaining guess : Nat}
    (primeProperty : IsPrime prime)
    (primeBound : 6 * phaseCount < prime)
    (layout : PhaseLayout phaseCount source guessPhase firstPhase secondPhase
      validatorPhase)
    {word : List PhysicalTemplate}
    (wordOver : WordOver
      (oddHalvingAlphabet source target guessPhase firstPhase secondPhase
        validatorPhase) word)
    (allLocal : AllStatesLocal prime word
      (phaseAffine firstPhase
        (firstAutomaticState prime (deleted + remaining) guess deleted)))
    (lengthEq : word.length = remaining + 1) :
    word = List.replicate remaining (identityZero firstPhase) ++
      [identityMarker firstPhase secondPhase] := by
  induction remaining generalizing deleted word with
  | zero =>
      cases word with
      | nil => simp at lengthEq
      | cons letter tail =>
          have tailEmpty : tail = [] := by
            apply List.eq_nil_of_length_eq_zero
            simpa using lengthEq
          subst tail
          have letterMem := wordOver letter (by simp)
          have letterEq := first_letter_at_marker
            (first := deleted) (guess := guess) primeProperty primeBound
            layout.sourceBound layout.guessBound layout.firstBound
            layout.secondBound layout.validatorBound
            layout.sourceFirstDistinct.symm layout.guessFirstDistinct.symm
            layout.firstSecondDistinct layout.firstValidatorDistinct
            letterMem (by exact allLocal.2)
          subst letter
          simp
  | succ remaining inductionHypothesis =>
      cases word with
      | nil => simp at lengthEq
      | cons letter tail =>
          have letterMem := wordOver letter (by simp)
          have tailOver : WordOver
              (oddHalvingAlphabet source target guessPhase firstPhase
                secondPhase validatorPhase) tail := by
            intro candidate candidateMem
            exact wordOver candidate (by simp [candidateMem])
          have tailLength : tail.length = remaining + 1 := by
            simpa using lengthEq
          have letterEq := first_letter_before_marker
            (first := deleted + (remaining + 1)) (guess := guess)
            (deleted := deleted) primeProperty primeBound layout.sourceBound
            layout.guessBound layout.firstBound layout.secondBound
            layout.validatorBound layout.sourceFirstDistinct.symm
            layout.guessFirstDistinct.symm layout.firstSecondDistinct
            layout.firstValidatorDistinct (by omega) letterMem
            allLocal.2.start
          subst letter
          have firstStep := firstZero_step prime firstPhase
            (deleted + (remaining + 1)) guess deleted primeProperty.1
            (by omega)
          have canonicalLocal : LocalAt prime
              (phaseAffine firstPhase
                (firstAutomaticState prime ((deleted + 1) + remaining)
                  guess (deleted + 1))) :=
            phaseLocal
              (firstAutomaticState_local prime ((deleted + 1) + remaining)
                guess (deleted + 1) primeProperty.1)
          have canonicalAll : AllStatesLocal prime tail
              (phaseAffine firstPhase
                (firstAutomaticState prime ((deleted + 1) + remaining)
                  guess (deleted + 1))) := by
            apply AllStatesLocal.of_sameLine
              (primePositive := by have := primeProperty.1; omega)
              allLocal.2 canonicalLocal.1
            simpa only [show deleted + (remaining + 1) =
              (deleted + 1) + remaining by omega] using firstStep.symm
          have tailEq := inductionHypothesis tailOver canonicalAll tailLength
          rw [tailEq]
          simp [List.replicate_succ]

/-- Exact-length converse for the remainder of the second marker-one
scan. -/
theorem secondScanTail_surviving_unique
    {prime phaseCount source target guessPhase firstPhase secondPhase
      validatorPhase deleted remaining guess : Nat}
    (primeProperty : IsPrime prime)
    (primeBound : 6 * phaseCount < prime)
    (guessPositive : 0 < guess)
    (layout : PhaseLayout phaseCount source guessPhase firstPhase secondPhase
      validatorPhase)
    {word : List PhysicalTemplate}
    (wordOver : WordOver
      (oddHalvingAlphabet source target guessPhase firstPhase secondPhase
        validatorPhase) word)
    (allLocal : AllStatesLocal prime word
      (phaseAffine secondPhase
        (secondAutomaticState prime (deleted + remaining) guess deleted)))
    (lengthEq : word.length = remaining + 1) :
    word = List.replicate remaining (identityZero secondPhase) ++
      [inverseTMarker secondPhase validatorPhase] := by
  induction remaining generalizing deleted word with
  | zero =>
      cases word with
      | nil => simp at lengthEq
      | cons letter tail =>
          have tailEmpty : tail = [] := by
            apply List.eq_nil_of_length_eq_zero
            simpa using lengthEq
          subst tail
          have letterMem := wordOver letter (by simp)
          have letterEq := second_letter_at_marker
            (first := deleted) (guess := guess) primeProperty primeBound
            guessPositive layout.sourceBound layout.guessBound
            layout.firstBound layout.secondBound layout.validatorBound
            layout.sourceSecondDistinct.symm
            layout.guessSecondDistinct.symm
            layout.firstSecondDistinct.symm layout.secondValidatorDistinct
            letterMem (by exact allLocal.2)
          subst letter
          simp
  | succ remaining inductionHypothesis =>
      cases word with
      | nil => simp at lengthEq
      | cons letter tail =>
          have letterMem := wordOver letter (by simp)
          have tailOver : WordOver
              (oddHalvingAlphabet source target guessPhase firstPhase
                secondPhase validatorPhase) tail := by
            intro candidate candidateMem
            exact wordOver candidate (by simp [candidateMem])
          have tailLength : tail.length = remaining + 1 := by
            simpa using lengthEq
          have letterEq := second_letter_before_marker
            (first := deleted + (remaining + 1)) (guess := guess)
            (deleted := deleted) primeProperty primeBound layout.sourceBound
            layout.guessBound layout.firstBound layout.secondBound
            layout.validatorBound layout.sourceSecondDistinct.symm
            layout.guessSecondDistinct.symm layout.firstSecondDistinct.symm
            layout.secondValidatorDistinct (by omega) letterMem
            allLocal.2.start
          subst letter
          have firstStep := secondZero_step prime secondPhase
            (deleted + (remaining + 1)) guess deleted primeProperty.1
            (by omega)
          have canonicalLocal : LocalAt prime
              (phaseAffine secondPhase
                (secondAutomaticState prime ((deleted + 1) + remaining)
                  guess (deleted + 1))) :=
            phaseLocal
              (secondAutomaticState_local prime ((deleted + 1) + remaining)
                guess (deleted + 1) primeProperty.1)
          have canonicalAll : AllStatesLocal prime tail
              (phaseAffine secondPhase
                (secondAutomaticState prime ((deleted + 1) + remaining)
                  guess (deleted + 1))) := by
            apply AllStatesLocal.of_sameLine
              (primePositive := by have := primeProperty.1; omega)
              allLocal.2 canonicalLocal.1
            simpa only [show deleted + (remaining + 1) =
              (deleted + 1) + remaining by omega] using firstStep.symm
          have tailEq := inductionHypothesis tailOver canonicalAll tailLength
          rw [tailEq]
          simp [List.replicate_succ]

/-- A complete surviving validator exists only for the correct split,
and its exact word is forced. -/
theorem validatorTail_surviving_unique
    {prime phaseCount source target guessPhase firstPhase secondPhase
      validatorPhase first guess deleted remaining : Nat}
    (primeProperty : IsPrime prime)
    (primeBound : 6 * phaseCount < prime)
    (guessPositive : 0 < guess)
    (layout : PhaseLayout phaseCount source guessPhase firstPhase secondPhase
      validatorPhase)
    {word : List PhysicalTemplate}
    (wordOver : WordOver
      (oddHalvingAlphabet source target guessPhase firstPhase secondPhase
        validatorPhase) word)
    (allLocal : AllStatesLocal prime word
      (phaseAffine validatorPhase
        (validatorState prime first guess deleted)))
    (sumEq : deleted + remaining = validatorLength first guess)
    (lengthEq : word.length = remaining + 1) :
    first = guess - 1 ∧
      word = List.replicate remaining (identityZero validatorPhase) ++
        [validatorMarker validatorPhase target] := by
  induction remaining generalizing deleted word with
  | zero =>
      cases word with
      | nil => simp at lengthEq
      | cons letter tail =>
          have tailEmpty : tail = [] := by
            apply List.eq_nil_of_length_eq_zero
            simpa using lengthEq
          subst tail
          have letterMem := wordOver letter (by simp)
          have deletedEq : deleted = validatorLength first guess := by
            omega
          have classified := validator_letter_at_marker
            (first := first) (guess := guess) primeProperty primeBound
            guessPositive layout.sourceBound layout.guessBound
            layout.firstBound layout.secondBound layout.validatorBound
            layout.sourceValidatorDistinct.symm
            layout.guessValidatorDistinct.symm
            layout.firstValidatorDistinct.symm
            layout.secondValidatorDistinct.symm letterMem
            (by subst deleted; exact allLocal.2)
          rcases classified with ⟨accepted, letterEq⟩
          subst letter
          exact ⟨accepted, by simp⟩
  | succ remaining inductionHypothesis =>
      cases word with
      | nil => simp at lengthEq
      | cons letter tail =>
          have letterMem := wordOver letter (by simp)
          have tailOver : WordOver
              (oddHalvingAlphabet source target guessPhase firstPhase
                secondPhase validatorPhase) tail := by
            intro candidate candidateMem
            exact wordOver candidate (by simp [candidateMem])
          have tailLength : tail.length = remaining + 1 := by
            simpa using lengthEq
          have deletedBelow : deleted < validatorLength first guess := by
            omega
          have letterEq := validator_letter_before_marker
            (first := first) (guess := guess) (deleted := deleted)
            primeProperty primeBound guessPositive layout.sourceBound
            layout.guessBound layout.firstBound layout.secondBound
            layout.validatorBound layout.sourceValidatorDistinct.symm
            layout.guessValidatorDistinct.symm
            layout.firstValidatorDistinct.symm
            layout.secondValidatorDistinct.symm deletedBelow letterMem
            allLocal.2.start
          subst letter
          have firstStep := validatorZero_step prime validatorPhase first guess
            deleted primeProperty.1 guessPositive deletedBelow
          have canonicalLocal : LocalAt prime
              (phaseAffine validatorPhase
                (validatorState prime first guess (deleted + 1))) :=
            phaseLocal (validatorState_local prime first guess (deleted + 1)
              primeProperty.1 guessPositive)
          have canonicalAll : AllStatesLocal prime tail
              (phaseAffine validatorPhase
                (validatorState prime first guess (deleted + 1))) := by
            apply AllStatesLocal.of_sameLine
              (primePositive := by have := primeProperty.1; omega)
              allLocal.2 canonicalLocal.1 firstStep.symm
          have tailClassified := inductionHypothesis tailOver canonicalAll
            (by omega) tailLength
          rcases tailClassified with ⟨accepted, tailEq⟩
          rw [tailEq]
          exact ⟨accepted, by simp [List.replicate_succ]⟩

/-- Once the prefix guess has handed control to the first automatic
phase, a complete surviving suffix is unique and certifies the guessed
equality. -/
theorem automaticSuffix_surviving_unique
    {prime phaseCount source target guessPhase firstPhase secondPhase
      validatorPhase first guess : Nat}
    (primeProperty : IsPrime prime)
    (primeBound : 6 * phaseCount < prime)
    (guessPositive : 0 < guess)
    (layout : PhaseLayout phaseCount source guessPhase firstPhase secondPhase
      validatorPhase)
    {word : List PhysicalTemplate}
    (wordOver : WordOver
      (oddHalvingAlphabet source target guessPhase firstPhase secondPhase
        validatorPhase) word)
    (allLocal : AllStatesLocal prime word
      (phaseAffine firstPhase
        (firstAutomaticState prime first guess 0)))
    (lengthEq : word.length =
      (first + 1) + (first + 1) + (validatorLength first guess + 1)) :
    first = guess - 1 ∧
      word = firstScanWord firstPhase secondPhase first ++
        secondScanWord secondPhase validatorPhase first ++
        validatorWord validatorPhase target first := by
  have firstLengthBound : first + 1 ≤ word.length := by omega
  have firstPartLength : (word.take (first + 1)).length = first + 1 := by
    rw [List.length_take, Nat.min_eq_left firstLengthBound]
  have firstPartLocal : AllStatesLocal prime (word.take (first + 1))
      (phaseAffine firstPhase
        (firstAutomaticState prime (0 + first) guess 0)) := by
    simpa using allLocal.take (first + 1)
  have firstPartEq := firstScanTail_surviving_unique
    (deleted := 0) (remaining := first) (guess := guess) primeProperty
    primeBound layout (wordOver.take (first + 1))
    firstPartLocal firstPartLength
  have afterFirstRaw := allLocal.drop (first + 1)
  rw [firstPartEq] at afterFirstRaw
  have firstRun := firstScanWord_correct prime firstPhase secondPhase first
    guess primeProperty.1
  have secondStartLocal : LocalAt prime
      (phaseAffine secondPhase
        (secondAutomaticState prime first guess 0)) :=
    phaseLocal
      (secondAutomaticState_local prime first guess 0 primeProperty.1)
  have afterFirst : AllStatesLocal prime (word.drop (first + 1))
      (phaseAffine secondPhase
        (secondAutomaticState prime first guess 0)) := by
    apply AllStatesLocal.of_sameLine
      (primePositive := by have := primeProperty.1; omega)
      afterFirstRaw secondStartLocal.1
    simpa [firstScanWord, secondAutomaticState_zero] using firstRun.symm
  have afterFirstLength : (word.drop (first + 1)).length =
      (first + 1) + (validatorLength first guess + 1) := by
    rw [List.length_drop, lengthEq]
    omega
  have secondLengthBound : first + 1 ≤
      (word.drop (first + 1)).length := by omega
  have secondPartLength :
      ((word.drop (first + 1)).take (first + 1)).length = first + 1 := by
    rw [List.length_take, Nat.min_eq_left secondLengthBound]
  have secondPartLocal : AllStatesLocal prime
      ((word.drop (first + 1)).take (first + 1))
      (phaseAffine secondPhase
        (secondAutomaticState prime (0 + first) guess 0)) := by
    simpa using afterFirst.take (first + 1)
  have secondPartEq := secondScanTail_surviving_unique
    (deleted := 0) (remaining := first) (guess := guess) primeProperty
    primeBound guessPositive layout
    ((wordOver.drop (first + 1)).take (first + 1))
    secondPartLocal secondPartLength
  have afterSecondRaw := afterFirst.drop (first + 1)
  rw [secondPartEq] at afterSecondRaw
  have secondRun := secondScanWord_correct prime secondPhase validatorPhase
    first guess primeProperty.1 guessPositive
  have secondRun' : SameLine
      (physicalWordAction prime
        (secondScanWord secondPhase validatorPhase first)
        (phaseAffine secondPhase
          (secondAutomaticState prime first guess 0)))
      (phaseAffine validatorPhase (validatorState prime first guess 0)) := by
    simpa [validatorState_zero] using secondRun
  have validatorStartLocal : LocalAt prime
      (phaseAffine validatorPhase (validatorState prime first guess 0)) :=
    phaseLocal
      (validatorState_local prime first guess 0 primeProperty.1 guessPositive)
  have afterSecond : AllStatesLocal prime
      ((word.drop (first + 1)).drop (first + 1))
      (phaseAffine validatorPhase (validatorState prime first guess 0)) := by
    apply AllStatesLocal.of_sameLine
      (primePositive := by have := primeProperty.1; omega)
      afterSecondRaw validatorStartLocal.1 secondRun'.symm
  have validatorLengthEq :
      ((word.drop (first + 1)).drop (first + 1)).length =
        validatorLength first guess + 1 := by
    rw [List.length_drop, afterFirstLength]
    omega
  have validatorClassified := validatorTail_surviving_unique
    (first := first) (guess := guess) (deleted := 0)
    (remaining := validatorLength first guess) primeProperty primeBound
    guessPositive layout
    ((wordOver.drop (first + 1)).drop (first + 1)) afterSecond
    (by omega) validatorLengthEq
  rcases validatorClassified with ⟨accepted, validatorPartEqRaw⟩
  have validatorPartEq :
      (word.drop (first + 1)).drop (first + 1) =
        validatorWord validatorPhase target first := by
    simpa [validatorWord, validatorLength, accepted] using validatorPartEqRaw
  have firstSplit := List.take_append_drop (first + 1) word
  have secondSplit := List.take_append_drop (first + 1)
    (word.drop (first + 1))
  refine ⟨accepted, ?_⟩
  calc
    word = word.take (first + 1) ++ word.drop (first + 1) := firstSplit.symm
    _ = firstScanWord firstPhase secondPhase first ++
        word.drop (first + 1) := by rw [firstPartEq]; rfl
    _ = firstScanWord firstPhase secondPhase first ++
        ((word.drop (first + 1)).take (first + 1) ++
          (word.drop (first + 1)).drop (first + 1)) := by rw [secondSplit]
    _ = firstScanWord firstPhase secondPhase first ++
        (secondScanWord secondPhase validatorPhase first ++
          validatorWord validatorPhase target first) := by
      rw [secondPartEq, validatorPartEq]
      rfl
    _ = firstScanWord firstPhase secondPhase first ++
        secondScanWord secondPhase validatorPhase first ++
        validatorWord validatorPhase target first := by
      simp [List.append_assoc]

/-- A sufficiently long surviving word in the private guess phase must
take an exit before the unary marker.  The theorem records the exact
number of preceding loops and transports the remaining word to the
canonical post-exit state. -/
theorem guessTail_exit_of_long_word
    {prime phaseCount source target guessPhase firstPhase secondPhase
      validatorPhase counter deleted remaining : Nat}
    (primeProperty : IsPrime prime)
    (primeBound : 6 * phaseCount < prime)
    (layout : PhaseLayout phaseCount source guessPhase firstPhase secondPhase
      validatorPhase)
    {word : List PhysicalTemplate}
    (wordOver : WordOver
      (oddHalvingAlphabet source target guessPhase firstPhase secondPhase
        validatorPhase) word)
    (allLocal : AllStatesLocal prime word
      (phaseAffine guessPhase (prefixState prime counter deleted)))
    (sumEq : deleted + remaining = counter)
    (longEnough : remaining + 1 ≤ word.length) :
    ∃ loops suffix,
      loops < remaining ∧
      word = prefixTail guessPhase firstPhase loops ++ suffix ∧
      WordOver
        (oddHalvingAlphabet source target guessPhase firstPhase secondPhase
          validatorPhase) suffix ∧
      AllStatesLocal prime suffix
        (phaseAffine firstPhase
          (T prime (prefixState prime counter (deleted + loops + 1)))) := by
  induction remaining generalizing deleted word with
  | zero =>
      cases word with
      | nil => simp at longEnough
      | cons letter tail =>
          have letterMem := wordOver letter (by simp)
          have rejected := guess_rejects_marker (counter := counter)
            primeProperty primeBound layout letterMem
          have deletedEq : deleted = counter := by omega
          exact False.elim (rejected (by
            simpa only [deletedEq] using allLocal.2.start))
  | succ remaining inductionHypothesis =>
      cases word with
      | nil => simp at longEnough
      | cons letter tail =>
          have letterMem := wordOver letter (by simp)
          have tailOver : WordOver
              (oddHalvingAlphabet source target guessPhase firstPhase
                secondPhase validatorPhase) tail := by
            intro candidate candidateMem
            exact wordOver candidate (by simp [candidateMem])
          have deletedBelow : deleted < counter := by omega
          have classified := guess_letter_before_marker primeProperty
            primeBound layout deletedBelow letterMem allLocal.2.start
          rcases classified with letterEq | letterEq
          · subst letter
            have firstStep := privateLoop_step prime guessPhase counter deleted
              primeProperty.1 deletedBelow
            have nextLocal := phasePrefixState_local prime guessPhase counter
              (deleted + 1) primeProperty.1
            have tailLocal : AllStatesLocal prime tail
                (phaseAffine guessPhase
                  (prefixState prime counter (deleted + 1))) := by
              apply AllStatesLocal.of_sameLine
                (primePositive := by have := primeProperty.1; omega)
                allLocal.2 nextLocal.1 firstStep.symm
            have tailLong : remaining + 1 ≤ tail.length := by
              simpa using longEnough
            have tailChoice := inductionHypothesis tailOver tailLocal
              (by omega) tailLong
            rcases tailChoice with
              ⟨loops, suffix, loopsBound, tailEq, suffixOver, suffixLocal⟩
            refine ⟨loops + 1, suffix, by omega, ?_, suffixOver, ?_⟩
            · rw [tailEq]
              simp [prefixTail, List.replicate_succ]
            · simpa only [show deleted + 1 + loops + 1 =
                deleted + (loops + 1) + 1 by omega] using suffixLocal
          · subst letter
            have firstStep := privateExit_step prime guessPhase firstPhase
              counter deleted primeProperty.1 deletedBelow
            have exitLocal := phaseTPrefixState_local prime firstPhase counter
              (deleted + 1) primeProperty.1
            have tailLocal : AllStatesLocal prime tail
                (phaseAffine firstPhase
                  (T prime (prefixState prime counter (deleted + 1)))) := by
              apply AllStatesLocal.of_sameLine
                (primePositive := by have := primeProperty.1; omega)
                allLocal.2 exitLocal.1 firstStep.symm
            exact ⟨0, tail, by omega, by simp [prefixTail], tailOver,
              by simpa using tailLocal⟩

/-- From the source phase, every sufficiently long surviving word first
chooses one nonempty prefix.  The result exposes both the guessed length
and the remaining unary length, together with the canonical state from
which the automatic scans begin. -/
theorem prefix_choice_of_long_word
    {prime phaseCount source target guessPhase firstPhase secondPhase
      validatorPhase counter : Nat}
    (primeProperty : IsPrime prime)
    (primeBound : 6 * phaseCount < prime)
    (layout : PhaseLayout phaseCount source guessPhase firstPhase secondPhase
      validatorPhase)
    (counterPositive : 0 < counter)
    {word : List PhysicalTemplate}
    (wordOver : WordOver
      (oddHalvingAlphabet source target guessPhase firstPhase secondPhase
        validatorPhase) word)
    (allLocal : AllStatesLocal prime word
      (phaseAffine source (unaryCode prime counter)))
    (longEnough : counter + 1 ≤ word.length) :
    ∃ first guess suffix,
      0 < guess ∧ first + guess = counter ∧
      word = prefixWord source guessPhase firstPhase guess ++ suffix ∧
      WordOver
        (oddHalvingAlphabet source target guessPhase firstPhase secondPhase
          validatorPhase) suffix ∧
      AllStatesLocal prime suffix
        (phaseAffine firstPhase
          (firstAutomaticState prime first guess 0)) := by
  cases counter with
  | zero => omega
  | succ previous =>
      cases word with
      | nil => simp at longEnough
      | cons letter tail =>
          have letterMem := wordOver letter (by simp)
          have tailOver : WordOver
              (oddHalvingAlphabet source target guessPhase firstPhase
                secondPhase validatorPhase) tail := by
            intro candidate candidateMem
            exact wordOver candidate (by simp [candidateMem])
          have classified := source_letter_positive
            (counter := previous) primeProperty primeBound layout letterMem
            allLocal.2.start
          rcases classified with letterEq | letterEq
          · subst letter
            have firstStep := startContinue_step prime source guessPhase
              (previous + 1) primeProperty.1 (by omega)
            have guessStartLocal := phasePrefixState_local prime guessPhase
              (previous + 1) 1 primeProperty.1
            have tailLocal : AllStatesLocal prime tail
                (phaseAffine guessPhase
                  (prefixState prime (previous + 1) 1)) := by
              apply AllStatesLocal.of_sameLine
                (primePositive := by have := primeProperty.1; omega)
                allLocal.2 guessStartLocal.1 firstStep.symm
            have tailLong : previous + 1 ≤ tail.length := by
              simpa using longEnough
            have tailChoice := guessTail_exit_of_long_word
              (counter := previous + 1) (deleted := 1)
              (remaining := previous) primeProperty primeBound layout tailOver
              tailLocal (by omega) tailLong
            rcases tailChoice with
              ⟨loops, suffix, loopsBound, tailEq, suffixOver, suffixLocal⟩
            have splitEq :
                (previous - (loops + 1)) + (loops + 2) = previous + 1 := by
              omega
            refine ⟨previous - (loops + 1), loops + 2, suffix, by omega,
              splitEq, ?_, suffixOver, ?_⟩
            · rw [tailEq]
              simp [prefixWord, prefixTail]
            · rw [firstAutomaticState_zero prime
                (previous - (loops + 1)) (loops + 2) primeProperty.1]
              rw [splitEq]
              simpa only [show 1 + loops + 1 = loops + 2 by omega]
                using suffixLocal
          · subst letter
            have firstStep := startExit_step prime source firstPhase
              (previous + 1) primeProperty.1 (by omega)
            have exitLocal := phaseTPrefixState_local prime firstPhase
              (previous + 1) 1 primeProperty.1
            have tailLocal : AllStatesLocal prime tail
                (phaseAffine firstPhase
                  (T prime (prefixState prime (previous + 1) 1))) := by
              apply AllStatesLocal.of_sameLine
                (primePositive := by have := primeProperty.1; omega)
                allLocal.2 exitLocal.1 firstStep.symm
            refine ⟨previous, 1, tail, by omega, by omega, ?_, tailOver, ?_⟩
            · simp [prefixWord]
            · rw [firstAutomaticState_zero prime previous 1
                primeProperty.1]
              simpa using tailLocal

/-- Exact-length converse for the complete odd-halving module.  A
surviving word of the prescribed clock length exists only on an odd
input, and is literally the intended ten-letter-module execution. -/
theorem oddHalvingWord_surviving_unique
    {prime phaseCount source target guessPhase firstPhase secondPhase
      validatorPhase counter : Nat}
    (primeProperty : IsPrime prime)
    (primeBound : 6 * phaseCount < prime)
    (layout : PhaseLayout phaseCount source guessPhase firstPhase secondPhase
      validatorPhase)
    (counterPositive : 0 < counter)
    {word : List PhysicalTemplate}
    (wordOver : WordOver
      (oddHalvingAlphabet source target guessPhase firstPhase secondPhase
        validatorPhase) word)
    (allLocal : AllStatesLocal prime word
      (phaseAffine source (unaryCode prime counter)))
    (lengthEq : word.length = 2 * counter + 2) :
    ∃ first,
      counter = 2 * first + 1 ∧
      word = oddHalvingWord source target guessPhase firstPhase secondPhase
        validatorPhase first := by
  have longEnough : counter + 1 ≤ word.length := by omega
  have prefixChoice := prefix_choice_of_long_word primeProperty primeBound
    layout counterPositive wordOver allLocal longEnough
  rcases prefixChoice with
    ⟨first, guess, suffix, guessPositive, splitEq, wordEq, suffixOver,
      suffixLocal⟩
  have prefixLength := prefixWord_length
    (source := source) (privatePhase := guessPhase) (handoff := firstPhase)
    guessPositive
  have lengthSum : guess + suffix.length = 2 * counter + 2 := by
    rw [wordEq] at lengthEq
    simpa [prefixLength] using lengthEq
  have validatorBound : validatorLength first guess ≤ guess - 1 := by
    exact Nat.min_le_right _ _
  have automaticLengthBound :
      (first + 1) + (first + 1) + (validatorLength first guess + 1) ≤
        suffix.length := by
    omega
  have automaticPartLength :
      (suffix.take
        ((first + 1) + (first + 1) +
          (validatorLength first guess + 1))).length =
        (first + 1) + (first + 1) +
          (validatorLength first guess + 1) := by
    rw [List.length_take, Nat.min_eq_left automaticLengthBound]
  have automaticClassified := automaticSuffix_surviving_unique
    primeProperty primeBound guessPositive layout
    (suffixOver.take
      ((first + 1) + (first + 1) +
        (validatorLength first guess + 1)))
    (suffixLocal.take
      ((first + 1) + (first + 1) +
        (validatorLength first guess + 1))) automaticPartLength
  rcases automaticClassified with ⟨accepted, automaticPartEq⟩
  have guessEq : guess = first + 1 := by omega
  have counterEq : counter = 2 * first + 1 := by omega
  have automaticLengthEq :
      (first + 1) + (first + 1) +
          (validatorLength first guess + 1) = suffix.length := by
    simp [validatorLength, accepted]
    omega
  have suffixEq : suffix =
      firstScanWord firstPhase secondPhase first ++
        secondScanWord secondPhase validatorPhase first ++
        validatorWord validatorPhase target first := by
    rw [automaticLengthEq] at automaticPartEq
    simpa using automaticPartEq
  refine ⟨first, counterEq, ?_⟩
  rw [wordEq, suffixEq, guessEq]
  simp [oddHalvingWord, List.append_assoc]

/-- Endpoint-local unrestricted-word form of the odd-halving converse.
Any long enough ambient word over the ten-letter alphabet must begin
with the complete accepted odd-halving block. -/
theorem oddHalvingWord_forced_prefix_of_final_local
    {prime phaseCount source target guessPhase firstPhase secondPhase
      validatorPhase counter : Nat}
    (primeProperty : IsPrime prime)
    (primeBound : 6 * phaseCount < prime)
    (layout : PhaseLayout phaseCount source guessPhase firstPhase secondPhase
      validatorPhase)
    (counterPositive : 0 < counter)
    {word : List PhysicalTemplate}
    (wordOver : WordOver
      (oddHalvingAlphabet source target guessPhase firstPhase secondPhase
        validatorPhase) word)
    (finalLocal : LocalAt prime
      (physicalWordAction prime word
        (phaseAffine source (unaryCode prime counter))))
    (longEnough : 2 * counter + 2 ≤ word.length) :
    ∃ first,
      counter = 2 * first + 1 ∧
      word.take (2 * counter + 2) =
        oddHalvingWord source target guessPhase firstPhase secondPhase
          validatorPhase first := by
  have inputLocal := phaseUnaryCode_local prime source counter
    primeProperty.1
  have allLocal := allStatesLocal_of_final_local
    (by have := primeProperty.1; omega) word inputLocal.1 finalLocal
  apply oddHalvingWord_surviving_unique primeProperty primeBound layout
    counterPositive (wordOver.take (2 * counter + 2))
    (allLocal.take (2 * counter + 2))
  rw [List.length_take, Nat.min_eq_left longEnough]

end Mortality.Compiler.OddHalvingModule
