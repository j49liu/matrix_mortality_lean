import Mortality.Compiler.TernaryFrontModule
import Mortality.Compiler.RightSubtractionModule
import Mortality.Compiler.BoundaryParser

/-!
# The fourteen-letter ternary-division module

This file fuses the ternary front end with its typed regeneration scan.
The front-end exit applies `T` after negation, and the final marker of the
subtraction scan applies `T` rather than `T⁻¹`.  Thus the two constituents
use exactly fourteen physical letters and six private phases.
-/

namespace Mortality.Compiler.TernaryDivisionModule

open Mortality.PeriodicCode
open Mortality.Compiler.UnaryArithmetic
open Mortality.Compiler.IncrementModule
open Mortality.Compiler.PrefixGuessModule
open Mortality.Compiler.OddHalvingArithmetic
open Mortality.Compiler.OddHalvingModule
open Mortality.Compiler.TernaryFrontArithmetic
open Mortality.Compiler.TernaryFrontModule
open Mortality.Compiler.RightSubtractionModule

/-- The fused validator exit `T ∘ ℕ`. -/
def linkedValidatorMarker (source target : Nat) : PhysicalTemplate :=
  { sourcePhase := source
    targetPhase := target
    digit := 2
    preCoefficient := 0
    postSign := .negative
    postCoefficient := 1 }

/-- The regeneration marker applies `T`. -/
def regenerationMarker (source target : Nat) : PhysicalTemplate :=
  { sourcePhase := source
    targetPhase := target
    digit := 1
    preCoefficient := 0
    postSign := .positive
    postCoefficient := -1 }

def ternaryDivisionAlphabet (source target guessPhase firstPhase secondPhase
    thirdPhase validatorPhase handoffPhase : Nat) : List PhysicalTemplate :=
  prefixAlphabet source guessPhase firstPhase ++
    [identityZero firstPhase, identityMarker firstPhase secondPhase,
      identityZero secondPhase, identityMarker secondPhase thirdPhase,
      identityZero thirdPhase, inverseTMarker thirdPhase validatorPhase,
      identityZero validatorPhase,
      linkedValidatorMarker validatorPhase handoffPhase,
      zeroLoop handoffPhase, regenerationMarker handoffPhase target]

structure PhaseLayout (phaseCount source guessPhase firstPhase secondPhase
    thirdPhase validatorPhase handoffPhase : Nat) : Prop where
  front : TernaryFrontModule.PhaseLayout phaseCount source guessPhase
    firstPhase secondPhase thirdPhase validatorPhase
  handoffBound : handoffPhase < phaseCount
  sourceHandoffDistinct : source ≠ handoffPhase
  guessHandoffDistinct : guessPhase ≠ handoffPhase
  firstHandoffDistinct : firstPhase ≠ handoffPhase
  secondHandoffDistinct : secondPhase ≠ handoffPhase
  thirdHandoffDistinct : thirdPhase ≠ handoffPhase
  validatorHandoffDistinct : validatorPhase ≠ handoffPhase

def linkedValidatorWord (source target zeros : Nat) :
    List PhysicalTemplate :=
  List.replicate zeros (identityZero source) ++
    [linkedValidatorMarker source target]

def regenerationWord (source target zeros : Nat) : List PhysicalTemplate :=
  List.replicate zeros (zeroLoop source) ++
    [regenerationMarker source target]

def linkedFrontWord (source handoffPhase guessPhase firstPhase secondPhase
    thirdPhase validatorPhase first : Nat) : List PhysicalTemplate :=
  prefixWord source guessPhase firstPhase (2 * first + 2) ++
    plainScanWord firstPhase secondPhase first ++
    plainScanWord secondPhase thirdPhase first ++
    thirdScanWord thirdPhase validatorPhase first ++
    linkedValidatorWord validatorPhase handoffPhase first

def ternaryDivisionWord (source target guessPhase firstPhase secondPhase
    thirdPhase validatorPhase handoffPhase first : Nat) :
    List PhysicalTemplate :=
  linkedFrontWord source handoffPhase guessPhase firstPhase secondPhase
      thirdPhase validatorPhase first ++
    regenerationWord handoffPhase target first

@[simp] theorem ternaryDivisionAlphabet_length
    (source target guessPhase firstPhase secondPhase thirdPhase validatorPhase
      handoffPhase : Nat) :
    (ternaryDivisionAlphabet source target guessPhase firstPhase secondPhase
      thirdPhase validatorPhase handoffPhase).length = 14 := by
  simp [ternaryDivisionAlphabet]

@[simp] theorem linkedValidatorWord_length (source target zeros : Nat) :
    (linkedValidatorWord source target zeros).length = zeros + 1 := by
  simp [linkedValidatorWord]

@[simp] theorem regenerationWord_length (source target zeros : Nat) :
    (regenerationWord source target zeros).length = zeros + 1 := by
  simp [regenerationWord]

@[simp] theorem ternaryDivisionWord_length
    (source target guessPhase firstPhase secondPhase thirdPhase validatorPhase
      handoffPhase first : Nat) :
    (ternaryDivisionWord source target guessPhase firstPhase secondPhase
      thirdPhase validatorPhase handoffPhase first).length = 7 * first + 7 := by
  simp [ternaryDivisionWord, linkedFrontWord,
    prefixWord_length (by omega : 0 < 2 * first + 2)]
  omega

/-- On the typed diagonal instance, the regeneration scan's middle
value is `p^a`; applying `T` recovers the unary periodic code. -/
theorem ternary_regeneration_arithmetic (base first : Nat)
    (baseAtLeastTwo : 2 ≤ base) :
    T base
        (scanDigits (base : Rat) (unaryDigits first)
          (T base (twoFieldCode base first (2 * first + 1)))) =
      unaryCode base first := by
  rw [right_subtraction_middle base first (2 * first + 1) baseAtLeastTwo,
    unaryCode_eq]
  have denominatorNonzero := one_sub_pow_ne_zero base (first + 1)
    baseAtLeastTwo (by omega)
  have powerSplit : (base : Rat) ^ (2 * first + 1) =
      (base : Rat) ^ first * (base : Rat) ^ (first + 1) := by
    rw [show 2 * first + 1 = first + (first + 1) by omega]
    exact Lean.Grind.Semiring.pow_add _ _ _
  unfold T
  rw [powerSplit]
  simp only [Rat.div_def]
  have denominatorCancel := Rat.mul_inv_cancel
    ((1 : Rat) - (base : Rat) ^ (first + 1)) denominatorNonzero
  grind

theorem linkedValidatorMarker_step
    (base validatorPhase handoffPhase first : Nat)
    (baseAtLeastTwo : 2 ≤ base) :
    SameLine
      ((linkedValidatorMarker validatorPhase handoffPhase).act base
        (phaseAffine validatorPhase
          (ternaryValidatorState base first (2 * first + 2) first)))
      (phaseAffine handoffPhase
        (T base (twoFieldCode base first (2 * first + 1)))) := by
  have deletedEq := accepted_ternary_validator_delete_marker base first
    baseAtLeastTwo
  have twoFieldLocal := periodicCode_local_affine base
    (twoFieldDigits first (2 * first + 1)) baseAtLeastTwo (by
      simp [twoFieldDigits])
  have deletedLocal : LocalAt base
      (Vec2.affine (-(twoFieldCode base first (2 * first + 1)))) := by
    have negativeLocal := mutationMap_local_of_local .negative 0 twoFieldLocal
    have negativeEq : mutationMap base .negative 0
          (twoFieldCode base first (2 * first + 1)) =
        -(twoFieldCode base first (2 * first + 1)) := by
      simp [mutationMap, mutationDenominator, Sign.value, Rat.div_def]
      grind
    rw [← negativeEq]
    exact negativeLocal
  have outputEq : mutationMap base .negative 1
        (-(twoFieldCode base first (2 * first + 1))) =
      T base (twoFieldCode base first (2 * first + 1)) := by
    simp [mutationMap, mutationDenominator, Sign.value, T, Rat.div_def]
    grind
  have step := marker_step (source := validatorPhase)
    (target := handoffPhase) (digit := 2) (coefficient := 1)
    (sign := .negative)
    (value := ternaryValidatorState base first (2 * first + 2) first)
    (deleted := -(twoFieldCode base first (2 * first + 1)))
    (output := T base (twoFieldCode base first (2 * first + 1))) (by omega)
    (ternaryValidatorState_local base first (2 * first + 2) first
      baseAtLeastTwo) deletedLocal deletedEq outputEq
  simpa [linkedValidatorMarker, PhysicalTemplate.act,
    PhysicalTemplate.matrix] using step

theorem linkedValidatorTail_correct
    (base validatorPhase handoffPhase first deleted remaining : Nat)
    (baseAtLeastTwo : 2 ≤ base) (sumEq : deleted + remaining = first) :
    SameLine
      (physicalWordAction base
        (List.replicate remaining (identityZero validatorPhase) ++
          [linkedValidatorMarker validatorPhase handoffPhase])
        (phaseAffine validatorPhase
          (ternaryValidatorState base first (2 * first + 2) deleted)))
      (phaseAffine handoffPhase
        (T base (twoFieldCode base first (2 * first + 1)))) := by
  induction remaining generalizing deleted with
  | zero =>
      simpa [physicalWordAction, show deleted = first by omega] using
        linkedValidatorMarker_step base validatorPhase handoffPhase first
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
      exact physicalWordAction_cons_sameLine base (identityZero validatorPhase)
        (List.replicate remaining (identityZero validatorPhase) ++
          [linkedValidatorMarker validatorPhase handoffPhase]) firstStep
        (by simpa only [show deleted + 1 + remaining = first by omega] using
          tailRun)

theorem linkedValidatorWord_correct
    (base validatorPhase handoffPhase first : Nat)
    (baseAtLeastTwo : 2 ≤ base) :
    SameLine
      (physicalWordAction base
        (linkedValidatorWord validatorPhase handoffPhase first)
        (phaseAffine validatorPhase
          (ternaryValidatorState base first (2 * first + 2) 0)))
      (phaseAffine handoffPhase
        (T base (twoFieldCode base first (2 * first + 1)))) := by
  simpa [linkedValidatorWord] using
    linkedValidatorTail_correct base validatorPhase handoffPhase first 0 first
      baseAtLeastTwo (by omega)

theorem linkedFrontWord_correct
    (base source handoffPhase guessPhase firstPhase secondPhase thirdPhase
      validatorPhase first : Nat) (baseAtLeastTwo : 2 ≤ base) :
    SameLine
      (physicalWordAction base
        (linkedFrontWord source handoffPhase guessPhase firstPhase secondPhase
          thirdPhase validatorPhase first)
        (phaseAffine source (unaryCode base (3 * first + 2))))
      (phaseAffine handoffPhase
        (T base (twoFieldCode base first (2 * first + 1)))) := by
  have counterSplit : 3 * first + 2 = first + (2 * first + 2) := by omega
  have prefixRun := prefixWord_correct base source guessPhase firstPhase
    (3 * first + 2) (2 * first + 2) baseAtLeastTwo (by omega) (by omega)
  have prefixRun' : SameLine
      (physicalWordAction base
        (prefixWord source guessPhase firstPhase (2 * first + 2))
        (phaseAffine source (unaryCode base (3 * first + 2))))
      (phaseAffine firstPhase
        (firstAutomaticState base first (2 * first + 2) 0)) := by
    rw [firstAutomaticState_zero base first (2 * first + 2) baseAtLeastTwo]
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
  have thirdLengthEq : thirdScanLength first (2 * first + 2) = first :=
    Nat.min_eq_left (by omega)
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
  have validatorRun := linkedValidatorWord_correct base validatorPhase
    handoffPhase first baseAtLeastTwo
  have complete := physicalWordAction_append_sameLine base
    (prefixWord source guessPhase firstPhase (2 * first + 2) ++
      plainScanWord firstPhase secondPhase first ++
      plainScanWord secondPhase thirdPhase first ++
      thirdScanWord thirdPhase validatorPhase first)
    (linkedValidatorWord validatorPhase handoffPhase first) throughThird
    validatorRun
  simpa [linkedFrontWord, List.append_assoc] using complete

theorem regenerationMarker_step
    (base handoffPhase target first : Nat) (baseAtLeastTwo : 2 ≤ base) :
    SameLine
      ((regenerationMarker handoffPhase target).act base
        (phaseAffine handoffPhase
          (subtractionState base first (2 * first + 1) first)))
      (phaseAffine target (unaryCode base first)) := by
  have deletedEq := subtractionState_delete_marker base first
    (2 * first + 1) baseAtLeastTwo
  let middle : Rat :=
    ((base : Rat) ^ first - (base : Rat) ^ (2 * first + 1)) /
      (1 - (base : Rat) ^ (first + 1))
  have deletedLocal : LocalAt base (Vec2.affine middle) := by
    have denominatorNotDivisible := one_sub_power_not_dvd base (first + 1)
      baseAtLeastTwo (by omega)
    have localFraction := local_affine_integer_div
      (prime := base)
      (numerator := (base : Int) ^ first - (base : Int) ^ (2 * first + 1))
      (denominator := 1 - (base : Int) ^ (first + 1))
      denominatorNotDivisible
    simpa [middle, Rat.intCast_sub, Rat.intCast_pow, Rat.intCast_natCast]
      using localFraction
  have outputEq : mutationMap base .positive (-1) middle =
      unaryCode base first := by
    rw [← T_eq_mutationMap]
    have arithmetic := ternary_regeneration_arithmetic base first
      baseAtLeastTwo
    rw [right_subtraction_middle base first (2 * first + 1)
      baseAtLeastTwo] at arithmetic
    exact arithmetic
  have step := marker_step (source := handoffPhase) (target := target)
    (digit := 1) (coefficient := -1) (sign := .positive)
    (value := subtractionState base first (2 * first + 1) first)
    (deleted := middle) (output := unaryCode base first) (by omega)
    (subtractionState_local base first (2 * first + 1) first baseAtLeastTwo)
    deletedLocal (by simpa [middle] using deletedEq) outputEq
  simpa [regenerationMarker, PhysicalTemplate.act,
    PhysicalTemplate.matrix] using step

theorem regenerationTail_correct
    (base handoffPhase target first deleted remaining : Nat)
    (baseAtLeastTwo : 2 ≤ base) (sumEq : deleted + remaining = first) :
    SameLine
      (physicalWordAction base
        (List.replicate remaining (zeroLoop handoffPhase) ++
          [regenerationMarker handoffPhase target])
        (phaseAffine handoffPhase
          (subtractionState base first (2 * first + 1) deleted)))
      (phaseAffine target (unaryCode base first)) := by
  induction remaining generalizing deleted with
  | zero =>
      simpa [physicalWordAction, show deleted = first by omega] using
        regenerationMarker_step base handoffPhase target first baseAtLeastTwo
  | succ remaining inductionHypothesis =>
      have firstStep := zeroLoop_step base handoffPhase first
        (2 * first + 1) deleted baseAtLeastTwo (by omega)
      have tailRun := inductionHypothesis (deleted := deleted + 1) (by omega)
      exact physicalWordAction_cons_sameLine base (zeroLoop handoffPhase)
        (List.replicate remaining (zeroLoop handoffPhase) ++
          [regenerationMarker handoffPhase target]) firstStep tailRun

theorem regenerationWord_correct
    (base handoffPhase target first : Nat) (baseAtLeastTwo : 2 ≤ base) :
    SameLine
      (physicalWordAction base (regenerationWord handoffPhase target first)
        (phaseAffine handoffPhase
          (T base (twoFieldCode base first (2 * first + 1)))))
      (phaseAffine target (unaryCode base first)) := by
  rw [← subtractionState_zero base first (2 * first + 1) baseAtLeastTwo]
  simpa [regenerationWord] using
    regenerationTail_correct base handoffPhase target first 0 first
      baseAtLeastTwo (by omega)

theorem ternaryDivisionWord_correct
    (base source target guessPhase firstPhase secondPhase thirdPhase
      validatorPhase handoffPhase first : Nat) (baseAtLeastTwo : 2 ≤ base) :
    SameLine
      (physicalWordAction base
        (ternaryDivisionWord source target guessPhase firstPhase secondPhase
          thirdPhase validatorPhase handoffPhase first)
        (phaseAffine source (unaryCode base (3 * first + 2))))
      (phaseAffine target (unaryCode base first)) := by
  exact physicalWordAction_append_sameLine base
    (linkedFrontWord source handoffPhase guessPhase firstPhase secondPhase
      thirdPhase validatorPhase first)
    (regenerationWord handoffPhase target first)
    (linkedFrontWord_correct base source handoffPhase guessPhase firstPhase
      secondPhase thirdPhase validatorPhase first baseAtLeastTwo)
    (regenerationWord_correct base handoffPhase target first baseAtLeastTwo)

theorem ternaryDivisionWord_wordOver
    (source target guessPhase firstPhase secondPhase thirdPhase validatorPhase
      handoffPhase first : Nat) :
    WordOver
      (ternaryDivisionAlphabet source target guessPhase firstPhase secondPhase
        thirdPhase validatorPhase handoffPhase)
      (ternaryDivisionWord source target guessPhase firstPhase secondPhase
        thirdPhase validatorPhase handoffPhase first) := by
  let alphabet := ternaryDivisionAlphabet source target guessPhase firstPhase
    secondPhase thirdPhase validatorPhase handoffPhase
  have prefixOver : WordOver alphabet
      (prefixWord source guessPhase firstPhase (2 * first + 2)) := by
    apply (prefixWord_wordOver source guessPhase firstPhase
      (2 * first + 2)).mono
    intro letter letterMem
    simp [alphabet, ternaryDivisionAlphabet, letterMem]
  have firstOver : WordOver alphabet
      (plainScanWord firstPhase secondPhase first) := by
    intro letter letterMem
    simp [plainScanWord] at letterMem
    rcases letterMem with ⟨_, rfl⟩ | rfl <;>
      simp [alphabet, ternaryDivisionAlphabet]
  have secondOver : WordOver alphabet
      (plainScanWord secondPhase thirdPhase first) := by
    intro letter letterMem
    simp [plainScanWord] at letterMem
    rcases letterMem with ⟨_, rfl⟩ | rfl <;>
      simp [alphabet, ternaryDivisionAlphabet]
  have thirdOver : WordOver alphabet
      (thirdScanWord thirdPhase validatorPhase first) := by
    intro letter letterMem
    simp [thirdScanWord] at letterMem
    rcases letterMem with ⟨_, rfl⟩ | rfl <;>
      simp [alphabet, ternaryDivisionAlphabet]
  have validatorOver : WordOver alphabet
      (linkedValidatorWord validatorPhase handoffPhase first) := by
    intro letter letterMem
    simp [linkedValidatorWord] at letterMem
    rcases letterMem with ⟨_, rfl⟩ | rfl <;>
      simp [alphabet, ternaryDivisionAlphabet]
  have regenerationOver : WordOver alphabet
      (regenerationWord handoffPhase target first) := by
    intro letter letterMem
    simp [regenerationWord] at letterMem
    rcases letterMem with ⟨_, rfl⟩ | rfl <;>
      simp [alphabet, ternaryDivisionAlphabet]
  unfold ternaryDivisionWord linkedFrontWord
  exact wordOver_append
    (wordOver_append
      (wordOver_append
        (wordOver_append (wordOver_append prefixOver firstOver) secondOver)
        thirdOver) validatorOver) regenerationOver

/-- Complete forward obligation for the fourteen-letter module. -/
theorem ternaryDivision_execution
    (base source target guessPhase firstPhase secondPhase thirdPhase
      validatorPhase handoffPhase first : Nat) (baseAtLeastTwo : 2 ≤ base) :
    let word := ternaryDivisionWord source target guessPhase firstPhase
      secondPhase thirdPhase validatorPhase handoffPhase first
    WordOver
        (ternaryDivisionAlphabet source target guessPhase firstPhase
          secondPhase thirdPhase validatorPhase handoffPhase) word ∧
      word.length = 7 * first + 7 ∧
      SameLine
        (physicalWordAction base word
          (phaseAffine source (unaryCode base (3 * first + 2))))
        (phaseAffine target (unaryCode base first)) ∧
      AllStatesLocal base word
        (phaseAffine source (unaryCode base (3 * first + 2))) := by
  dsimp
  have action := ternaryDivisionWord_correct base source target guessPhase
    firstPhase secondPhase thirdPhase validatorPhase handoffPhase first
    baseAtLeastTwo
  have inputLocal := phaseUnaryCode_local base source (3 * first + 2)
    baseAtLeastTwo
  have outputNonzero := physicalWordAction_nonzero (prime := base) (by omega)
    (ternaryDivisionWord source target guessPhase firstPhase secondPhase
      thirdPhase validatorPhase handoffPhase first) inputLocal.1
  have outputLocal := phaseUnaryCode_local base target first baseAtLeastTwo
  have finalLocal := LocalAt.of_sameLine outputLocal outputNonzero action
  exact ⟨ternaryDivisionWord_wordOver source target guessPhase firstPhase
      secondPhase thirdPhase validatorPhase handoffPhase first,
    ternaryDivisionWord_length source target guessPhase firstPhase secondPhase
      thirdPhase validatorPhase handoffPhase first,
    action, allStatesLocal_of_final_local (by omega) _ inputLocal.1
      finalLocal⟩

private theorem divisionLetter_source_bound
    {phaseCount source target guessPhase firstPhase secondPhase thirdPhase
      validatorPhase handoffPhase : Nat} {letter : PhysicalTemplate}
    (layout : PhaseLayout phaseCount source guessPhase firstPhase secondPhase
      thirdPhase validatorPhase handoffPhase)
    (letterMem : letter ∈ ternaryDivisionAlphabet source target guessPhase
      firstPhase secondPhase thirdPhase validatorPhase handoffPhase) :
    letter.sourcePhase < phaseCount := by
  simp [ternaryDivisionAlphabet, prefixAlphabet] at letterMem
  rcases letterMem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp [startContinue, startExit, privateLoop, privateExit, identityZero,
      identityMarker, inverseTMarker, linkedValidatorMarker, zeroLoop,
      regenerationMarker, layout.front.core.sourceBound,
      layout.front.core.guessBound, layout.front.core.firstBound,
      layout.front.core.secondBound, layout.front.core.validatorBound,
      layout.front.validatorBound, layout.handoffBound]

private theorem divisionLetter_reserved
    {source target guessPhase firstPhase secondPhase thirdPhase validatorPhase
      handoffPhase : Nat} {letter : PhysicalTemplate}
    (letterMem : letter ∈ ternaryDivisionAlphabet source target guessPhase
      firstPhase secondPhase thirdPhase validatorPhase handoffPhase) :
    ReservedDigit letter.digit := by
  simp [ternaryDivisionAlphabet, prefixAlphabet] at letterMem
  rcases letterMem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp [startContinue, startExit, privateLoop, privateExit, identityZero,
      identityMarker, inverseTMarker, linkedValidatorMarker, zeroLoop,
      regenerationMarker, ReservedDigit]

private theorem regenerationState_inPhaseAt_before
    {prime handoffPhase first deleted : Nat}
    (primeProperty : IsPrime prime) (deletedBelow : deleted < first) :
    InPhaseAt prime handoffPhase 0
      (phaseAffine handoffPhase
        (subtractionState prime first (2 * first + 1) deleted)) := by
  have residue : (prime : Int) ∣
      (prime : Int) ^ (first - deleted) *
          (1 - (prime : Int) ^ (2 * first + 2)) -
        0 * (1 - (prime : Int) ^ (first + 1)) := by
    obtain ⟨factor, factorEq⟩ :=
      base_dvd_positive_power prime (first - deleted) (by omega)
    refine ⟨factor * (1 - (prime : Int) ^ (2 * first + 2)), ?_⟩
    simp only [Int.zero_mul, Int.sub_zero]
    rw [factorEq]
    grind
  apply inPhaseAt_phaseAffine_integer (by simp [ReservedDigit])
    (one_sub_power_not_dvd prime (first + 1) primeProperty.1 (by omega))
    residue
  exact subtractionState_sameLine_integer prime first (2 * first + 1)
    deleted primeProperty.1

private theorem regenerationState_inPhaseAt_marker
    {prime handoffPhase first : Nat} (primeProperty : IsPrime prime) :
    InPhaseAt prime handoffPhase 1
      (phaseAffine handoffPhase
        (subtractionState prime first (2 * first + 1) first)) := by
  have firstPower := base_dvd_positive_power prime (first + 1) (by omega)
  have secondPower := base_dvd_positive_power prime (2 * first + 2)
    (by omega)
  have residue : (prime : Int) ∣
      (prime : Int) ^ (first - first) *
          (1 - (prime : Int) ^ (2 * first + 2)) -
        1 * (1 - (prime : Int) ^ (first + 1)) := by
    simp only [Nat.sub_self, Int.pow_zero, Int.one_mul]
    obtain ⟨firstFactor, firstEq⟩ := firstPower
    obtain ⟨secondFactor, secondEq⟩ := secondPower
    refine ⟨firstFactor - secondFactor, ?_⟩
    rw [firstEq, secondEq]
    grind
  apply inPhaseAt_phaseAffine_integer (by simp [ReservedDigit])
    (one_sub_power_not_dvd prime (first + 1) primeProperty.1 (by omega))
    residue
  exact subtractionState_sameLine_integer prime first (2 * first + 1) first
    primeProperty.1

theorem regeneration_letter_before_marker
    {prime phaseCount source target guessPhase firstPhase secondPhase
      thirdPhase validatorPhase handoffPhase first deleted : Nat}
    (primeProperty : IsPrime prime) (primeBound : 6 * phaseCount < prime)
    (layout : PhaseLayout phaseCount source guessPhase firstPhase secondPhase
      thirdPhase validatorPhase handoffPhase)
    (deletedBelow : deleted < first) {letter : PhysicalTemplate}
    (letterMem : letter ∈ ternaryDivisionAlphabet source target guessPhase
      firstPhase secondPhase thirdPhase validatorPhase handoffPhase)
    (outputLocal : LocalAt prime
      (letter.act prime
        (phaseAffine handoffPhase
          (subtractionState prime first (2 * first + 1) deleted)))) :
    letter = zeroLoop handoffPhase := by
  have membership := regenerationState_inPhaseAt_before
    (handoffPhase := handoffPhase) (first := first) (deleted := deleted)
    primeProperty deletedBelow
  have forced := membership.physicalLetter_source_digit_unique primeProperty
    primeBound layout.handoffBound (divisionLetter_source_bound layout
      letterMem) (divisionLetter_reserved letterMem) (by
        simpa [PhysicalTemplate.act, PhysicalTemplate.matrix] using
          outputLocal)
  simp [ternaryDivisionAlphabet, prefixAlphabet] at letterMem
  rcases letterMem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl
  · exact False.elim (layout.sourceHandoffDistinct forced.1.symm)
  · exact False.elim (layout.sourceHandoffDistinct forced.1.symm)
  · exact False.elim (layout.guessHandoffDistinct forced.1.symm)
  · exact False.elim (layout.guessHandoffDistinct forced.1.symm)
  · exact False.elim (layout.firstHandoffDistinct forced.1.symm)
  · exact False.elim (layout.firstHandoffDistinct forced.1.symm)
  · exact False.elim (layout.secondHandoffDistinct forced.1.symm)
  · exact False.elim (layout.secondHandoffDistinct forced.1.symm)
  · exact False.elim (layout.thirdHandoffDistinct forced.1.symm)
  · exact False.elim (layout.thirdHandoffDistinct forced.1.symm)
  · exact False.elim (layout.validatorHandoffDistinct forced.1.symm)
  · exact False.elim (layout.validatorHandoffDistinct forced.1.symm)
  · rfl
  · simp [regenerationMarker] at forced

theorem regeneration_letter_at_marker
    {prime phaseCount source target guessPhase firstPhase secondPhase
      thirdPhase validatorPhase handoffPhase first : Nat}
    (primeProperty : IsPrime prime) (primeBound : 6 * phaseCount < prime)
    (layout : PhaseLayout phaseCount source guessPhase firstPhase secondPhase
      thirdPhase validatorPhase handoffPhase) {letter : PhysicalTemplate}
    (letterMem : letter ∈ ternaryDivisionAlphabet source target guessPhase
      firstPhase secondPhase thirdPhase validatorPhase handoffPhase)
    (outputLocal : LocalAt prime
      (letter.act prime
        (phaseAffine handoffPhase
          (subtractionState prime first (2 * first + 1) first)))) :
    letter = regenerationMarker handoffPhase target := by
  have membership := regenerationState_inPhaseAt_marker
    (handoffPhase := handoffPhase) (first := first) primeProperty
  have forced := membership.physicalLetter_source_digit_unique primeProperty
    primeBound layout.handoffBound (divisionLetter_source_bound layout
      letterMem) (divisionLetter_reserved letterMem) (by
        simpa [PhysicalTemplate.act, PhysicalTemplate.matrix] using
          outputLocal)
  simp [ternaryDivisionAlphabet, prefixAlphabet] at letterMem
  rcases letterMem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl
  · exact False.elim (layout.sourceHandoffDistinct forced.1.symm)
  · exact False.elim (layout.sourceHandoffDistinct forced.1.symm)
  · exact False.elim (layout.guessHandoffDistinct forced.1.symm)
  · exact False.elim (layout.guessHandoffDistinct forced.1.symm)
  · exact False.elim (layout.firstHandoffDistinct forced.1.symm)
  · exact False.elim (layout.firstHandoffDistinct forced.1.symm)
  · exact False.elim (layout.secondHandoffDistinct forced.1.symm)
  · exact False.elim (layout.secondHandoffDistinct forced.1.symm)
  · exact False.elim (layout.thirdHandoffDistinct forced.1.symm)
  · exact False.elim (layout.thirdHandoffDistinct forced.1.symm)
  · exact False.elim (layout.validatorHandoffDistinct forced.1.symm)
  · exact False.elim (layout.validatorHandoffDistinct forced.1.symm)
  · simp [zeroLoop] at forced
  · rfl

/-- A completed path cannot stop in the regeneration phase.  The exact
zero block and final marker are forced, and the remaining word starts at
the regenerated unary code. -/
theorem regenerationTail_forced_prefix_to_endpoint
    {prime phaseCount source target guessPhase firstPhase secondPhase
      thirdPhase validatorPhase handoffPhase endpointPhase : Nat}
    {endpointDigit : Int} {endpoint : Vec2}
    (primeProperty : IsPrime prime) (primeBound : 6 * phaseCount < prime)
    (layout : PhaseLayout phaseCount source guessPhase firstPhase secondPhase
      thirdPhase validatorPhase handoffPhase)
    (endpointBound : endpointPhase < phaseCount)
    (handoffEndpointDistinct : handoffPhase ≠ endpointPhase)
    (endpointMembership : InPhaseAt prime endpointPhase endpointDigit endpoint)
    {first deleted remaining : Nat} (sumEq : deleted + remaining = first)
    {word : List PhysicalTemplate}
    (wordOver : WordOver
      (ternaryDivisionAlphabet source target guessPhase firstPhase secondPhase
        thirdPhase validatorPhase handoffPhase) word)
    (allLocal : AllStatesLocal prime word
      (phaseAffine handoffPhase
        (subtractionState prime first (2 * first + 1) deleted)))
    (completeRun : SameLine
      (physicalWordAction prime word
        (phaseAffine handoffPhase
          (subtractionState prime first (2 * first + 1) deleted))) endpoint) :
    ∃ suffix,
      word = List.replicate remaining (zeroLoop handoffPhase) ++
          [regenerationMarker handoffPhase target] ++ suffix ∧
      WordOver
        (ternaryDivisionAlphabet source target guessPhase firstPhase
          secondPhase thirdPhase validatorPhase handoffPhase) suffix ∧
      AllStatesLocal prime suffix
        (phaseAffine target (unaryCode prime first)) ∧
      SameLine
        (physicalWordAction prime suffix
          (phaseAffine target (unaryCode prime first))) endpoint := by
  induction remaining generalizing deleted word with
  | zero =>
      have deletedEq : deleted = first := by omega
      have currentMembership := regenerationState_inPhaseAt_marker
        (handoffPhase := handoffPhase) (first := first) primeProperty
      have wordNonempty : word ≠ [] := by
        intro wordEmpty
        subst word
        have phasesEq := (currentMembership.unique primeProperty primeBound
          layout.handoffBound endpointBound endpointMembership (by
            simpa only [physicalWordAction, deletedEq] using completeRun)).1
        exact handoffEndpointDistinct phasesEq
      cases word with
      | nil => exact False.elim (wordNonempty rfl)
      | cons letter tail =>
          have letterMem := wordOver letter (by simp)
          have tailOver : WordOver
              (ternaryDivisionAlphabet source target guessPhase firstPhase
                secondPhase thirdPhase validatorPhase handoffPhase) tail := by
            intro candidate candidateMem
            exact wordOver candidate (by simp [candidateMem])
          have letterEq := regeneration_letter_at_marker
            (first := first) primeProperty primeBound layout letterMem
            (by simpa only [deletedEq] using allLocal.2.start)
          subst letter
          have firstStep := regenerationMarker_step prime handoffPhase target
            first primeProperty.1
          have canonicalLocal := phaseUnaryCode_local prime target first
            primeProperty.1
          have tailLocal : AllStatesLocal prime tail
              (phaseAffine target (unaryCode prime first)) := by
            apply AllStatesLocal.of_sameLine
              (primePositive := by have := primeProperty.1; omega)
              allLocal.2 canonicalLocal.1
            simpa only [deletedEq] using firstStep.symm
          have tailRun : SameLine
              (physicalWordAction prime tail
                (phaseAffine target (unaryCode prime first))) endpoint := by
            apply physicalWordAction_tail_sameLine prime
              (regenerationMarker handoffPhase target) tail
                (completeRun := by simpa only [deletedEq] using completeRun)
            simpa only [deletedEq] using firstStep
          exact ⟨tail, by simp, tailOver, tailLocal, tailRun⟩
  | succ remaining inductionHypothesis =>
      have deletedBelow : deleted < first := by omega
      have currentMembership := regenerationState_inPhaseAt_before
        (handoffPhase := handoffPhase) (first := first) (deleted := deleted)
        primeProperty deletedBelow
      have wordNonempty : word ≠ [] := by
        intro wordEmpty
        subst word
        have phasesEq := (currentMembership.unique primeProperty primeBound
          layout.handoffBound endpointBound endpointMembership (by
            simpa only [physicalWordAction] using completeRun)).1
        exact handoffEndpointDistinct phasesEq
      cases word with
      | nil => exact False.elim (wordNonempty rfl)
      | cons letter tail =>
          have letterMem := wordOver letter (by simp)
          have tailOver : WordOver
              (ternaryDivisionAlphabet source target guessPhase firstPhase
                secondPhase thirdPhase validatorPhase handoffPhase) tail := by
            intro candidate candidateMem
            exact wordOver candidate (by simp [candidateMem])
          have letterEq := regeneration_letter_before_marker
            (first := first) (deleted := deleted) primeProperty primeBound
            layout deletedBelow letterMem allLocal.2.start
          subst letter
          have firstStep := zeroLoop_step prime handoffPhase first
            (2 * first + 1) deleted primeProperty.1 deletedBelow
          have canonicalLocal := phaseSubtractionState_local prime
            handoffPhase first (2 * first + 1) (deleted + 1)
            primeProperty.1
          have tailLocal : AllStatesLocal prime tail
              (phaseAffine handoffPhase
                (subtractionState prime first (2 * first + 1)
                  (deleted + 1))) := by
            apply AllStatesLocal.of_sameLine
              (primePositive := by have := primeProperty.1; omega)
              allLocal.2 canonicalLocal.1 firstStep.symm
          have tailRun : SameLine
              (physicalWordAction prime tail
                (phaseAffine handoffPhase
                  (subtractionState prime first (2 * first + 1)
                    (deleted + 1)))) endpoint :=
            physicalWordAction_tail_sameLine prime (zeroLoop handoffPhase)
              tail firstStep completeRun
          obtain ⟨suffix, tailEq, suffixOver, suffixLocal, suffixRun⟩ :=
            inductionHypothesis (deleted := deleted + 1) (by omega) tailOver
              tailLocal tailRun
          refine ⟨suffix, ?_, suffixOver, suffixLocal, suffixRun⟩
          rw [tailEq]
          simp [List.replicate_succ]

private theorem divisionLetter_source_digit_unique
    {prime phaseCount source target guessPhase firstPhase secondPhase
      thirdPhase validatorPhase handoffPhase actualPhase : Nat}
    {actualDigit : Int} {state : Vec2} {letter : PhysicalTemplate}
    (primeProperty : IsPrime prime) (primeBound : 6 * phaseCount < prime)
    (layout : PhaseLayout phaseCount source guessPhase firstPhase secondPhase
      thirdPhase validatorPhase handoffPhase)
    (actualBound : actualPhase < phaseCount)
    (membership : InPhaseAt prime actualPhase actualDigit state)
    (letterMem : letter ∈ ternaryDivisionAlphabet source target guessPhase
      firstPhase secondPhase thirdPhase validatorPhase handoffPhase)
    (outputLocal : LocalAt prime (letter.act prime state)) :
    actualPhase = letter.sourcePhase ∧ actualDigit = letter.digit := by
  apply membership.physicalLetter_source_digit_unique primeProperty
    primeBound actualBound (divisionLetter_source_bound layout letterMem)
    (divisionLetter_reserved letterMem)
  simpa [PhysicalTemplate.act, PhysicalTemplate.matrix] using outputLocal

theorem source_letter_positive
    {prime phaseCount source target guessPhase firstPhase secondPhase
      thirdPhase validatorPhase handoffPhase counter : Nat}
    (primeProperty : IsPrime prime) (primeBound : 6 * phaseCount < prime)
    (layout : PhaseLayout phaseCount source guessPhase firstPhase secondPhase
      thirdPhase validatorPhase handoffPhase) {letter : PhysicalTemplate}
    (letterMem : letter ∈ ternaryDivisionAlphabet source target guessPhase
      firstPhase secondPhase thirdPhase validatorPhase handoffPhase)
    (outputLocal : LocalAt prime
      (letter.act prime
        (phaseAffine source (unaryCode prime (counter + 1))))) :
    letter = startContinue source guessPhase ∨
      letter = startExit source firstPhase := by
  have membership := sourceState_inPhaseAt_positive
    (prime := prime) (source := source) (counter := counter + 1)
    primeProperty (by omega)
  have forced := divisionLetter_source_digit_unique primeProperty primeBound
    layout layout.front.core.sourceBound membership letterMem outputLocal
  simp [ternaryDivisionAlphabet, prefixAlphabet] at letterMem
  rcases letterMem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl
  · exact Or.inl rfl
  · exact Or.inr rfl
  · exact False.elim (layout.front.core.sourceGuessDistinct forced.1)
  · exact False.elim (layout.front.core.sourceGuessDistinct forced.1)
  · exact False.elim (layout.front.core.sourceFirstDistinct forced.1)
  · exact False.elim (layout.front.core.sourceFirstDistinct forced.1)
  · exact False.elim (layout.front.core.sourceSecondDistinct forced.1)
  · exact False.elim (layout.front.core.sourceSecondDistinct forced.1)
  · exact False.elim (layout.front.core.sourceValidatorDistinct forced.1)
  · exact False.elim (layout.front.core.sourceValidatorDistinct forced.1)
  · exact False.elim (layout.front.sourceValidatorDistinct forced.1)
  · exact False.elim (layout.front.sourceValidatorDistinct forced.1)
  · exact False.elim (layout.sourceHandoffDistinct forced.1)
  · exact False.elim (layout.sourceHandoffDistinct forced.1)

theorem source_rejects_zero
    {prime phaseCount source target guessPhase firstPhase secondPhase
      thirdPhase validatorPhase handoffPhase : Nat}
    (primeProperty : IsPrime prime) (primeBound : 6 * phaseCount < prime)
    (layout : PhaseLayout phaseCount source guessPhase firstPhase secondPhase
      thirdPhase validatorPhase handoffPhase) {letter : PhysicalTemplate}
    (letterMem : letter ∈ ternaryDivisionAlphabet source target guessPhase
      firstPhase secondPhase thirdPhase validatorPhase handoffPhase) :
    ¬LocalAt prime
      (letter.act prime (phaseAffine source (unaryCode prime 0))) := by
  intro outputLocal
  have membership : InPhaseAt prime source 1
      (phaseAffine source (unaryCode prime 0)) := by
    simpa [unaryCode, unaryDigits] using
      (periodicCode_inPhaseAt prime source 1 [] primeProperty.1
        (by simp [ReservedDigit]))
  have forced := divisionLetter_source_digit_unique primeProperty primeBound
    layout layout.front.core.sourceBound membership letterMem outputLocal
  simp [ternaryDivisionAlphabet, prefixAlphabet] at letterMem
  rcases letterMem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl
  · simp [startContinue] at forced
  · simp [startExit] at forced
  · exact layout.front.core.sourceGuessDistinct forced.1
  · exact layout.front.core.sourceGuessDistinct forced.1
  · exact layout.front.core.sourceFirstDistinct forced.1
  · exact layout.front.core.sourceFirstDistinct forced.1
  · exact layout.front.core.sourceSecondDistinct forced.1
  · exact layout.front.core.sourceSecondDistinct forced.1
  · exact layout.front.core.sourceValidatorDistinct forced.1
  · exact layout.front.core.sourceValidatorDistinct forced.1
  · exact layout.front.sourceValidatorDistinct forced.1
  · exact layout.front.sourceValidatorDistinct forced.1
  · exact layout.sourceHandoffDistinct forced.1
  · exact layout.sourceHandoffDistinct forced.1

theorem guess_letter_before_marker
    {prime phaseCount source target guessPhase firstPhase secondPhase
      thirdPhase validatorPhase handoffPhase counter deleted : Nat}
    (primeProperty : IsPrime prime) (primeBound : 6 * phaseCount < prime)
    (layout : PhaseLayout phaseCount source guessPhase firstPhase secondPhase
      thirdPhase validatorPhase handoffPhase) (deletedBelow : deleted < counter)
    {letter : PhysicalTemplate}
    (letterMem : letter ∈ ternaryDivisionAlphabet source target guessPhase
      firstPhase secondPhase thirdPhase validatorPhase handoffPhase)
    (outputLocal : LocalAt prime
      (letter.act prime
        (phaseAffine guessPhase (prefixState prime counter deleted)))) :
    letter = privateLoop guessPhase ∨
      letter = privateExit guessPhase firstPhase := by
  have membership := guessState_inPhaseAt_before
    (guessPhase := guessPhase) (counter := counter) (deleted := deleted)
    primeProperty deletedBelow
  have forced := divisionLetter_source_digit_unique primeProperty primeBound
    layout layout.front.core.guessBound membership letterMem outputLocal
  simp [ternaryDivisionAlphabet, prefixAlphabet] at letterMem
  rcases letterMem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl
  · exact False.elim (layout.front.core.sourceGuessDistinct forced.1.symm)
  · exact False.elim (layout.front.core.sourceGuessDistinct forced.1.symm)
  · exact Or.inl rfl
  · exact Or.inr rfl
  · exact False.elim (layout.front.core.guessFirstDistinct forced.1)
  · exact False.elim (layout.front.core.guessFirstDistinct forced.1)
  · exact False.elim (layout.front.core.guessSecondDistinct forced.1)
  · exact False.elim (layout.front.core.guessSecondDistinct forced.1)
  · exact False.elim (layout.front.core.guessValidatorDistinct forced.1)
  · exact False.elim (layout.front.core.guessValidatorDistinct forced.1)
  · exact False.elim (layout.front.guessValidatorDistinct forced.1)
  · exact False.elim (layout.front.guessValidatorDistinct forced.1)
  · exact False.elim (layout.guessHandoffDistinct forced.1)
  · exact False.elim (layout.guessHandoffDistinct forced.1)

theorem guess_rejects_marker
    {prime phaseCount source target guessPhase firstPhase secondPhase
      thirdPhase validatorPhase handoffPhase counter : Nat}
    (primeProperty : IsPrime prime) (primeBound : 6 * phaseCount < prime)
    (layout : PhaseLayout phaseCount source guessPhase firstPhase secondPhase
      thirdPhase validatorPhase handoffPhase) {letter : PhysicalTemplate}
    (letterMem : letter ∈ ternaryDivisionAlphabet source target guessPhase
      firstPhase secondPhase thirdPhase validatorPhase handoffPhase) :
    ¬LocalAt prime
      (letter.act prime
        (phaseAffine guessPhase (prefixState prime counter counter))) := by
  intro outputLocal
  have membership := guessState_inPhaseAt_marker
    (guessPhase := guessPhase) (counter := counter) primeProperty
  have forced := divisionLetter_source_digit_unique primeProperty primeBound
    layout layout.front.core.guessBound membership letterMem outputLocal
  simp [ternaryDivisionAlphabet, prefixAlphabet] at letterMem
  rcases letterMem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl
  · exact layout.front.core.sourceGuessDistinct forced.1.symm
  · exact layout.front.core.sourceGuessDistinct forced.1.symm
  · simp [privateLoop] at forced
  · simp [privateExit] at forced
  · exact layout.front.core.guessFirstDistinct forced.1
  · exact layout.front.core.guessFirstDistinct forced.1
  · exact layout.front.core.guessSecondDistinct forced.1
  · exact layout.front.core.guessSecondDistinct forced.1
  · exact layout.front.core.guessValidatorDistinct forced.1
  · exact layout.front.core.guessValidatorDistinct forced.1
  · exact layout.front.guessValidatorDistinct forced.1
  · exact layout.front.guessValidatorDistinct forced.1
  · exact layout.guessHandoffDistinct forced.1
  · exact layout.guessHandoffDistinct forced.1

private theorem first_letter_cases
    {prime phaseCount source target guessPhase firstPhase secondPhase
      thirdPhase validatorPhase handoffPhase : Nat}
    {actualDigit : Int} {state : Vec2} {letter : PhysicalTemplate}
    (primeProperty : IsPrime prime) (primeBound : 6 * phaseCount < prime)
    (layout : PhaseLayout phaseCount source guessPhase firstPhase secondPhase
      thirdPhase validatorPhase handoffPhase)
    (membership : InPhaseAt prime firstPhase actualDigit state)
    (letterMem : letter ∈ ternaryDivisionAlphabet source target guessPhase
      firstPhase secondPhase thirdPhase validatorPhase handoffPhase)
    (outputLocal : LocalAt prime (letter.act prime state)) :
    (letter = identityZero firstPhase ∧ actualDigit = 0) ∨
      (letter = identityMarker firstPhase secondPhase ∧ actualDigit = 1) := by
  have forced := divisionLetter_source_digit_unique primeProperty primeBound
    layout layout.front.core.firstBound membership letterMem outputLocal
  simp [ternaryDivisionAlphabet, prefixAlphabet] at letterMem
  rcases letterMem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl
  · exact False.elim (layout.front.core.sourceFirstDistinct forced.1.symm)
  · exact False.elim (layout.front.core.sourceFirstDistinct forced.1.symm)
  · exact False.elim (layout.front.core.guessFirstDistinct forced.1.symm)
  · exact False.elim (layout.front.core.guessFirstDistinct forced.1.symm)
  · exact Or.inl ⟨rfl, by simpa [identityZero] using forced.2⟩
  · exact Or.inr ⟨rfl, by simpa [identityMarker] using forced.2⟩
  · exact False.elim (layout.front.core.firstSecondDistinct forced.1)
  · exact False.elim (layout.front.core.firstSecondDistinct forced.1)
  · exact False.elim (layout.front.core.firstValidatorDistinct forced.1)
  · exact False.elim (layout.front.core.firstValidatorDistinct forced.1)
  · exact False.elim (layout.front.firstValidatorDistinct forced.1)
  · exact False.elim (layout.front.firstValidatorDistinct forced.1)
  · exact False.elim (layout.firstHandoffDistinct forced.1)
  · exact False.elim (layout.firstHandoffDistinct forced.1)

theorem first_letter_before_marker
    {prime phaseCount source target guessPhase firstPhase secondPhase
      thirdPhase validatorPhase handoffPhase first guess deleted : Nat}
    (primeProperty : IsPrime prime) (primeBound : 6 * phaseCount < prime)
    (layout : PhaseLayout phaseCount source guessPhase firstPhase secondPhase
      thirdPhase validatorPhase handoffPhase) (deletedBelow : deleted < first)
    {letter : PhysicalTemplate}
    (letterMem : letter ∈ ternaryDivisionAlphabet source target guessPhase
      firstPhase secondPhase thirdPhase validatorPhase handoffPhase)
    (outputLocal : LocalAt prime
      (letter.act prime (phaseAffine firstPhase
        (firstAutomaticState prime first guess deleted)))) :
    letter = identityZero firstPhase := by
  have membership := firstState_inPhaseAt_before
    (firstPhase := firstPhase) (first := first) (guess := guess)
    (deleted := deleted) primeProperty deletedBelow
  rcases first_letter_cases primeProperty primeBound layout membership
    letterMem outputLocal with firstCase | markerCase
  · exact firstCase.1
  · omega

theorem first_letter_at_marker
    {prime phaseCount source target guessPhase firstPhase secondPhase
      thirdPhase validatorPhase handoffPhase first guess : Nat}
    (primeProperty : IsPrime prime) (primeBound : 6 * phaseCount < prime)
    (layout : PhaseLayout phaseCount source guessPhase firstPhase secondPhase
      thirdPhase validatorPhase handoffPhase) {letter : PhysicalTemplate}
    (letterMem : letter ∈ ternaryDivisionAlphabet source target guessPhase
      firstPhase secondPhase thirdPhase validatorPhase handoffPhase)
    (outputLocal : LocalAt prime
      (letter.act prime (phaseAffine firstPhase
        (firstAutomaticState prime first guess first)))) :
    letter = identityMarker firstPhase secondPhase := by
  have membership := firstState_inPhaseAt_marker
    (firstPhase := firstPhase) (first := first) (guess := guess) primeProperty
  rcases first_letter_cases primeProperty primeBound layout membership
    letterMem outputLocal with firstCase | markerCase
  · omega
  · exact markerCase.1

private theorem second_letter_cases
    {prime phaseCount source target guessPhase firstPhase secondPhase
      thirdPhase validatorPhase handoffPhase : Nat}
    {actualDigit : Int} {state : Vec2} {letter : PhysicalTemplate}
    (primeProperty : IsPrime prime) (primeBound : 6 * phaseCount < prime)
    (layout : PhaseLayout phaseCount source guessPhase firstPhase secondPhase
      thirdPhase validatorPhase handoffPhase)
    (membership : InPhaseAt prime secondPhase actualDigit state)
    (letterMem : letter ∈ ternaryDivisionAlphabet source target guessPhase
      firstPhase secondPhase thirdPhase validatorPhase handoffPhase)
    (outputLocal : LocalAt prime (letter.act prime state)) :
    (letter = identityZero secondPhase ∧ actualDigit = 0) ∨
      (letter = identityMarker secondPhase thirdPhase ∧ actualDigit = 1) := by
  have forced := divisionLetter_source_digit_unique primeProperty primeBound
    layout layout.front.core.secondBound membership letterMem outputLocal
  simp [ternaryDivisionAlphabet, prefixAlphabet] at letterMem
  rcases letterMem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl
  · exact False.elim (layout.front.core.sourceSecondDistinct forced.1.symm)
  · exact False.elim (layout.front.core.sourceSecondDistinct forced.1.symm)
  · exact False.elim (layout.front.core.guessSecondDistinct forced.1.symm)
  · exact False.elim (layout.front.core.guessSecondDistinct forced.1.symm)
  · exact False.elim (layout.front.core.firstSecondDistinct forced.1.symm)
  · exact False.elim (layout.front.core.firstSecondDistinct forced.1.symm)
  · exact Or.inl ⟨rfl, by simpa [identityZero] using forced.2⟩
  · exact Or.inr ⟨rfl, by simpa [identityMarker] using forced.2⟩
  · exact False.elim (layout.front.core.secondValidatorDistinct forced.1)
  · exact False.elim (layout.front.core.secondValidatorDistinct forced.1)
  · exact False.elim (layout.front.secondValidatorDistinct forced.1)
  · exact False.elim (layout.front.secondValidatorDistinct forced.1)
  · exact False.elim (layout.secondHandoffDistinct forced.1)
  · exact False.elim (layout.secondHandoffDistinct forced.1)

theorem second_letter_before_marker
    {prime phaseCount source target guessPhase firstPhase secondPhase
      thirdPhase validatorPhase handoffPhase first guess deleted : Nat}
    (primeProperty : IsPrime prime) (primeBound : 6 * phaseCount < prime)
    (layout : PhaseLayout phaseCount source guessPhase firstPhase secondPhase
      thirdPhase validatorPhase handoffPhase) (deletedBelow : deleted < first)
    {letter : PhysicalTemplate}
    (letterMem : letter ∈ ternaryDivisionAlphabet source target guessPhase
      firstPhase secondPhase thirdPhase validatorPhase handoffPhase)
    (outputLocal : LocalAt prime
      (letter.act prime (phaseAffine secondPhase
        (secondAutomaticState prime first guess deleted)))) :
    letter = identityZero secondPhase := by
  have membership := secondState_inPhaseAt_before
    (secondPhase := secondPhase) (first := first) (guess := guess)
    (deleted := deleted) primeProperty deletedBelow
  rcases second_letter_cases primeProperty primeBound layout membership
    letterMem outputLocal with zeroCase | markerCase
  · exact zeroCase.1
  · omega

theorem second_letter_at_marker
    {prime phaseCount source target guessPhase firstPhase secondPhase
      thirdPhase validatorPhase handoffPhase first guess : Nat}
    (primeProperty : IsPrime prime) (primeBound : 6 * phaseCount < prime)
    (guessPositive : 0 < guess)
    (layout : PhaseLayout phaseCount source guessPhase firstPhase secondPhase
      thirdPhase validatorPhase handoffPhase) {letter : PhysicalTemplate}
    (letterMem : letter ∈ ternaryDivisionAlphabet source target guessPhase
      firstPhase secondPhase thirdPhase validatorPhase handoffPhase)
    (outputLocal : LocalAt prime
      (letter.act prime (phaseAffine secondPhase
        (secondAutomaticState prime first guess first)))) :
    letter = identityMarker secondPhase thirdPhase := by
  have membership := secondState_inPhaseAt_marker
    (secondPhase := secondPhase) (first := first) (guess := guess)
    primeProperty guessPositive
  rcases second_letter_cases primeProperty primeBound layout membership
    letterMem outputLocal with zeroCase | markerCase
  · omega
  · exact markerCase.1

private theorem third_letter_cases
    {prime phaseCount source target guessPhase firstPhase secondPhase
      thirdPhase validatorPhase handoffPhase : Nat}
    {actualDigit : Int} {state : Vec2} {letter : PhysicalTemplate}
    (primeProperty : IsPrime prime) (primeBound : 6 * phaseCount < prime)
    (layout : PhaseLayout phaseCount source guessPhase firstPhase secondPhase
      thirdPhase validatorPhase handoffPhase)
    (membership : InPhaseAt prime thirdPhase actualDigit state)
    (letterMem : letter ∈ ternaryDivisionAlphabet source target guessPhase
      firstPhase secondPhase thirdPhase validatorPhase handoffPhase)
    (outputLocal : LocalAt prime (letter.act prime state)) :
    (letter = identityZero thirdPhase ∧ actualDigit = 0) ∨
      (letter = inverseTMarker thirdPhase validatorPhase ∧
        actualDigit = 1) := by
  have forced := divisionLetter_source_digit_unique primeProperty primeBound
    layout layout.front.core.validatorBound membership letterMem outputLocal
  simp [ternaryDivisionAlphabet, prefixAlphabet] at letterMem
  rcases letterMem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl
  · exact False.elim
      (layout.front.core.sourceValidatorDistinct forced.1.symm)
  · exact False.elim
      (layout.front.core.sourceValidatorDistinct forced.1.symm)
  · exact False.elim
      (layout.front.core.guessValidatorDistinct forced.1.symm)
  · exact False.elim
      (layout.front.core.guessValidatorDistinct forced.1.symm)
  · exact False.elim
      (layout.front.core.firstValidatorDistinct forced.1.symm)
  · exact False.elim
      (layout.front.core.firstValidatorDistinct forced.1.symm)
  · exact False.elim
      (layout.front.core.secondValidatorDistinct forced.1.symm)
  · exact False.elim
      (layout.front.core.secondValidatorDistinct forced.1.symm)
  · exact Or.inl ⟨rfl, by simpa [identityZero] using forced.2⟩
  · exact Or.inr ⟨rfl, by simpa [inverseTMarker] using forced.2⟩
  · exact False.elim (layout.front.thirdValidatorDistinct forced.1)
  · exact False.elim (layout.front.thirdValidatorDistinct forced.1)
  · exact False.elim (layout.thirdHandoffDistinct forced.1)
  · exact False.elim (layout.thirdHandoffDistinct forced.1)

theorem third_letter_before_marker
    {prime phaseCount source target guessPhase firstPhase secondPhase
      thirdPhase validatorPhase handoffPhase first guess deleted : Nat}
    (primeProperty : IsPrime prime) (primeBound : 6 * phaseCount < prime)
    (layout : PhaseLayout phaseCount source guessPhase firstPhase secondPhase
      thirdPhase validatorPhase handoffPhase)
    (deletedBelow : deleted < thirdScanLength first guess)
    {letter : PhysicalTemplate}
    (letterMem : letter ∈ ternaryDivisionAlphabet source target guessPhase
      firstPhase secondPhase thirdPhase validatorPhase handoffPhase)
    (outputLocal : LocalAt prime
      (letter.act prime (phaseAffine thirdPhase
        (thirdAutomaticState prime first guess deleted)))) :
    letter = identityZero thirdPhase := by
  have membership := thirdState_inPhaseAt_before
    (thirdPhase := thirdPhase) (first := first) (guess := guess)
    (deleted := deleted) primeProperty deletedBelow
  rcases third_letter_cases primeProperty primeBound layout membership
    letterMem outputLocal with zeroCase | markerCase
  · exact zeroCase.1
  · omega

theorem third_letter_at_marker
    {prime phaseCount source target guessPhase firstPhase secondPhase
      thirdPhase validatorPhase handoffPhase first guess : Nat}
    (primeProperty : IsPrime prime) (primeBound : 6 * phaseCount < prime)
    (guessPositive : 0 < guess)
    (layout : PhaseLayout phaseCount source guessPhase firstPhase secondPhase
      thirdPhase validatorPhase handoffPhase) {letter : PhysicalTemplate}
    (letterMem : letter ∈ ternaryDivisionAlphabet source target guessPhase
      firstPhase secondPhase thirdPhase validatorPhase handoffPhase)
    (outputLocal : LocalAt prime
      (letter.act prime (phaseAffine thirdPhase
        (thirdAutomaticState prime first guess
          (thirdScanLength first guess))))) :
    first ≠ guess - 1 ∧
      letter = inverseTMarker thirdPhase validatorPhase := by
  have membership := thirdState_inPhaseAt_marker
    (thirdPhase := thirdPhase) (first := first) (guess := guess)
    primeProperty guessPositive
  rcases third_letter_cases primeProperty primeBound layout membership
    letterMem outputLocal with zeroCase | markerCase
  · have digitEq := zeroCase.2
    unfold thirdMarkerDigit at digitEq
    split at digitEq <;> omega
  · by_cases middle : first = guess - 1
    · have digitEq := markerCase.2
      simp [thirdMarkerDigit, middle] at digitEq
    · exact ⟨middle, markerCase.1⟩

private theorem validator_letter_cases
    {prime phaseCount source target guessPhase firstPhase secondPhase
      thirdPhase validatorPhase handoffPhase : Nat}
    {actualDigit : Int} {state : Vec2} {letter : PhysicalTemplate}
    (primeProperty : IsPrime prime) (primeBound : 6 * phaseCount < prime)
    (layout : PhaseLayout phaseCount source guessPhase firstPhase secondPhase
      thirdPhase validatorPhase handoffPhase)
    (membership : InPhaseAt prime validatorPhase actualDigit state)
    (letterMem : letter ∈ ternaryDivisionAlphabet source target guessPhase
      firstPhase secondPhase thirdPhase validatorPhase handoffPhase)
    (outputLocal : LocalAt prime (letter.act prime state)) :
    (letter = identityZero validatorPhase ∧ actualDigit = 0) ∨
      (letter = linkedValidatorMarker validatorPhase handoffPhase ∧
        actualDigit = 2) := by
  have forced := divisionLetter_source_digit_unique primeProperty primeBound
    layout layout.front.validatorBound membership letterMem outputLocal
  simp [ternaryDivisionAlphabet, prefixAlphabet] at letterMem
  rcases letterMem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl
  · exact False.elim (layout.front.sourceValidatorDistinct forced.1.symm)
  · exact False.elim (layout.front.sourceValidatorDistinct forced.1.symm)
  · exact False.elim (layout.front.guessValidatorDistinct forced.1.symm)
  · exact False.elim (layout.front.guessValidatorDistinct forced.1.symm)
  · exact False.elim (layout.front.firstValidatorDistinct forced.1.symm)
  · exact False.elim (layout.front.firstValidatorDistinct forced.1.symm)
  · exact False.elim (layout.front.secondValidatorDistinct forced.1.symm)
  · exact False.elim (layout.front.secondValidatorDistinct forced.1.symm)
  · exact False.elim (layout.front.thirdValidatorDistinct forced.1.symm)
  · exact False.elim (layout.front.thirdValidatorDistinct forced.1.symm)
  · exact Or.inl ⟨rfl, by simpa [identityZero] using forced.2⟩
  · exact Or.inr ⟨rfl, by simpa [linkedValidatorMarker] using forced.2⟩
  · exact False.elim (layout.validatorHandoffDistinct forced.1)
  · exact False.elim (layout.validatorHandoffDistinct forced.1)

theorem validator_letter_before_marker
    {prime phaseCount source target guessPhase firstPhase secondPhase
      thirdPhase validatorPhase handoffPhase first guess deleted : Nat}
    (primeProperty : IsPrime prime) (primeBound : 6 * phaseCount < prime)
    (layout : PhaseLayout phaseCount source guessPhase firstPhase secondPhase
      thirdPhase validatorPhase handoffPhase)
    (deletedBelow : deleted < ternaryValidatorLength first guess)
    {letter : PhysicalTemplate}
    (letterMem : letter ∈ ternaryDivisionAlphabet source target guessPhase
      firstPhase secondPhase thirdPhase validatorPhase handoffPhase)
    (outputLocal : LocalAt prime
      (letter.act prime (phaseAffine validatorPhase
        (ternaryValidatorState prime first guess deleted)))) :
    letter = identityZero validatorPhase := by
  have membership := validatorState_inPhaseAt_before
    (validatorPhase := validatorPhase) (first := first) (guess := guess)
    (deleted := deleted) primeProperty deletedBelow
  rcases validator_letter_cases primeProperty primeBound layout membership
    letterMem outputLocal with zeroCase | markerCase
  · exact zeroCase.1
  · omega

theorem validator_letter_at_marker
    {prime phaseCount source target guessPhase firstPhase secondPhase
      thirdPhase validatorPhase handoffPhase first guess : Nat}
    (primeProperty : IsPrime prime) (primeBound : 6 * phaseCount < prime)
    (guessPositive : 0 < guess) (middleRejected : first ≠ guess - 1)
    (layout : PhaseLayout phaseCount source guessPhase firstPhase secondPhase
      thirdPhase validatorPhase handoffPhase) {letter : PhysicalTemplate}
    (letterMem : letter ∈ ternaryDivisionAlphabet source target guessPhase
      firstPhase secondPhase thirdPhase validatorPhase handoffPhase)
    (outputLocal : LocalAt prime
      (letter.act prime (phaseAffine validatorPhase
        (ternaryValidatorState prime first guess
          (ternaryValidatorLength first guess))))) :
    guess = 2 * first + 2 ∧
      letter = linkedValidatorMarker validatorPhase handoffPhase := by
  have membership := validatorState_inPhaseAt_marker
    (validatorPhase := validatorPhase) (first := first) (guess := guess)
    primeProperty guessPositive middleRejected
  rcases validator_letter_cases primeProperty primeBound layout membership
    letterMem outputLocal with zeroCase | markerCase
  · have digitEq := zeroCase.2
    unfold ternaryValidatorMarkerDigit at digitEq
    split at digitEq <;> omega
  · by_cases accepted : guess = 2 * first + 2
    · exact ⟨accepted, markerCase.1⟩
    · have digitEq := markerCase.2
      simp [ternaryValidatorMarkerDigit, accepted] at digitEq

theorem firstScanTail_forced_prefix_to_endpoint
    {prime phaseCount source target guessPhase firstPhase secondPhase
      thirdPhase validatorPhase handoffPhase endpointPhase : Nat}
    {endpointDigit : Int} {endpoint : Vec2}
    (primeProperty : IsPrime prime) (primeBound : 6 * phaseCount < prime)
    (layout : PhaseLayout phaseCount source guessPhase firstPhase secondPhase
      thirdPhase validatorPhase handoffPhase)
    (endpointBound : endpointPhase < phaseCount)
    (firstEndpointDistinct : firstPhase ≠ endpointPhase)
    (endpointMembership : InPhaseAt prime endpointPhase endpointDigit endpoint)
    {first guess deleted remaining : Nat}
    (sumEq : deleted + remaining = first) {word : List PhysicalTemplate}
    (wordOver : WordOver
      (ternaryDivisionAlphabet source target guessPhase firstPhase secondPhase
        thirdPhase validatorPhase handoffPhase) word)
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
        (ternaryDivisionAlphabet source target guessPhase firstPhase
          secondPhase thirdPhase validatorPhase handoffPhase) suffix ∧
      AllStatesLocal prime suffix
        (phaseAffine secondPhase
          (secondAutomaticState prime first guess 0)) ∧
      SameLine
        (physicalWordAction prime suffix
          (phaseAffine secondPhase
            (secondAutomaticState prime first guess 0))) endpoint := by
  let state : Nat → Vec2 := fun position =>
    phaseAffine firstPhase
      (firstAutomaticState prime first guess position)
  let next := phaseAffine secondPhase
    (secondAutomaticState prime first guess 0)
  obtain ⟨suffix, _, wordEq, suffixOver, suffixLocal, suffixRun⟩ :=
    forcedScanPrefixToEndpoint (Certificate := True)
      (currentPhase := firstPhase) (endpointPhase := endpointPhase)
      (markerDigit := 1) (endpointDigit := endpointDigit)
      (endpoint := endpoint) (next := next)
      (alphabet := ternaryDivisionAlphabet source target guessPhase firstPhase
        secondPhase thirdPhase validatorPhase handoffPhase)
      (loopLetter := identityZero firstPhase)
      (exitLetter := identityMarker firstPhase secondPhase)
      (limit := first) (deleted := deleted) (remaining := remaining)
      (state := state) primeProperty primeBound layout.front.core.firstBound
      endpointBound firstEndpointDistinct endpointMembership
      (fun position positionBelow => firstState_inPhaseAt_before
        (firstPhase := firstPhase) (first := first) (guess := guess)
        (deleted := position) primeProperty positionBelow)
      (firstState_inPhaseAt_marker (firstPhase := firstPhase)
        (first := first) (guess := guess) primeProperty)
      (fun position _ => phaseLocal
        (firstAutomaticState_local prime first guess position
          primeProperty.1))
      (phaseLocal
        (secondAutomaticState_local prime first guess 0 primeProperty.1))
      (fun position positionBelow {letter} letterMem outputLocal =>
        first_letter_before_marker primeProperty primeBound layout
          positionBelow letterMem (by simpa [state] using outputLocal))
      (fun {letter} letterMem outputLocal => ⟨True.intro,
        first_letter_at_marker primeProperty primeBound layout letterMem (by
          simpa [state] using outputLocal)⟩)
      (fun position positionBelow => by
        simpa [state] using firstZero_step prime firstPhase first guess
          position primeProperty.1 positionBelow)
      (fun _ => by
        rw [show next = phaseAffine secondPhase
          (secondAutomaticState prime first guess 0) by rfl]
        rw [secondAutomaticState_zero]
        simpa [state] using firstMarker_step prime firstPhase secondPhase
          first guess primeProperty.1)
      sumEq wordOver (by simpa [state] using allLocal)
      (by simpa [state] using completeRun)
  exact ⟨suffix, wordEq, suffixOver, by simpa [next] using suffixLocal,
    by simpa [next] using suffixRun⟩

theorem secondScanTail_forced_prefix_to_endpoint
    {prime phaseCount source target guessPhase firstPhase secondPhase
      thirdPhase validatorPhase handoffPhase endpointPhase : Nat}
    {endpointDigit : Int} {endpoint : Vec2}
    (primeProperty : IsPrime prime) (primeBound : 6 * phaseCount < prime)
    (layout : PhaseLayout phaseCount source guessPhase firstPhase secondPhase
      thirdPhase validatorPhase handoffPhase)
    (endpointBound : endpointPhase < phaseCount)
    (secondEndpointDistinct : secondPhase ≠ endpointPhase)
    (endpointMembership : InPhaseAt prime endpointPhase endpointDigit endpoint)
    {first guess deleted remaining : Nat} (guessPositive : 0 < guess)
    (sumEq : deleted + remaining = first) {word : List PhysicalTemplate}
    (wordOver : WordOver
      (ternaryDivisionAlphabet source target guessPhase firstPhase secondPhase
        thirdPhase validatorPhase handoffPhase) word)
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
        (ternaryDivisionAlphabet source target guessPhase firstPhase
          secondPhase thirdPhase validatorPhase handoffPhase) suffix ∧
      AllStatesLocal prime suffix
        (phaseAffine thirdPhase
          (thirdAutomaticState prime first guess 0)) ∧
      SameLine
        (physicalWordAction prime suffix
          (phaseAffine thirdPhase
            (thirdAutomaticState prime first guess 0))) endpoint := by
  let state : Nat → Vec2 := fun position =>
    phaseAffine secondPhase
      (secondAutomaticState prime first guess position)
  let next := phaseAffine thirdPhase
    (thirdAutomaticState prime first guess 0)
  obtain ⟨suffix, _, wordEq, suffixOver, suffixLocal, suffixRun⟩ :=
    forcedScanPrefixToEndpoint (Certificate := True)
      (currentPhase := secondPhase) (endpointPhase := endpointPhase)
      (markerDigit := 1) (endpointDigit := endpointDigit)
      (endpoint := endpoint) (next := next)
      (alphabet := ternaryDivisionAlphabet source target guessPhase firstPhase
        secondPhase thirdPhase validatorPhase handoffPhase)
      (loopLetter := identityZero secondPhase)
      (exitLetter := identityMarker secondPhase thirdPhase)
      (limit := first) (deleted := deleted) (remaining := remaining)
      (state := state) primeProperty primeBound layout.front.core.secondBound
      endpointBound secondEndpointDistinct endpointMembership
      (fun position positionBelow => secondState_inPhaseAt_before
        (secondPhase := secondPhase) (first := first) (guess := guess)
        (deleted := position) primeProperty positionBelow)
      (secondState_inPhaseAt_marker (secondPhase := secondPhase)
        (first := first) (guess := guess) primeProperty guessPositive)
      (fun position _ => phaseLocal
        (secondAutomaticState_local prime first guess position
          primeProperty.1))
      (phaseLocal
        (thirdAutomaticState_local prime first guess 0 primeProperty.1))
      (fun position positionBelow {letter} letterMem outputLocal =>
        second_letter_before_marker primeProperty primeBound layout
          positionBelow letterMem (by simpa [state] using outputLocal))
      (fun {letter} letterMem outputLocal => ⟨True.intro,
        second_letter_at_marker primeProperty primeBound guessPositive layout
          letterMem (by simpa [state] using outputLocal)⟩)
      (fun position positionBelow => by
        simpa [state] using secondZero_step prime secondPhase first guess
          position primeProperty.1 positionBelow)
      (fun _ => by
        rw [show next = phaseAffine thirdPhase
          (thirdAutomaticState prime first guess 0) by rfl]
        rw [thirdAutomaticState_zero]
        simpa [state] using secondPlainMarker_step prime secondPhase
          thirdPhase first guess primeProperty.1 guessPositive)
      sumEq wordOver (by simpa [state] using allLocal)
      (by simpa [state] using completeRun)
  exact ⟨suffix, wordEq, suffixOver, by simpa [next] using suffixLocal,
    by simpa [next] using suffixRun⟩

theorem thirdScanTail_forced_prefix_to_endpoint
    {prime phaseCount source target guessPhase firstPhase secondPhase
      thirdPhase validatorPhase handoffPhase endpointPhase : Nat}
    {endpointDigit : Int} {endpoint : Vec2}
    (primeProperty : IsPrime prime) (primeBound : 6 * phaseCount < prime)
    (layout : PhaseLayout phaseCount source guessPhase firstPhase secondPhase
      thirdPhase validatorPhase handoffPhase)
    (endpointBound : endpointPhase < phaseCount)
    (thirdEndpointDistinct : thirdPhase ≠ endpointPhase)
    (endpointMembership : InPhaseAt prime endpointPhase endpointDigit endpoint)
    {first guess deleted remaining : Nat} (guessPositive : 0 < guess)
    (sumEq : deleted + remaining = thirdScanLength first guess)
    {word : List PhysicalTemplate}
    (wordOver : WordOver
      (ternaryDivisionAlphabet source target guessPhase firstPhase secondPhase
        thirdPhase validatorPhase handoffPhase) word)
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
        (ternaryDivisionAlphabet source target guessPhase firstPhase
          secondPhase thirdPhase validatorPhase handoffPhase) suffix ∧
      AllStatesLocal prime suffix
        (phaseAffine validatorPhase
          (ternaryValidatorState prime first guess 0)) ∧
      SameLine
        (physicalWordAction prime suffix
          (phaseAffine validatorPhase
            (ternaryValidatorState prime first guess 0))) endpoint := by
  let state : Nat → Vec2 := fun position =>
    phaseAffine thirdPhase
      (thirdAutomaticState prime first guess position)
  let next := phaseAffine validatorPhase
    (ternaryValidatorState prime first guess 0)
  obtain ⟨suffix, middleRejected, wordEq, suffixOver, suffixLocal,
      suffixRun⟩ := forcedScanPrefixToEndpoint
    (Certificate := first ≠ guess - 1)
    (currentPhase := thirdPhase) (endpointPhase := endpointPhase)
    (markerDigit := thirdMarkerDigit first guess)
    (endpointDigit := endpointDigit) (endpoint := endpoint) (next := next)
    (alphabet := ternaryDivisionAlphabet source target guessPhase firstPhase
      secondPhase thirdPhase validatorPhase handoffPhase)
    (loopLetter := identityZero thirdPhase)
    (exitLetter := inverseTMarker thirdPhase validatorPhase)
    (limit := thirdScanLength first guess) (deleted := deleted)
    (remaining := remaining) (state := state) primeProperty primeBound
    layout.front.core.validatorBound endpointBound thirdEndpointDistinct
    endpointMembership
    (fun position positionBelow => thirdState_inPhaseAt_before
      (thirdPhase := thirdPhase) (first := first) (guess := guess)
      (deleted := position) primeProperty positionBelow)
    (thirdState_inPhaseAt_marker (thirdPhase := thirdPhase)
      (first := first) (guess := guess) primeProperty guessPositive)
    (fun position _ => phaseLocal
      (thirdAutomaticState_local prime first guess position primeProperty.1))
    (phaseLocal
      (ternaryValidatorState_local prime first guess 0 primeProperty.1))
    (fun position positionBelow {letter} letterMem outputLocal =>
      third_letter_before_marker primeProperty primeBound layout
        positionBelow letterMem (by simpa [state] using outputLocal))
    (fun {letter} letterMem outputLocal =>
      third_letter_at_marker primeProperty primeBound guessPositive layout
        letterMem (by simpa [state] using outputLocal))
    (fun position positionBelow => by
      simpa [state] using thirdZero_step prime thirdPhase first guess position
        primeProperty.1 positionBelow)
    (fun certificate => by
      simpa [state, next] using thirdMarker_step prime thirdPhase
        validatorPhase first guess primeProperty.1 guessPositive certificate)
    sumEq wordOver (by simpa [state] using allLocal)
    (by simpa [state] using completeRun)
  exact ⟨suffix, middleRejected, wordEq, suffixOver,
    by simpa [next] using suffixLocal, by simpa [next] using suffixRun⟩

theorem validatorTail_forced_prefix_to_endpoint
    {prime phaseCount source target guessPhase firstPhase secondPhase
      thirdPhase validatorPhase handoffPhase endpointPhase : Nat}
    {endpointDigit : Int} {endpoint : Vec2}
    (primeProperty : IsPrime prime) (primeBound : 6 * phaseCount < prime)
    (layout : PhaseLayout phaseCount source guessPhase firstPhase secondPhase
      thirdPhase validatorPhase handoffPhase)
    (endpointBound : endpointPhase < phaseCount)
    (validatorEndpointDistinct : validatorPhase ≠ endpointPhase)
    (endpointMembership : InPhaseAt prime endpointPhase endpointDigit endpoint)
    {first guess deleted remaining : Nat} (guessPositive : 0 < guess)
    (middleRejected : first ≠ guess - 1)
    (sumEq : deleted + remaining = ternaryValidatorLength first guess)
    {word : List PhysicalTemplate}
    (wordOver : WordOver
      (ternaryDivisionAlphabet source target guessPhase firstPhase secondPhase
        thirdPhase validatorPhase handoffPhase) word)
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
          [linkedValidatorMarker validatorPhase handoffPhase] ++ suffix ∧
      WordOver
        (ternaryDivisionAlphabet source target guessPhase firstPhase
          secondPhase thirdPhase validatorPhase handoffPhase) suffix ∧
      AllStatesLocal prime suffix
        (phaseAffine handoffPhase
          (T prime (twoFieldCode prime first (2 * first + 1)))) ∧
      SameLine
        (physicalWordAction prime suffix
          (phaseAffine handoffPhase
            (T prime (twoFieldCode prime first (2 * first + 1)))))
        endpoint := by
  let state : Nat → Vec2 := fun position =>
    phaseAffine validatorPhase
      (ternaryValidatorState prime first guess position)
  let next := phaseAffine handoffPhase
    (T prime (twoFieldCode prime first (2 * first + 1)))
  obtain ⟨suffix, accepted, wordEq, suffixOver, suffixLocal, suffixRun⟩ :=
    forcedScanPrefixToEndpoint (Certificate := guess = 2 * first + 2)
      (currentPhase := validatorPhase) (endpointPhase := endpointPhase)
      (markerDigit := ternaryValidatorMarkerDigit first guess)
      (endpointDigit := endpointDigit) (endpoint := endpoint) (next := next)
      (alphabet := ternaryDivisionAlphabet source target guessPhase firstPhase
        secondPhase thirdPhase validatorPhase handoffPhase)
      (loopLetter := identityZero validatorPhase)
      (exitLetter := linkedValidatorMarker validatorPhase handoffPhase)
      (limit := ternaryValidatorLength first guess) (deleted := deleted)
      (remaining := remaining) (state := state) primeProperty primeBound
      layout.front.validatorBound endpointBound validatorEndpointDistinct
      endpointMembership
      (fun position positionBelow => validatorState_inPhaseAt_before
        (validatorPhase := validatorPhase) (first := first) (guess := guess)
        (deleted := position) primeProperty positionBelow)
      (validatorState_inPhaseAt_marker (validatorPhase := validatorPhase)
        (first := first) (guess := guess) primeProperty guessPositive
        middleRejected)
      (fun position _ => phaseLocal
        (ternaryValidatorState_local prime first guess position
          primeProperty.1))
      (by
        dsimp [next]
        rw [← subtractionState_zero prime first (2 * first + 1)
          primeProperty.1]
        exact phaseSubtractionState_local prime handoffPhase first
          (2 * first + 1) 0 primeProperty.1)
      (fun position positionBelow {letter} letterMem outputLocal =>
        validator_letter_before_marker primeProperty primeBound layout
          positionBelow letterMem (by simpa [state] using outputLocal))
      (fun {letter} letterMem outputLocal =>
        validator_letter_at_marker primeProperty primeBound guessPositive
          middleRejected layout letterMem (by simpa [state] using outputLocal))
      (fun position positionBelow => by
        simpa [state] using frontValidatorZero_step prime validatorPhase first
          guess position primeProperty.1 positionBelow)
      (fun certificate => by
        subst guess
        have lengthEq :
            ternaryValidatorLength first (2 * first + 2) = first := by
          unfold ternaryValidatorLength
          rw [if_pos (by omega)]
          exact Nat.min_eq_left (by omega)
        simpa [state, next, lengthEq] using
          linkedValidatorMarker_step prime validatorPhase handoffPhase first
            primeProperty.1)
      sumEq wordOver (by simpa [state] using allLocal)
      (by simpa [state] using completeRun)
  exact ⟨suffix, accepted, wordEq, suffixOver,
    by simpa [next] using suffixLocal, by simpa [next] using suffixRun⟩

theorem automaticSuffix_forced_prefix_to_endpoint
    {prime phaseCount source target guessPhase firstPhase secondPhase
      thirdPhase validatorPhase handoffPhase endpointPhase : Nat}
    {endpointDigit : Int} {endpoint : Vec2}
    (primeProperty : IsPrime prime) (primeBound : 6 * phaseCount < prime)
    (layout : PhaseLayout phaseCount source guessPhase firstPhase secondPhase
      thirdPhase validatorPhase handoffPhase)
    (endpointBound : endpointPhase < phaseCount)
    (firstEndpointDistinct : firstPhase ≠ endpointPhase)
    (secondEndpointDistinct : secondPhase ≠ endpointPhase)
    (thirdEndpointDistinct : thirdPhase ≠ endpointPhase)
    (validatorEndpointDistinct : validatorPhase ≠ endpointPhase)
    (endpointMembership : InPhaseAt prime endpointPhase endpointDigit endpoint)
    {first guess : Nat} (guessPositive : 0 < guess)
    {word : List PhysicalTemplate}
    (wordOver : WordOver
      (ternaryDivisionAlphabet source target guessPhase firstPhase secondPhase
        thirdPhase validatorPhase handoffPhase) word)
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
          linkedValidatorWord validatorPhase handoffPhase first ++ suffix ∧
      WordOver
        (ternaryDivisionAlphabet source target guessPhase firstPhase
          secondPhase thirdPhase validatorPhase handoffPhase) suffix ∧
      AllStatesLocal prime suffix
        (phaseAffine handoffPhase
          (T prime (twoFieldCode prime first (2 * first + 1)))) ∧
      SameLine
        (physicalWordAction prime suffix
          (phaseAffine handoffPhase
            (T prime (twoFieldCode prime first (2 * first + 1)))))
        endpoint := by
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
  simp only [plainScanWord, thirdScanWord, linkedValidatorWord,
    thirdLengthEq, validatorLengthEq, List.append_assoc]

theorem guessTail_forced_exit_to_endpoint
    {prime phaseCount source target guessPhase firstPhase secondPhase
      thirdPhase validatorPhase handoffPhase endpointPhase : Nat}
    {endpointDigit : Int} {endpoint : Vec2}
    (primeProperty : IsPrime prime) (primeBound : 6 * phaseCount < prime)
    (layout : PhaseLayout phaseCount source guessPhase firstPhase secondPhase
      thirdPhase validatorPhase handoffPhase)
    (endpointBound : endpointPhase < phaseCount)
    (guessEndpointDistinct : guessPhase ≠ endpointPhase)
    (endpointMembership : InPhaseAt prime endpointPhase endpointDigit endpoint)
    {counter deleted remaining : Nat} (sumEq : deleted + remaining = counter)
    {word : List PhysicalTemplate}
    (wordOver : WordOver
      (ternaryDivisionAlphabet source target guessPhase firstPhase secondPhase
        thirdPhase validatorPhase handoffPhase) word)
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
        (ternaryDivisionAlphabet source target guessPhase firstPhase
          secondPhase thirdPhase validatorPhase handoffPhase) suffix ∧
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
      have membership := guessState_inPhaseAt_marker
        (guessPhase := guessPhase) (counter := counter) primeProperty
      have wordNonempty : word ≠ [] := by
        intro wordEmpty
        subst word
        have phasesEq := (membership.unique primeProperty primeBound
          layout.front.core.guessBound endpointBound endpointMembership (by
            simpa only [physicalWordAction, deletedEq] using completeRun)).1
        exact guessEndpointDistinct phasesEq
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
      have membership := guessState_inPhaseAt_before
        (guessPhase := guessPhase) (counter := counter) (deleted := deleted)
        primeProperty deletedBelow
      have wordNonempty : word ≠ [] := by
        intro wordEmpty
        subst word
        have phasesEq := (membership.unique primeProperty primeBound
          layout.front.core.guessBound endpointBound endpointMembership (by
            simpa only [physicalWordAction] using completeRun)).1
        exact guessEndpointDistinct phasesEq
      cases word with
      | nil => exact False.elim (wordNonempty rfl)
      | cons letter tail =>
          have letterMem := wordOver letter (by simp)
          have tailOver : WordOver
              (ternaryDivisionAlphabet source target guessPhase firstPhase
                secondPhase thirdPhase validatorPhase handoffPhase) tail := by
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

theorem prefix_choice_forced_to_endpoint_of_nonempty
    {prime phaseCount source target guessPhase firstPhase secondPhase
      thirdPhase validatorPhase handoffPhase endpointPhase : Nat}
    {endpointDigit : Int} {endpoint : Vec2}
    (primeProperty : IsPrime prime) (primeBound : 6 * phaseCount < prime)
    (layout : PhaseLayout phaseCount source guessPhase firstPhase secondPhase
      thirdPhase validatorPhase handoffPhase)
    (endpointBound : endpointPhase < phaseCount)
    (guessEndpointDistinct : guessPhase ≠ endpointPhase)
    (endpointMembership : InPhaseAt prime endpointPhase endpointDigit endpoint)
    {counter : Nat} (counterPositive : 0 < counter)
    {word : List PhysicalTemplate}
    (wordOver : WordOver
      (ternaryDivisionAlphabet source target guessPhase firstPhase secondPhase
        thirdPhase validatorPhase handoffPhase) word)
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
        (ternaryDivisionAlphabet source target guessPhase firstPhase
          secondPhase thirdPhase validatorPhase handoffPhase) suffix ∧
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
  have membership := sourceState_inPhaseAt_positive
    (prime := prime) (source := source) (counter := previous + 1)
    primeProperty (by omega)
  cases word with
  | nil => exact False.elim (wordNonempty rfl)
  | cons letter tail =>
      have letterMem := wordOver letter (by simp)
      have tailOver : WordOver
          (ternaryDivisionAlphabet source target guessPhase firstPhase
            secondPhase thirdPhase validatorPhase handoffPhase) tail := by
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

/-- Endpoint parser in the original phase-separated form.  The only use of
source/endpoint separation is to exclude the empty word; the nonempty parser
above is useful when global-alphabet splitting has already exposed a first
selected letter. -/
theorem prefix_choice_forced_to_endpoint
    {prime phaseCount source target guessPhase firstPhase secondPhase
      thirdPhase validatorPhase handoffPhase endpointPhase : Nat}
    {endpointDigit : Int} {endpoint : Vec2}
    (primeProperty : IsPrime prime) (primeBound : 6 * phaseCount < prime)
    (layout : PhaseLayout phaseCount source guessPhase firstPhase secondPhase
      thirdPhase validatorPhase handoffPhase)
    (endpointBound : endpointPhase < phaseCount)
    (sourceEndpointDistinct : source ≠ endpointPhase)
    (guessEndpointDistinct : guessPhase ≠ endpointPhase)
    (endpointMembership : InPhaseAt prime endpointPhase endpointDigit endpoint)
    {counter : Nat} (counterPositive : 0 < counter)
    {word : List PhysicalTemplate}
    (wordOver : WordOver
      (ternaryDivisionAlphabet source target guessPhase firstPhase secondPhase
        thirdPhase validatorPhase handoffPhase) word)
    (allLocal : AllStatesLocal prime word
      (phaseAffine source (unaryCode prime counter)))
    (completeRun : SameLine
      (physicalWordAction prime word
        (phaseAffine source (unaryCode prime counter))) endpoint) :
    ∃ first guess suffix,
      0 < guess ∧ first + guess = counter ∧
      word = prefixWord source guessPhase firstPhase guess ++ suffix ∧
      WordOver
        (ternaryDivisionAlphabet source target guessPhase firstPhase
          secondPhase thirdPhase validatorPhase handoffPhase) suffix ∧
      AllStatesLocal prime suffix
        (phaseAffine firstPhase
          (firstAutomaticState prime first guess 0)) ∧
      SameLine
        (physicalWordAction prime suffix
          (phaseAffine firstPhase
            (firstAutomaticState prime first guess 0))) endpoint := by
  have sourceMembership := sourceState_inPhaseAt_positive
    (prime := prime) (source := source) (counter := counter)
    primeProperty counterPositive
  have wordNonempty : word ≠ [] := by
    intro wordEmpty
    subst word
    have phasesEq := (sourceMembership.unique primeProperty primeBound
      layout.front.core.sourceBound endpointBound endpointMembership (by
        simpa only [physicalWordAction] using completeRun)).1
    exact sourceEndpointDistinct phasesEq
  exact prefix_choice_forced_to_endpoint_of_nonempty primeProperty primeBound
    layout endpointBound guessEndpointDistinct endpointMembership
    counterPositive wordOver wordNonempty allLocal completeRun

theorem linkedFrontWord_forced_prefix_to_endpoint_of_nonempty
    {prime phaseCount source target guessPhase firstPhase secondPhase
      thirdPhase validatorPhase handoffPhase endpointPhase counter : Nat}
    {endpointDigit : Int} {endpoint : Vec2}
    (primeProperty : IsPrime prime) (primeBound : 6 * phaseCount < prime)
    (layout : PhaseLayout phaseCount source guessPhase firstPhase secondPhase
      thirdPhase validatorPhase handoffPhase)
    (endpointBound : endpointPhase < phaseCount)
    (guessEndpointDistinct : guessPhase ≠ endpointPhase)
    (firstEndpointDistinct : firstPhase ≠ endpointPhase)
    (secondEndpointDistinct : secondPhase ≠ endpointPhase)
    (thirdEndpointDistinct : thirdPhase ≠ endpointPhase)
    (validatorEndpointDistinct : validatorPhase ≠ endpointPhase)
    (endpointMembership : InPhaseAt prime endpointPhase endpointDigit endpoint)
    (counterPositive : 0 < counter) {word : List PhysicalTemplate}
    (wordOver : WordOver
      (ternaryDivisionAlphabet source target guessPhase firstPhase secondPhase
        thirdPhase validatorPhase handoffPhase) word)
    (wordNonempty : word ≠ [])
    (completeRun : SameLine
      (physicalWordAction prime word
        (phaseAffine source (unaryCode prime counter))) endpoint) :
    ∃ first suffix,
      counter = 3 * first + 2 ∧
      word = linkedFrontWord source handoffPhase guessPhase firstPhase
          secondPhase thirdPhase validatorPhase first ++ suffix ∧
      WordOver
        (ternaryDivisionAlphabet source target guessPhase firstPhase
          secondPhase thirdPhase validatorPhase handoffPhase) suffix ∧
      AllStatesLocal prime suffix
        (phaseAffine handoffPhase
          (T prime (twoFieldCode prime first (2 * first + 1)))) ∧
      SameLine
        (physicalWordAction prime suffix
          (phaseAffine handoffPhase
            (T prime (twoFieldCode prime first (2 * first + 1)))))
        endpoint := by
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
    prefix_choice_forced_to_endpoint_of_nonempty primeProperty primeBound layout
      endpointBound guessEndpointDistinct endpointMembership counterPositive
      wordOver wordNonempty allLocal completeRun
  obtain ⟨suffix, accepted, suffixEq, suffixOver, suffixLocal,
      suffixRun⟩ := automaticSuffix_forced_prefix_to_endpoint
    primeProperty primeBound layout endpointBound firstEndpointDistinct
    secondEndpointDistinct thirdEndpointDistinct validatorEndpointDistinct
    endpointMembership guessPositive afterPrefixOver afterPrefixLocal
    afterPrefixRun
  have counterEq : counter = 3 * first + 2 := by omega
  refine ⟨first, suffix, counterEq, ?_, suffixOver, suffixLocal, suffixRun⟩
  rw [wordEq, suffixEq, accepted]
  simp [linkedFrontWord, List.append_assoc]

theorem linkedFrontWord_forced_prefix_to_endpoint
    {prime phaseCount source target guessPhase firstPhase secondPhase
      thirdPhase validatorPhase handoffPhase endpointPhase counter : Nat}
    {endpointDigit : Int} {endpoint : Vec2}
    (primeProperty : IsPrime prime) (primeBound : 6 * phaseCount < prime)
    (layout : PhaseLayout phaseCount source guessPhase firstPhase secondPhase
      thirdPhase validatorPhase handoffPhase)
    (endpointBound : endpointPhase < phaseCount)
    (sourceEndpointDistinct : source ≠ endpointPhase)
    (guessEndpointDistinct : guessPhase ≠ endpointPhase)
    (firstEndpointDistinct : firstPhase ≠ endpointPhase)
    (secondEndpointDistinct : secondPhase ≠ endpointPhase)
    (thirdEndpointDistinct : thirdPhase ≠ endpointPhase)
    (validatorEndpointDistinct : validatorPhase ≠ endpointPhase)
    (endpointMembership : InPhaseAt prime endpointPhase endpointDigit endpoint)
    (counterPositive : 0 < counter) {word : List PhysicalTemplate}
    (wordOver : WordOver
      (ternaryDivisionAlphabet source target guessPhase firstPhase secondPhase
        thirdPhase validatorPhase handoffPhase) word)
    (completeRun : SameLine
      (physicalWordAction prime word
        (phaseAffine source (unaryCode prime counter))) endpoint) :
    ∃ first suffix,
      counter = 3 * first + 2 ∧
      word = linkedFrontWord source handoffPhase guessPhase firstPhase
          secondPhase thirdPhase validatorPhase first ++ suffix ∧
      WordOver
        (ternaryDivisionAlphabet source target guessPhase firstPhase
          secondPhase thirdPhase validatorPhase handoffPhase) suffix ∧
      AllStatesLocal prime suffix
        (phaseAffine handoffPhase
          (T prime (twoFieldCode prime first (2 * first + 1)))) ∧
      SameLine
        (physicalWordAction prime suffix
          (phaseAffine handoffPhase
            (T prime (twoFieldCode prime first (2 * first + 1)))))
        endpoint := by
  have sourceMembership := sourceState_inPhaseAt_positive
    (prime := prime) (source := source) (counter := counter)
    primeProperty counterPositive
  have wordNonempty : word ≠ [] := by
    intro wordEmpty
    subst word
    have phasesEq := (sourceMembership.unique primeProperty primeBound
      layout.front.core.sourceBound endpointBound endpointMembership (by
        simpa only [physicalWordAction] using completeRun)).1
    exact sourceEndpointDistinct phasesEq
  exact linkedFrontWord_forced_prefix_to_endpoint_of_nonempty primeProperty
    primeBound layout endpointBound guessEndpointDistinct firstEndpointDistinct
    secondEndpointDistinct thirdEndpointDistinct validatorEndpointDistinct
    endpointMembership counterPositive wordOver wordNonempty completeRun

/-- Full completed-path converse for the fourteen-letter ternary-division
module on positive unary inputs.  The theorem returns the residual ambient
word at the output boundary, ready for the next instruction parser. -/
theorem ternaryDivisionWord_forced_prefix_to_endpoint_of_nonempty
    {prime phaseCount source target guessPhase firstPhase secondPhase
      thirdPhase validatorPhase handoffPhase endpointPhase counter : Nat}
    {endpointDigit : Int} {endpoint : Vec2}
    (primeProperty : IsPrime prime) (primeBound : 6 * phaseCount < prime)
    (layout : PhaseLayout phaseCount source guessPhase firstPhase secondPhase
      thirdPhase validatorPhase handoffPhase)
    (endpointBound : endpointPhase < phaseCount)
    (guessEndpointDistinct : guessPhase ≠ endpointPhase)
    (firstEndpointDistinct : firstPhase ≠ endpointPhase)
    (secondEndpointDistinct : secondPhase ≠ endpointPhase)
    (thirdEndpointDistinct : thirdPhase ≠ endpointPhase)
    (validatorEndpointDistinct : validatorPhase ≠ endpointPhase)
    (handoffEndpointDistinct : handoffPhase ≠ endpointPhase)
    (endpointMembership : InPhaseAt prime endpointPhase endpointDigit endpoint)
    (counterPositive : 0 < counter) {word : List PhysicalTemplate}
    (wordOver : WordOver
      (ternaryDivisionAlphabet source target guessPhase firstPhase secondPhase
        thirdPhase validatorPhase handoffPhase) word)
    (wordNonempty : word ≠ [])
    (completeRun : SameLine
      (physicalWordAction prime word
        (phaseAffine source (unaryCode prime counter))) endpoint) :
    ∃ first suffix,
      counter = 3 * first + 2 ∧
      word = ternaryDivisionWord source target guessPhase firstPhase secondPhase
          thirdPhase validatorPhase handoffPhase first ++ suffix ∧
      WordOver
        (ternaryDivisionAlphabet source target guessPhase firstPhase
          secondPhase thirdPhase validatorPhase handoffPhase) suffix ∧
      AllStatesLocal prime suffix
        (phaseAffine target (unaryCode prime first)) ∧
      SameLine
        (physicalWordAction prime suffix
          (phaseAffine target (unaryCode prime first))) endpoint := by
  obtain ⟨first, afterFront, counterEq, wordEq, afterFrontOver,
      afterFrontLocal, afterFrontRun⟩ :=
    linkedFrontWord_forced_prefix_to_endpoint_of_nonempty primeProperty
      primeBound layout endpointBound guessEndpointDistinct
      firstEndpointDistinct secondEndpointDistinct thirdEndpointDistinct
      validatorEndpointDistinct endpointMembership counterPositive wordOver
      wordNonempty completeRun
  have afterFrontLocal' : AllStatesLocal prime afterFront
      (phaseAffine handoffPhase
        (subtractionState prime first (2 * first + 1) 0)) := by
    rw [subtractionState_zero prime first (2 * first + 1) primeProperty.1]
    exact afterFrontLocal
  have afterFrontRun' : SameLine
      (physicalWordAction prime afterFront
        (phaseAffine handoffPhase
          (subtractionState prime first (2 * first + 1) 0))) endpoint := by
    rw [subtractionState_zero prime first (2 * first + 1) primeProperty.1]
    exact afterFrontRun
  obtain ⟨suffix, regenerationEq, suffixOver, suffixLocal, suffixRun⟩ :=
    regenerationTail_forced_prefix_to_endpoint primeProperty primeBound
      layout endpointBound handoffEndpointDistinct endpointMembership
      (deleted := 0) (remaining := first) (by omega) afterFrontOver
      afterFrontLocal' afterFrontRun'
  refine ⟨first, suffix, counterEq, ?_, suffixOver, suffixLocal, suffixRun⟩
  rw [wordEq, regenerationEq]
  simp [ternaryDivisionWord, regenerationWord, List.append_assoc]

/-- Phase-separated wrapper for the nonempty completed-path parser. -/
theorem ternaryDivisionWord_forced_prefix_to_endpoint
    {prime phaseCount source target guessPhase firstPhase secondPhase
      thirdPhase validatorPhase handoffPhase endpointPhase counter : Nat}
    {endpointDigit : Int} {endpoint : Vec2}
    (primeProperty : IsPrime prime) (primeBound : 6 * phaseCount < prime)
    (layout : PhaseLayout phaseCount source guessPhase firstPhase secondPhase
      thirdPhase validatorPhase handoffPhase)
    (endpointBound : endpointPhase < phaseCount)
    (sourceEndpointDistinct : source ≠ endpointPhase)
    (guessEndpointDistinct : guessPhase ≠ endpointPhase)
    (firstEndpointDistinct : firstPhase ≠ endpointPhase)
    (secondEndpointDistinct : secondPhase ≠ endpointPhase)
    (thirdEndpointDistinct : thirdPhase ≠ endpointPhase)
    (validatorEndpointDistinct : validatorPhase ≠ endpointPhase)
    (handoffEndpointDistinct : handoffPhase ≠ endpointPhase)
    (endpointMembership : InPhaseAt prime endpointPhase endpointDigit endpoint)
    (counterPositive : 0 < counter) {word : List PhysicalTemplate}
    (wordOver : WordOver
      (ternaryDivisionAlphabet source target guessPhase firstPhase secondPhase
        thirdPhase validatorPhase handoffPhase) word)
    (completeRun : SameLine
      (physicalWordAction prime word
        (phaseAffine source (unaryCode prime counter))) endpoint) :
    ∃ first suffix,
      counter = 3 * first + 2 ∧
      word = ternaryDivisionWord source target guessPhase firstPhase secondPhase
          thirdPhase validatorPhase handoffPhase first ++ suffix ∧
      WordOver
        (ternaryDivisionAlphabet source target guessPhase firstPhase
          secondPhase thirdPhase validatorPhase handoffPhase) suffix ∧
      AllStatesLocal prime suffix
        (phaseAffine target (unaryCode prime first)) ∧
      SameLine
        (physicalWordAction prime suffix
          (phaseAffine target (unaryCode prime first))) endpoint := by
  have sourceMembership := sourceState_inPhaseAt_positive
    (prime := prime) (source := source) (counter := counter)
    primeProperty counterPositive
  have wordNonempty : word ≠ [] := by
    intro wordEmpty
    subst word
    have phasesEq := (sourceMembership.unique primeProperty primeBound
      layout.front.core.sourceBound endpointBound endpointMembership (by
        simpa only [physicalWordAction] using completeRun)).1
    exact sourceEndpointDistinct phasesEq
  exact ternaryDivisionWord_forced_prefix_to_endpoint_of_nonempty
    primeProperty primeBound layout endpointBound guessEndpointDistinct
    firstEndpointDistinct secondEndpointDistinct thirdEndpointDistinct
    validatorEndpointDistinct handoffEndpointDistinct endpointMembership
    counterPositive wordOver wordNonempty completeRun

/-- All-input form of the completed-path converse.  The zero input cannot
leave the source phase, so no positivity premise is needed. -/
theorem ternaryDivisionWord_forced_prefix_to_endpoint_all_inputs
    {prime phaseCount source target guessPhase firstPhase secondPhase
      thirdPhase validatorPhase handoffPhase endpointPhase counter : Nat}
    {endpointDigit : Int} {endpoint : Vec2}
    (primeProperty : IsPrime prime) (primeBound : 6 * phaseCount < prime)
    (layout : PhaseLayout phaseCount source guessPhase firstPhase secondPhase
      thirdPhase validatorPhase handoffPhase)
    (endpointBound : endpointPhase < phaseCount)
    (sourceEndpointDistinct : source ≠ endpointPhase)
    (guessEndpointDistinct : guessPhase ≠ endpointPhase)
    (firstEndpointDistinct : firstPhase ≠ endpointPhase)
    (secondEndpointDistinct : secondPhase ≠ endpointPhase)
    (thirdEndpointDistinct : thirdPhase ≠ endpointPhase)
    (validatorEndpointDistinct : validatorPhase ≠ endpointPhase)
    (handoffEndpointDistinct : handoffPhase ≠ endpointPhase)
    (endpointMembership : InPhaseAt prime endpointPhase endpointDigit endpoint)
    {word : List PhysicalTemplate}
    (wordOver : WordOver
      (ternaryDivisionAlphabet source target guessPhase firstPhase secondPhase
        thirdPhase validatorPhase handoffPhase) word)
    (completeRun : SameLine
      (physicalWordAction prime word
        (phaseAffine source (unaryCode prime counter))) endpoint) :
    ∃ first suffix,
      counter = 3 * first + 2 ∧
      word = ternaryDivisionWord source target guessPhase firstPhase secondPhase
          thirdPhase validatorPhase handoffPhase first ++ suffix ∧
      WordOver
        (ternaryDivisionAlphabet source target guessPhase firstPhase
          secondPhase thirdPhase validatorPhase handoffPhase) suffix ∧
      AllStatesLocal prime suffix
        (phaseAffine target (unaryCode prime first)) ∧
      SameLine
        (physicalWordAction prime suffix
          (phaseAffine target (unaryCode prime first))) endpoint := by
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
  have counterPositive : 0 < counter := by
    cases counter with
    | zero =>
        have sourceMembership : InPhaseAt prime source 1
            (phaseAffine source (unaryCode prime 0)) := by
          simpa [unaryCode, unaryDigits] using
            (periodicCode_inPhaseAt prime source 1 [] primeProperty.1
              (by simp [ReservedDigit]))
        have wordNonempty : word ≠ [] := by
          intro wordEmpty
          subst word
          have phasesEq := (sourceMembership.unique primeProperty primeBound
            layout.front.core.sourceBound endpointBound endpointMembership (by
              simpa only [physicalWordAction] using completeRun)).1
          exact sourceEndpointDistinct phasesEq
        cases word with
        | nil => exact False.elim (wordNonempty rfl)
        | cons letter tail =>
            have letterMem := wordOver letter (by simp)
            exact False.elim
              (source_rejects_zero primeProperty primeBound layout letterMem
                allLocal.2.start)
    | succ previous => omega
  exact ternaryDivisionWord_forced_prefix_to_endpoint primeProperty
    primeBound layout endpointBound sourceEndpointDistinct
    guessEndpointDistinct firstEndpointDistinct secondEndpointDistinct
    thirdEndpointDistinct validatorEndpointDistinct handoffEndpointDistinct
    endpointMembership counterPositive wordOver completeRun

end Mortality.Compiler.TernaryDivisionModule
