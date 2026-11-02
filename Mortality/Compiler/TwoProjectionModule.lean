import Mortality.Compiler.TwoProjectionClassification
import Mortality.Compiler.MutatingScan
import Mortality.Compiler.OddHalvingArithmetic
import Mortality.Compiler.BoundaryParser

/-!
# The ten-letter two-to-one projection module

This file gives the literal physical alphabet from the manuscript and
proves its complete accepted execution.  The converse arithmetic for every
guess is in `TwoProjectionClassification`; the boundary parser is developed
below the forward construction.
-/

namespace Mortality.Compiler.TwoProjectionModule

open Mortality.PeriodicCode
open Mortality.Compiler
open Mortality.Compiler.UnaryArithmetic
open Mortality.Compiler.ContractionProjectionArithmetic
open Mortality.Compiler.ContractionArithmetic
open Mortality.Compiler.TwoProjectionClassification
open Mortality.Compiler.OddHalvingArithmetic

abbrev zeroLoop (phase : Nat) : PhysicalTemplate :=
  MutatingScan.loopLetter phase 0

abbrev markerOneExit (source target : Nat) : PhysicalTemplate :=
  MutatingScan.exitLetter source target 1 .positive 0

abbrev inverseTZeroExit (source target : Nat) : PhysicalTemplate :=
  MutatingScan.exitLetter source target 0 .positive 1

abbrev inverseFNegativeExit (source target : Nat) : PhysicalTemplate :=
  MutatingScan.exitLetter source target (-1) .positive (-2)

def alphabet (source target guessPhase negativePhase firstValidator
    secondValidator : Nat) : List PhysicalTemplate :=
  [zeroLoop source, markerOneExit source guessPhase,
    zeroLoop guessPhase, inverseTZeroExit guessPhase negativePhase,
    zeroLoop negativePhase,
      inverseFNegativeExit negativePhase firstValidator,
    zeroLoop firstValidator,
      markerOneExit firstValidator secondValidator,
    zeroLoop secondValidator, markerOneExit secondValidator target]

structure PhaseLayout (phaseCount source guessPhase negativePhase
    firstValidator secondValidator : Nat) : Prop where
  sourceBound : source < phaseCount
  guessBound : guessPhase < phaseCount
  negativeBound : negativePhase < phaseCount
  firstValidatorBound : firstValidator < phaseCount
  secondValidatorBound : secondValidator < phaseCount
  sourceGuessDistinct : source ≠ guessPhase
  sourceNegativeDistinct : source ≠ negativePhase
  sourceFirstValidatorDistinct : source ≠ firstValidator
  sourceSecondValidatorDistinct : source ≠ secondValidator
  guessNegativeDistinct : guessPhase ≠ negativePhase
  guessFirstValidatorDistinct : guessPhase ≠ firstValidator
  guessSecondValidatorDistinct : guessPhase ≠ secondValidator
  negativeFirstValidatorDistinct : negativePhase ≠ firstValidator
  negativeSecondValidatorDistinct : negativePhase ≠ secondValidator
  validatorsDistinct : firstValidator ≠ secondValidator

def firstScanWord (source target first : Nat) : List PhysicalTemplate :=
  MutatingScan.word source target (List.replicate first 0) 1 .positive 0

def guessWord (source target first : Nat) : List PhysicalTemplate :=
  MutatingScan.word source target (List.replicate first 0) 0 .positive 1

def negativeWord (source target first : Nat) : List PhysicalTemplate :=
  List.replicate first (zeroLoop source) ++
    [inverseFNegativeExit source target]

def validatorWord (source target counter : Nat) : List PhysicalTemplate :=
  MutatingScan.word source target (List.replicate counter 0) 1 .positive 0

def acceptedWord (source target guessPhase negativePhase firstValidator
    secondValidator first : Nat) : List PhysicalTemplate :=
  firstScanWord source guessPhase first ++
    guessWord guessPhase negativePhase first ++
    negativeWord negativePhase firstValidator first ++
    validatorWord firstValidator secondValidator (2 * first + 1) ++
    validatorWord secondValidator target (2 * first + 1)

@[simp] theorem alphabet_length
    (source target guessPhase negativePhase firstValidator secondValidator : Nat) :
    (alphabet source target guessPhase negativePhase firstValidator
      secondValidator).length = 10 := by
  simp [alphabet]

@[simp] theorem firstScanWord_length (source target first : Nat) :
    (firstScanWord source target first).length = first + 1 := by
  simp [firstScanWord]

@[simp] theorem guessWord_length (source target first : Nat) :
    (guessWord source target first).length = first + 1 := by
  simp [guessWord]

@[simp] theorem negativeWord_length (source target first : Nat) :
    (negativeWord source target first).length = first + 1 := by
  simp [negativeWord]

@[simp] theorem validatorWord_length (source target counter : Nat) :
    (validatorWord source target counter).length = counter + 1 := by
  simp [validatorWord]

@[simp] theorem acceptedWord_length
    (source target guessPhase negativePhase firstValidator secondValidator
      first : Nat) :
    (acceptedWord source target guessPhase negativePhase firstValidator
      secondValidator first).length = 7 * first + 7 := by
  simp [acceptedWord]
  omega

theorem acceptedWord_wordOver
    (source target guessPhase negativePhase firstValidator secondValidator
      first : Nat) :
    WordOver
      (alphabet source target guessPhase negativePhase firstValidator
        secondValidator)
      (acceptedWord source target guessPhase negativePhase firstValidator
        secondValidator first) := by
  intro letter letterMem
  simp [acceptedWord, firstScanWord, guessWord, negativeWord, validatorWord,
    MutatingScan.word] at letterMem
  rcases letterMem with ⟨_, rfl⟩ | rfl | ⟨_, rfl⟩ | rfl | ⟨_, rfl⟩ |
      rfl | ⟨_, rfl⟩ | rfl | ⟨_, rfl⟩ | rfl <;> simp [alphabet]

private theorem positive_zero_mutation (base : Nat) (value : Rat) :
    mutationMap base .positive 0 value = value := by
  simp [mutationMap, mutationDenominator, Sign.value, Rat.div_def]
  grind

private theorem positive_one_mutation (base : Nat) (value : Rat) :
    mutationMap base .positive 1 value = Tinv base value := by
  unfold mutationMap mutationDenominator Tinv
  simp only [Sign.value, Rat.intCast_one, Rat.one_mul]
  congr 2
  rw [Rat.mul_one]

private theorem positive_minus_two_mutation (base : Nat) (value : Rat) :
    mutationMap base .positive (-2) value = Finv base value := by
  unfold mutationMap mutationDenominator Finv
  simp only [Sign.value, Rat.intCast_one, Rat.one_mul]
  congr 1 <;> grind

theorem phase_local {base phase : Nat} {value : Rat}
    (membership : LocalAt base (Vec2.affine value)) :
    LocalAt base (phaseAffine phase value) := by
  rw [show phaseAffine phase value =
      Matrix2.apply (IntMatrix2.cast (chart phase)) (Vec2.affine value) by
    simpa [phaseAffine] using (chart_apply phase value).symm]
  exact (local_chart_iff base phase _).mpr membership

theorem zeroLoop_affine_step
    (base phase : Nat) (value next : Rat) (baseAtLeastTwo : 2 ≤ base)
    (valueLocal : LocalAt base (Vec2.affine value))
    (nextLocal : LocalAt base (Vec2.affine next))
    (deleteEq : deleteDigit (base : Rat) 0 value = next) :
    SameLine
      ((zeroLoop phase).act base (phaseAffine phase value))
      (phaseAffine phase next) := by
  have action := physicalLetter_affine_sameLine_of_local
    (sourcePhase := phase) (targetPhase := phase) (digit := 0)
    (preCoefficient := 0) (postCoefficient := 0)
    (postSign := .positive) (primePositive := by omega) valueLocal (by
      rw [positive_zero_mutation]
      change LocalAt base
        (Vec2.affine (deleteDigit (base : Rat) 0 value))
      rw [deleteEq]
      exact nextLocal)
  simp [localLetterMap] at action
  have deleteRaw := deleteEq
  unfold deleteDigit at deleteRaw
  simp only [Rat.intCast_zero] at deleteRaw
  rw [deleteRaw] at action
  simpa [zeroLoop, MutatingScan.loopLetter, PhysicalTemplate.act,
    PhysicalTemplate.matrix, phaseAffine] using action

theorem markerOneExit_affine_step
    (base source target : Nat) (value next : Rat)
    (baseAtLeastTwo : 2 ≤ base)
    (valueLocal : LocalAt base (Vec2.affine value))
    (nextLocal : LocalAt base (Vec2.affine next))
    (deleteEq : deleteDigit (base : Rat) 1 value = next) :
    SameLine
      ((markerOneExit source target).act base (phaseAffine source value))
      (phaseAffine target next) := by
  have action := physicalLetter_affine_sameLine_of_local
    (sourcePhase := source) (targetPhase := target) (digit := 1)
    (preCoefficient := 0) (postCoefficient := 0)
    (postSign := .positive) (primePositive := by omega) valueLocal (by
      rw [positive_zero_mutation]
      change LocalAt base
        (Vec2.affine (deleteDigit (base : Rat) 1 value))
      rw [deleteEq]
      exact nextLocal)
  simp [localLetterMap] at action
  have deleteRaw := deleteEq
  unfold deleteDigit at deleteRaw
  simp only [Rat.intCast_one] at deleteRaw
  rw [deleteRaw] at action
  simpa [markerOneExit, MutatingScan.exitLetter, PhysicalTemplate.act,
    PhysicalTemplate.matrix, phaseAffine] using action

theorem firstScan_rotated
    (base first : Nat) (baseAtLeastTwo : 2 ≤ base) :
    periodicCode (base : Rat)
        (List.replicate (2 * first + 1) 0 ++ [-1] ++
          List.replicate first 0 ++ [1]) =
      twoProjectionFirstState base first := by
  have scan := MutatingScan.scanDigits_periodic_prefix base
    (List.replicate first 0)
    (List.replicate (2 * first + 1) 0 ++ [-1]) 1 baseAtLeastTwo
  simpa [twoProjectionFirstState, twoFieldCode, twoFieldDigits,
    unaryDigits, List.append_assoc] using scan.symm

theorem firstScanWord_correct
    (base source target first : Nat) (baseAtLeastTwo : 2 ≤ base) :
    SameLine
      (physicalWordAction base (firstScanWord source target first)
        (phaseAffine source
          (twoFieldCode base first (2 * first + 1))))
      (phaseAffine target (twoProjectionFirstState base first)) := by
  have action := MutatingScan.word_correct base source target
    (List.replicate first 0)
    (List.replicate (2 * first + 1) 0 ++ [-1]) 1 .positive 0
    baseAtLeastTwo
  rw [positive_zero_mutation] at action
  rw [firstScan_rotated base first baseAtLeastTwo] at action
  simpa [firstScanWord, twoFieldCode, twoFieldDigits, List.append_assoc]
    using action

theorem firstState_digit_decomposition
    (base first : Nat) (baseAtLeastTwo : 2 ≤ base) :
    twoProjectionFirstState base first =
      periodicCode (base : Rat)
        (List.replicate first 0 ++ [0] ++
          (List.replicate first 0 ++ [-1] ++
            List.replicate first 0 ++ [1])) := by
  rw [← firstScan_rotated base first baseAtLeastTwo]
  congr 1
  have zerosEq : List.replicate (2 * first + 1) (0 : Int) =
      List.replicate first 0 ++ [0] ++ List.replicate first 0 := by
    rw [← List.replicate_succ']
    simp only [List.replicate_append_replicate]
    congr 1 <;> omega
  rw [zerosEq]
  simp [List.append_assoc]

theorem guessedState_rotated
    (base first : Nat) (baseAtLeastTwo : 2 ≤ base) :
    Tinv base
        (periodicCode (base : Rat)
          ((List.replicate first 0 ++ [-1] ++
              List.replicate first 0 ++ [1]) ++
            List.replicate first 0 ++ [0])) =
      twoProjectionGuessedState base first := by
  have scan := MutatingScan.scanDigits_periodic_prefix base
    (List.replicate first 0)
    (List.replicate first 0 ++ [-1] ++
      List.replicate first 0 ++ [1]) 0 baseAtLeastTwo
  rw [← firstState_digit_decomposition base first baseAtLeastTwo] at scan
  unfold twoProjectionGuessedState
  change Tinv base
      (periodicCode (base : Rat)
        ((List.replicate first 0 ++ [-1] ++
            List.replicate first 0 ++ [1]) ++
          List.replicate first 0 ++ [0])) =
    Tinv base
      (scanDigits (base : Rat) (zeroDigits (first + 1))
        (twoProjectionFirstState base first))
  rw [show zeroDigits (first + 1) = List.replicate first 0 ++ [0] by
    simp only [zeroDigits, List.replicate_succ']]
  rw [scan]

theorem guessWord_correct
    (base source target first : Nat) (baseAtLeastTwo : 2 ≤ base) :
    SameLine
      (physicalWordAction base (guessWord source target first)
        (phaseAffine source (twoProjectionFirstState base first)))
      (phaseAffine target (twoProjectionGuessedState base first)) := by
  have action := MutatingScan.word_correct base source target
    (List.replicate first 0)
    (List.replicate first 0 ++ [-1] ++
      List.replicate first 0 ++ [1]) 0 .positive 1 baseAtLeastTwo
  rw [positive_one_mutation] at action
  rw [firstState_digit_decomposition base first baseAtLeastTwo]
  rw [guessedState_rotated base first baseAtLeastTwo] at action
  simpa [guessWord, List.append_assoc] using action

/-! ## States for arbitrary prefix choices -/

def guessState (base first deleted : Nat) : Rat :=
  MutatingScan.zeroState base (2 * first + 1) (-1)
    (List.replicate first 0 ++ [1]) deleted

theorem guessState_zero
    (base first : Nat) (baseAtLeastTwo : 2 ≤ base) :
    guessState base first 0 = twoProjectionFirstState base first := by
  unfold guessState MutatingScan.zeroState
  rw [MutatingScan.zeroStateDigits_zero]
  simpa [List.append_assoc] using
    firstScan_rotated base first baseAtLeastTwo

theorem prefixState_eq_guessState
    (base first guess : Nat) (baseAtLeastTwo : 2 ≤ base)
    (guessBound : guess ≤ 2 * first + 1) :
    twoProjectionPrefixState base first guess =
      guessState base first guess := by
  unfold twoProjectionPrefixState zeroDigits
  rw [← guessState_zero base first baseAtLeastTwo]
  simpa [guessState] using
    MutatingScan.scan_zeroState base (2 * first + 1) (-1)
      (List.replicate first 0 ++ [1]) 0 guess baseAtLeastTwo (by omega)

theorem generalGuessState_eq
    (base first guess : Nat) (baseAtLeastTwo : 2 ≤ base)
    (guessBound : guess ≤ 2 * first + 1) :
    twoProjectionGeneralGuessState base first guess =
      Tinv base (guessState base first guess) := by
  unfold twoProjectionGeneralGuessState
  rw [prefixState_eq_guessState base first guess baseAtLeastTwo guessBound]

def generalNegativeDenominator (base Q h : Nat) : Int :=
  1 + (base : Int) ^ Q + (base : Int) ^ (2 * Q) - (base : Int) ^ h

def generalNegativeZeroState
    (base Q h deleted : Nat) : Rat :=
  -((base : Rat) ^ (h - 1 - deleted)) /
    (generalNegativeDenominator base Q h : Rat)

theorem generalNegativeDenominator_one_residue
    (base Q h : Nat) (QPositive : 0 < Q) (hPositive : 0 < h) :
    (base : Int) ∣ 1 - generalNegativeDenominator base Q h := by
  rcases base_dvd_positive_power base Q QPositive with ⟨q, hq⟩
  rcases base_dvd_positive_power base (2 * Q) (by omega) with ⟨q2, hq2⟩
  rcases base_dvd_positive_power base h hPositive with ⟨rh, hrh⟩
  refine ⟨-q - q2 + rh, ?_⟩
  unfold generalNegativeDenominator
  rw [hq, hq2, hrh]
  grind

theorem generalNegativeDenominator_not_dvd
    (base Q h : Nat) (baseAtLeastTwo : 2 ≤ base)
    (QPositive : 0 < Q) (hPositive : 0 < h) :
    ¬(base : Int) ∣ generalNegativeDenominator base Q h := by
  intro denominatorDivisible
  have differenceDivisible := generalNegativeDenominator_one_residue
    base Q h QPositive hPositive
  have oneDivisible := Int.dvd_add differenceDivisible denominatorDivisible
  have sumEq : 1 - generalNegativeDenominator base Q h +
      generalNegativeDenominator base Q h = 1 := by grind
  rw [sumEq] at oneDivisible
  have naturalDivisible : base ∣ 1 := by
    simpa using (Int.ofNat_dvd.mp oneDivisible)
  have baseAtMostOne := Nat.le_of_dvd Nat.zero_lt_one naturalDivisible
  omega

theorem generalNegativeZeroState_local
    (base Q h deleted : Nat) (baseAtLeastTwo : 2 ≤ base)
    (QPositive : 0 < Q) (hPositive : 0 < h) :
    LocalAt base
      (Vec2.affine (generalNegativeZeroState base Q h deleted)) := by
  have localFraction := local_affine_integer_div
    (prime := base)
    (numerator := -((base : Int) ^ (h - 1 - deleted)))
    (denominator := generalNegativeDenominator base Q h)
    (generalNegativeDenominator_not_dvd base Q h baseAtLeastTwo QPositive
      hPositive)
  simpa [generalNegativeZeroState, Rat.intCast_neg, Rat.intCast_pow,
    Rat.intCast_natCast] using localFraction

theorem generalNegativeZeroState_sameLine_integer
    (base Q h deleted : Nat) (baseAtLeastTwo : 2 ≤ base)
    (QPositive : 0 < Q) (hPositive : 0 < h) :
    SameLine (Vec2.affine (generalNegativeZeroState base Q h deleted))
      (integerVector (-((base : Int) ^ (h - 1 - deleted)))
        (generalNegativeDenominator base Q h)) := by
  have denominatorNotDivisible := generalNegativeDenominator_not_dvd
    base Q h baseAtLeastTwo QPositive hPositive
  have denominatorNonzero : generalNegativeDenominator base Q h ≠ 0 :=
    fun denominatorZero => denominatorNotDivisible (by
      rw [denominatorZero]
      exact Int.dvd_zero _)
  have same := affine_div_sameLine_integerVector
    (numerator := -((base : Int) ^ (h - 1 - deleted)))
    (denominator := generalNegativeDenominator base Q h) denominatorNonzero
  simpa [generalNegativeZeroState, Rat.intCast_neg, Rat.intCast_pow,
    Rat.intCast_natCast] using same

theorem generalNegativeZeroState_zero_residue
    (base h deleted : Nat) (deletedBelow : deleted < h - 1) :
    (base : Int) ∣ -((base : Int) ^ (h - 1 - deleted)) := by
  rcases base_dvd_positive_power base (h - 1 - deleted) (by omega) with
    ⟨factor, factorEq⟩
  refine ⟨-factor, ?_⟩
  rw [factorEq]
  grind

theorem generalNegativeZeroState_marker_residue
    (base Q h : Nat) (QPositive : 0 < Q) (hPositive : 0 < h) :
    (base : Int) ∣
      -((base : Int) ^ (h - 1 - (h - 1))) -
        (-1) * generalNegativeDenominator base Q h := by
  rcases base_dvd_positive_power base Q QPositive with ⟨q, hq⟩
  rcases base_dvd_positive_power base (2 * Q) (by omega) with ⟨q2, hq2⟩
  rcases base_dvd_positive_power base h hPositive with ⟨rh, hrh⟩
  refine ⟨q + q2 - rh, ?_⟩
  unfold generalNegativeDenominator
  rw [show h - 1 - (h - 1) = 0 by omega, Int.pow_zero, hq, hq2, hrh]
  grind

theorem generalNegativeZeroState_delete_zero
    (base Q h deleted : Nat) (baseAtLeastTwo : 2 ≤ base)
    (deletedBelow : deleted < h - 1) :
    deleteDigit (base : Rat) 0
        (generalNegativeZeroState base Q h deleted) =
      generalNegativeZeroState base Q h (deleted + 1) := by
  unfold generalNegativeZeroState deleteDigit
  have baseNonzero : (base : Rat) ≠ 0 := by
    simpa using (show base ≠ 0 by omega)
  have exponentEq : h - 1 - deleted =
      h - 1 - (deleted + 1) + 1 := by omega
  rw [exponentEq, Rat.pow_succ]
  simp only [Rat.intCast_zero, Rat.div_def]
  have baseCancel := Rat.mul_inv_cancel (base : Rat) baseNonzero
  grind

theorem generalNegativeZeroState_zero
    (base Q h : Nat) (baseAtLeastTwo : 2 ≤ base)
    (QPositive : 0 < Q) (hPositive : 0 < h) (hBelowDouble : h < 2 * Q) :
    generalNegativeZeroState base Q h 0 =
      twoProjectionGeneralGuessState base (Q - 1) (2 * Q - h) := by
  have guessPositive : 0 < 2 * Q - h := by omega
  have guessBelow : 2 * Q - h < 2 * ((Q - 1) + 1) := by omega
  have auxiliary := twoProjectionGeneralGuessState_auxiliary base (Q - 1)
    (2 * Q - h) baseAtLeastTwo guessPositive guessBelow
  have firstExponentEq : Q - 1 + 1 = Q := by omega
  have remainingEq : 2 * Q - (2 * Q - h) = h := by omega
  simp only [firstExponentEq, remainingEq] at auxiliary
  let q : Rat := (base : Rat) ^ Q
  let R : Rat := (base : Rat) ^ h
  let denominator : Rat := 1 + q + q ^ 2 - R
  have squarePower : q ^ 2 = (base : Rat) ^ (2 * Q) := by
    calc
      q ^ 2 = q * q := by
        rw [show (2 : Nat) = 1 + 1 by omega,
          Lean.Grind.Semiring.pow_add]
        simp only [Rat.pow_one]
      _ = (base : Rat) ^ Q * (base : Rat) ^ Q := by rfl
      _ = (base : Rat) ^ (Q + Q) :=
        (Lean.Grind.Semiring.pow_add (base : Rat) Q Q).symm
      _ = (base : Rat) ^ (2 * Q) := by congr 1 <;> omega
  have hSucc : (base : Rat) ^ h =
      (base : Rat) ^ (h - 1) * (base : Rat) := by
    calc
      (base : Rat) ^ h = (base : Rat) ^ (h - 1 + 1) := by
        congr 1 <;> omega
      _ = _ := by rw [Rat.pow_succ]
  have baseNonzero : (base : Rat) ≠ 0 := by
    simpa using (show base ≠ 0 by omega)
  have denominatorCast : (generalNegativeDenominator base Q h : Rat) =
      denominator := by
    unfold generalNegativeDenominator denominator q R
    simp only [Rat.intCast_sub, Rat.intCast_add, Rat.intCast_pow,
      Rat.intCast_natCast, Rat.intCast_ofNat]
    rw [squarePower]
  have productEq : (base : Rat) *
      generalNegativeZeroState base Q h 0 =
      (base : Rat) *
        twoProjectionGeneralGuessState base (Q - 1) (2 * Q - h) := by
    rw [auxiliary]
    unfold generalNegativeZeroState
    simp only [Nat.sub_zero, Rat.div_def]
    rw [denominatorCast, hSucc]
    grind
  calc
    generalNegativeZeroState base Q h 0 =
        ((base : Rat)⁻¹ * (base : Rat)) *
          generalNegativeZeroState base Q h 0 := by
      rw [Rat.inv_mul_cancel (base : Rat) baseNonzero, Rat.one_mul]
    _ = (base : Rat)⁻¹ * ((base : Rat) *
        generalNegativeZeroState base Q h 0) := by rw [Rat.mul_assoc]
    _ = (base : Rat)⁻¹ * ((base : Rat) *
        twoProjectionGeneralGuessState base (Q - 1) (2 * Q - h)) := by
      rw [productEq]
    _ = ((base : Rat)⁻¹ * (base : Rat)) *
        twoProjectionGeneralGuessState base (Q - 1) (2 * Q - h) := by
      rw [Rat.mul_assoc]
    _ = twoProjectionGeneralGuessState base (Q - 1) (2 * Q - h) := by
      rw [Rat.inv_mul_cancel (base : Rat) baseNonzero, Rat.one_mul]

def generalNegativeDeletedState (base Q h : Nat) : Rat :=
  ((base : Rat) ^ (Q - 1) + (base : Rat) ^ (2 * Q - 1) -
      (base : Rat) ^ (h - 1)) /
    (generalNegativeDenominator base Q h : Rat)

theorem generalNegativeDeletedState_local
    (base Q h : Nat) (baseAtLeastTwo : 2 ≤ base)
    (QPositive : 0 < Q) (hPositive : 0 < h) :
    LocalAt base
      (Vec2.affine (generalNegativeDeletedState base Q h)) := by
  have localFraction := local_affine_integer_div
    (prime := base)
    (numerator := (base : Int) ^ (Q - 1) +
      (base : Int) ^ (2 * Q - 1) - (base : Int) ^ (h - 1))
    (denominator := generalNegativeDenominator base Q h)
    (generalNegativeDenominator_not_dvd base Q h baseAtLeastTwo QPositive
      hPositive)
  simpa [generalNegativeDeletedState, Rat.intCast_sub, Rat.intCast_add,
    Rat.intCast_pow, Rat.intCast_natCast] using localFraction

theorem generalNegativeZeroState_delete_marker
    (base Q h : Nat) (baseAtLeastTwo : 2 ≤ base)
    (QPositive : 0 < Q) (hPositive : 0 < h) :
    deleteDigit (base : Rat) (-1)
        (generalNegativeZeroState base Q h (h - 1)) =
      generalNegativeDeletedState base Q h := by
  have denominatorNotDivisible := generalNegativeDenominator_not_dvd
    base Q h baseAtLeastTwo QPositive hPositive
  have denominatorNonzeroInt : generalNegativeDenominator base Q h ≠ 0 :=
    fun denominatorZero => denominatorNotDivisible (by
      rw [denominatorZero]
      exact Int.dvd_zero _)
  have denominatorNonzeroRat :
      (generalNegativeDenominator base Q h : Rat) ≠ 0 := by
    exact_mod_cast denominatorNonzeroInt
  have baseNonzero : (base : Rat) ≠ 0 := by
    simpa using (show base ≠ 0 by omega)
  have qSucc : (base : Rat) ^ Q =
      (base : Rat) ^ (Q - 1) * (base : Rat) := by
    calc
      (base : Rat) ^ Q = (base : Rat) ^ (Q - 1 + 1) := by
        congr 1 <;> omega
      _ = _ := by rw [Rat.pow_succ]
  have q2Succ : (base : Rat) ^ (2 * Q) =
      (base : Rat) ^ (2 * Q - 1) * (base : Rat) := by
    calc
      (base : Rat) ^ (2 * Q) =
          (base : Rat) ^ (2 * Q - 1 + 1) := by congr 1 <;> omega
      _ = _ := by rw [Rat.pow_succ]
  have hSucc : (base : Rat) ^ h =
      (base : Rat) ^ (h - 1) * (base : Rat) := by
    calc
      (base : Rat) ^ h = (base : Rat) ^ (h - 1 + 1) := by
        congr 1 <;> omega
      _ = _ := by rw [Rat.pow_succ]
  have expandedDenominatorNonzero :
      (1 : Rat) + (base : Rat) ^ (Q - 1) * (base : Rat) +
          (base : Rat) ^ (2 * Q - 1) * (base : Rat) -
          (base : Rat) ^ (h - 1) * (base : Rat) ≠ 0 := by
    simpa [generalNegativeDenominator, Rat.intCast_sub, Rat.intCast_add,
      Rat.intCast_pow, Rat.intCast_natCast, Rat.intCast_ofNat,
      qSucc, q2Succ, hSucc] using denominatorNonzeroRat
  unfold generalNegativeZeroState generalNegativeDeletedState deleteDigit
  simp only [show h - 1 - (h - 1) = 0 by omega, Rat.pow_zero,
    Rat.intCast_neg, Rat.intCast_one, Rat.div_def]
  unfold generalNegativeDenominator
  simp only [Rat.intCast_sub, Rat.intCast_add, Rat.intCast_pow,
    Rat.intCast_natCast, Rat.intCast_ofNat]
  rw [qSucc, q2Succ, hSucc]
  have baseCancel := Rat.mul_inv_cancel (base : Rat) baseNonzero
  have denominatorCancel := Rat.mul_inv_cancel
    ((1 : Rat) + (base : Rat) ^ (Q - 1) * (base : Rat) +
      (base : Rat) ^ (2 * Q - 1) * (base : Rat) -
      (base : Rat) ^ (h - 1) * (base : Rat)) expandedDenominatorNonzero
  grind

theorem generalNegativeDeletedState_finv
    (base Q h : Nat) (baseAtLeastTwo : 2 ≤ base)
    (QPositive : 0 < Q) (hPositive : 0 < h) :
    Finv base (generalNegativeDeletedState base Q h) =
      candidateState base Q h 0 := by
  have sourceNotDivisible := generalNegativeDenominator_not_dvd
    base Q h baseAtLeastTwo QPositive hPositive
  have targetNotDivisible := candidateDenominator_not_dvd base Q h
    baseAtLeastTwo QPositive hPositive
  have sourceNonzeroInt : generalNegativeDenominator base Q h ≠ 0 :=
    fun denominatorZero => sourceNotDivisible (by
      rw [denominatorZero]
      exact Int.dvd_zero _)
  have targetNonzeroInt : candidateDenominator base Q h ≠ 0 :=
    fun denominatorZero => targetNotDivisible (by
      rw [denominatorZero]
      exact Int.dvd_zero _)
  have sourceNonzero : (generalNegativeDenominator base Q h : Rat) ≠ 0 := by
    exact_mod_cast sourceNonzeroInt
  have targetNonzero : (candidateDenominator base Q h : Rat) ≠ 0 := by
    exact_mod_cast targetNonzeroInt
  have qSucc : (base : Rat) ^ Q =
      (base : Rat) ^ (Q - 1) * (base : Rat) := by
    calc
      (base : Rat) ^ Q = (base : Rat) ^ (Q - 1 + 1) := by
        congr 1 <;> omega
      _ = _ := by rw [Rat.pow_succ]
  have q2Succ : (base : Rat) ^ (2 * Q) =
      (base : Rat) ^ (2 * Q - 1) * (base : Rat) := by
    calc
      (base : Rat) ^ (2 * Q) =
          (base : Rat) ^ (2 * Q - 1 + 1) := by congr 1 <;> omega
      _ = _ := by rw [Rat.pow_succ]
  have hSucc : (base : Rat) ^ h =
      (base : Rat) ^ (h - 1) * (base : Rat) := by
    calc
      (base : Rat) ^ h = (base : Rat) ^ (h - 1 + 1) := by
        congr 1 <;> omega
      _ = _ := by rw [Rat.pow_succ]
  have expandedSourceNonzero :
      (1 : Rat) + (base : Rat) ^ (Q - 1) * (base : Rat) +
          (base : Rat) ^ (2 * Q - 1) * (base : Rat) -
          (base : Rat) ^ (h - 1) * (base : Rat) ≠ 0 := by
    simpa [generalNegativeDenominator, Rat.intCast_sub, Rat.intCast_add,
      Rat.intCast_pow, Rat.intCast_natCast, Rat.intCast_ofNat,
      qSucc, q2Succ, hSucc] using sourceNonzero
  have expandedTargetNonzero :
      (1 : Rat) - (base : Rat) ^ (Q - 1) * (base : Rat) -
          (base : Rat) ^ (2 * Q - 1) * (base : Rat) +
          (base : Rat) ^ (h - 1) * (base : Rat) ≠ 0 := by
    simpa [candidateDenominator, Rat.intCast_sub, Rat.intCast_add,
      Rat.intCast_pow, Rat.intCast_natCast, Rat.intCast_ofNat,
      qSucc, q2Succ, hSucc] using targetNonzero
  unfold Finv generalNegativeDeletedState candidateState candidateNumerator
    generalNegativeDenominator candidateDenominator
  simp only [Nat.sub_zero, Rat.intCast_sub, Rat.intCast_add,
    Rat.intCast_pow, Rat.intCast_natCast, Rat.intCast_ofNat, Rat.div_def]
  rw [qSucc, q2Succ, hSucc]
  have sourceCancel := Rat.mul_inv_cancel
    ((1 : Rat) + (base : Rat) ^ (Q - 1) * (base : Rat) +
      (base : Rat) ^ (2 * Q - 1) * (base : Rat) -
      (base : Rat) ^ (h - 1) * (base : Rat)) expandedSourceNonzero
  have targetCancel := Rat.mul_inv_cancel
    ((1 : Rat) - (base : Rat) ^ (Q - 1) * (base : Rat) -
      (base : Rat) ^ (2 * Q - 1) * (base : Rat) +
      (base : Rat) ^ (h - 1) * (base : Rat)) expandedTargetNonzero
  grind

theorem generalNegativeZero_step
    (base phase Q h deleted : Nat) (baseAtLeastTwo : 2 ≤ base)
    (QPositive : 0 < Q) (hPositive : 0 < h)
    (deletedBelow : deleted < h - 1) :
    SameLine
      ((zeroLoop phase).act base
        (phaseAffine phase
          (generalNegativeZeroState base Q h deleted)))
      (phaseAffine phase
        (generalNegativeZeroState base Q h (deleted + 1))) := by
  have deletedEq := generalNegativeZeroState_delete_zero base Q h deleted
    baseAtLeastTwo deletedBelow
  have action := physicalLetter_affine_sameLine_of_local
    (sourcePhase := phase) (targetPhase := phase) (digit := 0)
    (preCoefficient := 0) (postCoefficient := 0)
    (postSign := .positive) (by omega)
    (generalNegativeZeroState_local base Q h deleted baseAtLeastTwo
      QPositive hPositive) (by
      rw [positive_zero_mutation]
      change LocalAt base
        (Vec2.affine
          (deleteDigit (base : Rat) 0
            (generalNegativeZeroState base Q h deleted)))
      rw [deletedEq]
      exact generalNegativeZeroState_local base Q h (deleted + 1)
        baseAtLeastTwo QPositive hPositive)
  simp [localLetterMap] at action
  change SameLine
    (Matrix2.apply
      (IntMatrix2.cast
        (physicalLetter base phase phase 0 0 .positive 0))
      (phaseAffine phase (generalNegativeZeroState base Q h deleted)))
    (phaseAffine phase
      (deleteDigit (base : Rat) 0
        (generalNegativeZeroState base Q h deleted))) at action
  rw [deletedEq] at action
  simpa [zeroLoop, MutatingScan.loopLetter, PhysicalTemplate.act,
    PhysicalTemplate.matrix] using action

theorem generalNegativeMarker_step
    (base source target Q h : Nat) (baseAtLeastTwo : 2 ≤ base)
    (QPositive : 0 < Q) (hPositive : 0 < h) :
    SameLine
      ((inverseFNegativeExit source target).act base
        (phaseAffine source
          (generalNegativeZeroState base Q h (h - 1))))
      (phaseAffine target (candidateState base Q h 0)) := by
  have deletedEq := generalNegativeZeroState_delete_marker base Q h
    baseAtLeastTwo QPositive hPositive
  have outputEq := generalNegativeDeletedState_finv base Q h baseAtLeastTwo
    QPositive hPositive
  have action := physicalLetter_affine_sameLine_of_local
    (sourcePhase := source) (targetPhase := target) (digit := -1)
    (preCoefficient := 0) (postCoefficient := -2)
    (postSign := .positive) (by omega)
    (generalNegativeZeroState_local base Q h (h - 1) baseAtLeastTwo
      QPositive hPositive) (by
      rw [positive_zero_mutation]
      change LocalAt base
        (Vec2.affine
          (deleteDigit (base : Rat) (-1)
            (generalNegativeZeroState base Q h (h - 1))))
      rw [deletedEq]
      exact generalNegativeDeletedState_local base Q h baseAtLeastTwo
        QPositive hPositive)
  simp [localLetterMap] at action
  change SameLine
    (Matrix2.apply
      (IntMatrix2.cast
        (physicalLetter base source target (-1) 0 .positive (-2)))
      (phaseAffine source
        (generalNegativeZeroState base Q h (h - 1))))
    (phaseAffine target
      (mutationMap base .positive (-2)
        (deleteDigit (base : Rat) (-1)
          (generalNegativeZeroState base Q h (h - 1))))) at action
  rw [deletedEq, positive_minus_two_mutation, outputEq] at action
  simpa [inverseFNegativeExit, MutatingScan.exitLetter,
    PhysicalTemplate.act, PhysicalTemplate.matrix] using action

def generalNegativeWord (source target h : Nat) : List PhysicalTemplate :=
  List.replicate (h - 1) (zeroLoop source) ++
    [inverseFNegativeExit source target]

theorem generalNegativeTail_correct
    (base source target Q h deleted remaining : Nat)
    (baseAtLeastTwo : 2 ≤ base) (QPositive : 0 < Q)
    (hPositive : 0 < h) (sumEq : deleted + remaining = h - 1) :
    SameLine
      (physicalWordAction base
        (List.replicate remaining (zeroLoop source) ++
          [inverseFNegativeExit source target])
        (phaseAffine source
          (generalNegativeZeroState base Q h deleted)))
      (phaseAffine target (candidateState base Q h 0)) := by
  induction remaining generalizing deleted with
  | zero =>
      simpa [physicalWordAction, show deleted = h - 1 by omega] using
        generalNegativeMarker_step base source target Q h baseAtLeastTwo
          QPositive hPositive
  | succ remaining inductionHypothesis =>
      have firstStep := generalNegativeZero_step base source Q h deleted
        baseAtLeastTwo QPositive hPositive (by omega)
      have tailRun := inductionHypothesis (deleted := deleted + 1) (by omega)
      exact physicalWordAction_cons_sameLine base (zeroLoop source)
        (List.replicate remaining (zeroLoop source) ++
          [inverseFNegativeExit source target]) firstStep tailRun

theorem generalNegativeWord_correct
    (base source target Q h : Nat) (baseAtLeastTwo : 2 ≤ base)
    (QPositive : 0 < Q) (hPositive : 0 < h)
    (hBelowDouble : h < 2 * Q) :
    SameLine
      (physicalWordAction base (generalNegativeWord source target h)
        (phaseAffine source
          (twoProjectionGeneralGuessState base (Q - 1) (2 * Q - h))))
      (phaseAffine target (candidateState base Q h 0)) := by
  rw [← generalNegativeZeroState_zero base Q h baseAtLeastTwo QPositive
    hPositive hBelowDouble]
  simpa [generalNegativeWord] using
    generalNegativeTail_correct base source target Q h 0 (h - 1)
      baseAtLeastTwo QPositive hPositive (by omega)

def negativeZeroState (base first deleted : Nat) : Rat :=
  -((base : Rat) ^ (first - deleted)) /
    (1 + (base : Rat) ^ (2 * first + 2))

theorem negativeZeroState_zero
    (base first : Nat) (baseAtLeastTwo : 2 ≤ base) :
    negativeZeroState base first 0 =
      twoProjectionGuessedState base first := by
  have auxiliary := twoProjectionGuessedState_auxiliary base first
    baseAtLeastTwo
  let q : Rat := (base : Rat) ^ (first + 1)
  have squarePower : q ^ 2 = (base : Rat) ^ (2 * first + 2) := by
    calc
      q ^ 2 = q * q := by
        rw [show (2 : Nat) = 1 + 1 by omega,
          Lean.Grind.Semiring.pow_add]
        simp only [Rat.pow_one]
      _ = (base : Rat) ^ (first + 1) *
          (base : Rat) ^ (first + 1) := by rfl
      _ = (base : Rat) ^ ((first + 1) + (first + 1)) :=
        (Lean.Grind.Semiring.pow_add (base : Rat) (first + 1)
          (first + 1)).symm
      _ = (base : Rat) ^ (2 * first + 2) := by congr 1 <;> omega
  have firstPower : (base : Rat) ^ (first + 1) =
      (base : Rat) ^ first * (base : Rat) := by rw [Rat.pow_succ]
  have baseNonzero : (base : Rat) ≠ 0 := by
    simpa using (show base ≠ 0 by omega)
  dsimp at auxiliary
  rw [squarePower] at auxiliary
  have productEq :
      (base : Rat) * negativeZeroState base first 0 =
        (base : Rat) * twoProjectionGuessedState base first := by
    rw [auxiliary]
    unfold negativeZeroState
    simp only [Nat.sub_zero, Rat.div_def]
    rw [firstPower]
    grind
  calc
    negativeZeroState base first 0 =
        ((base : Rat)⁻¹ * (base : Rat)) *
          negativeZeroState base first 0 := by
      rw [Rat.inv_mul_cancel (base : Rat) baseNonzero, Rat.one_mul]
    _ = (base : Rat)⁻¹ *
        ((base : Rat) * negativeZeroState base first 0) := by
      rw [Rat.mul_assoc]
    _ = (base : Rat)⁻¹ *
        ((base : Rat) * twoProjectionGuessedState base first) := by
      rw [productEq]
    _ = ((base : Rat)⁻¹ * (base : Rat)) *
        twoProjectionGuessedState base first := by rw [Rat.mul_assoc]
    _ = twoProjectionGuessedState base first := by
      rw [Rat.inv_mul_cancel (base : Rat) baseNonzero, Rat.one_mul]

theorem negativeZeroState_local
    (base first deleted : Nat) (baseAtLeastTwo : 2 ≤ base) :
    LocalAt base (Vec2.affine (negativeZeroState base first deleted)) := by
  have denominatorNotDivisible := one_add_power_not_dvd base
    (2 * first + 2) baseAtLeastTwo (by omega)
  have localFraction := local_affine_integer_div
    (prime := base)
    (numerator := -((base : Int) ^ (first - deleted)))
    (denominator := 1 + (base : Int) ^ (2 * first + 2))
    denominatorNotDivisible
  simpa [negativeZeroState, Rat.intCast_neg, Rat.intCast_pow,
    Rat.intCast_natCast, Rat.intCast_add] using localFraction

theorem negativeZeroState_delete_zero
    (base first deleted : Nat) (baseAtLeastTwo : 2 ≤ base)
    (deletedBelow : deleted < first) :
    deleteDigit (base : Rat) 0 (negativeZeroState base first deleted) =
      negativeZeroState base first (deleted + 1) := by
  unfold negativeZeroState deleteDigit
  have baseNonzero : (base : Rat) ≠ 0 := by
    simpa using (show base ≠ 0 by omega)
  have exponentEq : first - deleted =
      first - (deleted + 1) + 1 := by omega
  rw [exponentEq, Rat.pow_succ]
  simp only [Rat.intCast_zero, Rat.div_def]
  have baseCancel := Rat.mul_inv_cancel (base : Rat) baseNonzero
  grind

def negativeDeletedState (base first : Nat) : Rat :=
  (base : Rat) ^ (2 * first + 1) /
    (1 + (base : Rat) ^ (2 * first + 2))

theorem negativeZeroState_delete_marker
    (base first : Nat) (baseAtLeastTwo : 2 ≤ base) :
    deleteDigit (base : Rat) (-1) (negativeZeroState base first first) =
      negativeDeletedState base first := by
  unfold negativeZeroState negativeDeletedState deleteDigit
  have baseNonzero : (base : Rat) ≠ 0 := by
    simpa using (show base ≠ 0 by omega)
  have denominatorNonzero :
      (1 : Rat) + (base : Rat) ^ (2 * first + 2) ≠ 0 := by
    let power : Nat := base ^ (2 * first + 2)
    have : (1 : Rat) + (power : Rat) ≠ 0 := by
      have positive : (0 : Rat) < ((1 + power : Nat) : Rat) := by
        exact_mod_cast (show 0 < 1 + power by omega)
      simpa [Rat.natCast_add] using Rat.ne_of_gt positive
    simpa [power, Rat.natCast_pow] using this
  have powerSucc : (base : Rat) ^ (2 * first + 2) =
      (base : Rat) ^ (2 * first + 1) * (base : Rat) := by
    rw [Rat.pow_succ]
  simp only [Nat.sub_self, Rat.pow_zero, Rat.intCast_neg,
    Rat.intCast_one]
  rw [Rat.div_def, Rat.div_def]
  have baseCancel := Rat.mul_inv_cancel (base : Rat) baseNonzero
  have denominatorCancel := Rat.mul_inv_cancel
    ((1 : Rat) + (base : Rat) ^ (2 * first + 2)) denominatorNonzero
  grind

theorem negativeDeletedState_local
    (base first : Nat) (baseAtLeastTwo : 2 ≤ base) :
    LocalAt base (Vec2.affine (negativeDeletedState base first)) := by
  have denominatorNotDivisible := one_add_power_not_dvd base
    (2 * first + 2) baseAtLeastTwo (by omega)
  have localFraction := local_affine_integer_div
    (prime := base) (numerator := (base : Int) ^ (2 * first + 1))
    (denominator := 1 + (base : Int) ^ (2 * first + 2))
    denominatorNotDivisible
  simpa [negativeDeletedState, Rat.intCast_pow, Rat.intCast_natCast,
    Rat.intCast_add] using localFraction

theorem negativeZero_step
    (base phase first deleted : Nat) (baseAtLeastTwo : 2 ≤ base)
    (deletedBelow : deleted < first) :
    SameLine
      ((zeroLoop phase).act base
        (phaseAffine phase (negativeZeroState base first deleted)))
      (phaseAffine phase
        (negativeZeroState base first (deleted + 1))) := by
  have deletedEq := negativeZeroState_delete_zero base first deleted
    baseAtLeastTwo deletedBelow
  have action := physicalLetter_affine_sameLine_of_local
    (sourcePhase := phase) (targetPhase := phase) (digit := 0)
    (preCoefficient := 0) (postCoefficient := 0)
    (postSign := .positive) (by omega)
    (negativeZeroState_local base first deleted baseAtLeastTwo) (by
      rw [positive_zero_mutation]
      change LocalAt base
        (Vec2.affine
          (deleteDigit (base : Rat) 0
            (negativeZeroState base first deleted)))
      rw [deletedEq]
      exact negativeZeroState_local base first (deleted + 1) baseAtLeastTwo)
  simp [localLetterMap] at action
  have deletedRaw := deletedEq
  unfold deleteDigit at deletedRaw
  simp only [Rat.intCast_zero] at deletedRaw
  rw [deletedRaw] at action
  simpa [zeroLoop, MutatingScan.loopLetter, PhysicalTemplate.act,
    PhysicalTemplate.matrix, phaseAffine] using action

theorem negativeMarker_step
    (base source target first : Nat) (baseAtLeastTwo : 2 ≤ base) :
    SameLine
      ((inverseFNegativeExit source target).act base
        (phaseAffine source (negativeZeroState base first first)))
      (phaseAffine target (twoProjectionCandidate base first)) := by
  have deletedEq := negativeZeroState_delete_marker base first baseAtLeastTwo
  have outputEq : mutationMap base .positive (-2)
      (negativeDeletedState base first) =
      twoProjectionCandidate base first := by
    rw [positive_minus_two_mutation]
    unfold twoProjectionCandidate twoProjectionNegativeState
    have negativeScan : scanDigits (base : Rat)
        (markerScanDigits first (-1))
        (twoProjectionGuessedState base first) =
      negativeDeletedState base first := by
      rw [← negativeZeroState_zero base first baseAtLeastTwo]
      have baseNonzero : (base : Rat) ≠ 0 := by
        simpa using (show base ≠ 0 by omega)
      rw [scanDigits_eq]
      · rw [digitPolynomial_markerScanDigits,
          markerScanDigits_length]
        rw [show first + 1 = first + 1 by rfl]
        unfold negativeZeroState negativeDeletedState
        simp only [Nat.sub_zero, Rat.intCast_neg, Rat.intCast_one]
        have powerNonzero := pow_ne_zero baseNonzero (first + 1)
        have denominatorNonzero :
            (1 : Rat) + (base : Rat) ^ (2 * first + 2) ≠ 0 := by
          let power : Nat := base ^ (2 * first + 2)
          have positive : (0 : Rat) < ((1 + power : Nat) : Rat) := by
            exact_mod_cast (show 0 < 1 + power by omega)
          simpa [power, Rat.natCast_add, Rat.natCast_pow] using
            Rat.ne_of_gt positive
        simp only [Rat.div_def]
        have powerCancel := Rat.mul_inv_cancel
          ((base : Rat) ^ (first + 1)) powerNonzero
        have denominatorCancel := Rat.mul_inv_cancel
          ((1 : Rat) + (base : Rat) ^ (2 * first + 2))
          denominatorNonzero
        grind
      · exact baseNonzero
    rw [negativeScan]
  have action := physicalLetter_affine_sameLine_of_local
    (sourcePhase := source) (targetPhase := target) (digit := -1)
    (preCoefficient := 0) (postCoefficient := -2)
    (postSign := .positive) (by omega)
    (negativeZeroState_local base first first baseAtLeastTwo) (by
      rw [positive_zero_mutation]
      change LocalAt base
        (Vec2.affine
          (deleteDigit (base : Rat) (-1)
            (negativeZeroState base first first)))
      rw [deletedEq]
      exact negativeDeletedState_local base first baseAtLeastTwo)
  simp [localLetterMap] at action
  change SameLine
    (Matrix2.apply
      (IntMatrix2.cast
        (physicalLetter base source target (-1) 0 .positive (-2)))
      (phaseAffine source (negativeZeroState base first first)))
    (phaseAffine target
      (mutationMap base .positive (-2)
        (deleteDigit (base : Rat) (-1)
          (negativeZeroState base first first)))) at action
  rw [deletedEq, outputEq] at action
  simpa [inverseFNegativeExit, MutatingScan.exitLetter,
    PhysicalTemplate.act, PhysicalTemplate.matrix] using action

theorem negativeTail_correct
    (base source target first deleted remaining : Nat)
    (baseAtLeastTwo : 2 ≤ base) (sumEq : deleted + remaining = first) :
    SameLine
      (physicalWordAction base
        (List.replicate remaining (zeroLoop source) ++
          [inverseFNegativeExit source target])
        (phaseAffine source (negativeZeroState base first deleted)))
      (phaseAffine target (twoProjectionCandidate base first)) := by
  induction remaining generalizing deleted with
  | zero =>
      simpa [physicalWordAction, show deleted = first by omega] using
        negativeMarker_step base source target first baseAtLeastTwo
  | succ remaining inductionHypothesis =>
      have firstStep := negativeZero_step base source first deleted
        baseAtLeastTwo (by omega)
      have tailRun := inductionHypothesis (deleted := deleted + 1) (by omega)
      exact physicalWordAction_cons_sameLine base (zeroLoop source)
        (List.replicate remaining (zeroLoop source) ++
          [inverseFNegativeExit source target]) firstStep tailRun

theorem negativeWord_correct
    (base source target first : Nat) (baseAtLeastTwo : 2 ≤ base) :
    SameLine
      (physicalWordAction base (negativeWord source target first)
        (phaseAffine source (twoProjectionGuessedState base first)))
      (phaseAffine target (twoProjectionCandidate base first)) := by
  rw [← negativeZeroState_zero base first baseAtLeastTwo]
  simpa [negativeWord] using
    negativeTail_correct base source target first 0 first baseAtLeastTwo
      (by omega)

theorem validatorWord_correct
    (base source target counter : Nat) (baseAtLeastTwo : 2 ≤ base) :
    SameLine
      (physicalWordAction base (validatorWord source target counter)
        (phaseAffine source (unaryCode base counter)))
      (phaseAffine target (unaryCode base counter)) := by
  have action := MutatingScan.word_correct base source target
    (List.replicate counter 0) [] 1 .positive 0 baseAtLeastTwo
  rw [positive_zero_mutation] at action
  simpa [validatorWord, unaryCode, unaryDigits, List.append_assoc]
    using action

theorem acceptedWord_correct
    (base source target guessPhase negativePhase firstValidator
      secondValidator first : Nat) (baseAtLeastTwo : 2 ≤ base) :
    SameLine
      (physicalWordAction base
        (acceptedWord source target guessPhase negativePhase firstValidator
          secondValidator first)
        (phaseAffine source
          (twoFieldCode base first (2 * first + 1))))
      (phaseAffine target (unaryCode base (2 * first + 1))) := by
  have firstRun := firstScanWord_correct base source guessPhase first
    baseAtLeastTwo
  have guessRun := guessWord_correct base guessPhase negativePhase first
    baseAtLeastTwo
  have negativeRun := negativeWord_correct base negativePhase firstValidator
    first baseAtLeastTwo
  have candidateEq := twoProjectionCandidate_eq base first baseAtLeastTwo
  rw [candidateEq] at negativeRun
  have firstValidatorRun := validatorWord_correct base firstValidator
    secondValidator (2 * first + 1) baseAtLeastTwo
  have secondValidatorRun := validatorWord_correct base secondValidator target
    (2 * first + 1) baseAtLeastTwo
  have throughGuess := physicalWordAction_append_sameLine base
    (firstScanWord source guessPhase first)
    (guessWord guessPhase negativePhase first) firstRun guessRun
  have throughNegative := physicalWordAction_append_sameLine base
    (firstScanWord source guessPhase first ++
      guessWord guessPhase negativePhase first)
    (negativeWord negativePhase firstValidator first) throughGuess negativeRun
  have throughFirstValidator := physicalWordAction_append_sameLine base
    (firstScanWord source guessPhase first ++
      guessWord guessPhase negativePhase first ++
      negativeWord negativePhase firstValidator first)
    (validatorWord firstValidator secondValidator (2 * first + 1))
    throughNegative firstValidatorRun
  have complete := physicalWordAction_append_sameLine base
    (firstScanWord source guessPhase first ++
      guessWord guessPhase negativePhase first ++
      negativeWord negativePhase firstValidator first ++
      validatorWord firstValidator secondValidator (2 * first + 1))
    (validatorWord secondValidator target (2 * first + 1))
    throughFirstValidator secondValidatorRun
  simpa [acceptedWord, List.append_assoc] using complete

/-- Complete accepted execution, including exact alphabet, length, endpoint,
and locality of every physical prefix. -/
theorem accepted_execution
    (base source target guessPhase negativePhase firstValidator
      secondValidator first : Nat) (baseAtLeastTwo : 2 ≤ base) :
    let moduleWord := acceptedWord source target guessPhase negativePhase
      firstValidator secondValidator first
    WordOver
        (alphabet source target guessPhase negativePhase firstValidator
          secondValidator) moduleWord ∧
      moduleWord.length = 7 * first + 7 ∧
      SameLine
        (physicalWordAction base moduleWord
          (phaseAffine source
            (twoFieldCode base first (2 * first + 1))))
        (phaseAffine target (unaryCode base (2 * first + 1))) ∧
      AllStatesLocal base moduleWord
        (phaseAffine source
          (twoFieldCode base first (2 * first + 1))) := by
  dsimp
  have action := acceptedWord_correct base source target guessPhase
    negativePhase firstValidator secondValidator first baseAtLeastTwo
  have phaseLocal' {phase : Nat} {value : Rat}
      (membership : LocalAt base (Vec2.affine value)) :
      LocalAt base (phaseAffine phase value) := by
    rw [show phaseAffine phase value =
        Matrix2.apply (IntMatrix2.cast (chart phase)) (Vec2.affine value) by
      simpa [phaseAffine] using (chart_apply phase value).symm]
    exact (local_chart_iff base phase _).mpr membership
  have inputLocal := phaseLocal' (phase := source)
    (periodicCode_local_affine base (twoFieldDigits first (2 * first + 1))
      baseAtLeastTwo (by simp [twoFieldDigits]))
  have finalLocal := phaseLocal' (phase := target)
    (periodicCode_local_affine base (unaryDigits (2 * first + 1))
      baseAtLeastTwo (by simp [unaryDigits]))
  have outputNonzero := physicalWordAction_nonzero (prime := base) (by omega)
    (acceptedWord source target guessPhase negativePhase firstValidator
      secondValidator first) inputLocal.1
  have actualFinalLocal := LocalAt.of_sameLine finalLocal outputNonzero action
  exact ⟨acceptedWord_wordOver source target guessPhase negativePhase
      firstValidator secondValidator first,
    acceptedWord_length source target guessPhase negativePhase firstValidator
      secondValidator first,
    action, allStatesLocal_of_final_local (by omega) _ inputLocal.1
      actualFinalLocal⟩

/-! ## Phase-and-digit classification for the converse -/

private theorem letter_source_bound
    {phaseCount source target guessPhase negativePhase firstValidator
      secondValidator : Nat} {letter : PhysicalTemplate}
    (layout : PhaseLayout phaseCount source guessPhase negativePhase
      firstValidator secondValidator)
    (letterMem : letter ∈ alphabet source target guessPhase negativePhase
      firstValidator secondValidator) :
    letter.sourcePhase < phaseCount := by
  simp [alphabet] at letterMem
  rcases letterMem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl <;>
    simp [zeroLoop, markerOneExit, inverseTZeroExit,
      inverseFNegativeExit, MutatingScan.loopLetter, MutatingScan.exitLetter,
      layout.sourceBound, layout.guessBound, layout.negativeBound,
      layout.firstValidatorBound, layout.secondValidatorBound]

private theorem letter_reserved
    {source target guessPhase negativePhase firstValidator secondValidator : Nat}
    {letter : PhysicalTemplate}
    (letterMem : letter ∈ alphabet source target guessPhase negativePhase
      firstValidator secondValidator) :
    ReservedDigit letter.digit := by
  simp [alphabet] at letterMem
  rcases letterMem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl <;>
    simp [zeroLoop, markerOneExit, inverseTZeroExit,
      inverseFNegativeExit, MutatingScan.loopLetter, MutatingScan.exitLetter,
      ReservedDigit]

/-- Every two-projection letter starts in one of the five active module
phases. -/
theorem letter_source_mem_active
    {source target guessPhase negativePhase firstValidator secondValidator :
      Nat} {letter : PhysicalTemplate}
    (letterMem : letter ∈ alphabet source target guessPhase negativePhase
      firstValidator secondValidator) :
    letter.sourcePhase ∈
      [source, guessPhase, negativePhase, firstValidator, secondValidator] := by
  simp [alphabet] at letterMem
  rcases letterMem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl <;>
    simp [zeroLoop, markerOneExit, inverseTZeroExit,
      inverseFNegativeExit, MutatingScan.loopLetter, MutatingScan.exitLetter]

theorem public_letter_source_bound
    {phaseCount source target guessPhase negativePhase firstValidator
      secondValidator : Nat} {letter : PhysicalTemplate}
    (layout : PhaseLayout phaseCount source guessPhase negativePhase
      firstValidator secondValidator)
    (letterMem : letter ∈ alphabet source target guessPhase negativePhase
      firstValidator secondValidator) :
    letter.sourcePhase < phaseCount :=
  letter_source_bound layout letterMem

theorem public_letter_reserved
    {source target guessPhase negativePhase firstValidator secondValidator : Nat}
    {letter : PhysicalTemplate}
    (letterMem : letter ∈ alphabet source target guessPhase negativePhase
      firstValidator secondValidator) :
    ReservedDigit letter.digit :=
  letter_reserved letterMem

private theorem force_metadata
    {prime phaseCount source target guessPhase negativePhase firstValidator
      secondValidator actualPhase : Nat}
    {actualDigit : Int} {state : Vec2} {letter : PhysicalTemplate}
    (primeProperty : IsPrime prime) (primeBound : 6 * phaseCount < prime)
    (layout : PhaseLayout phaseCount source guessPhase negativePhase
      firstValidator secondValidator)
    (actualBound : actualPhase < phaseCount)
    (membership : InPhaseAt prime actualPhase actualDigit state)
    (letterMem : letter ∈ alphabet source target guessPhase negativePhase
      firstValidator secondValidator)
    (outputLocal : LocalAt prime (letter.act prime state)) :
    actualPhase = letter.sourcePhase ∧ actualDigit = letter.digit := by
  apply membership.physicalLetter_source_digit_unique primeProperty
    primeBound actualBound (letter_source_bound layout letterMem)
    (letter_reserved letterMem)
  simpa [PhysicalTemplate.act, PhysicalTemplate.matrix] using outputLocal

theorem source_zero_letter
    {prime phaseCount source target guessPhase negativePhase firstValidator
      secondValidator : Nat} {state : Vec2} {letter : PhysicalTemplate}
    (primeProperty : IsPrime prime) (primeBound : 6 * phaseCount < prime)
    (layout : PhaseLayout phaseCount source guessPhase negativePhase
      firstValidator secondValidator)
    (membership : InPhaseAt prime source 0 state)
    (letterMem : letter ∈ alphabet source target guessPhase negativePhase
      firstValidator secondValidator)
    (outputLocal : LocalAt prime (letter.act prime state)) :
    letter = zeroLoop source := by
  have forced := force_metadata primeProperty primeBound layout
    layout.sourceBound membership letterMem outputLocal
  simp [alphabet] at letterMem
  rcases letterMem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl
  · rfl
  · simp [markerOneExit, MutatingScan.exitLetter] at forced
  · exact False.elim (layout.sourceGuessDistinct forced.1)
  · exact False.elim (layout.sourceGuessDistinct forced.1)
  · exact False.elim (layout.sourceNegativeDistinct forced.1)
  · exact False.elim (layout.sourceNegativeDistinct forced.1)
  · exact False.elim (layout.sourceFirstValidatorDistinct forced.1)
  · exact False.elim (layout.sourceFirstValidatorDistinct forced.1)
  · exact False.elim (layout.sourceSecondValidatorDistinct forced.1)
  · exact False.elim (layout.sourceSecondValidatorDistinct forced.1)

theorem source_marker_letter
    {prime phaseCount source target guessPhase negativePhase firstValidator
      secondValidator : Nat} {state : Vec2} {letter : PhysicalTemplate}
    (primeProperty : IsPrime prime) (primeBound : 6 * phaseCount < prime)
    (layout : PhaseLayout phaseCount source guessPhase negativePhase
      firstValidator secondValidator)
    (membership : InPhaseAt prime source 1 state)
    (letterMem : letter ∈ alphabet source target guessPhase negativePhase
      firstValidator secondValidator)
    (outputLocal : LocalAt prime (letter.act prime state)) :
    letter = markerOneExit source guessPhase := by
  have forced := force_metadata primeProperty primeBound layout
    layout.sourceBound membership letterMem outputLocal
  simp [alphabet] at letterMem
  rcases letterMem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl
  · simp [zeroLoop, MutatingScan.loopLetter] at forced
  · rfl
  · exact False.elim (layout.sourceGuessDistinct forced.1)
  · exact False.elim (layout.sourceGuessDistinct forced.1)
  · exact False.elim (layout.sourceNegativeDistinct forced.1)
  · exact False.elim (layout.sourceNegativeDistinct forced.1)
  · exact False.elim (layout.sourceFirstValidatorDistinct forced.1)
  · exact False.elim (layout.sourceFirstValidatorDistinct forced.1)
  · exact False.elim (layout.sourceSecondValidatorDistinct forced.1)
  · exact False.elim (layout.sourceSecondValidatorDistinct forced.1)

theorem guess_zero_letter
    {prime phaseCount source target guessPhase negativePhase firstValidator
      secondValidator : Nat} {state : Vec2} {letter : PhysicalTemplate}
    (primeProperty : IsPrime prime) (primeBound : 6 * phaseCount < prime)
    (layout : PhaseLayout phaseCount source guessPhase negativePhase
      firstValidator secondValidator)
    (membership : InPhaseAt prime guessPhase 0 state)
    (letterMem : letter ∈ alphabet source target guessPhase negativePhase
      firstValidator secondValidator)
    (outputLocal : LocalAt prime (letter.act prime state)) :
    letter = zeroLoop guessPhase ∨
      letter = inverseTZeroExit guessPhase negativePhase := by
  have forced := force_metadata primeProperty primeBound layout
    layout.guessBound membership letterMem outputLocal
  simp [alphabet] at letterMem
  rcases letterMem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl
  · exact False.elim (layout.sourceGuessDistinct forced.1.symm)
  · exact False.elim (layout.sourceGuessDistinct forced.1.symm)
  · exact Or.inl rfl
  · exact Or.inr rfl
  · exact False.elim (layout.guessNegativeDistinct forced.1)
  · exact False.elim (layout.guessNegativeDistinct forced.1)
  · exact False.elim (layout.guessFirstValidatorDistinct forced.1)
  · exact False.elim (layout.guessFirstValidatorDistinct forced.1)
  · exact False.elim (layout.guessSecondValidatorDistinct forced.1)
  · exact False.elim (layout.guessSecondValidatorDistinct forced.1)

theorem negative_zero_letter
    {prime phaseCount source target guessPhase negativePhase firstValidator
      secondValidator : Nat} {state : Vec2} {letter : PhysicalTemplate}
    (primeProperty : IsPrime prime) (primeBound : 6 * phaseCount < prime)
    (layout : PhaseLayout phaseCount source guessPhase negativePhase
      firstValidator secondValidator)
    (membership : InPhaseAt prime negativePhase 0 state)
    (letterMem : letter ∈ alphabet source target guessPhase negativePhase
      firstValidator secondValidator)
    (outputLocal : LocalAt prime (letter.act prime state)) :
    letter = zeroLoop negativePhase := by
  have forced := force_metadata primeProperty primeBound layout
    layout.negativeBound membership letterMem outputLocal
  simp [alphabet] at letterMem
  rcases letterMem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl
  · exact False.elim (layout.sourceNegativeDistinct forced.1.symm)
  · exact False.elim (layout.sourceNegativeDistinct forced.1.symm)
  · exact False.elim (layout.guessNegativeDistinct forced.1.symm)
  · exact False.elim (layout.guessNegativeDistinct forced.1.symm)
  · rfl
  · simp [inverseFNegativeExit, MutatingScan.exitLetter] at forced
  · exact False.elim (layout.negativeFirstValidatorDistinct forced.1)
  · exact False.elim (layout.negativeFirstValidatorDistinct forced.1)
  · exact False.elim (layout.negativeSecondValidatorDistinct forced.1)
  · exact False.elim (layout.negativeSecondValidatorDistinct forced.1)

theorem negative_marker_letter
    {prime phaseCount source target guessPhase negativePhase firstValidator
      secondValidator : Nat} {state : Vec2} {letter : PhysicalTemplate}
    (primeProperty : IsPrime prime) (primeBound : 6 * phaseCount < prime)
    (layout : PhaseLayout phaseCount source guessPhase negativePhase
      firstValidator secondValidator)
    (membership : InPhaseAt prime negativePhase (-1) state)
    (letterMem : letter ∈ alphabet source target guessPhase negativePhase
      firstValidator secondValidator)
    (outputLocal : LocalAt prime (letter.act prime state)) :
    letter = inverseFNegativeExit negativePhase firstValidator := by
  have forced := force_metadata primeProperty primeBound layout
    layout.negativeBound membership letterMem outputLocal
  simp [alphabet] at letterMem
  rcases letterMem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl
  · exact False.elim (layout.sourceNegativeDistinct forced.1.symm)
  · exact False.elim (layout.sourceNegativeDistinct forced.1.symm)
  · exact False.elim (layout.guessNegativeDistinct forced.1.symm)
  · exact False.elim (layout.guessNegativeDistinct forced.1.symm)
  · simp [zeroLoop, MutatingScan.loopLetter] at forced
  · rfl
  · exact False.elim (layout.negativeFirstValidatorDistinct forced.1)
  · exact False.elim (layout.negativeFirstValidatorDistinct forced.1)
  · exact False.elim (layout.negativeSecondValidatorDistinct forced.1)
  · exact False.elim (layout.negativeSecondValidatorDistinct forced.1)

theorem first_validator_letter
    {prime phaseCount source target guessPhase negativePhase firstValidator
      secondValidator : Nat} {digit : Int} {state : Vec2}
    {letter : PhysicalTemplate}
    (primeProperty : IsPrime prime) (primeBound : 6 * phaseCount < prime)
    (layout : PhaseLayout phaseCount source guessPhase negativePhase
      firstValidator secondValidator)
    (membership : InPhaseAt prime firstValidator digit state)
    (letterMem : letter ∈ alphabet source target guessPhase negativePhase
      firstValidator secondValidator)
    (outputLocal : LocalAt prime (letter.act prime state)) :
    (digit = 0 ∧ letter = zeroLoop firstValidator) ∨
      (digit = 1 ∧ letter = markerOneExit firstValidator secondValidator) := by
  have forced := force_metadata primeProperty primeBound layout
    layout.firstValidatorBound membership letterMem outputLocal
  simp [alphabet] at letterMem
  rcases letterMem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl
  · exact False.elim (layout.sourceFirstValidatorDistinct forced.1.symm)
  · exact False.elim (layout.sourceFirstValidatorDistinct forced.1.symm)
  · exact False.elim (layout.guessFirstValidatorDistinct forced.1.symm)
  · exact False.elim (layout.guessFirstValidatorDistinct forced.1.symm)
  · exact False.elim (layout.negativeFirstValidatorDistinct forced.1.symm)
  · exact False.elim (layout.negativeFirstValidatorDistinct forced.1.symm)
  · exact Or.inl ⟨forced.2, rfl⟩
  · exact Or.inr ⟨forced.2, rfl⟩
  · exact False.elim (layout.validatorsDistinct forced.1)
  · exact False.elim (layout.validatorsDistinct forced.1)

theorem second_validator_letter
    {prime phaseCount source target guessPhase negativePhase firstValidator
      secondValidator : Nat} {digit : Int} {state : Vec2}
    {letter : PhysicalTemplate}
    (primeProperty : IsPrime prime) (primeBound : 6 * phaseCount < prime)
    (layout : PhaseLayout phaseCount source guessPhase negativePhase
      firstValidator secondValidator)
    (membership : InPhaseAt prime secondValidator digit state)
    (letterMem : letter ∈ alphabet source target guessPhase negativePhase
      firstValidator secondValidator)
    (outputLocal : LocalAt prime (letter.act prime state)) :
    (digit = 0 ∧ letter = zeroLoop secondValidator) ∨
      (digit = 1 ∧ letter = markerOneExit secondValidator target) := by
  have forced := force_metadata primeProperty primeBound layout
    layout.secondValidatorBound membership letterMem outputLocal
  simp [alphabet] at letterMem
  rcases letterMem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl
  · exact False.elim (layout.sourceSecondValidatorDistinct forced.1.symm)
  · exact False.elim (layout.sourceSecondValidatorDistinct forced.1.symm)
  · exact False.elim (layout.guessSecondValidatorDistinct forced.1.symm)
  · exact False.elim (layout.guessSecondValidatorDistinct forced.1.symm)
  · exact False.elim (layout.negativeSecondValidatorDistinct forced.1.symm)
  · exact False.elim (layout.negativeSecondValidatorDistinct forced.1.symm)
  · exact False.elim (layout.validatorsDistinct forced.1.symm)
  · exact False.elim (layout.validatorsDistinct forced.1.symm)
  · exact Or.inl ⟨forced.2, rfl⟩
  · exact Or.inr ⟨forced.2, rfl⟩

theorem generalNegativeState_inPhaseAt_before
    {prime negativePhase Q h deleted : Nat}
    (primeProperty : IsPrime prime) (QPositive : 0 < Q)
    (hPositive : 0 < h) (deletedBelow : deleted < h - 1) :
    InPhaseAt prime negativePhase 0
      (phaseAffine negativePhase
        (generalNegativeZeroState prime Q h deleted)) := by
  apply inPhaseAt_phaseAffine_integer (by simp [ReservedDigit])
    (generalNegativeDenominator_not_dvd prime Q h primeProperty.1 QPositive
      hPositive)
    (by
      simpa only [Int.zero_mul, Int.sub_zero] using
        generalNegativeZeroState_zero_residue prime h deleted deletedBelow)
  exact generalNegativeZeroState_sameLine_integer prime Q h deleted
    primeProperty.1 QPositive hPositive

theorem generalNegativeState_inPhaseAt_marker
    {prime negativePhase Q h : Nat}
    (primeProperty : IsPrime prime) (QPositive : 0 < Q)
    (hPositive : 0 < h) :
    InPhaseAt prime negativePhase (-1)
      (phaseAffine negativePhase
        (generalNegativeZeroState prime Q h (h - 1))) := by
  apply inPhaseAt_phaseAffine_integer (by simp [ReservedDigit])
    (generalNegativeDenominator_not_dvd prime Q h primeProperty.1 QPositive
      hPositive)
    (generalNegativeZeroState_marker_residue prime Q h QPositive hPositive)
  exact generalNegativeZeroState_sameLine_integer prime Q h (h - 1)
    primeProperty.1 QPositive hPositive

theorem candidateState_inPhaseAt_below_before
    {prime phase Q h deleted : Nat} (primeProperty : IsPrime prime)
    (QPositive : 0 < Q) (hPositive : 0 < h) (hBelowQ : h < Q)
    (deletedBelow : deleted < h - 1) :
    InPhaseAt prime phase 0
      (phaseAffine phase (candidateState prime Q h deleted)) := by
  apply inPhaseAt_phaseAffine_integer (by simp [ReservedDigit])
    (candidateDenominator_not_dvd prime Q h primeProperty.1 QPositive
      hPositive)
    (by
      simpa only [Int.zero_mul, Int.sub_zero] using
        candidate_zero_residue_below_h prime Q h deleted hBelowQ
          deletedBelow)
  exact candidateState_sameLine_integer prime Q h deleted primeProperty.1
    QPositive hPositive

theorem candidateState_inPhaseAt_below_marker
    {prime phase Q h : Nat} (primeProperty : IsPrime prime)
    (QPositive : 0 < Q) (hPositive : 0 < h) (hBelowQ : h < Q) :
    InPhaseAt prime phase (-1)
      (phaseAffine phase (candidateState prime Q h (h - 1))) := by
  apply inPhaseAt_phaseAffine_integer (by simp [ReservedDigit])
    (candidateDenominator_not_dvd prime Q h primeProperty.1 QPositive
      hPositive)
    (candidate_marker_residue_below prime Q h QPositive hPositive hBelowQ)
  exact candidateState_sameLine_integer prime Q h (h - 1)
    primeProperty.1 QPositive hPositive

theorem candidateState_inPhaseAt_above_before
    {prime phase Q h deleted : Nat} (primeProperty : IsPrime prime)
    (QPositive : 0 < Q) (QBelowH : Q < h) (hBelowDouble : h < 2 * Q)
    (deletedBelow : deleted < Q - 1) :
    InPhaseAt prime phase 0
      (phaseAffine phase (candidateState prime Q h deleted)) := by
  apply inPhaseAt_phaseAffine_integer (by simp [ReservedDigit])
    (candidateDenominator_not_dvd prime Q h primeProperty.1 QPositive
      (by omega))
    (by
      simpa only [Int.zero_mul, Int.sub_zero] using
        candidate_zero_residue_above_Q prime Q h deleted QPositive QBelowH
          deletedBelow)
  exact candidateState_sameLine_integer prime Q h deleted primeProperty.1
    QPositive (by omega)

theorem candidateState_inPhaseAt_above_marker
    {prime phase Q h : Nat} (primeProperty : IsPrime prime)
    (QPositive : 0 < Q) (QBelowH : Q < h) (hBelowDouble : h < 2 * Q) :
    InPhaseAt prime phase 1
      (phaseAffine phase (candidateState prime Q h (Q - 1))) := by
  apply inPhaseAt_phaseAffine_integer (by simp [ReservedDigit])
    (candidateDenominator_not_dvd prime Q h primeProperty.1 QPositive
      (by omega))
    (by
      simpa only [Int.one_mul] using
        (candidate_marker_residue_above prime Q h QPositive QBelowH
          hBelowDouble))
  exact candidateState_sameLine_integer prime Q h (Q - 1)
    primeProperty.1 QPositive (by omega)

theorem secondState_inPhaseAt_before
    {prime phase Q h deleted : Nat} (primeProperty : IsPrime prime)
    (QPositive : 0 < Q) (QBelowH : Q < h) (hBelowDouble : h < 2 * Q)
    (deletedBelow : deleted < h - Q - 1) :
    InPhaseAt prime phase 0
      (phaseAffine phase (secondState prime Q h deleted)) := by
  apply inPhaseAt_phaseAffine_integer (by simp [ReservedDigit])
    (candidateDenominator_not_dvd prime Q h primeProperty.1 QPositive
      (by omega))
    (by
      simpa only [Int.zero_mul, Int.sub_zero] using
        second_zero_residue prime Q h deleted QBelowH hBelowDouble
          deletedBelow)
  exact secondState_sameLine_integer prime Q h deleted primeProperty.1
    QPositive (by omega)

theorem secondState_inPhaseAt_marker
    {prime phase Q h : Nat} (primeProperty : IsPrime prime)
    (QPositive : 0 < Q) (QBelowH : Q < h) (hBelowDouble : h < 2 * Q) :
    InPhaseAt prime phase (-1)
      (phaseAffine phase (secondState prime Q h (h - Q - 1))) := by
  apply inPhaseAt_phaseAffine_integer (by simp [ReservedDigit])
    (candidateDenominator_not_dvd prime Q h primeProperty.1 QPositive
      (by omega))
    (second_marker_residue prime Q h QPositive QBelowH hBelowDouble)
  exact secondState_sameLine_integer prime Q h (h - Q - 1)
    primeProperty.1 QPositive (by omega)

theorem candidateZero_step
    (base phase Q h deleted : Nat) (baseAtLeastTwo : 2 ≤ base)
    (QPositive : 0 < Q) (hPositive : 0 < h)
    (deletedBelowQ : deleted < Q - 1)
    (deletedBelowH : deleted < h - 1) :
    SameLine
      ((zeroLoop phase).act base
        (phaseAffine phase (candidateState base Q h deleted)))
      (phaseAffine phase (candidateState base Q h (deleted + 1))) := by
  apply zeroLoop_affine_step base phase
    (candidateState base Q h deleted)
    (candidateState base Q h (deleted + 1)) baseAtLeastTwo
  · exact candidateState_local base Q h deleted baseAtLeastTwo QPositive
      hPositive
  · exact candidateState_local base Q h (deleted + 1) baseAtLeastTwo
      QPositive hPositive
  · exact candidateState_delete_zero base Q h deleted baseAtLeastTwo
      QPositive hPositive deletedBelowQ deletedBelowH

theorem candidateMarkerAbove_step
    (base source target Q h : Nat) (baseAtLeastTwo : 2 ≤ base)
    (QPositive : 0 < Q) (QBelowH : Q < h)
    (hBelowDouble : h < 2 * Q) :
    SameLine
      ((markerOneExit source target).act base
        (phaseAffine source (candidateState base Q h (Q - 1))))
      (phaseAffine target (secondState base Q h 0)) := by
  apply markerOneExit_affine_step base source target
    (candidateState base Q h (Q - 1)) (secondState base Q h 0)
    baseAtLeastTwo
  · exact candidateState_local base Q h (Q - 1) baseAtLeastTwo QPositive
      (by omega)
  · exact secondState_local base Q h 0 baseAtLeastTwo QPositive (by omega)
  · exact candidateState_delete_marker_above base Q h baseAtLeastTwo
      QPositive QBelowH hBelowDouble

theorem secondZero_step
    (base phase Q h deleted : Nat) (baseAtLeastTwo : 2 ≤ base)
    (QPositive : 0 < Q) (QBelowH : Q < h)
    (hBelowDouble : h < 2 * Q)
    (deletedBelow : deleted < h - Q - 1) :
    SameLine
      ((zeroLoop phase).act base
        (phaseAffine phase (secondState base Q h deleted)))
      (phaseAffine phase (secondState base Q h (deleted + 1))) := by
  apply zeroLoop_affine_step base phase
    (secondState base Q h deleted) (secondState base Q h (deleted + 1))
    baseAtLeastTwo
  · exact secondState_local base Q h deleted baseAtLeastTwo QPositive
      (by omega)
  · exact secondState_local base Q h (deleted + 1) baseAtLeastTwo QPositive
      (by omega)
  · exact secondState_delete_zero base Q h deleted baseAtLeastTwo
      QPositive QBelowH hBelowDouble deletedBelow

theorem first_validator_rejects_forbidden
    {prime phaseCount source target guessPhase negativePhase firstValidator
      secondValidator : Nat} {digit : Int} {state : Vec2}
    (primeProperty : IsPrime prime) (primeBound : 6 * phaseCount < prime)
    (layout : PhaseLayout phaseCount source guessPhase negativePhase
      firstValidator secondValidator)
    (digitNeZero : digit ≠ 0) (digitNeOne : digit ≠ 1)
    (membership : InPhaseAt prime firstValidator digit state)
    {letter : PhysicalTemplate}
    (letterMem : letter ∈ alphabet source target guessPhase negativePhase
      firstValidator secondValidator) :
    ¬LocalAt prime (letter.act prime state) := by
  intro outputLocal
  rcases first_validator_letter primeProperty primeBound layout membership
    letterMem outputLocal with ⟨digitZero, _⟩ | ⟨digitOne, _⟩
  · exact digitNeZero digitZero
  · exact digitNeOne digitOne

theorem second_validator_rejects_forbidden
    {prime phaseCount source target guessPhase negativePhase firstValidator
      secondValidator : Nat} {digit : Int} {state : Vec2}
    (primeProperty : IsPrime prime) (primeBound : 6 * phaseCount < prime)
    (layout : PhaseLayout phaseCount source guessPhase negativePhase
      firstValidator secondValidator)
    (digitNeZero : digit ≠ 0) (digitNeOne : digit ≠ 1)
    (membership : InPhaseAt prime secondValidator digit state)
    {letter : PhysicalTemplate}
    (letterMem : letter ∈ alphabet source target guessPhase negativePhase
      firstValidator secondValidator) :
    ¬LocalAt prime (letter.act prime state) := by
  intro outputLocal
  rcases second_validator_letter primeProperty primeBound layout membership
    letterMem outputLocal with ⟨digitZero, _⟩ | ⟨digitOne, _⟩
  · exact digitNeZero digitZero
  · exact digitNeOne digitOne

/-! ## Boundary-aware parsing through the guessed candidate -/

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

def sourceScanState (base first deleted : Nat) : Rat :=
  MutatingScan.zeroState base first 1
    (List.replicate (2 * first + 1) 0 ++ [-1]) deleted

def validatorState (base counter deleted : Nat) : Rat :=
  MutatingScan.zeroState base counter 1 [] deleted

theorem validatorState_zero (base counter : Nat) :
    validatorState base counter 0 = unaryCode base counter := by
  unfold validatorState MutatingScan.zeroState unaryCode unaryDigits
  rw [MutatingScan.zeroStateDigits_zero]
  simp

theorem validatorMarker_step
    (base source target counter : Nat) (baseAtLeastTwo : 2 ≤ base) :
    SameLine
      ((markerOneExit source target).act base
        (phaseAffine source (validatorState base counter counter)))
      (phaseAffine target (unaryCode base counter)) := by
  have step := MutatingScan.zeroExit_step base source target counter 1 []
    .positive 0 baseAtLeastTwo
  rw [positive_zero_mutation] at step
  simpa [validatorState, unaryCode, unaryDigits, markerOneExit]
    using step

theorem sourceScanState_zero (base first : Nat) :
    sourceScanState base first 0 =
      twoFieldCode base first (2 * first + 1) := by
  unfold sourceScanState MutatingScan.zeroState twoFieldCode
  rw [MutatingScan.zeroStateDigits_zero]
  simp [twoFieldDigits, List.append_assoc]

theorem sourceScanMarker_step
    (base source target first : Nat) (baseAtLeastTwo : 2 ≤ base) :
    SameLine
      ((markerOneExit source target).act base
        (phaseAffine source (sourceScanState base first first)))
      (phaseAffine target (twoProjectionFirstState base first)) := by
  have step := MutatingScan.zeroExit_step base source target first 1
    (List.replicate (2 * first + 1) 0 ++ [-1]) .positive 0
    baseAtLeastTwo
  rw [positive_zero_mutation] at step
  rw [firstScan_rotated base first baseAtLeastTwo] at step
  simpa [sourceScanState, markerOneExit] using step

theorem sourceScanTail_forced_prefix_to_endpoint
    {prime phaseCount source target guessPhase negativePhase firstValidator
      secondValidator endpointPhase : Nat}
    {endpointDigit : Int} {endpoint : Vec2}
    (primeProperty : IsPrime prime) (primeBound : 6 * phaseCount < prime)
    (layout : PhaseLayout phaseCount source guessPhase negativePhase
      firstValidator secondValidator)
    (endpointBound : endpointPhase < phaseCount)
    (sourceEndpointDistinct : source ≠ endpointPhase)
    (endpointMembership : InPhaseAt prime endpointPhase endpointDigit endpoint)
    {first deleted remaining : Nat} (sumEq : deleted + remaining = first)
    {word : List PhysicalTemplate}
    (wordOver : WordOver
      (alphabet source target guessPhase negativePhase firstValidator
        secondValidator) word)
    (allLocal : AllStatesLocal prime word
      (phaseAffine source (sourceScanState prime first deleted)))
    (completeRun : SameLine
      (physicalWordAction prime word
        (phaseAffine source (sourceScanState prime first deleted))) endpoint) :
    ∃ suffix,
      word = List.replicate remaining (zeroLoop source) ++
          [markerOneExit source guessPhase] ++ suffix ∧
      WordOver
        (alphabet source target guessPhase negativePhase firstValidator
          secondValidator) suffix ∧
      AllStatesLocal prime suffix
        (phaseAffine guessPhase (twoProjectionFirstState prime first)) ∧
      SameLine
        (physicalWordAction prime suffix
          (phaseAffine guessPhase (twoProjectionFirstState prime first)))
        endpoint := by
  have nextLocal' : LocalAt prime
      (phaseAffine guessPhase (twoProjectionFirstState prime first)) := by
    apply phase_local (phase := guessPhase)
    rw [← firstScan_rotated prime first primeProperty.1]
    exact periodicCode_local_affine prime
      (List.replicate (2 * first + 1) 0 ++ [-1] ++
        List.replicate first 0 ++ [1]) primeProperty.1 (by simp)
  have parsed := forcedScanPrefixToEndpoint
    (Certificate := True) (primeProperty := primeProperty)
    (primeBound := primeBound) (currentBound := layout.sourceBound)
    (endpointBound := endpointBound) (phaseDistinct := sourceEndpointDistinct)
    (endpointMembership := endpointMembership)
    (beforeMembership := fun position positionBelow =>
      MutatingScan.zeroState_inPhaseAt_before prime source first 1
        (List.replicate (2 * first + 1) 0 ++ [-1]) position
        primeProperty.1 positionBelow)
    (markerMembership := MutatingScan.zeroState_inPhaseAt_marker prime source
      first 1 (List.replicate (2 * first + 1) 0 ++ [-1]) primeProperty.1
      (by simp [ReservedDigit]))
    (stateLocal := fun position _ =>
      MutatingScan.phaseZeroState_local prime source first 1
        (List.replicate (2 * first + 1) 0 ++ [-1]) position
        primeProperty.1)
    (nextLocal := nextLocal')
    (forceLoop := fun position positionBelow letter letterMem outputLocal =>
      source_zero_letter primeProperty primeBound layout
        (MutatingScan.zeroState_inPhaseAt_before prime source first 1
          (List.replicate (2 * first + 1) 0 ++ [-1]) position
          primeProperty.1 positionBelow) letterMem outputLocal)
    (forceExit := fun {letter} letterMem outputLocal =>
      ⟨True.intro, source_marker_letter primeProperty primeBound layout
        (MutatingScan.zeroState_inPhaseAt_marker prime source first 1
          (List.replicate (2 * first + 1) 0 ++ [-1]) primeProperty.1
          (by simp [ReservedDigit])) letterMem outputLocal⟩)
    (loopStep := fun position positionBelow =>
      MutatingScan.zeroLoop_step prime source first 1
        (List.replicate (2 * first + 1) 0 ++ [-1]) position
        primeProperty.1 positionBelow)
    (exitStep := fun _ => sourceScanMarker_step prime source guessPhase first
      primeProperty.1)
    sumEq wordOver allLocal completeRun
  rcases parsed with ⟨suffix, _, wordEq, suffixOver, suffixLocal, suffixRun⟩
  exact ⟨suffix, wordEq, suffixOver, suffixLocal, suffixRun⟩

def generalGuessWord (source target guess : Nat) : List PhysicalTemplate :=
  List.replicate (guess - 1) (zeroLoop source) ++
    [inverseTZeroExit source target]

theorem guess_marker_rejects
    {prime phaseCount source target guessPhase negativePhase firstValidator
      secondValidator first : Nat}
    (primeProperty : IsPrime prime) (primeBound : 6 * phaseCount < prime)
    (layout : PhaseLayout phaseCount source guessPhase negativePhase
      firstValidator secondValidator) {letter : PhysicalTemplate}
    (letterMem : letter ∈ alphabet source target guessPhase negativePhase
      firstValidator secondValidator) :
    ¬LocalAt prime
      (letter.act prime
        (phaseAffine guessPhase (guessState prime first (2 * first + 1)))) := by
  intro outputLocal
  have membership : InPhaseAt prime guessPhase (-1)
      (phaseAffine guessPhase (guessState prime first (2 * first + 1))) := by
    unfold guessState
    exact MutatingScan.zeroState_inPhaseAt_marker prime guessPhase
      (2 * first + 1) (-1) (List.replicate first 0 ++ [1])
      primeProperty.1 (by simp [ReservedDigit])
  have forced := force_metadata primeProperty primeBound layout
    layout.guessBound membership letterMem outputLocal
  simp [alphabet] at letterMem
  rcases letterMem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl
  · exact layout.sourceGuessDistinct forced.1.symm
  · exact layout.sourceGuessDistinct forced.1.symm
  · simp [zeroLoop, MutatingScan.loopLetter] at forced
  · simp [inverseTZeroExit, MutatingScan.exitLetter] at forced
  · exact layout.guessNegativeDistinct forced.1
  · exact layout.guessNegativeDistinct forced.1
  · exact layout.guessFirstValidatorDistinct forced.1
  · exact layout.guessFirstValidatorDistinct forced.1
  · exact layout.guessSecondValidatorDistinct forced.1
  · exact layout.guessSecondValidatorDistinct forced.1

theorem guessTail_forced_exit_to_endpoint
    {prime phaseCount source target guessPhase negativePhase firstValidator
      secondValidator endpointPhase : Nat}
    {endpointDigit : Int} {endpoint : Vec2}
    (primeProperty : IsPrime prime) (primeBound : 6 * phaseCount < prime)
    (layout : PhaseLayout phaseCount source guessPhase negativePhase
      firstValidator secondValidator)
    (endpointBound : endpointPhase < phaseCount)
    (guessEndpointDistinct : guessPhase ≠ endpointPhase)
    (endpointMembership : InPhaseAt prime endpointPhase endpointDigit endpoint)
    {first deleted remaining : Nat}
    (sumEq : deleted + remaining = 2 * first + 1)
    {word : List PhysicalTemplate}
    (wordOver : WordOver
      (alphabet source target guessPhase negativePhase firstValidator
        secondValidator) word)
    (allLocal : AllStatesLocal prime word
      (phaseAffine guessPhase (guessState prime first deleted)))
    (completeRun : SameLine
      (physicalWordAction prime word
        (phaseAffine guessPhase (guessState prime first deleted))) endpoint) :
    ∃ guess suffix,
      deleted < guess ∧ guess ≤ 2 * first + 1 ∧
      word = List.replicate (guess - deleted - 1) (zeroLoop guessPhase) ++
          [inverseTZeroExit guessPhase negativePhase] ++ suffix ∧
      WordOver
        (alphabet source target guessPhase negativePhase firstValidator
          secondValidator) suffix ∧
      AllStatesLocal prime suffix
        (phaseAffine negativePhase
          (twoProjectionGeneralGuessState prime first guess)) ∧
      SameLine
        (physicalWordAction prime suffix
          (phaseAffine negativePhase
            (twoProjectionGeneralGuessState prime first guess))) endpoint := by
  induction remaining generalizing deleted word with
  | zero =>
      have deletedEq : deleted = 2 * first + 1 := by omega
      have membership : InPhaseAt prime guessPhase (-1)
          (phaseAffine guessPhase (guessState prime first deleted)) := by
        rw [deletedEq]
        unfold guessState
        exact MutatingScan.zeroState_inPhaseAt_marker prime guessPhase
          (2 * first + 1) (-1) (List.replicate first 0 ++ [1])
          primeProperty.1 (by simp [ReservedDigit])
      have wordNonempty := word_nonempty_of_endpoint_phase_ne primeProperty
        primeBound layout.guessBound endpointBound guessEndpointDistinct
        membership endpointMembership completeRun
      cases word with
      | nil => exact False.elim (wordNonempty rfl)
      | cons letter tail =>
          have letterMem := wordOver letter (by simp)
          exact False.elim (guess_marker_rejects primeProperty primeBound
            layout letterMem (by simpa only [deletedEq] using
              allLocal.2.start))
  | succ remaining inductionHypothesis =>
      have deletedBelow : deleted < 2 * first + 1 := by omega
      have membership : InPhaseAt prime guessPhase 0
          (phaseAffine guessPhase (guessState prime first deleted)) := by
        unfold guessState
        exact MutatingScan.zeroState_inPhaseAt_before prime guessPhase
          (2 * first + 1) (-1) (List.replicate first 0 ++ [1]) deleted
          primeProperty.1 deletedBelow
      have wordNonempty := word_nonempty_of_endpoint_phase_ne primeProperty
        primeBound layout.guessBound endpointBound guessEndpointDistinct
        membership endpointMembership completeRun
      cases word with
      | nil => exact False.elim (wordNonempty rfl)
      | cons letter tail =>
          have letterMem := wordOver letter (by simp)
          have tailOver : WordOver
              (alphabet source target guessPhase negativePhase firstValidator
                secondValidator) tail := by
            intro candidate candidateMem
            exact wordOver candidate (by simp [candidateMem])
          rcases guess_zero_letter primeProperty primeBound layout membership
            letterMem allLocal.2.start with letterEq | letterEq
          · subst letter
            have firstStep := MutatingScan.zeroLoop_step prime guessPhase
              (2 * first + 1) (-1) (List.replicate first 0 ++ [1]) deleted
              primeProperty.1 deletedBelow
            have nextLocal := MutatingScan.phaseZeroState_local prime
              guessPhase (2 * first + 1) (-1)
              (List.replicate first 0 ++ [1]) (deleted + 1)
              primeProperty.1
            have tailLocal : AllStatesLocal prime tail
                (phaseAffine guessPhase (guessState prime first (deleted + 1))) := by
              apply AllStatesLocal.of_sameLine
                (primePositive := by have := primeProperty.1; omega)
                allLocal.2 nextLocal.1
              simpa [guessState] using firstStep.symm
            have tailRun : SameLine
                (physicalWordAction prime tail
                  (phaseAffine guessPhase
                    (guessState prime first (deleted + 1)))) endpoint := by
              apply physicalWordAction_tail_sameLine prime
                (zeroLoop guessPhase) tail (completeRun := completeRun)
              simpa [guessState] using firstStep
            obtain ⟨guess, suffix, deletedGuess, guessBound, tailEq,
                suffixOver, suffixLocal, suffixRun⟩ :=
              inductionHypothesis (deleted := deleted + 1) (by omega)
                tailOver tailLocal tailRun
            refine ⟨guess, suffix, by omega, guessBound, ?_, suffixOver,
              suffixLocal, suffixRun⟩
            rw [tailEq]
            have countEq : guess - deleted - 1 =
                (guess - (deleted + 1) - 1) + 1 := by omega
            rw [countEq, List.replicate_succ]
            simp
          · subst letter
            let guess := deleted + 1
            have guessPositive : 0 < guess := by unfold guess; omega
            have guessBound : guess ≤ 2 * first + 1 := by unfold guess; omega
            have firstStep := MutatingScan.zeroMutationExit_step prime
              guessPhase negativePhase (2 * first + 1) deleted (-1)
              (List.replicate first 0 ++ [1]) .positive 1
              primeProperty.1 deletedBelow
            rw [positive_one_mutation] at firstStep
            have outputEq :
                Tinv prime
                    (MutatingScan.zeroState prime (2 * first + 1) (-1)
                      (List.replicate first 0 ++ [1]) (deleted + 1)) =
                  twoProjectionGeneralGuessState prime first guess := by
              simpa [guessState, guess] using
                (generalGuessState_eq prime first guess primeProperty.1
                  guessBound).symm
            rw [outputEq] at firstStep
            have unchartedLocal := mutationMap_local_of_local .positive 1
              (MutatingScan.zeroState_local prime (2 * first + 1) (-1)
                (List.replicate first 0 ++ [1]) guess primeProperty.1)
            rw [positive_one_mutation, outputEq] at unchartedLocal
            have nextLocal := phase_local (phase := negativePhase)
              unchartedLocal
            have tailLocal : AllStatesLocal prime tail
                (phaseAffine negativePhase
                  (twoProjectionGeneralGuessState prime first guess)) := by
              apply AllStatesLocal.of_sameLine
                (primePositive := by have := primeProperty.1; omega)
                allLocal.2 nextLocal.1 firstStep.symm
            have tailRun : SameLine
                (physicalWordAction prime tail
                  (phaseAffine negativePhase
                    (twoProjectionGeneralGuessState prime first guess)))
                endpoint := by
              apply physicalWordAction_tail_sameLine prime
                (inverseTZeroExit guessPhase negativePhase) tail
                (completeRun := completeRun)
              exact firstStep
            exact ⟨guess, tail, by unfold guess; omega, guessBound,
              by simp [guess],
              tailOver, tailLocal, tailRun⟩

theorem negativeTail_forced_prefix_to_endpoint
    {prime phaseCount source target guessPhase negativePhase firstValidator
      secondValidator endpointPhase Q h : Nat}
    {endpointDigit : Int} {endpoint : Vec2}
    (primeProperty : IsPrime prime) (primeBound : 6 * phaseCount < prime)
    (layout : PhaseLayout phaseCount source guessPhase negativePhase
      firstValidator secondValidator)
    (endpointBound : endpointPhase < phaseCount)
    (negativeEndpointDistinct : negativePhase ≠ endpointPhase)
    (endpointMembership : InPhaseAt prime endpointPhase endpointDigit endpoint)
    (QPositive : 0 < Q) (hPositive : 0 < h)
    {deleted remaining : Nat} (sumEq : deleted + remaining = h - 1)
    {word : List PhysicalTemplate}
    (wordOver : WordOver
      (alphabet source target guessPhase negativePhase firstValidator
        secondValidator) word)
    (allLocal : AllStatesLocal prime word
      (phaseAffine negativePhase
        (generalNegativeZeroState prime Q h deleted)))
    (completeRun : SameLine
      (physicalWordAction prime word
        (phaseAffine negativePhase
          (generalNegativeZeroState prime Q h deleted))) endpoint) :
    ∃ suffix,
      word = List.replicate remaining (zeroLoop negativePhase) ++
          [inverseFNegativeExit negativePhase firstValidator] ++ suffix ∧
      WordOver
        (alphabet source target guessPhase negativePhase firstValidator
          secondValidator) suffix ∧
      AllStatesLocal prime suffix
        (phaseAffine firstValidator (candidateState prime Q h 0)) ∧
      SameLine
        (physicalWordAction prime suffix
          (phaseAffine firstValidator (candidateState prime Q h 0)))
        endpoint := by
  have nextLocal' : LocalAt prime
      (phaseAffine firstValidator (candidateState prime Q h 0)) :=
    phase_local (phase := firstValidator)
      (candidateState_local prime Q h 0 primeProperty.1 QPositive hPositive)
  have parsed := forcedScanPrefixToEndpoint
    (Certificate := True) (primeProperty := primeProperty)
    (primeBound := primeBound) (currentBound := layout.negativeBound)
    (endpointBound := endpointBound)
    (phaseDistinct := negativeEndpointDistinct)
    (endpointMembership := endpointMembership)
    (beforeMembership := fun position positionBelow =>
      generalNegativeState_inPhaseAt_before primeProperty QPositive
        hPositive positionBelow)
    (markerMembership := generalNegativeState_inPhaseAt_marker primeProperty
      QPositive hPositive)
    (stateLocal := fun position _ =>
      phase_local (generalNegativeZeroState_local prime Q h position
        primeProperty.1 QPositive hPositive))
    (nextLocal := nextLocal')
    (forceLoop := fun position positionBelow letter letterMem outputLocal =>
      negative_zero_letter primeProperty primeBound layout
        (generalNegativeState_inPhaseAt_before primeProperty QPositive
          hPositive positionBelow) letterMem outputLocal)
    (forceExit := fun {letter} letterMem outputLocal =>
      ⟨True.intro, negative_marker_letter primeProperty primeBound layout
        (generalNegativeState_inPhaseAt_marker primeProperty QPositive
          hPositive) letterMem outputLocal⟩)
    (loopStep := fun position positionBelow =>
      generalNegativeZero_step prime negativePhase Q h position
        primeProperty.1 QPositive hPositive positionBelow)
    (exitStep := fun _ => generalNegativeMarker_step prime negativePhase
      firstValidator Q h primeProperty.1 QPositive hPositive)
    sumEq wordOver allLocal completeRun
  rcases parsed with ⟨suffix, _, wordEq, suffixOver, suffixLocal, suffixRun⟩
  exact ⟨suffix, wordEq, suffixOver, suffixLocal, suffixRun⟩

theorem candidateBelow_rejects_to_endpoint
    {prime phaseCount source target guessPhase negativePhase firstValidator
      secondValidator endpointPhase Q h : Nat}
    {endpointDigit : Int} {endpoint : Vec2}
    (primeProperty : IsPrime prime) (primeBound : 6 * phaseCount < prime)
    (layout : PhaseLayout phaseCount source guessPhase negativePhase
      firstValidator secondValidator)
    (endpointBound : endpointPhase < phaseCount)
    (validatorEndpointDistinct : firstValidator ≠ endpointPhase)
    (endpointMembership : InPhaseAt prime endpointPhase endpointDigit endpoint)
    (QPositive : 0 < Q) (hPositive : 0 < h) (hBelowQ : h < Q)
    {deleted remaining : Nat} (sumEq : deleted + remaining = h - 1)
    {word : List PhysicalTemplate}
    (wordOver : WordOver
      (alphabet source target guessPhase negativePhase firstValidator
        secondValidator) word)
    (allLocal : AllStatesLocal prime word
      (phaseAffine firstValidator (candidateState prime Q h deleted)))
    (completeRun : SameLine
      (physicalWordAction prime word
        (phaseAffine firstValidator (candidateState prime Q h deleted)))
      endpoint) :
    False := by
  apply forcedScanRejectsAtMarker
    (primeProperty := primeProperty) (primeBound := primeBound)
    (currentBound := layout.firstValidatorBound)
    (endpointBound := endpointBound)
    (phaseDistinct := validatorEndpointDistinct)
    (endpointMembership := endpointMembership)
    (beforeMembership := fun position positionBelow =>
      candidateState_inPhaseAt_below_before primeProperty QPositive
        hPositive hBelowQ positionBelow)
    (markerMembership := candidateState_inPhaseAt_below_marker primeProperty
      QPositive hPositive hBelowQ)
    (stateLocal := fun position _ =>
      phase_local (phase := firstValidator)
        (candidateState_local prime Q h position primeProperty.1 QPositive
          hPositive))
    (forceLoop := fun position positionBelow {letter} letterMem outputLocal =>
      by
        rcases first_validator_letter primeProperty primeBound layout
            (candidateState_inPhaseAt_below_before primeProperty QPositive
              hPositive hBelowQ positionBelow) letterMem outputLocal with
          ⟨_, letterEq⟩ | ⟨digitEq, _⟩
        · exact letterEq
        · omega)
    (rejectMarker := fun {letter} letterMem =>
      first_validator_rejects_forbidden primeProperty primeBound layout
        (by omega) (by omega)
        (candidateState_inPhaseAt_below_marker primeProperty QPositive
          hPositive hBelowQ) letterMem)
    (loopStep := fun position positionBelow =>
      candidateZero_step prime firstValidator Q h position primeProperty.1
        QPositive hPositive (by omega) positionBelow)
    sumEq wordOver allLocal completeRun

theorem candidateAboveTail_forced_prefix_to_endpoint
    {prime phaseCount source target guessPhase negativePhase firstValidator
      secondValidator endpointPhase Q h : Nat}
    {endpointDigit : Int} {endpoint : Vec2}
    (primeProperty : IsPrime prime) (primeBound : 6 * phaseCount < prime)
    (layout : PhaseLayout phaseCount source guessPhase negativePhase
      firstValidator secondValidator)
    (endpointBound : endpointPhase < phaseCount)
    (validatorEndpointDistinct : firstValidator ≠ endpointPhase)
    (endpointMembership : InPhaseAt prime endpointPhase endpointDigit endpoint)
    (QPositive : 0 < Q) (QBelowH : Q < h)
    (hBelowDouble : h < 2 * Q)
    {deleted remaining : Nat} (sumEq : deleted + remaining = Q - 1)
    {word : List PhysicalTemplate}
    (wordOver : WordOver
      (alphabet source target guessPhase negativePhase firstValidator
        secondValidator) word)
    (allLocal : AllStatesLocal prime word
      (phaseAffine firstValidator (candidateState prime Q h deleted)))
    (completeRun : SameLine
      (physicalWordAction prime word
        (phaseAffine firstValidator (candidateState prime Q h deleted)))
      endpoint) :
    ∃ suffix,
      word = List.replicate remaining (zeroLoop firstValidator) ++
          [markerOneExit firstValidator secondValidator] ++ suffix ∧
      WordOver
        (alphabet source target guessPhase negativePhase firstValidator
          secondValidator) suffix ∧
      AllStatesLocal prime suffix
        (phaseAffine secondValidator (secondState prime Q h 0)) ∧
      SameLine
        (physicalWordAction prime suffix
          (phaseAffine secondValidator (secondState prime Q h 0)))
        endpoint := by
  have parsed := forcedScanPrefixToEndpoint
    (Certificate := True) (primeProperty := primeProperty)
    (primeBound := primeBound) (currentBound := layout.firstValidatorBound)
    (endpointBound := endpointBound)
    (phaseDistinct := validatorEndpointDistinct)
    (endpointMembership := endpointMembership)
    (beforeMembership := fun position positionBelow =>
      candidateState_inPhaseAt_above_before primeProperty QPositive QBelowH
        hBelowDouble positionBelow)
    (markerMembership := candidateState_inPhaseAt_above_marker primeProperty
      QPositive QBelowH hBelowDouble)
    (stateLocal := fun position _ =>
      phase_local (phase := firstValidator)
        (candidateState_local prime Q h position primeProperty.1 QPositive
          (by omega)))
    (nextLocal := phase_local (phase := secondValidator)
      (secondState_local prime Q h 0 primeProperty.1 QPositive (by omega)))
    (forceLoop := fun position positionBelow {letter} letterMem outputLocal =>
      by
        rcases first_validator_letter primeProperty primeBound layout
            (candidateState_inPhaseAt_above_before primeProperty QPositive
              QBelowH hBelowDouble positionBelow) letterMem outputLocal with
          ⟨_, letterEq⟩ | ⟨digitEq, _⟩
        · exact letterEq
        · omega)
    (forceExit := fun {letter} letterMem outputLocal => by
      rcases first_validator_letter primeProperty primeBound layout
          (candidateState_inPhaseAt_above_marker primeProperty QPositive
            QBelowH hBelowDouble) letterMem outputLocal with
        ⟨digitEq, _⟩ | ⟨_, letterEq⟩
      · omega
      · exact ⟨True.intro, letterEq⟩)
    (loopStep := fun position positionBelow =>
      candidateZero_step prime firstValidator Q h position primeProperty.1
        QPositive (by omega) positionBelow (by omega))
    (exitStep := fun _ => candidateMarkerAbove_step prime firstValidator
      secondValidator Q h primeProperty.1 QPositive QBelowH hBelowDouble)
    sumEq wordOver allLocal completeRun
  rcases parsed with ⟨suffix, _, wordEq, suffixOver, suffixLocal, suffixRun⟩
  exact ⟨suffix, wordEq, suffixOver, suffixLocal, suffixRun⟩

theorem secondCandidate_rejects_to_endpoint
    {prime phaseCount source target guessPhase negativePhase firstValidator
      secondValidator endpointPhase Q h : Nat}
    {endpointDigit : Int} {endpoint : Vec2}
    (primeProperty : IsPrime prime) (primeBound : 6 * phaseCount < prime)
    (layout : PhaseLayout phaseCount source guessPhase negativePhase
      firstValidator secondValidator)
    (endpointBound : endpointPhase < phaseCount)
    (validatorEndpointDistinct : secondValidator ≠ endpointPhase)
    (endpointMembership : InPhaseAt prime endpointPhase endpointDigit endpoint)
    (QPositive : 0 < Q) (QBelowH : Q < h)
    (hBelowDouble : h < 2 * Q)
    {deleted remaining : Nat}
    (sumEq : deleted + remaining = h - Q - 1)
    {word : List PhysicalTemplate}
    (wordOver : WordOver
      (alphabet source target guessPhase negativePhase firstValidator
        secondValidator) word)
    (allLocal : AllStatesLocal prime word
      (phaseAffine secondValidator (secondState prime Q h deleted)))
    (completeRun : SameLine
      (physicalWordAction prime word
        (phaseAffine secondValidator (secondState prime Q h deleted)))
      endpoint) :
    False := by
  apply forcedScanRejectsAtMarker
    (primeProperty := primeProperty) (primeBound := primeBound)
    (currentBound := layout.secondValidatorBound)
    (endpointBound := endpointBound)
    (phaseDistinct := validatorEndpointDistinct)
    (endpointMembership := endpointMembership)
    (beforeMembership := fun position positionBelow =>
      secondState_inPhaseAt_before primeProperty QPositive QBelowH
        hBelowDouble positionBelow)
    (markerMembership := secondState_inPhaseAt_marker primeProperty QPositive
      QBelowH hBelowDouble)
    (stateLocal := fun position _ =>
      phase_local (phase := secondValidator)
        (secondState_local prime Q h position primeProperty.1 QPositive
          (by omega)))
    (forceLoop := fun position positionBelow {letter} letterMem outputLocal =>
      by
        rcases second_validator_letter primeProperty primeBound layout
            (secondState_inPhaseAt_before primeProperty QPositive QBelowH
              hBelowDouble positionBelow) letterMem outputLocal with
          ⟨_, letterEq⟩ | ⟨digitEq, _⟩
        · exact letterEq
        · omega)
    (rejectMarker := fun {letter} letterMem =>
      second_validator_rejects_forbidden primeProperty primeBound layout
        (by omega) (by omega)
        (secondState_inPhaseAt_marker primeProperty QPositive QBelowH
          hBelowDouble) letterMem)
    (loopStep := fun position positionBelow =>
      secondZero_step prime secondValidator Q h position primeProperty.1
        QPositive QBelowH hBelowDouble positionBelow)
    sumEq wordOver allLocal completeRun

theorem validatorTail_forced_prefix_to_endpoint
    {prime phaseCount currentPhase nextPhase endpointPhase counter : Nat}
    {endpointDigit : Int} {endpoint : Vec2}
    {moduleAlphabet : List PhysicalTemplate}
    (primeProperty : IsPrime prime) (primeBound : 6 * phaseCount < prime)
    (currentBound : currentPhase < phaseCount)
    (endpointBound : endpointPhase < phaseCount)
    (currentEndpointDistinct : currentPhase ≠ endpointPhase)
    (endpointMembership : InPhaseAt prime endpointPhase endpointDigit endpoint)
    (forceZero : ∀ {state : Vec2} {letter : PhysicalTemplate},
      InPhaseAt prime currentPhase 0 state →
      letter ∈ moduleAlphabet → LocalAt prime (letter.act prime state) →
      letter = zeroLoop currentPhase)
    (forceMarker : ∀ {state : Vec2} {letter : PhysicalTemplate},
      InPhaseAt prime currentPhase 1 state →
      letter ∈ moduleAlphabet → LocalAt prime (letter.act prime state) →
      letter = markerOneExit currentPhase nextPhase)
    {deleted remaining : Nat} (sumEq : deleted + remaining = counter)
    {word : List PhysicalTemplate} (wordOver : WordOver moduleAlphabet word)
    (allLocal : AllStatesLocal prime word
      (phaseAffine currentPhase (validatorState prime counter deleted)))
    (completeRun : SameLine
      (physicalWordAction prime word
        (phaseAffine currentPhase (validatorState prime counter deleted)))
      endpoint) :
    ∃ suffix,
      word = List.replicate remaining (zeroLoop currentPhase) ++
          [markerOneExit currentPhase nextPhase] ++ suffix ∧
      WordOver moduleAlphabet suffix ∧
      AllStatesLocal prime suffix
        (phaseAffine nextPhase (unaryCode prime counter)) ∧
      SameLine
        (physicalWordAction prime suffix
          (phaseAffine nextPhase (unaryCode prime counter))) endpoint := by
  have nextLocal' : LocalAt prime
      (phaseAffine nextPhase (unaryCode prime counter)) := by
    apply phase_local (phase := nextPhase)
    exact periodicCode_local_affine prime (unaryDigits counter)
      primeProperty.1 (by simp [unaryDigits])
  have parsed := forcedScanPrefixToEndpoint
    (Certificate := True) (primeProperty := primeProperty)
    (primeBound := primeBound) (currentBound := currentBound)
    (endpointBound := endpointBound)
    (phaseDistinct := currentEndpointDistinct)
    (endpointMembership := endpointMembership)
    (beforeMembership := fun position positionBelow =>
      MutatingScan.zeroState_inPhaseAt_before prime currentPhase counter 1 []
        position primeProperty.1 positionBelow)
    (markerMembership := MutatingScan.zeroState_inPhaseAt_marker prime
      currentPhase counter 1 [] primeProperty.1 (by simp [ReservedDigit]))
    (stateLocal := fun position _ =>
      MutatingScan.phaseZeroState_local prime currentPhase counter 1 []
        position primeProperty.1)
    (nextLocal := nextLocal')
    (forceLoop := fun position positionBelow {letter} letterMem outputLocal =>
      forceZero
        (MutatingScan.zeroState_inPhaseAt_before prime currentPhase counter 1
          [] position primeProperty.1 positionBelow) letterMem outputLocal)
    (forceExit := fun {letter} letterMem outputLocal =>
      ⟨True.intro, forceMarker
        (MutatingScan.zeroState_inPhaseAt_marker prime currentPhase counter 1
          [] primeProperty.1 (by simp [ReservedDigit])) letterMem
        outputLocal⟩)
    (loopStep := fun position positionBelow =>
      MutatingScan.zeroLoop_step prime currentPhase counter 1 [] position
        primeProperty.1 positionBelow)
    (exitStep := fun _ => validatorMarker_step prime currentPhase nextPhase
      counter primeProperty.1)
    sumEq wordOver allLocal completeRun
  rcases parsed with ⟨suffix, _, wordEq, suffixOver, suffixLocal, suffixRun⟩
  exact ⟨suffix, wordEq, suffixOver, suffixLocal, suffixRun⟩

theorem acceptedCandidateValidators_forced_prefix_to_endpoint
    {prime phaseCount source target guessPhase negativePhase firstValidator
      secondValidator endpointPhase Q : Nat}
    {endpointDigit : Int} {endpoint : Vec2}
    (primeProperty : IsPrime prime) (primeBound : 6 * phaseCount < prime)
    (layout : PhaseLayout phaseCount source guessPhase negativePhase
      firstValidator secondValidator)
    (endpointBound : endpointPhase < phaseCount)
    (firstEndpointDistinct : firstValidator ≠ endpointPhase)
    (secondEndpointDistinct : secondValidator ≠ endpointPhase)
    (endpointMembership : InPhaseAt prime endpointPhase endpointDigit endpoint)
    (QPositive : 0 < Q)
    {word : List PhysicalTemplate}
    (wordOver : WordOver
      (alphabet source target guessPhase negativePhase firstValidator
        secondValidator) word)
    (allLocal : AllStatesLocal prime word
      (phaseAffine firstValidator (candidateState prime Q Q 0)))
    (completeRun : SameLine
      (physicalWordAction prime word
        (phaseAffine firstValidator (candidateState prime Q Q 0)))
      endpoint) :
    ∃ suffix,
      word = validatorWord firstValidator secondValidator (2 * Q - 1) ++
          validatorWord secondValidator target (2 * Q - 1) ++ suffix ∧
      WordOver
        (alphabet source target guessPhase negativePhase firstValidator
          secondValidator) suffix ∧
      AllStatesLocal prime suffix
        (phaseAffine target (unaryCode prime (2 * Q - 1))) ∧
      SameLine
        (physicalWordAction prime suffix
          (phaseAffine target (unaryCode prime (2 * Q - 1)))) endpoint := by
  have startEq :
      phaseAffine firstValidator (candidateState prime Q Q 0) =
        phaseAffine firstValidator
          (validatorState prime (2 * Q - 1) 0) := by
    rw [accepted_candidate_state prime Q QPositive,
      validatorState_zero]
  rw [startEq] at allLocal completeRun
  obtain ⟨middle, wordEq, middleOver, middleLocal, middleRun⟩ :=
    validatorTail_forced_prefix_to_endpoint
      (primeProperty := primeProperty) (primeBound := primeBound)
      (currentBound := layout.firstValidatorBound)
      (endpointBound := endpointBound)
      (currentEndpointDistinct := firstEndpointDistinct)
      (endpointMembership := endpointMembership)
      (forceZero := fun {state} {letter} membership letterMem outputLocal => by
        rcases first_validator_letter primeProperty primeBound layout
            membership letterMem outputLocal with
          ⟨_, letterEq⟩ | ⟨digitEq, _⟩
        · exact letterEq
        · omega)
      (forceMarker := fun {state} {letter} membership letterMem outputLocal =>
        by
          rcases first_validator_letter primeProperty primeBound layout
              membership letterMem outputLocal with
            ⟨digitEq, _⟩ | ⟨_, letterEq⟩
          · omega
          · exact letterEq)
      (sumEq := show 0 + (2 * Q - 1) = 2 * Q - 1 by omega)
      wordOver allLocal completeRun
  have middleStartEq :
      phaseAffine secondValidator (unaryCode prime (2 * Q - 1)) =
        phaseAffine secondValidator
          (validatorState prime (2 * Q - 1) 0) := by
    rw [validatorState_zero]
  rw [middleStartEq] at middleLocal middleRun
  obtain ⟨suffix, middleEq, suffixOver, suffixLocal, suffixRun⟩ :=
    validatorTail_forced_prefix_to_endpoint
      (primeProperty := primeProperty) (primeBound := primeBound)
      (currentBound := layout.secondValidatorBound)
      (endpointBound := endpointBound)
      (currentEndpointDistinct := secondEndpointDistinct)
      (endpointMembership := endpointMembership)
      (forceZero := fun {state} {letter} membership letterMem outputLocal => by
        rcases second_validator_letter primeProperty primeBound layout
            membership letterMem outputLocal with
          ⟨_, letterEq⟩ | ⟨digitEq, _⟩
        · exact letterEq
        · omega)
      (forceMarker := fun {state} {letter} membership letterMem outputLocal =>
        by
          rcases second_validator_letter primeProperty primeBound layout
              membership letterMem outputLocal with
            ⟨digitEq, _⟩ | ⟨_, letterEq⟩
          · omega
          · exact letterEq)
      (sumEq := show 0 + (2 * Q - 1) = 2 * Q - 1 by omega)
      middleOver middleLocal middleRun
  rw [middleEq] at wordEq
  refine ⟨suffix, ?_, suffixOver, suffixLocal, suffixRun⟩
  simpa [validatorWord, MutatingScan.word, List.append_assoc] using wordEq

/-- Any completed local path through the ten-letter alphabet begins with
the unique accepted module word.  The theorem quantifies over the entire
remaining word, so it rules out spurious prefixes inside the module rather
than merely classifying completed arithmetic scans. -/
theorem completedPath_forces_accepted_prefix
    {prime phaseCount source target guessPhase negativePhase firstValidator
      secondValidator endpointPhase first : Nat}
    {endpointDigit : Int} {endpoint : Vec2}
    (primeProperty : IsPrime prime) (primeBound : 6 * phaseCount < prime)
    (layout : PhaseLayout phaseCount source guessPhase negativePhase
      firstValidator secondValidator)
    (endpointBound : endpointPhase < phaseCount)
    (sourceEndpointDistinct : source ≠ endpointPhase)
    (guessEndpointDistinct : guessPhase ≠ endpointPhase)
    (negativeEndpointDistinct : negativePhase ≠ endpointPhase)
    (firstEndpointDistinct : firstValidator ≠ endpointPhase)
    (secondEndpointDistinct : secondValidator ≠ endpointPhase)
    (endpointMembership : InPhaseAt prime endpointPhase endpointDigit endpoint)
    {word : List PhysicalTemplate}
    (wordOver : WordOver
      (alphabet source target guessPhase negativePhase firstValidator
        secondValidator) word)
    (allLocal : AllStatesLocal prime word
      (phaseAffine source
        (twoFieldCode prime first (2 * first + 1))))
    (completeRun : SameLine
      (physicalWordAction prime word
        (phaseAffine source
          (twoFieldCode prime first (2 * first + 1)))) endpoint) :
    ∃ suffix,
      word = acceptedWord source target guessPhase negativePhase
          firstValidator secondValidator first ++ suffix ∧
      WordOver
        (alphabet source target guessPhase negativePhase firstValidator
          secondValidator) suffix ∧
      AllStatesLocal prime suffix
        (phaseAffine target (unaryCode prime (2 * first + 1))) ∧
      SameLine
        (physicalWordAction prime suffix
          (phaseAffine target (unaryCode prime (2 * first + 1)))) endpoint := by
  rw [← sourceScanState_zero prime first] at allLocal completeRun
  obtain ⟨afterSource, sourceWordEq, afterSourceOver, afterSourceLocal,
      afterSourceRun⟩ :=
    sourceScanTail_forced_prefix_to_endpoint primeProperty primeBound layout
      endpointBound sourceEndpointDistinct endpointMembership
      (show 0 + first = first by omega) wordOver allLocal completeRun
  rw [← guessState_zero prime first primeProperty.1] at afterSourceLocal afterSourceRun
  obtain ⟨guess, afterGuess, guessPositive, guessBound, guessWordEq,
      afterGuessOver, afterGuessLocal, afterGuessRun⟩ :=
    guessTail_forced_exit_to_endpoint primeProperty primeBound layout
      endpointBound guessEndpointDistinct endpointMembership
      (show 0 + (2 * first + 1) = 2 * first + 1 by omega)
      afterSourceOver afterSourceLocal afterSourceRun
  let Q := first + 1
  let h := 2 * Q - guess
  have QPositive : 0 < Q := by simp [Q]
  have hPositive : 0 < h := by
    dsimp [h, Q]
    omega
  have hBelowDouble : h < 2 * Q := by
    dsimp [h]
    omega
  have firstEq : Q - 1 = first := by simp [Q]
  have guessFromH : 2 * Q - h = guess := by
    dsimp [h, Q]
    omega
  have negativeStartEq :
      phaseAffine negativePhase
          (twoProjectionGeneralGuessState prime first guess) =
        phaseAffine negativePhase
          (generalNegativeZeroState prime Q h 0) := by
    have arithmetic := generalNegativeZeroState_zero prime Q h
      primeProperty.1 QPositive hPositive hBelowDouble
    rw [firstEq, guessFromH] at arithmetic
    exact congrArg (phaseAffine negativePhase) arithmetic.symm
  rw [negativeStartEq] at afterGuessLocal afterGuessRun
  obtain ⟨afterNegative, negativeWordEq, afterNegativeOver,
      afterNegativeLocal, afterNegativeRun⟩ :=
    negativeTail_forced_prefix_to_endpoint primeProperty primeBound layout
      endpointBound negativeEndpointDistinct endpointMembership QPositive
      hPositive (show 0 + (h - 1) = h - 1 by omega) afterGuessOver
      afterGuessLocal afterGuessRun
  rcases Nat.lt_trichotomy h Q with hBelowQ | hEqQ | QBelowH
  · exact False.elim (candidateBelow_rejects_to_endpoint primeProperty
      primeBound layout endpointBound firstEndpointDistinct endpointMembership
      QPositive hPositive hBelowQ
      (show 0 + (h - 1) = h - 1 by omega) afterNegativeOver
      afterNegativeLocal afterNegativeRun)
  · rw [hEqQ] at afterNegativeLocal afterNegativeRun
    obtain ⟨suffix, validatorsWordEq, suffixOver, suffixLocal, suffixRun⟩ :=
      acceptedCandidateValidators_forced_prefix_to_endpoint primeProperty
        primeBound layout endpointBound firstEndpointDistinct
        secondEndpointDistinct endpointMembership QPositive afterNegativeOver
        afterNegativeLocal afterNegativeRun
    rw [validatorsWordEq] at negativeWordEq
    rw [negativeWordEq] at guessWordEq
    rw [guessWordEq] at sourceWordEq
    have acceptedGuess : guess = first + 1 := by
      dsimp [h, Q] at hEqQ
      omega
    have acceptedCounter : 2 * Q - 1 = 2 * first + 1 := by
      dsimp [Q]
      omega
    have acceptedCounterAfterSubstitution :
        2 * (first + 1) - 1 = 2 * first + 1 := by omega
    refine ⟨suffix, ?_, suffixOver, ?_, ?_⟩
    · simpa [acceptedWord, firstScanWord, guessWord, negativeWord,
        validatorWord, MutatingScan.word, zeroLoop, markerOneExit,
        inverseTZeroExit, inverseFNegativeExit, acceptedGuess, hEqQ, Q,
        acceptedCounterAfterSubstitution, List.append_assoc] using sourceWordEq
    · simpa [acceptedCounter] using suffixLocal
    · simpa [acceptedCounter] using suffixRun
  · obtain ⟨afterFirstValidator, firstValidatorWordEq,
        afterFirstValidatorOver, afterFirstValidatorLocal,
        afterFirstValidatorRun⟩ :=
      candidateAboveTail_forced_prefix_to_endpoint primeProperty primeBound
        layout endpointBound firstEndpointDistinct endpointMembership QPositive
        QBelowH hBelowDouble (show 0 + (Q - 1) = Q - 1 by omega)
        afterNegativeOver afterNegativeLocal afterNegativeRun
    exact False.elim (secondCandidate_rejects_to_endpoint primeProperty
      primeBound layout endpointBound secondEndpointDistinct endpointMembership
      QPositive QBelowH hBelowDouble
      (show 0 + (h - Q - 1) = h - Q - 1 by omega)
      afterFirstValidatorOver afterFirstValidatorLocal afterFirstValidatorRun)

theorem no_letter_from_target
    {prime phaseCount source target guessPhase negativePhase firstValidator
      secondValidator : Nat}
    {digit : Int} {state : Vec2} {letter : PhysicalTemplate}
    (primeProperty : IsPrime prime) (primeBound : 6 * phaseCount < prime)
    (layout : PhaseLayout phaseCount source guessPhase negativePhase
      firstValidator secondValidator)
    (targetBound : target < phaseCount)
    (targetNotActive : target ∉
      [source, guessPhase, negativePhase, firstValidator, secondValidator])
    (membership : InPhaseAt prime target digit state)
    (letterMem : letter ∈ alphabet source target guessPhase negativePhase
      firstValidator secondValidator)
    (outputLocal : LocalAt prime (letter.act prime state)) : False := by
  have forced := membership.physicalLetter_source_digit_unique primeProperty
    primeBound targetBound (letter_source_bound layout letterMem)
    (letter_reserved letterMem)
    (by simpa [PhysicalTemplate.act, PhysicalTemplate.matrix] using outputLocal)
  apply targetNotActive
  rw [forced.1]
  exact letter_source_mem_active letterMem

theorem word_from_target_eq_nil
    {prime phaseCount source target guessPhase negativePhase firstValidator
      secondValidator : Nat}
    {digit : Int} {state : Vec2}
    (primeProperty : IsPrime prime) (primeBound : 6 * phaseCount < prime)
    (layout : PhaseLayout phaseCount source guessPhase negativePhase
      firstValidator secondValidator)
    (targetBound : target < phaseCount)
    (targetNotActive : target ∉
      [source, guessPhase, negativePhase, firstValidator, secondValidator])
    (membership : InPhaseAt prime target digit state)
    {word : List PhysicalTemplate}
    (wordOver : WordOver
      (alphabet source target guessPhase negativePhase firstValidator
        secondValidator) word)
    (allLocal : AllStatesLocal prime word state) : word = [] := by
  cases word with
  | nil => rfl
  | cons letter tail =>
      exact False.elim (no_letter_from_target primeProperty primeBound layout
        targetBound targetNotActive membership (wordOver letter (by simp))
        allLocal.2.start)

private theorem active_ne_endpoint
    {source guessPhase negativePhase firstValidator secondValidator
      endpointPhase : Nat}
    (endpointNotActive : endpointPhase ∉
      [source, guessPhase, negativePhase, firstValidator, secondValidator])
    {phase : Nat}
    (phaseActive : phase ∈
      [source, guessPhase, negativePhase, firstValidator, secondValidator]) :
    phase ≠ endpointPhase := by
  intro phaseEq
  apply endpointNotActive
  simpa [phaseEq] using phaseActive

/-- Exact unrestricted-word converse for the ten-letter projection module. -/
theorem completedPath_unique
    {prime phaseCount source target guessPhase negativePhase firstValidator
      secondValidator first : Nat}
    {endpointDigit : Int} {endpoint : Vec2}
    (primeProperty : IsPrime prime) (primeBound : 6 * phaseCount < prime)
    (layout : PhaseLayout phaseCount source guessPhase negativePhase
      firstValidator secondValidator)
    (targetBound : target < phaseCount)
    (targetNotActive : target ∉
      [source, guessPhase, negativePhase, firstValidator, secondValidator])
    (endpointMembership : InPhaseAt prime target endpointDigit endpoint)
    {word : List PhysicalTemplate}
    (wordOver : WordOver
      (alphabet source target guessPhase negativePhase firstValidator
        secondValidator) word)
    (allLocal : AllStatesLocal prime word
      (phaseAffine source (twoFieldCode prime first (2 * first + 1))))
    (completeRun : SameLine
      (physicalWordAction prime word
        (phaseAffine source (twoFieldCode prime first (2 * first + 1))))
      endpoint) :
    word = acceptedWord source target guessPhase negativePhase firstValidator
      secondValidator first := by
  obtain ⟨suffix, wordEq, suffixOver, suffixLocal, _⟩ :=
    completedPath_forces_accepted_prefix primeProperty primeBound layout
      targetBound
      (active_ne_endpoint targetNotActive (by simp))
      (active_ne_endpoint targetNotActive (by simp))
      (active_ne_endpoint targetNotActive (by simp))
      (active_ne_endpoint targetNotActive (by simp))
      (active_ne_endpoint targetNotActive (by simp))
      endpointMembership wordOver allLocal completeRun
  obtain ⟨targetDigit, targetMembership⟩ := unaryCode_inPhaseAt
    (phase := target) (counter := 2 * first + 1) primeProperty.1
  have suffixEq := word_from_target_eq_nil primeProperty primeBound layout
    targetBound targetNotActive targetMembership suffixOver suffixLocal
  subst suffix
  simpa using wordEq

/-- A projection-only word cannot end in a guarded phase outside both its
active controls and its declared target. -/
theorem completedPath_cannot_reach_foreign_phase
    {prime phaseCount source target guessPhase negativePhase firstValidator
      secondValidator endpointPhase first : Nat}
    {endpointDigit : Int} {endpoint : Vec2}
    (primeProperty : IsPrime prime) (primeBound : 6 * phaseCount < prime)
    (layout : PhaseLayout phaseCount source guessPhase negativePhase
      firstValidator secondValidator)
    (targetBound : target < phaseCount)
    (endpointBound : endpointPhase < phaseCount)
    (targetNotActive : target ∉
      [source, guessPhase, negativePhase, firstValidator, secondValidator])
    (endpointNotActive : endpointPhase ∉
      [source, guessPhase, negativePhase, firstValidator, secondValidator])
    (targetEndpointDistinct : target ≠ endpointPhase)
    (endpointMembership : InPhaseAt prime endpointPhase endpointDigit endpoint)
    {word : List PhysicalTemplate}
    (wordOver : WordOver
      (alphabet source target guessPhase negativePhase firstValidator
        secondValidator) word)
    (allLocal : AllStatesLocal prime word
      (phaseAffine source (twoFieldCode prime first (2 * first + 1))))
    (completeRun : SameLine
      (physicalWordAction prime word
        (phaseAffine source (twoFieldCode prime first (2 * first + 1))))
      endpoint) : False := by
  obtain ⟨suffix, _, suffixOver, suffixLocal, suffixRun⟩ :=
    completedPath_forces_accepted_prefix primeProperty primeBound layout
      endpointBound
      (active_ne_endpoint endpointNotActive (by simp))
      (active_ne_endpoint endpointNotActive (by simp))
      (active_ne_endpoint endpointNotActive (by simp))
      (active_ne_endpoint endpointNotActive (by simp))
      (active_ne_endpoint endpointNotActive (by simp))
      endpointMembership wordOver allLocal completeRun
  obtain ⟨targetDigit, targetMembership⟩ := unaryCode_inPhaseAt
    (phase := target) (counter := 2 * first + 1) primeProperty.1
  have suffixEq := word_from_target_eq_nil primeProperty primeBound layout
    targetBound targetNotActive targetMembership suffixOver suffixLocal
  subst suffix
  have phaseEq := (targetMembership.unique primeProperty primeBound
    targetBound endpointBound endpointMembership (by
      simpa [physicalWordAction] using suffixRun)).1
  exact targetEndpointDistinct phaseEq

end Mortality.Compiler.TwoProjectionModule
