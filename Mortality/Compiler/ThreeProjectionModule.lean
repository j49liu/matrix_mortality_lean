import Mortality.Compiler.ThreeProjectionClassification
import Mortality.Compiler.TwoProjectionModule

/-!
# The fourteen-letter three-to-one projection module

This file realizes the manuscript's two guessed prefixes, forced negative
scan, and three validators by the literal fourteen physical templates.
-/

namespace Mortality.Compiler.ThreeProjectionModule

open Mortality.PeriodicCode
open Mortality.Compiler
open Mortality.Compiler.UnaryArithmetic
open Mortality.Compiler.ContractionArithmetic
open Mortality.Compiler.ContractionProjectionArithmetic
open Mortality.Compiler.ThreeProjectionClassification

abbrev zeroLoop (phase : Nat) : PhysicalTemplate :=
  MutatingScan.loopLetter phase 0

abbrev markerOneExit (source target : Nat) : PhysicalTemplate :=
  MutatingScan.exitLetter source target 1 .positive 0

abbrev inverseTZeroExit (source target : Nat) : PhysicalTemplate :=
  MutatingScan.exitLetter source target 0 .positive 1

abbrev inverseFNegativeExit (source target : Nat) : PhysicalTemplate :=
  MutatingScan.exitLetter source target (-1) .positive (-2)

def alphabet (source target firstGuess secondGuess negativePhase
    firstValidator secondValidator thirdValidator : Nat) :
    List PhysicalTemplate :=
  [zeroLoop source, markerOneExit source firstGuess,
    zeroLoop firstGuess, inverseTZeroExit firstGuess secondGuess,
    zeroLoop secondGuess, inverseTZeroExit secondGuess negativePhase,
    zeroLoop negativePhase,
      inverseFNegativeExit negativePhase firstValidator,
    zeroLoop firstValidator,
      markerOneExit firstValidator secondValidator,
    zeroLoop secondValidator,
      markerOneExit secondValidator thirdValidator,
    zeroLoop thirdValidator, markerOneExit thirdValidator target]

structure PhaseLayout (phaseCount source firstGuess secondGuess negativePhase
    firstValidator secondValidator thirdValidator : Nat) : Prop where
  sourceBound : source < phaseCount
  firstGuessBound : firstGuess < phaseCount
  secondGuessBound : secondGuess < phaseCount
  negativeBound : negativePhase < phaseCount
  firstValidatorBound : firstValidator < phaseCount
  secondValidatorBound : secondValidator < phaseCount
  thirdValidatorBound : thirdValidator < phaseCount
  sourceFirstGuessDistinct : source ≠ firstGuess
  sourceSecondGuessDistinct : source ≠ secondGuess
  sourceNegativeDistinct : source ≠ negativePhase
  sourceFirstValidatorDistinct : source ≠ firstValidator
  sourceSecondValidatorDistinct : source ≠ secondValidator
  sourceThirdValidatorDistinct : source ≠ thirdValidator
  guessesDistinct : firstGuess ≠ secondGuess
  firstGuessNegativeDistinct : firstGuess ≠ negativePhase
  firstGuessFirstValidatorDistinct : firstGuess ≠ firstValidator
  firstGuessSecondValidatorDistinct : firstGuess ≠ secondValidator
  firstGuessThirdValidatorDistinct : firstGuess ≠ thirdValidator
  secondGuessNegativeDistinct : secondGuess ≠ negativePhase
  secondGuessFirstValidatorDistinct : secondGuess ≠ firstValidator
  secondGuessSecondValidatorDistinct : secondGuess ≠ secondValidator
  secondGuessThirdValidatorDistinct : secondGuess ≠ thirdValidator
  negativeFirstValidatorDistinct : negativePhase ≠ firstValidator
  negativeSecondValidatorDistinct : negativePhase ≠ secondValidator
  negativeThirdValidatorDistinct : negativePhase ≠ thirdValidator
  firstSecondValidatorDistinct : firstValidator ≠ secondValidator
  firstThirdValidatorDistinct : firstValidator ≠ thirdValidator
  secondThirdValidatorDistinct : secondValidator ≠ thirdValidator

def sourceWord (source target first : Nat) : List PhysicalTemplate :=
  MutatingScan.word source target (List.replicate first 0) 1 .positive 0

def guessWord (source target count : Nat) : List PhysicalTemplate :=
  List.replicate (count - 1) (zeroLoop source) ++
    [inverseTZeroExit source target]

def negativeWord (source target count : Nat) : List PhysicalTemplate :=
  List.replicate (count - 1) (zeroLoop source) ++
    [inverseFNegativeExit source target]

def validatorWord (source target counter : Nat) : List PhysicalTemplate :=
  MutatingScan.word source target (List.replicate counter 0) 1 .positive 0

def acceptedWord (source target firstGuess secondGuess negativePhase
    firstValidator secondValidator thirdValidator first : Nat) :
    List PhysicalTemplate :=
  let Q := first + 1
  sourceWord source firstGuess first ++
    guessWord firstGuess secondGuess Q ++
    guessWord secondGuess negativePhase Q ++
    negativeWord negativePhase firstValidator Q ++
    validatorWord firstValidator secondValidator (3 * first + 2) ++
    validatorWord secondValidator thirdValidator (3 * first + 2) ++
    validatorWord thirdValidator target (3 * first + 2)

@[simp] theorem alphabet_length
    (source target firstGuess secondGuess negativePhase firstValidator
      secondValidator thirdValidator : Nat) :
    (alphabet source target firstGuess secondGuess negativePhase
      firstValidator secondValidator thirdValidator).length = 14 := by
  simp [alphabet]

@[simp] theorem acceptedWord_length
    (source target firstGuess secondGuess negativePhase firstValidator
      secondValidator thirdValidator first : Nat) :
    (acceptedWord source target firstGuess secondGuess negativePhase
      firstValidator secondValidator thirdValidator first).length =
        13 * first + 13 := by
  simp [acceptedWord, sourceWord, guessWord, negativeWord, validatorWord,
    MutatingScan.word]
  omega

theorem acceptedWord_wordOver
    (source target firstGuess secondGuess negativePhase firstValidator
      secondValidator thirdValidator first : Nat) :
    WordOver
      (alphabet source target firstGuess secondGuess negativePhase
        firstValidator secondValidator thirdValidator)
      (acceptedWord source target firstGuess secondGuess negativePhase
        firstValidator secondValidator thirdValidator first) := by
  intro letter letterMem
  simp [acceptedWord, sourceWord, guessWord, negativeWord, validatorWord,
    MutatingScan.word] at letterMem
  rcases letterMem with ⟨_, rfl⟩ | rfl | ⟨_, rfl⟩ | rfl | ⟨_, rfl⟩ |
      rfl | ⟨_, rfl⟩ | rfl | ⟨_, rfl⟩ | rfl | ⟨_, rfl⟩ | rfl |
      ⟨_, rfl⟩ | rfl <;> simp [alphabet]

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

def sourceScanState (base first deleted : Nat) : Rat :=
  MutatingScan.zeroState base first 1
    (List.replicate (3 * first + 2) 0 ++ [-1]) deleted

theorem sourceScanState_zero (base first : Nat) :
    sourceScanState base first 0 =
      twoFieldCode base first (3 * first + 2) := by
  unfold sourceScanState MutatingScan.zeroState twoFieldCode
  rw [MutatingScan.zeroStateDigits_zero]
  simp [twoFieldDigits, List.append_assoc]

theorem firstScan_rotated
    (base first : Nat) (baseAtLeastTwo : 2 ≤ base) :
    periodicCode (base : Rat)
        (List.replicate (3 * first + 2) 0 ++ [-1] ++
          List.replicate first 0 ++ [1]) =
      threeProjectionFirstState base first := by
  have scan := MutatingScan.scanDigits_periodic_prefix base
    (List.replicate first 0)
    (List.replicate (3 * first + 2) 0 ++ [-1]) 1 baseAtLeastTwo
  simpa [threeProjectionFirstState, twoFieldCode, twoFieldDigits,
    unaryDigits, List.append_assoc] using scan.symm

def firstGuessState (base first deleted : Nat) : Rat :=
  MutatingScan.zeroState base (3 * first + 2) (-1)
    (List.replicate first 0 ++ [1]) deleted

theorem firstGuessState_zero
    (base first : Nat) (baseAtLeastTwo : 2 ≤ base) :
    firstGuessState base first 0 = threeProjectionFirstState base first := by
  unfold firstGuessState MutatingScan.zeroState
  rw [MutatingScan.zeroStateDigits_zero]
  simpa [List.append_assoc] using
    firstScan_rotated base first baseAtLeastTwo

theorem firstPrefixState_eq_firstGuessState
    (base first guess : Nat) (baseAtLeastTwo : 2 ≤ base)
    (guessBound : guess ≤ 3 * first + 2) :
    threeProjectionFirstPrefixState base first guess =
      firstGuessState base first guess := by
  unfold threeProjectionFirstPrefixState zeroDigits
  rw [← firstGuessState_zero base first baseAtLeastTwo]
  simpa [firstGuessState] using
    MutatingScan.scan_zeroState base (3 * first + 2) (-1)
      (List.replicate first 0 ++ [1]) 0 guess baseAtLeastTwo (by omega)

theorem generalFirstGuessState_eq
    (base first guess : Nat) (baseAtLeastTwo : 2 ≤ base)
    (guessBound : guess ≤ 3 * first + 2) :
    threeProjectionGeneralFirstGuessState base first guess =
      Tinv base (firstGuessState base first guess) := by
  unfold threeProjectionGeneralFirstGuessState
  rw [firstPrefixState_eq_firstGuessState base first guess baseAtLeastTwo
    guessBound]

def firstGuessDenominator (base Q r : Nat) : Int :=
  1 + (base : Int) ^ Q + (base : Int) ^ (2 * Q) +
    (base : Int) ^ (3 * Q) - (base : Int) ^ r

def secondGuessDenominator (base Q r s : Nat) : Int :=
  firstGuessDenominator base Q r - (base : Int) ^ s

def powerZeroState (base exponent deleted : Nat) (denominator : Int) : Rat :=
  -((base : Rat) ^ (exponent - 1 - deleted)) / (denominator : Rat)

theorem firstGuessDenominator_one_residue
    (base Q r : Nat) (QPositive : 0 < Q) (rPositive : 0 < r) :
    (base : Int) ∣ 1 - firstGuessDenominator base Q r := by
  rcases base_dvd_positive_power base Q QPositive with ⟨f1, e1⟩
  rcases base_dvd_positive_power base (2 * Q) (by omega) with ⟨f2, e2⟩
  rcases base_dvd_positive_power base (3 * Q) (by omega) with ⟨f3, e3⟩
  rcases base_dvd_positive_power base r rPositive with ⟨fr, er⟩
  refine ⟨-f1 - f2 - f3 + fr, ?_⟩
  unfold firstGuessDenominator
  rw [e1, e2, e3, er]
  grind

theorem secondGuessDenominator_one_residue
    (base Q r s : Nat) (QPositive : 0 < Q)
    (rPositive : 0 < r) (sPositive : 0 < s) :
    (base : Int) ∣ 1 - secondGuessDenominator base Q r s := by
  obtain ⟨factor, firstEq⟩ := firstGuessDenominator_one_residue
    base Q r QPositive rPositive
  rcases base_dvd_positive_power base s sPositive with ⟨fs, es⟩
  refine ⟨factor + fs, ?_⟩
  unfold secondGuessDenominator
  have rearranged :
      1 - (firstGuessDenominator base Q r - (base : Int) ^ s) =
        (1 - firstGuessDenominator base Q r) + (base : Int) ^ s := by
    grind
  rw [rearranged, firstEq, es]
  grind

private theorem denominator_not_dvd_of_one_residue
    (base : Nat) (denominator : Int) (baseAtLeastTwo : 2 ≤ base)
    (oneResidue : (base : Int) ∣ 1 - denominator) :
    ¬(base : Int) ∣ denominator := by
  intro denominatorDivisible
  have oneDivisible := Int.dvd_add oneResidue denominatorDivisible
  have sumEq : 1 - denominator + denominator = 1 := by grind
  rw [sumEq] at oneDivisible
  have naturalDivisible : base ∣ 1 := by
    simpa using (Int.ofNat_dvd.mp oneDivisible)
  have baseAtMostOne := Nat.le_of_dvd Nat.zero_lt_one naturalDivisible
  omega

theorem firstGuessDenominator_not_dvd
    (base Q r : Nat) (baseAtLeastTwo : 2 ≤ base)
    (QPositive : 0 < Q) (rPositive : 0 < r) :
    ¬(base : Int) ∣ firstGuessDenominator base Q r :=
  denominator_not_dvd_of_one_residue base _ baseAtLeastTwo
    (firstGuessDenominator_one_residue base Q r QPositive rPositive)

theorem secondGuessDenominator_not_dvd
    (base Q r s : Nat) (baseAtLeastTwo : 2 ≤ base)
    (QPositive : 0 < Q) (rPositive : 0 < r) (sPositive : 0 < s) :
    ¬(base : Int) ∣ secondGuessDenominator base Q r s :=
  denominator_not_dvd_of_one_residue base _ baseAtLeastTwo
    (secondGuessDenominator_one_residue base Q r s QPositive rPositive
      sPositive)

theorem powerZeroState_local
    (base exponent deleted : Nat) (denominator : Int)
    (denominatorNotDivisible : ¬(base : Int) ∣ denominator) :
    LocalAt base
      (Vec2.affine (powerZeroState base exponent deleted denominator)) := by
  have localFraction := local_affine_integer_div
    (prime := base) (numerator := -((base : Int) ^ (exponent - 1 - deleted)))
    (denominator := denominator) denominatorNotDivisible
  simpa [powerZeroState, Rat.intCast_neg, Rat.intCast_pow,
    Rat.intCast_natCast] using localFraction

theorem powerZeroState_sameLine_integer
    (base exponent deleted : Nat) (denominator : Int)
    (denominatorNotDivisible : ¬(base : Int) ∣ denominator) :
    SameLine (Vec2.affine (powerZeroState base exponent deleted denominator))
      (integerVector (-((base : Int) ^ (exponent - 1 - deleted)))
        denominator) := by
  have denominatorNonzero : denominator ≠ 0 :=
    fun zero => denominatorNotDivisible (by rw [zero]; exact Int.dvd_zero _)
  simpa [powerZeroState, Rat.intCast_neg, Rat.intCast_pow,
    Rat.intCast_natCast] using affine_div_sameLine_integerVector
      (numerator := -((base : Int) ^ (exponent - 1 - deleted)))
      (denominator := denominator) denominatorNonzero

theorem powerZeroState_delete_zero
    (base exponent deleted : Nat) (denominator : Int)
    (baseAtLeastTwo : 2 ≤ base) (deletedBelow : deleted < exponent - 1) :
    deleteDigit (base : Rat) 0
        (powerZeroState base exponent deleted denominator) =
      powerZeroState base exponent (deleted + 1) denominator := by
  unfold powerZeroState deleteDigit
  have baseNonzero : (base : Rat) ≠ 0 := by
    simpa using (show base ≠ 0 by omega)
  have exponentEq : exponent - 1 - deleted =
      exponent - 1 - (deleted + 1) + 1 := by omega
  rw [exponentEq, Rat.pow_succ]
  simp only [Rat.intCast_zero, Rat.div_def]
  have baseCancel := Rat.mul_inv_cancel (base : Rat) baseNonzero
  grind

theorem powerZeroState_zero_residue
    (base exponent deleted : Nat) (deletedBelow : deleted < exponent - 1) :
    (base : Int) ∣ -((base : Int) ^ (exponent - 1 - deleted)) := by
  rcases base_dvd_positive_power base (exponent - 1 - deleted) (by omega)
      with ⟨factor, factorEq⟩
  refine ⟨-factor, ?_⟩
  rw [factorEq]
  grind

theorem powerZeroState_negative_residue
    (base exponent : Nat) (denominator : Int)
    (oneResidue : (base : Int) ∣ 1 - denominator) :
    (base : Int) ∣
      -((base : Int) ^ (exponent - 1 - (exponent - 1))) -
        (-1) * denominator := by
  have negated := Int.dvd_neg.mpr oneResidue
  have expressionEq :
      -((base : Int) ^ (exponent - 1 - (exponent - 1))) -
          (-1) * denominator = -(1 - denominator) := by
    simp
    grind
  rw [expressionEq]
  exact negated

private theorem squarePower (base Q : Nat) :
    ((base : Rat) ^ Q) ^ 2 = (base : Rat) ^ (2 * Q) := by
  calc
    ((base : Rat) ^ Q) ^ 2 =
        (base : Rat) ^ Q * (base : Rat) ^ Q := by
      rw [show (2 : Nat) = 1 + 1 by omega,
        Lean.Grind.Semiring.pow_add]
      simp
    _ = (base : Rat) ^ (Q + Q) :=
      (Lean.Grind.Semiring.pow_add _ _ _).symm
    _ = (base : Rat) ^ (2 * Q) := by congr 1 <;> omega

private theorem cubePower (base Q : Nat) :
    ((base : Rat) ^ Q) ^ 3 = (base : Rat) ^ (3 * Q) := by
  calc
    ((base : Rat) ^ Q) ^ 3 =
        (base : Rat) ^ Q * (base : Rat) ^ Q * (base : Rat) ^ Q := by
      rw [show (3 : Nat) = 1 + 1 + 1 by omega]
      repeat' rw [Lean.Grind.Semiring.pow_add]
      simp
    _ = (base : Rat) ^ (Q + Q + Q) := by
      repeat' rw [Lean.Grind.Semiring.pow_add]
    _ = (base : Rat) ^ (3 * Q) := by congr 1 <;> omega

private theorem powerZeroState_zero_eq_of_auxiliary
    (base exponent : Nat) (denominator : Int) (value : Rat)
    (baseAtLeastTwo : 2 ≤ base) (exponentPositive : 0 < exponent)
    (auxiliary : (base : Rat) * value =
      -((base : Rat) ^ exponent / (denominator : Rat))) :
    powerZeroState base exponent 0 denominator = value := by
  have exponentEq : exponent - 1 + 1 = exponent := by omega
  have stateProduct :
      (base : Rat) * powerZeroState base exponent 0 denominator =
        -((base : Rat) ^ exponent / (denominator : Rat)) := by
    unfold powerZeroState
    simp only [Nat.sub_zero]
    rw [← exponentEq, Rat.pow_succ]
    simp only [Rat.div_def]
    grind
  have productEq :
      (base : Rat) * powerZeroState base exponent 0 denominator =
        (base : Rat) * value := stateProduct.trans auxiliary.symm
  have baseNonzero : (base : Rat) ≠ 0 := by
    simpa using (show base ≠ 0 by omega)
  calc
    powerZeroState base exponent 0 denominator =
        ((base : Rat)⁻¹ * (base : Rat)) *
          powerZeroState base exponent 0 denominator := by
      rw [Rat.inv_mul_cancel (base : Rat) baseNonzero, Rat.one_mul]
    _ = (base : Rat)⁻¹ *
        ((base : Rat) * powerZeroState base exponent 0 denominator) := by
      rw [Rat.mul_assoc]
    _ = (base : Rat)⁻¹ * ((base : Rat) * value) := by rw [productEq]
    _ = ((base : Rat)⁻¹ * (base : Rat)) * value := by
      rw [Rat.mul_assoc]
    _ = value := by
      rw [Rat.inv_mul_cancel (base : Rat) baseNonzero, Rat.one_mul]

def secondGuessState (base Q r deleted : Nat) : Rat :=
  powerZeroState base r deleted (firstGuessDenominator base Q r)

def negativeState (base Q r s deleted : Nat) : Rat :=
  powerZeroState base s deleted (secondGuessDenominator base Q r s)

theorem secondGuessState_zero
    (base Q r : Nat) (baseAtLeastTwo : 2 ≤ base)
    (QPositive : 0 < Q) (rPositive : 0 < r)
    (rBelowThreeQ : r < 3 * Q) :
    secondGuessState base Q r 0 =
      threeProjectionGeneralFirstGuessState
        base (Q - 1) (3 * Q - r) := by
  have firstGuessPositive : 0 < 3 * Q - r := by omega
  have firstGuessBelow : 3 * Q - r < 3 * ((Q - 1) + 1) := by omega
  have auxiliary :=
    threeProjectionGeneralFirstGuessState_auxiliary_independent base (Q - 1)
      (3 * Q - r) baseAtLeastTwo firstGuessPositive firstGuessBelow
  have qEq : Q - 1 + 1 = Q := by omega
  have rEq : 3 * Q - (3 * Q - r) = r := by omega
  simp only [qEq, rEq] at auxiliary
  rw [squarePower base Q, cubePower base Q] at auxiliary
  have castDenominator : (firstGuessDenominator base Q r : Rat) =
      1 + (base : Rat) ^ Q + (base : Rat) ^ (2 * Q) +
        (base : Rat) ^ (3 * Q) - (base : Rat) ^ r := by
    simp [firstGuessDenominator, Rat.intCast_sub, Rat.intCast_add,
      Rat.intCast_pow, Rat.intCast_natCast]
  rw [← castDenominator] at auxiliary
  exact powerZeroState_zero_eq_of_auxiliary base r
    (firstGuessDenominator base Q r) _ baseAtLeastTwo rPositive auxiliary

theorem negativeState_zero
    (base Q r s : Nat) (baseAtLeastTwo : 2 ≤ base)
    (QPositive : 0 < Q) (sPositive : 0 < s)
    (sBelowR : s < r) (rBelowThreeQ : r < 3 * Q) :
    negativeState base Q r s 0 =
      threeProjectionGeneralSecondGuessState
        base (Q - 1) (3 * Q - r) (r - s) := by
  have firstGuessPositive : 0 < 3 * Q - r := by omega
  have firstGuessBelow : 3 * Q - r < 3 * ((Q - 1) + 1) := by omega
  have secondGuessPositive : 0 < r - s := by omega
  have secondGuessBelow :
      r - s < 3 * ((Q - 1) + 1) - (3 * Q - r) := by omega
  have auxiliary := threeProjectionGeneralSecondGuessState_auxiliary base
    (Q - 1) (3 * Q - r) (r - s) baseAtLeastTwo firstGuessPositive
    firstGuessBelow secondGuessPositive secondGuessBelow
  have qEq : Q - 1 + 1 = Q := by omega
  have rEq : 3 * Q - (3 * Q - r) = r := by omega
  have sEq : r - (r - s) = s := by omega
  simp only [qEq, rEq, sEq] at auxiliary
  rw [squarePower base Q, cubePower base Q] at auxiliary
  have castDenominator : (secondGuessDenominator base Q r s : Rat) =
      1 + (base : Rat) ^ Q + (base : Rat) ^ (2 * Q) +
        (base : Rat) ^ (3 * Q) - (base : Rat) ^ r -
          (base : Rat) ^ s := by
    simp [secondGuessDenominator, firstGuessDenominator, Rat.intCast_sub,
      Rat.intCast_add, Rat.intCast_pow, Rat.intCast_natCast]
  rw [← castDenominator] at auxiliary
  exact powerZeroState_zero_eq_of_auxiliary base s
    (secondGuessDenominator base Q r s) _ baseAtLeastTwo sPositive
    auxiliary

theorem secondGuessPrefixState_eq
    (base Q r s : Nat) (baseAtLeastTwo : 2 ≤ base)
    (QPositive : 0 < Q) (sPositive : 0 < s)
    (sBelowR : s < r) (rBelowThreeQ : r < 3 * Q) :
    threeProjectionSecondPrefixState
        base (Q - 1) (3 * Q - r) (r - s) =
      secondGuessState base Q r (r - s) := by
  have firstGuessPositive : 0 < 3 * Q - r := by omega
  have firstGuessBelow : 3 * Q - r < 3 * ((Q - 1) + 1) := by omega
  have secondGuessPositive : 0 < r - s := by omega
  have secondGuessBelow :
      r - s < 3 * ((Q - 1) + 1) - (3 * Q - r) := by omega
  have auxiliary := threeProjectionSecondPrefixState_auxiliary base (Q - 1)
    (3 * Q - r) (r - s) baseAtLeastTwo firstGuessPositive firstGuessBelow
    secondGuessPositive secondGuessBelow
  have qEq : Q - 1 + 1 = Q := by omega
  have rEq : 3 * Q - (3 * Q - r) = r := by omega
  have sEq : r - (r - s) = s := by omega
  simp only [qEq, rEq, sEq] at auxiliary
  rw [squarePower base Q, cubePower base Q] at auxiliary
  have castDenominator : (firstGuessDenominator base Q r : Rat) =
      1 + (base : Rat) ^ Q + (base : Rat) ^ (2 * Q) +
        (base : Rat) ^ (3 * Q) - (base : Rat) ^ r := by
    simp [firstGuessDenominator, Rat.intCast_sub, Rat.intCast_add,
      Rat.intCast_pow, Rat.intCast_natCast]
  rw [← castDenominator] at auxiliary
  have powerStateEq := powerZeroState_zero_eq_of_auxiliary base s
    (firstGuessDenominator base Q r)
    (threeProjectionSecondPrefixState
      base (Q - 1) (3 * Q - r) (r - s)) baseAtLeastTwo sPositive
    auxiliary
  unfold secondGuessState powerZeroState
  rw [show r - 1 - (r - s) = s - 1 by omega]
  change threeProjectionSecondPrefixState base (Q - 1) (3 * Q - r) (r - s) =
    powerZeroState base s 0 (firstGuessDenominator base Q r)
  exact powerStateEq.symm

theorem secondGuessExit_eq_negativeState
    (base Q r s : Nat) (baseAtLeastTwo : 2 ≤ base)
    (QPositive : 0 < Q) (sPositive : 0 < s)
    (sBelowR : s < r) (rBelowThreeQ : r < 3 * Q) :
    Tinv base (secondGuessState base Q r (r - s)) =
      negativeState base Q r s 0 := by
  rw [← secondGuessPrefixState_eq base Q r s baseAtLeastTwo QPositive
    sPositive sBelowR rBelowThreeQ]
  rw [negativeState_zero base Q r s baseAtLeastTwo QPositive sPositive
    sBelowR rBelowThreeQ]
  rfl

theorem powerZeroState_inPhaseAt_before
    {base phase exponent deleted : Nat} {denominator : Int}
    (denominatorNotDivisible : ¬(base : Int) ∣ denominator)
    (deletedBelow : deleted < exponent - 1) :
    InPhaseAt base phase 0
      (phaseAffine phase
        (powerZeroState base exponent deleted denominator)) := by
  apply inPhaseAt_phaseAffine_integer (by simp [ReservedDigit])
    denominatorNotDivisible
  · simpa only [Int.zero_mul, Int.sub_zero] using
      powerZeroState_zero_residue base exponent deleted deletedBelow
  · exact powerZeroState_sameLine_integer base exponent deleted denominator
      denominatorNotDivisible

theorem powerZeroState_inPhaseAt_marker
    {base phase exponent : Nat} {denominator : Int}
    (denominatorNotDivisible : ¬(base : Int) ∣ denominator)
    (oneResidue : (base : Int) ∣ 1 - denominator) :
    InPhaseAt base phase (-1)
      (phaseAffine phase
        (powerZeroState base exponent (exponent - 1) denominator)) := by
  apply inPhaseAt_phaseAffine_integer (by simp [ReservedDigit])
    denominatorNotDivisible
  · exact powerZeroState_negative_residue base exponent denominator
      oneResidue
  · exact powerZeroState_sameLine_integer base exponent (exponent - 1)
      denominator denominatorNotDivisible

theorem powerZeroLoop_step
    (base phase exponent deleted : Nat) (denominator : Int)
    (baseAtLeastTwo : 2 ≤ base)
    (denominatorNotDivisible : ¬(base : Int) ∣ denominator)
    (deletedBelow : deleted < exponent - 1) :
    SameLine
      ((zeroLoop phase).act base
        (phaseAffine phase
          (powerZeroState base exponent deleted denominator)))
      (phaseAffine phase
        (powerZeroState base exponent (deleted + 1) denominator)) := by
  apply TwoProjectionModule.zeroLoop_affine_step base phase
    (powerZeroState base exponent deleted denominator)
    (powerZeroState base exponent (deleted + 1) denominator) baseAtLeastTwo
  · exact powerZeroState_local base exponent deleted denominator
      denominatorNotDivisible
  · exact powerZeroState_local base exponent (deleted + 1) denominator
      denominatorNotDivisible
  · exact powerZeroState_delete_zero base exponent deleted denominator
      baseAtLeastTwo deletedBelow

theorem inverseTZeroExit_power_step
    (base source target exponent deleted : Nat) (denominator : Int)
    (next : Rat) (baseAtLeastTwo : 2 ≤ base)
    (denominatorNotDivisible : ¬(base : Int) ∣ denominator)
    (deletedBelow : deleted < exponent - 1)
    (nextEq : Tinv base
      (powerZeroState base exponent (deleted + 1) denominator) = next) :
    SameLine
      ((inverseTZeroExit source target).act base
        (phaseAffine source
          (powerZeroState base exponent deleted denominator)))
      (phaseAffine target next) := by
  have deletedEq := powerZeroState_delete_zero base exponent deleted
    denominator baseAtLeastTwo deletedBelow
  have action := physicalLetter_affine_sameLine_of_local
    (sourcePhase := source) (targetPhase := target) (digit := 0)
    (preCoefficient := 0) (postCoefficient := 1)
    (postSign := .positive) (primePositive := by omega)
    (powerZeroState_local base exponent deleted denominator
      denominatorNotDivisible) (by
      rw [positive_zero_mutation]
      change LocalAt base
        (Vec2.affine (deleteDigit (base : Rat) 0
          (powerZeroState base exponent deleted denominator)))
      rw [deletedEq]
      exact powerZeroState_local base exponent (deleted + 1) denominator
        denominatorNotDivisible)
  simp [localLetterMap] at action
  change SameLine
    (Matrix2.apply
      (IntMatrix2.cast
        (physicalLetter base source target 0 0 .positive 1))
      (phaseAffine source
        (powerZeroState base exponent deleted denominator)))
    (phaseAffine target
      (mutationMap base .positive 1 (deleteDigit (base : Rat) 0
        (powerZeroState base exponent deleted denominator)))) at action
  rw [positive_one_mutation, deletedEq, nextEq] at action
  simpa [inverseTZeroExit, MutatingScan.exitLetter, PhysicalTemplate.act,
    PhysicalTemplate.matrix] using action

theorem sourceZero_step
    (base phase first deleted : Nat) (baseAtLeastTwo : 2 ≤ base)
    (deletedBelow : deleted < first) :
    SameLine
      ((zeroLoop phase).act base
        (phaseAffine phase (sourceScanState base first deleted)))
      (phaseAffine phase (sourceScanState base first (deleted + 1))) := by
  simpa [sourceScanState] using
    MutatingScan.zeroLoop_step base phase first 1
      (List.replicate (3 * first + 2) 0 ++ [-1]) deleted
      baseAtLeastTwo deletedBelow

theorem sourceMarker_step
    (base source target first : Nat) (baseAtLeastTwo : 2 ≤ base) :
    SameLine
      ((markerOneExit source target).act base
        (phaseAffine source (sourceScanState base first first)))
      (phaseAffine target (threeProjectionFirstState base first)) := by
  have step := MutatingScan.zeroExit_step base source target first 1
    (List.replicate (3 * first + 2) 0 ++ [-1]) .positive 0
    baseAtLeastTwo
  rw [positive_zero_mutation] at step
  rw [firstScan_rotated base first baseAtLeastTwo] at step
  simpa [sourceScanState, markerOneExit] using step

theorem firstGuessZero_step
    (base phase first deleted : Nat) (baseAtLeastTwo : 2 ≤ base)
    (deletedBelow : deleted < 3 * first + 2) :
    SameLine
      ((zeroLoop phase).act base
        (phaseAffine phase (firstGuessState base first deleted)))
      (phaseAffine phase (firstGuessState base first (deleted + 1))) := by
  simpa [firstGuessState] using
    MutatingScan.zeroLoop_step base phase (3 * first + 2) (-1)
      (List.replicate first 0 ++ [1]) deleted baseAtLeastTwo deletedBelow

theorem firstGuessExit_step
    (base source target first deleted : Nat) (baseAtLeastTwo : 2 ≤ base)
    (deletedBelow : deleted < 3 * first + 2) :
    let Q := first + 1
    let r := 3 * Q - (deleted + 1)
    SameLine
      ((inverseTZeroExit source target).act base
        (phaseAffine source (firstGuessState base first deleted)))
      (phaseAffine target (secondGuessState base Q r 0)) := by
  dsimp
  let Q := first + 1
  let r := 3 * Q - (deleted + 1)
  have QPositive : 0 < Q := by simp [Q]
  have rPositive : 0 < r := by unfold r Q; omega
  have rBelowThreeQ : r < 3 * Q := by unfold r; omega
  have guessBound : deleted + 1 ≤ 3 * first + 2 := by omega
  have operationalEq := generalFirstGuessState_eq base first (deleted + 1)
    baseAtLeastTwo guessBound
  have stateEq := secondGuessState_zero base Q r baseAtLeastTwo QPositive
    rPositive rBelowThreeQ
  have guessEq : 3 * Q - r = deleted + 1 := by unfold r Q; omega
  rw [guessEq] at stateEq
  have outputEq : Tinv base (firstGuessState base first (deleted + 1)) =
      secondGuessState base Q r 0 := operationalEq.symm.trans stateEq.symm
  have step := MutatingScan.zeroMutationExit_step base source target
    (3 * first + 2) deleted (-1) (List.replicate first 0 ++ [1])
    .positive 1 baseAtLeastTwo deletedBelow
  rw [positive_one_mutation] at step
  change SameLine
    ((inverseTZeroExit source target).act base
      (phaseAffine source (firstGuessState base first deleted)))
    (phaseAffine target
      (Tinv base (firstGuessState base first (deleted + 1)))) at step
  rw [outputEq] at step
  exact step

theorem secondGuessZero_step
    (base phase Q r deleted : Nat) (baseAtLeastTwo : 2 ≤ base)
    (QPositive : 0 < Q) (rPositive : 0 < r)
    (deletedBelow : deleted < r - 1) :
    SameLine
      ((zeroLoop phase).act base
        (phaseAffine phase (secondGuessState base Q r deleted)))
      (phaseAffine phase (secondGuessState base Q r (deleted + 1))) := by
  exact powerZeroLoop_step base phase r deleted
    (firstGuessDenominator base Q r) baseAtLeastTwo
    (firstGuessDenominator_not_dvd base Q r baseAtLeastTwo QPositive
      rPositive) deletedBelow

theorem secondGuessExit_step
    (base source target Q r deleted : Nat) (baseAtLeastTwo : 2 ≤ base)
    (QPositive : 0 < Q) (rPositive : 0 < r)
    (rBelowThreeQ : r < 3 * Q) (deletedBelow : deleted < r - 1) :
    let s := r - (deleted + 1)
    SameLine
      ((inverseTZeroExit source target).act base
        (phaseAffine source (secondGuessState base Q r deleted)))
      (phaseAffine target (negativeState base Q r s 0)) := by
  dsimp
  let s := r - (deleted + 1)
  have sPositive : 0 < s := by unfold s; omega
  have sBelowR : s < r := by unfold s; omega
  have countEq : r - s = deleted + 1 := by unfold s; omega
  have outputEq := secondGuessExit_eq_negativeState base Q r s
    baseAtLeastTwo QPositive sPositive sBelowR rBelowThreeQ
  rw [countEq] at outputEq
  exact inverseTZeroExit_power_step base source target r deleted
    (firstGuessDenominator base Q r) (negativeState base Q r s 0)
    baseAtLeastTwo
    (firstGuessDenominator_not_dvd base Q r baseAtLeastTwo QPositive
      rPositive) deletedBelow outputEq

theorem negativeZero_step
    (base phase Q r s deleted : Nat) (baseAtLeastTwo : 2 ≤ base)
    (QPositive : 0 < Q) (rPositive : 0 < r) (sPositive : 0 < s)
    (deletedBelow : deleted < s - 1) :
    SameLine
      ((zeroLoop phase).act base
        (phaseAffine phase (negativeState base Q r s deleted)))
      (phaseAffine phase (negativeState base Q r s (deleted + 1))) := by
  exact powerZeroLoop_step base phase s deleted
    (secondGuessDenominator base Q r s) baseAtLeastTwo
    (secondGuessDenominator_not_dvd base Q r s baseAtLeastTwo QPositive
      rPositive sPositive) deletedBelow

private theorem delete_integer_fraction
    (base : Nat) (digit numerator denominator quotient : Int)
    (basePositive : 0 < base) (denominatorNonzero : denominator ≠ 0)
    (differenceEq : numerator - digit * denominator =
      (base : Int) * quotient) :
    deleteDigit (base : Rat) digit
        ((numerator : Rat) / (denominator : Rat)) =
      (quotient : Rat) / (denominator : Rat) := by
  have baseNonzero : (base : Rat) ≠ 0 := by
    simpa using (show base ≠ 0 by omega)
  have denominatorNonzeroRat : (denominator : Rat) ≠ 0 := by
    exact_mod_cast denominatorNonzero
  have differenceRat :
      (numerator : Rat) - (digit : Rat) * (denominator : Rat) =
        (base : Rat) * (quotient : Rat) := by
    exact_mod_cast differenceEq
  unfold deleteDigit
  rw [Rat.div_def, Rat.div_def, Rat.div_def]
  have baseCancel := Rat.mul_inv_cancel (base : Rat) baseNonzero
  have denominatorCancel := Rat.mul_inv_cancel (denominator : Rat)
    denominatorNonzeroRat
  grind

def negativeDeletedState (base Q r s : Nat) : Rat :=
  (candidateNumerator base Q r s 0 : Rat) /
    (secondGuessDenominator base Q r s : Rat)

theorem negativeDeletedState_local
    (base Q r s : Nat) (baseAtLeastTwo : 2 ≤ base)
    (QPositive : 0 < Q) (rPositive : 0 < r) (sPositive : 0 < s) :
    LocalAt base (Vec2.affine (negativeDeletedState base Q r s)) := by
  have localFraction := local_affine_integer_div
    (prime := base) (numerator := candidateNumerator base Q r s 0)
    (denominator := secondGuessDenominator base Q r s)
    (secondGuessDenominator_not_dvd base Q r s baseAtLeastTwo QPositive
      rPositive sPositive)
  simpa [negativeDeletedState] using localFraction

theorem negativeState_delete_marker
    (base Q r s : Nat) (baseAtLeastTwo : 2 ≤ base)
    (QPositive : 0 < Q) (rPositive : 0 < r) (sPositive : 0 < s) :
    deleteDigit (base : Rat) (-1)
        (negativeState base Q r s (s - 1)) =
      negativeDeletedState base Q r s := by
  have notDivisible := secondGuessDenominator_not_dvd base Q r s
    baseAtLeastTwo QPositive rPositive sPositive
  have denominatorNonzero : secondGuessDenominator base Q r s ≠ 0 :=
    fun zero => notDivisible (by rw [zero]; exact Int.dvd_zero _)
  have qSucc : (base : Int) ^ Q =
      (base : Int) ^ (Q - 1) * (base : Int) := by
    calc
      (base : Int) ^ Q = (base : Int) ^ (Q - 1 + 1) := by
        congr 1 <;> omega
      _ = _ := by rw [Int.pow_succ]
  have q2Succ : (base : Int) ^ (2 * Q) =
      (base : Int) ^ (2 * Q - 1) * (base : Int) := by
    calc
      (base : Int) ^ (2 * Q) =
          (base : Int) ^ (2 * Q - 1 + 1) := by congr 1 <;> omega
      _ = _ := by rw [Int.pow_succ]
  have q3Succ : (base : Int) ^ (3 * Q) =
      (base : Int) ^ (3 * Q - 1) * (base : Int) := by
    calc
      (base : Int) ^ (3 * Q) =
          (base : Int) ^ (3 * Q - 1 + 1) := by congr 1 <;> omega
      _ = _ := by rw [Int.pow_succ]
  have rSucc : (base : Int) ^ r =
      (base : Int) ^ (r - 1) * (base : Int) := by
    calc
      (base : Int) ^ r = (base : Int) ^ (r - 1 + 1) := by
        congr 1 <;> omega
      _ = _ := by rw [Int.pow_succ]
  have sSucc : (base : Int) ^ s =
      (base : Int) ^ (s - 1) * (base : Int) := by
    calc
      (base : Int) ^ s = (base : Int) ^ (s - 1 + 1) := by
        congr 1 <;> omega
      _ = _ := by rw [Int.pow_succ]
  have differenceEq :
      (-1 : Int) - (-1) * secondGuessDenominator base Q r s =
        (base : Int) * candidateNumerator base Q r s 0 := by
    unfold secondGuessDenominator firstGuessDenominator candidateNumerator
    simp only [Nat.sub_zero]
    rw [qSucc, q2Succ, q3Succ, rSucc, sSucc]
    grind
  have deleted := delete_integer_fraction base (-1) (-1)
    (secondGuessDenominator base Q r s)
    (candidateNumerator base Q r s 0) (by omega) denominatorNonzero
    differenceEq
  unfold negativeState powerZeroState negativeDeletedState
  simpa using deleted

private theorem eq_of_base_mul_eq
    (base : Nat) (baseAtLeastTwo : 2 ≤ base) {first second : Rat}
    (productEq : (base : Rat) * first = (base : Rat) * second) :
    first = second := by
  have baseNonzero : (base : Rat) ≠ 0 := by
    simpa using (show base ≠ 0 by omega)
  calc
    first = ((base : Rat)⁻¹ * (base : Rat)) * first := by
      rw [Rat.inv_mul_cancel (base : Rat) baseNonzero, Rat.one_mul]
    _ = (base : Rat)⁻¹ * ((base : Rat) * first) := by
      rw [Rat.mul_assoc]
    _ = (base : Rat)⁻¹ * ((base : Rat) * second) := by rw [productEq]
    _ = ((base : Rat)⁻¹ * (base : Rat)) * second := by
      rw [Rat.mul_assoc]
    _ = second := by
      rw [Rat.inv_mul_cancel (base : Rat) baseNonzero, Rat.one_mul]

theorem negativeDeletedState_eq_operational
    (base Q r s : Nat) (baseAtLeastTwo : 2 ≤ base)
    (QPositive : 0 < Q) (sPositive : 0 < s)
    (sBelowR : s < r) (rBelowThreeQ : r < 3 * Q) :
    negativeDeletedState base Q r s =
      threeProjectionGeneralNegativeState
        base (Q - 1) (3 * Q - r) (r - s) := by
  have firstGuessPositive : 0 < 3 * Q - r := by omega
  have firstGuessBelow : 3 * Q - r < 3 * ((Q - 1) + 1) := by omega
  have secondGuessPositive : 0 < r - s := by omega
  have secondGuessBelow :
      r - s < 3 * ((Q - 1) + 1) - (3 * Q - r) := by omega
  have auxiliary := threeProjectionGeneralNegativeState_auxiliary base
    (Q - 1) (3 * Q - r) (r - s) baseAtLeastTwo firstGuessPositive
    firstGuessBelow secondGuessPositive secondGuessBelow
  have qEq : Q - 1 + 1 = Q := by omega
  have rEq : 3 * Q - (3 * Q - r) = r := by omega
  have sEq : r - (r - s) = s := by omega
  simp only [qEq, rEq, sEq] at auxiliary
  rw [squarePower base Q, cubePower base Q] at auxiliary
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
  have q3Succ : (base : Rat) ^ (3 * Q) =
      (base : Rat) ^ (3 * Q - 1) * (base : Rat) := by
    calc
      (base : Rat) ^ (3 * Q) =
          (base : Rat) ^ (3 * Q - 1 + 1) := by congr 1 <;> omega
      _ = _ := by rw [Rat.pow_succ]
  have rSucc : (base : Rat) ^ r =
      (base : Rat) ^ (r - 1) * (base : Rat) := by
    calc
      (base : Rat) ^ r = (base : Rat) ^ (r - 1 + 1) := by
        congr 1 <;> omega
      _ = _ := by rw [Rat.pow_succ]
  have sSucc : (base : Rat) ^ s =
      (base : Rat) ^ (s - 1) * (base : Rat) := by
    calc
      (base : Rat) ^ s = (base : Rat) ^ (s - 1 + 1) := by
        congr 1 <;> omega
      _ = _ := by rw [Rat.pow_succ]
  have castDenominator : (secondGuessDenominator base Q r s : Rat) =
      1 + (base : Rat) ^ Q + (base : Rat) ^ (2 * Q) +
        (base : Rat) ^ (3 * Q) - (base : Rat) ^ r -
          (base : Rat) ^ s := by
    simp [secondGuessDenominator, firstGuessDenominator, Rat.intCast_sub,
      Rat.intCast_add, Rat.intCast_pow, Rat.intCast_natCast]
  have productEq :
      (base : Rat) * negativeDeletedState base Q r s =
        (base : Rat) *
          threeProjectionGeneralNegativeState
            base (Q - 1) (3 * Q - r) (r - s) := by
    rw [auxiliary]
    unfold negativeDeletedState candidateNumerator
    simp only [Nat.sub_zero, Rat.intCast_sub, Rat.intCast_add,
      Rat.intCast_pow, Rat.intCast_natCast, Rat.div_def]
    rw [castDenominator, qSucc, q2Succ, q3Succ, rSucc, sSucc]
    grind
  exact eq_of_base_mul_eq base baseAtLeastTwo productEq

theorem negativeDeletedState_finv
    (base Q r s : Nat) (baseAtLeastTwo : 2 ≤ base)
    (QPositive : 0 < Q) (sPositive : 0 < s)
    (sBelowR : s < r) (rBelowThreeQ : r < 3 * Q) :
    Finv base (negativeDeletedState base Q r s) =
      candidateState base Q r s 0 := by
  rw [negativeDeletedState_eq_operational base Q r s baseAtLeastTwo
    QPositive sPositive sBelowR rBelowThreeQ]
  change threeProjectionGeneralCandidate
      base (Q - 1) (3 * Q - r) (r - s) = _
  exact operational_candidate_eq base Q r s baseAtLeastTwo QPositive
    sPositive sBelowR rBelowThreeQ

theorem negativeMarker_step
    (base source target Q r s : Nat) (baseAtLeastTwo : 2 ≤ base)
    (QPositive : 0 < Q) (sPositive : 0 < s)
    (sBelowR : s < r) (rBelowThreeQ : r < 3 * Q) :
    SameLine
      ((inverseFNegativeExit source target).act base
        (phaseAffine source (negativeState base Q r s (s - 1))))
      (phaseAffine target (candidateState base Q r s 0)) := by
  have rPositive : 0 < r := by omega
  have deletedEq := negativeState_delete_marker base Q r s baseAtLeastTwo
    QPositive rPositive sPositive
  have outputEq := negativeDeletedState_finv base Q r s baseAtLeastTwo
    QPositive sPositive sBelowR rBelowThreeQ
  have action := physicalLetter_affine_sameLine_of_local
    (sourcePhase := source) (targetPhase := target) (digit := -1)
    (preCoefficient := 0) (postCoefficient := -2)
    (postSign := .positive) (primePositive := by omega)
    (powerZeroState_local base s (s - 1)
      (secondGuessDenominator base Q r s)
      (secondGuessDenominator_not_dvd base Q r s baseAtLeastTwo QPositive
        rPositive sPositive)) (by
      rw [positive_zero_mutation]
      change LocalAt base
        (Vec2.affine (deleteDigit (base : Rat) (-1)
          (negativeState base Q r s (s - 1))))
      rw [deletedEq]
      exact negativeDeletedState_local base Q r s baseAtLeastTwo QPositive
        rPositive sPositive)
  simp [localLetterMap] at action
  change SameLine
    (Matrix2.apply
      (IntMatrix2.cast
        (physicalLetter base source target (-1) 0 .positive (-2)))
      (phaseAffine source (negativeState base Q r s (s - 1))))
    (phaseAffine target
      (mutationMap base .positive (-2)
        (deleteDigit (base : Rat) (-1)
          (negativeState base Q r s (s - 1))))) at action
  rw [positive_minus_two_mutation, deletedEq, outputEq] at action
  simpa [inverseFNegativeExit, MutatingScan.exitLetter,
    PhysicalTemplate.act, PhysicalTemplate.matrix] using action

theorem sourceWord_correct
    (base source target first : Nat) (baseAtLeastTwo : 2 ≤ base) :
    SameLine
      (physicalWordAction base (sourceWord source target first)
        (phaseAffine source
          (twoFieldCode base first (3 * first + 2))))
      (phaseAffine target (threeProjectionFirstState base first)) := by
  have action := MutatingScan.word_correct base source target
    (List.replicate first 0)
    (List.replicate (3 * first + 2) 0 ++ [-1]) 1 .positive 0
    baseAtLeastTwo
  rw [positive_zero_mutation] at action
  rw [firstScan_rotated base first baseAtLeastTwo] at action
  simpa [sourceWord, twoFieldCode, twoFieldDigits, List.append_assoc]
    using action

theorem firstGuessAcceptedTail_correct
    (base source target first deleted remaining : Nat)
    (baseAtLeastTwo : 2 ≤ base) (sumEq : deleted + remaining = first) :
    let Q := first + 1
    SameLine
      (physicalWordAction base
        (List.replicate remaining (zeroLoop source) ++
          [inverseTZeroExit source target])
        (phaseAffine source (firstGuessState base first deleted)))
      (phaseAffine target (secondGuessState base Q (2 * Q) 0)) := by
  dsimp
  induction remaining generalizing deleted with
  | zero =>
      have deletedEq : deleted = first := by omega
      subst deleted
      have step := firstGuessExit_step base source target first first
        baseAtLeastTwo (by omega)
      dsimp at step
      have rEq : 3 * (first + 1) - (first + 1) =
          2 * (first + 1) := by omega
      rw [rEq] at step
      simpa [physicalWordAction] using step
  | succ remaining inductionHypothesis =>
      have step := firstGuessZero_step base source first deleted
        baseAtLeastTwo (by omega)
      have tail := inductionHypothesis (deleted := deleted + 1) (by omega)
      exact physicalWordAction_cons_sameLine base (zeroLoop source)
        (List.replicate remaining (zeroLoop source) ++
          [inverseTZeroExit source target]) step tail

theorem firstGuessAccepted_correct
    (base source target first : Nat) (baseAtLeastTwo : 2 ≤ base) :
    let Q := first + 1
    SameLine
      (physicalWordAction base (guessWord source target Q)
        (phaseAffine source (threeProjectionFirstState base first)))
      (phaseAffine target (secondGuessState base Q (2 * Q) 0)) := by
  dsimp
  rw [← firstGuessState_zero base first baseAtLeastTwo]
  simpa [guessWord] using firstGuessAcceptedTail_correct base source target
    first 0 first baseAtLeastTwo (by omega)

theorem secondGuessAcceptedTail_correct
    (base source target Q deleted remaining : Nat)
    (baseAtLeastTwo : 2 ≤ base) (QPositive : 0 < Q)
    (sumEq : deleted + remaining = Q - 1) :
    SameLine
      (physicalWordAction base
        (List.replicate remaining (zeroLoop source) ++
          [inverseTZeroExit source target])
        (phaseAffine source (secondGuessState base Q (2 * Q) deleted)))
      (phaseAffine target (negativeState base Q (2 * Q) Q 0)) := by
  induction remaining generalizing deleted with
  | zero =>
      have deletedEq : deleted = Q - 1 := by omega
      subst deleted
      have step := secondGuessExit_step base source target Q (2 * Q) (Q - 1)
        baseAtLeastTwo QPositive (by omega) (by omega) (by omega)
      dsimp at step
      have sEq : 2 * Q - (Q - 1 + 1) = Q := by omega
      rw [sEq] at step
      simpa [physicalWordAction] using step
  | succ remaining inductionHypothesis =>
      have step := secondGuessZero_step base source Q (2 * Q) deleted
        baseAtLeastTwo QPositive (by omega) (by omega)
      have tail := inductionHypothesis (deleted := deleted + 1) (by omega)
      exact physicalWordAction_cons_sameLine base (zeroLoop source)
        (List.replicate remaining (zeroLoop source) ++
          [inverseTZeroExit source target]) step tail

theorem secondGuessAccepted_correct
    (base source target Q : Nat) (baseAtLeastTwo : 2 ≤ base)
    (QPositive : 0 < Q) :
    SameLine
      (physicalWordAction base (guessWord source target Q)
        (phaseAffine source (secondGuessState base Q (2 * Q) 0)))
      (phaseAffine target (negativeState base Q (2 * Q) Q 0)) := by
  simpa [guessWord] using secondGuessAcceptedTail_correct base source target
    Q 0 (Q - 1) baseAtLeastTwo QPositive (by omega)

theorem negativeAcceptedTail_correct
    (base source target Q deleted remaining : Nat)
    (baseAtLeastTwo : 2 ≤ base) (QPositive : 0 < Q)
    (sumEq : deleted + remaining = Q - 1) :
    SameLine
      (physicalWordAction base
        (List.replicate remaining (zeroLoop source) ++
          [inverseFNegativeExit source target])
        (phaseAffine source (negativeState base Q (2 * Q) Q deleted)))
      (phaseAffine target (candidateState base Q (2 * Q) Q 0)) := by
  induction remaining generalizing deleted with
  | zero =>
      have step := negativeMarker_step base source target Q (2 * Q) Q
        baseAtLeastTwo QPositive QPositive (by omega) (by omega)
      simpa [physicalWordAction, show deleted = Q - 1 by omega] using step
  | succ remaining inductionHypothesis =>
      have step := negativeZero_step base source Q (2 * Q) Q deleted
        baseAtLeastTwo QPositive (by omega) QPositive (by omega)
      have tail := inductionHypothesis (deleted := deleted + 1) (by omega)
      exact physicalWordAction_cons_sameLine base (zeroLoop source)
        (List.replicate remaining (zeroLoop source) ++
          [inverseFNegativeExit source target]) step tail

theorem negativeAccepted_correct
    (base source target Q : Nat) (baseAtLeastTwo : 2 ≤ base)
    (QPositive : 0 < Q) :
    SameLine
      (physicalWordAction base (negativeWord source target Q)
        (phaseAffine source (negativeState base Q (2 * Q) Q 0)))
      (phaseAffine target (candidateState base Q (2 * Q) Q 0)) := by
  simpa [negativeWord] using negativeAcceptedTail_correct base source target
    Q 0 (Q - 1) baseAtLeastTwo QPositive (by omega)

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
    (base source target firstGuess secondGuess negativePhase firstValidator
      secondValidator thirdValidator first : Nat)
    (baseAtLeastTwo : 2 ≤ base) :
    SameLine
      (physicalWordAction base
        (acceptedWord source target firstGuess secondGuess negativePhase
          firstValidator secondValidator thirdValidator first)
        (phaseAffine source
          (twoFieldCode base first (3 * first + 2))))
      (phaseAffine target (unaryCode base (3 * first + 2))) := by
  let Q := first + 1
  have QPositive : 0 < Q := by simp [Q]
  have sourceRun := sourceWord_correct base source firstGuess first
    baseAtLeastTwo
  have firstGuessRun := firstGuessAccepted_correct base firstGuess secondGuess
    first baseAtLeastTwo
  have secondGuessRun := secondGuessAccepted_correct base secondGuess
    negativePhase Q baseAtLeastTwo QPositive
  have negativeRun := negativeAccepted_correct base negativePhase
    firstValidator Q baseAtLeastTwo QPositive
  have acceptedEq := accepted_candidate_state base Q QPositive
  have counterEq : 3 * Q - 1 = 3 * first + 2 := by unfold Q; omega
  rw [acceptedEq, counterEq] at negativeRun
  have validatorOne := validatorWord_correct base firstValidator
    secondValidator (3 * first + 2) baseAtLeastTwo
  have validatorTwo := validatorWord_correct base secondValidator
    thirdValidator (3 * first + 2) baseAtLeastTwo
  have validatorThree := validatorWord_correct base thirdValidator target
    (3 * first + 2) baseAtLeastTwo
  have throughFirstGuess := physicalWordAction_append_sameLine base
    (sourceWord source firstGuess first)
    (guessWord firstGuess secondGuess Q) sourceRun firstGuessRun
  have throughSecondGuess := physicalWordAction_append_sameLine base
    (sourceWord source firstGuess first ++ guessWord firstGuess secondGuess Q)
    (guessWord secondGuess negativePhase Q) throughFirstGuess secondGuessRun
  have throughNegative := physicalWordAction_append_sameLine base
    (sourceWord source firstGuess first ++ guessWord firstGuess secondGuess Q ++
      guessWord secondGuess negativePhase Q)
    (negativeWord negativePhase firstValidator Q) throughSecondGuess
    negativeRun
  have throughV1 := physicalWordAction_append_sameLine base
    (sourceWord source firstGuess first ++ guessWord firstGuess secondGuess Q ++
      guessWord secondGuess negativePhase Q ++
      negativeWord negativePhase firstValidator Q)
    (validatorWord firstValidator secondValidator (3 * first + 2))
    throughNegative validatorOne
  have throughV2 := physicalWordAction_append_sameLine base
    (sourceWord source firstGuess first ++ guessWord firstGuess secondGuess Q ++
      guessWord secondGuess negativePhase Q ++
      negativeWord negativePhase firstValidator Q ++
      validatorWord firstValidator secondValidator (3 * first + 2))
    (validatorWord secondValidator thirdValidator (3 * first + 2))
    throughV1 validatorTwo
  have complete := physicalWordAction_append_sameLine base
    (sourceWord source firstGuess first ++ guessWord firstGuess secondGuess Q ++
      guessWord secondGuess negativePhase Q ++
      negativeWord negativePhase firstValidator Q ++
      validatorWord firstValidator secondValidator (3 * first + 2) ++
      validatorWord secondValidator thirdValidator (3 * first + 2))
    (validatorWord thirdValidator target (3 * first + 2))
    throughV2 validatorThree
  simpa [acceptedWord, Q, List.append_assoc] using complete

theorem accepted_execution
    (base source target firstGuess secondGuess negativePhase firstValidator
      secondValidator thirdValidator first : Nat)
    (baseAtLeastTwo : 2 ≤ base) :
    let moduleWord := acceptedWord source target firstGuess secondGuess
      negativePhase firstValidator secondValidator thirdValidator first
    WordOver
        (alphabet source target firstGuess secondGuess negativePhase
          firstValidator secondValidator thirdValidator) moduleWord ∧
      moduleWord.length = 13 * first + 13 ∧
      SameLine
        (physicalWordAction base moduleWord
          (phaseAffine source
            (twoFieldCode base first (3 * first + 2))))
        (phaseAffine target (unaryCode base (3 * first + 2))) ∧
      AllStatesLocal base moduleWord
        (phaseAffine source
          (twoFieldCode base first (3 * first + 2))) := by
  dsimp
  have action := acceptedWord_correct base source target firstGuess
    secondGuess negativePhase firstValidator secondValidator thirdValidator
    first baseAtLeastTwo
  have inputLocal := TwoProjectionModule.phase_local (phase := source)
    (periodicCode_local_affine base
      (twoFieldDigits first (3 * first + 2)) baseAtLeastTwo
      (by simp [twoFieldDigits]))
  have finalLocal := TwoProjectionModule.phase_local (phase := target)
    (periodicCode_local_affine base (unaryDigits (3 * first + 2))
      baseAtLeastTwo (by simp [unaryDigits]))
  have outputNonzero := physicalWordAction_nonzero (prime := base) (by omega)
    (acceptedWord source target firstGuess secondGuess negativePhase
      firstValidator secondValidator thirdValidator first) inputLocal.1
  have actualFinalLocal := LocalAt.of_sameLine finalLocal outputNonzero action
  exact ⟨acceptedWord_wordOver source target firstGuess secondGuess
      negativePhase firstValidator secondValidator thirdValidator first,
    acceptedWord_length source target firstGuess secondGuess negativePhase
      firstValidator secondValidator thirdValidator first,
    action,
    allStatesLocal_of_final_local (by omega) _ inputLocal.1 actualFinalLocal⟩

theorem letter_source_bound
    {phaseCount source target firstGuess secondGuess negativePhase
      firstValidator secondValidator thirdValidator : Nat}
    (layout : PhaseLayout phaseCount source firstGuess secondGuess
      negativePhase firstValidator secondValidator thirdValidator)
    {letter : PhysicalTemplate}
    (letterMem : letter ∈ alphabet source target firstGuess secondGuess
      negativePhase firstValidator secondValidator thirdValidator) :
    letter.sourcePhase < phaseCount := by
  simp [alphabet] at letterMem
  rcases letterMem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl
  · exact layout.sourceBound
  · exact layout.sourceBound
  · exact layout.firstGuessBound
  · exact layout.firstGuessBound
  · exact layout.secondGuessBound
  · exact layout.secondGuessBound
  · exact layout.negativeBound
  · exact layout.negativeBound
  · exact layout.firstValidatorBound
  · exact layout.firstValidatorBound
  · exact layout.secondValidatorBound
  · exact layout.secondValidatorBound
  · exact layout.thirdValidatorBound
  · exact layout.thirdValidatorBound

theorem letter_reserved
    {source target firstGuess secondGuess negativePhase firstValidator
      secondValidator thirdValidator : Nat} {letter : PhysicalTemplate}
    (letterMem : letter ∈ alphabet source target firstGuess secondGuess
      negativePhase firstValidator secondValidator thirdValidator) :
    ReservedDigit letter.digit := by
  simp [alphabet] at letterMem
  rcases letterMem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp [zeroLoop, markerOneExit, inverseTZeroExit, inverseFNegativeExit,
      MutatingScan.loopLetter, MutatingScan.exitLetter, ReservedDigit]

/-- Every three-projection letter starts in one of the seven active module
phases. -/
theorem letter_source_mem_active
    {source target firstGuess secondGuess negativePhase firstValidator
      secondValidator thirdValidator : Nat} {letter : PhysicalTemplate}
    (letterMem : letter ∈ alphabet source target firstGuess secondGuess
      negativePhase firstValidator secondValidator thirdValidator) :
    letter.sourcePhase ∈ [source, firstGuess, secondGuess, negativePhase,
      firstValidator, secondValidator, thirdValidator] := by
  simp [alphabet] at letterMem
  rcases letterMem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp [zeroLoop, markerOneExit, inverseTZeroExit, inverseFNegativeExit,
      MutatingScan.loopLetter, MutatingScan.exitLetter]

theorem force_metadata
    {prime phaseCount source target firstGuess secondGuess negativePhase
      firstValidator secondValidator thirdValidator actualPhase : Nat}
    {actualDigit : Int} {state : Vec2} {letter : PhysicalTemplate}
    (primeProperty : IsPrime prime) (primeBound : 6 * phaseCount < prime)
    (layout : PhaseLayout phaseCount source firstGuess secondGuess
      negativePhase firstValidator secondValidator thirdValidator)
    (actualBound : actualPhase < phaseCount)
    (membership : InPhaseAt prime actualPhase actualDigit state)
    (letterMem : letter ∈ alphabet source target firstGuess secondGuess
      negativePhase firstValidator secondValidator thirdValidator)
    (outputLocal : LocalAt prime (letter.act prime state)) :
    actualPhase = letter.sourcePhase ∧ actualDigit = letter.digit := by
  apply membership.physicalLetter_source_digit_unique primeProperty
    primeBound actualBound (letter_source_bound layout letterMem)
    (letter_reserved letterMem)
  simpa [PhysicalTemplate.act, PhysicalTemplate.matrix] using outputLocal

theorem source_letter
    {prime phaseCount source target firstGuess secondGuess negativePhase
      firstValidator secondValidator thirdValidator : Nat}
    {digit : Int} {state : Vec2} {letter : PhysicalTemplate}
    (primeProperty : IsPrime prime) (primeBound : 6 * phaseCount < prime)
    (layout : PhaseLayout phaseCount source firstGuess secondGuess
      negativePhase firstValidator secondValidator thirdValidator)
    (membership : InPhaseAt prime source digit state)
    (letterMem : letter ∈ alphabet source target firstGuess secondGuess
      negativePhase firstValidator secondValidator thirdValidator)
    (outputLocal : LocalAt prime (letter.act prime state)) :
    (digit = 0 ∧ letter = zeroLoop source) ∨
      (digit = 1 ∧ letter = markerOneExit source firstGuess) := by
  have forced := force_metadata primeProperty primeBound layout
    layout.sourceBound membership letterMem outputLocal
  simp [alphabet] at letterMem
  rcases letterMem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl
  · exact Or.inl ⟨forced.2, rfl⟩
  · exact Or.inr ⟨forced.2, rfl⟩
  · exact False.elim (layout.sourceFirstGuessDistinct forced.1)
  · exact False.elim (layout.sourceFirstGuessDistinct forced.1)
  · exact False.elim (layout.sourceSecondGuessDistinct forced.1)
  · exact False.elim (layout.sourceSecondGuessDistinct forced.1)
  · exact False.elim (layout.sourceNegativeDistinct forced.1)
  · exact False.elim (layout.sourceNegativeDistinct forced.1)
  · exact False.elim (layout.sourceFirstValidatorDistinct forced.1)
  · exact False.elim (layout.sourceFirstValidatorDistinct forced.1)
  · exact False.elim (layout.sourceSecondValidatorDistinct forced.1)
  · exact False.elim (layout.sourceSecondValidatorDistinct forced.1)
  · exact False.elim (layout.sourceThirdValidatorDistinct forced.1)
  · exact False.elim (layout.sourceThirdValidatorDistinct forced.1)

theorem first_guess_letter
    {prime phaseCount source target firstGuess secondGuess negativePhase
      firstValidator secondValidator thirdValidator : Nat}
    {digit : Int} {state : Vec2} {letter : PhysicalTemplate}
    (primeProperty : IsPrime prime) (primeBound : 6 * phaseCount < prime)
    (layout : PhaseLayout phaseCount source firstGuess secondGuess
      negativePhase firstValidator secondValidator thirdValidator)
    (membership : InPhaseAt prime firstGuess digit state)
    (letterMem : letter ∈ alphabet source target firstGuess secondGuess
      negativePhase firstValidator secondValidator thirdValidator)
    (outputLocal : LocalAt prime (letter.act prime state)) :
    digit = 0 ∧
      (letter = zeroLoop firstGuess ∨
        letter = inverseTZeroExit firstGuess secondGuess) := by
  have forced := force_metadata primeProperty primeBound layout
    layout.firstGuessBound membership letterMem outputLocal
  simp [alphabet] at letterMem
  rcases letterMem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl
  · exact False.elim (layout.sourceFirstGuessDistinct forced.1.symm)
  · exact False.elim (layout.sourceFirstGuessDistinct forced.1.symm)
  · exact ⟨forced.2, Or.inl rfl⟩
  · exact ⟨forced.2, Or.inr rfl⟩
  · exact False.elim (layout.guessesDistinct forced.1)
  · exact False.elim (layout.guessesDistinct forced.1)
  · exact False.elim (layout.firstGuessNegativeDistinct forced.1)
  · exact False.elim (layout.firstGuessNegativeDistinct forced.1)
  · exact False.elim (layout.firstGuessFirstValidatorDistinct forced.1)
  · exact False.elim (layout.firstGuessFirstValidatorDistinct forced.1)
  · exact False.elim (layout.firstGuessSecondValidatorDistinct forced.1)
  · exact False.elim (layout.firstGuessSecondValidatorDistinct forced.1)
  · exact False.elim (layout.firstGuessThirdValidatorDistinct forced.1)
  · exact False.elim (layout.firstGuessThirdValidatorDistinct forced.1)

theorem second_guess_letter
    {prime phaseCount source target firstGuess secondGuess negativePhase
      firstValidator secondValidator thirdValidator : Nat}
    {digit : Int} {state : Vec2} {letter : PhysicalTemplate}
    (primeProperty : IsPrime prime) (primeBound : 6 * phaseCount < prime)
    (layout : PhaseLayout phaseCount source firstGuess secondGuess
      negativePhase firstValidator secondValidator thirdValidator)
    (membership : InPhaseAt prime secondGuess digit state)
    (letterMem : letter ∈ alphabet source target firstGuess secondGuess
      negativePhase firstValidator secondValidator thirdValidator)
    (outputLocal : LocalAt prime (letter.act prime state)) :
    digit = 0 ∧
      (letter = zeroLoop secondGuess ∨
        letter = inverseTZeroExit secondGuess negativePhase) := by
  have forced := force_metadata primeProperty primeBound layout
    layout.secondGuessBound membership letterMem outputLocal
  simp [alphabet] at letterMem
  rcases letterMem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl
  · exact False.elim (layout.sourceSecondGuessDistinct forced.1.symm)
  · exact False.elim (layout.sourceSecondGuessDistinct forced.1.symm)
  · exact False.elim (layout.guessesDistinct forced.1.symm)
  · exact False.elim (layout.guessesDistinct forced.1.symm)
  · exact ⟨forced.2, Or.inl rfl⟩
  · exact ⟨forced.2, Or.inr rfl⟩
  · exact False.elim (layout.secondGuessNegativeDistinct forced.1)
  · exact False.elim (layout.secondGuessNegativeDistinct forced.1)
  · exact False.elim (layout.secondGuessFirstValidatorDistinct forced.1)
  · exact False.elim (layout.secondGuessFirstValidatorDistinct forced.1)
  · exact False.elim (layout.secondGuessSecondValidatorDistinct forced.1)
  · exact False.elim (layout.secondGuessSecondValidatorDistinct forced.1)
  · exact False.elim (layout.secondGuessThirdValidatorDistinct forced.1)
  · exact False.elim (layout.secondGuessThirdValidatorDistinct forced.1)

theorem negative_letter
    {prime phaseCount source target firstGuess secondGuess negativePhase
      firstValidator secondValidator thirdValidator : Nat}
    {digit : Int} {state : Vec2} {letter : PhysicalTemplate}
    (primeProperty : IsPrime prime) (primeBound : 6 * phaseCount < prime)
    (layout : PhaseLayout phaseCount source firstGuess secondGuess
      negativePhase firstValidator secondValidator thirdValidator)
    (membership : InPhaseAt prime negativePhase digit state)
    (letterMem : letter ∈ alphabet source target firstGuess secondGuess
      negativePhase firstValidator secondValidator thirdValidator)
    (outputLocal : LocalAt prime (letter.act prime state)) :
    (digit = 0 ∧ letter = zeroLoop negativePhase) ∨
      (digit = -1 ∧
        letter = inverseFNegativeExit negativePhase firstValidator) := by
  have forced := force_metadata primeProperty primeBound layout
    layout.negativeBound membership letterMem outputLocal
  simp [alphabet] at letterMem
  rcases letterMem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl
  · exact False.elim (layout.sourceNegativeDistinct forced.1.symm)
  · exact False.elim (layout.sourceNegativeDistinct forced.1.symm)
  · exact False.elim (layout.firstGuessNegativeDistinct forced.1.symm)
  · exact False.elim (layout.firstGuessNegativeDistinct forced.1.symm)
  · exact False.elim (layout.secondGuessNegativeDistinct forced.1.symm)
  · exact False.elim (layout.secondGuessNegativeDistinct forced.1.symm)
  · exact Or.inl ⟨forced.2, rfl⟩
  · exact Or.inr ⟨forced.2, rfl⟩
  · exact False.elim (layout.negativeFirstValidatorDistinct forced.1)
  · exact False.elim (layout.negativeFirstValidatorDistinct forced.1)
  · exact False.elim (layout.negativeSecondValidatorDistinct forced.1)
  · exact False.elim (layout.negativeSecondValidatorDistinct forced.1)
  · exact False.elim (layout.negativeThirdValidatorDistinct forced.1)
  · exact False.elim (layout.negativeThirdValidatorDistinct forced.1)

theorem first_validator_letter
    {prime phaseCount source target firstGuess secondGuess negativePhase
      firstValidator secondValidator thirdValidator : Nat}
    {digit : Int} {state : Vec2} {letter : PhysicalTemplate}
    (primeProperty : IsPrime prime) (primeBound : 6 * phaseCount < prime)
    (layout : PhaseLayout phaseCount source firstGuess secondGuess
      negativePhase firstValidator secondValidator thirdValidator)
    (membership : InPhaseAt prime firstValidator digit state)
    (letterMem : letter ∈ alphabet source target firstGuess secondGuess
      negativePhase firstValidator secondValidator thirdValidator)
    (outputLocal : LocalAt prime (letter.act prime state)) :
    (digit = 0 ∧ letter = zeroLoop firstValidator) ∨
      (digit = 1 ∧
        letter = markerOneExit firstValidator secondValidator) := by
  have forced := force_metadata primeProperty primeBound layout
    layout.firstValidatorBound membership letterMem outputLocal
  simp [alphabet] at letterMem
  rcases letterMem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl
  · exact False.elim (layout.sourceFirstValidatorDistinct forced.1.symm)
  · exact False.elim (layout.sourceFirstValidatorDistinct forced.1.symm)
  · exact False.elim (layout.firstGuessFirstValidatorDistinct forced.1.symm)
  · exact False.elim (layout.firstGuessFirstValidatorDistinct forced.1.symm)
  · exact False.elim (layout.secondGuessFirstValidatorDistinct forced.1.symm)
  · exact False.elim (layout.secondGuessFirstValidatorDistinct forced.1.symm)
  · exact False.elim (layout.negativeFirstValidatorDistinct forced.1.symm)
  · exact False.elim (layout.negativeFirstValidatorDistinct forced.1.symm)
  · exact Or.inl ⟨forced.2, rfl⟩
  · exact Or.inr ⟨forced.2, rfl⟩
  · exact False.elim (layout.firstSecondValidatorDistinct forced.1)
  · exact False.elim (layout.firstSecondValidatorDistinct forced.1)
  · exact False.elim (layout.firstThirdValidatorDistinct forced.1)
  · exact False.elim (layout.firstThirdValidatorDistinct forced.1)

theorem second_validator_letter
    {prime phaseCount source target firstGuess secondGuess negativePhase
      firstValidator secondValidator thirdValidator : Nat}
    {digit : Int} {state : Vec2} {letter : PhysicalTemplate}
    (primeProperty : IsPrime prime) (primeBound : 6 * phaseCount < prime)
    (layout : PhaseLayout phaseCount source firstGuess secondGuess
      negativePhase firstValidator secondValidator thirdValidator)
    (membership : InPhaseAt prime secondValidator digit state)
    (letterMem : letter ∈ alphabet source target firstGuess secondGuess
      negativePhase firstValidator secondValidator thirdValidator)
    (outputLocal : LocalAt prime (letter.act prime state)) :
    (digit = 0 ∧ letter = zeroLoop secondValidator) ∨
      (digit = 1 ∧
        letter = markerOneExit secondValidator thirdValidator) := by
  have forced := force_metadata primeProperty primeBound layout
    layout.secondValidatorBound membership letterMem outputLocal
  simp [alphabet] at letterMem
  rcases letterMem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl
  · exact False.elim (layout.sourceSecondValidatorDistinct forced.1.symm)
  · exact False.elim (layout.sourceSecondValidatorDistinct forced.1.symm)
  · exact False.elim (layout.firstGuessSecondValidatorDistinct forced.1.symm)
  · exact False.elim (layout.firstGuessSecondValidatorDistinct forced.1.symm)
  · exact False.elim (layout.secondGuessSecondValidatorDistinct forced.1.symm)
  · exact False.elim (layout.secondGuessSecondValidatorDistinct forced.1.symm)
  · exact False.elim (layout.negativeSecondValidatorDistinct forced.1.symm)
  · exact False.elim (layout.negativeSecondValidatorDistinct forced.1.symm)
  · exact False.elim (layout.firstSecondValidatorDistinct forced.1.symm)
  · exact False.elim (layout.firstSecondValidatorDistinct forced.1.symm)
  · exact Or.inl ⟨forced.2, rfl⟩
  · exact Or.inr ⟨forced.2, rfl⟩
  · exact False.elim (layout.secondThirdValidatorDistinct forced.1)
  · exact False.elim (layout.secondThirdValidatorDistinct forced.1)

theorem third_validator_letter
    {prime phaseCount source target firstGuess secondGuess negativePhase
      firstValidator secondValidator thirdValidator : Nat}
    {digit : Int} {state : Vec2} {letter : PhysicalTemplate}
    (primeProperty : IsPrime prime) (primeBound : 6 * phaseCount < prime)
    (layout : PhaseLayout phaseCount source firstGuess secondGuess
      negativePhase firstValidator secondValidator thirdValidator)
    (membership : InPhaseAt prime thirdValidator digit state)
    (letterMem : letter ∈ alphabet source target firstGuess secondGuess
      negativePhase firstValidator secondValidator thirdValidator)
    (outputLocal : LocalAt prime (letter.act prime state)) :
    (digit = 0 ∧ letter = zeroLoop thirdValidator) ∨
      (digit = 1 ∧ letter = markerOneExit thirdValidator target) := by
  have forced := force_metadata primeProperty primeBound layout
    layout.thirdValidatorBound membership letterMem outputLocal
  simp [alphabet] at letterMem
  rcases letterMem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl
  · exact False.elim (layout.sourceThirdValidatorDistinct forced.1.symm)
  · exact False.elim (layout.sourceThirdValidatorDistinct forced.1.symm)
  · exact False.elim (layout.firstGuessThirdValidatorDistinct forced.1.symm)
  · exact False.elim (layout.firstGuessThirdValidatorDistinct forced.1.symm)
  · exact False.elim (layout.secondGuessThirdValidatorDistinct forced.1.symm)
  · exact False.elim (layout.secondGuessThirdValidatorDistinct forced.1.symm)
  · exact False.elim (layout.negativeThirdValidatorDistinct forced.1.symm)
  · exact False.elim (layout.negativeThirdValidatorDistinct forced.1.symm)
  · exact False.elim (layout.firstThirdValidatorDistinct forced.1.symm)
  · exact False.elim (layout.firstThirdValidatorDistinct forced.1.symm)
  · exact False.elim (layout.secondThirdValidatorDistinct forced.1.symm)
  · exact False.elim (layout.secondThirdValidatorDistinct forced.1.symm)
  · exact Or.inl ⟨forced.2, rfl⟩
  · exact Or.inr ⟨forced.2, rfl⟩

theorem candidateState_inPhaseAt
    {prime phase Q r s deleted : Nat} {digit : Int}
    (primeProperty : IsPrime prime) (QPositive : 0 < Q)
    (rPositive : 0 < r) (sPositive : 0 < s)
    (reserved : ReservedDigit digit)
    (residue : (prime : Int) ∣
      candidateNumerator prime Q r s deleted -
        digit * candidateDenominator prime Q r s) :
    InPhaseAt prime phase digit
      (phaseAffine phase (candidateState prime Q r s deleted)) := by
  apply inPhaseAt_phaseAffine_integer reserved
    (candidateDenominator_not_dvd prime Q r s primeProperty.1 QPositive
      rPositive sPositive) residue
  exact candidateState_sameLine_integer prime Q r s deleted primeProperty.1
    QPositive rPositive sPositive

theorem sEqualsQCandidateState_inPhaseAt
    {prime phase Q r deleted : Nat} {digit : Int}
    (primeProperty : IsPrime prime) (QPositive : 0 < Q)
    (rPositive : 0 < r) (reserved : ReservedDigit digit)
    (residue : (prime : Int) ∣
      sEqualsQCandidateNumerator prime Q r deleted -
        digit * candidateDenominator prime Q r Q) :
    InPhaseAt prime phase digit
      (phaseAffine phase (sEqualsQCandidateState prime Q r deleted)) := by
  apply inPhaseAt_phaseAffine_integer reserved
    (candidateDenominator_not_dvd prime Q r Q primeProperty.1 QPositive
      rPositive QPositive) residue
  exact sEqualsQCandidateState_sameLine_integer prime Q r deleted
    primeProperty.1 QPositive rPositive

theorem generalFirstOutputState_inPhaseAt
    {prime phase Q r s deleted : Nat} {digit : Int}
    (primeProperty : IsPrime prime) (QPositive : 0 < Q)
    (rPositive : 0 < r) (sPositive : 0 < s)
    (reserved : ReservedDigit digit)
    (residue : (prime : Int) ∣
      generalFirstOutputNumerator prime Q r s deleted -
        digit * candidateDenominator prime Q r s) :
    InPhaseAt prime phase digit
      (phaseAffine phase
        (generalFirstOutputState prime Q r s deleted)) := by
  apply inPhaseAt_phaseAffine_integer reserved
    (candidateDenominator_not_dvd prime Q r s primeProperty.1 QPositive
      rPositive sPositive) residue
  exact generalFirstOutputState_sameLine_integer prime Q r s deleted
    primeProperty.1 QPositive rPositive sPositive

theorem sEqualsQFirstOutputState_inPhaseAt
    {prime phase Q r deleted : Nat} {digit : Int}
    (primeProperty : IsPrime prime) (QPositive : 0 < Q)
    (rPositive : 0 < r) (reserved : ReservedDigit digit)
    (residue : (prime : Int) ∣
      sEqualsQFirstOutputNumerator prime Q r deleted -
        digit * candidateDenominator prime Q r Q) :
    InPhaseAt prime phase digit
      (phaseAffine phase
        (sEqualsQFirstOutputState prime Q r deleted)) := by
  apply inPhaseAt_phaseAffine_integer reserved
    (candidateDenominator_not_dvd prime Q r Q primeProperty.1 QPositive
      rPositive QPositive) residue
  exact sEqualsQFirstOutputState_sameLine_integer prime Q r deleted
    primeProperty.1 QPositive rPositive

theorem sEqualsTwoQSecondOutputState_inPhaseAt
    {prime phase Q r deleted : Nat} {digit : Int}
    (primeProperty : IsPrime prime) (QPositive : 0 < Q)
    (rPositive : 0 < r) (reserved : ReservedDigit digit)
    (residue : (prime : Int) ∣
      sEqualsTwoQSecondOutputNumerator prime Q r deleted -
        digit * candidateDenominator prime Q r (2 * Q)) :
    InPhaseAt prime phase digit
      (phaseAffine phase
        (sEqualsTwoQSecondOutputState prime Q r deleted)) := by
  apply inPhaseAt_phaseAffine_integer reserved
    (candidateDenominator_not_dvd prime Q r (2 * Q) primeProperty.1
      QPositive rPositive (by omega)) residue
  exact sEqualsTwoQSecondOutputState_sameLine_integer prime Q r deleted
    primeProperty.1 QPositive rPositive

theorem candidateZero_step
    (base phase Q r s deleted : Nat) (baseAtLeastTwo : 2 ≤ base)
    (QPositive : 0 < Q) (rPositive : 0 < r) (sPositive : 0 < s)
    (dQ : deleted < Q - 1) (dr : deleted < r - 1)
    (ds : deleted < s - 1) :
    SameLine
      ((zeroLoop phase).act base
        (phaseAffine phase (candidateState base Q r s deleted)))
      (phaseAffine phase (candidateState base Q r s (deleted + 1))) := by
  apply TwoProjectionModule.zeroLoop_affine_step base phase
    (candidateState base Q r s deleted)
    (candidateState base Q r s (deleted + 1)) baseAtLeastTwo
  · exact candidateState_local base Q r s deleted baseAtLeastTwo QPositive
      rPositive sPositive
  · exact candidateState_local base Q r s (deleted + 1) baseAtLeastTwo
      QPositive rPositive sPositive
  · exact candidateState_delete_zero base Q r s deleted baseAtLeastTwo
      QPositive rPositive sPositive dQ dr ds

theorem sEqualsQCandidateZero_step
    (base phase Q r deleted : Nat) (baseAtLeastTwo : 2 ≤ base)
    (QPositive : 0 < Q) (rPositive : 0 < r)
    (dTwoQ : deleted < 2 * Q - 1) (dr : deleted < r - 1) :
    SameLine
      ((zeroLoop phase).act base
        (phaseAffine phase (sEqualsQCandidateState base Q r deleted)))
      (phaseAffine phase
        (sEqualsQCandidateState base Q r (deleted + 1))) := by
  apply TwoProjectionModule.zeroLoop_affine_step base phase
    (sEqualsQCandidateState base Q r deleted)
    (sEqualsQCandidateState base Q r (deleted + 1)) baseAtLeastTwo
  · exact sEqualsQCandidateState_local base Q r deleted baseAtLeastTwo
      QPositive rPositive
  · exact sEqualsQCandidateState_local base Q r (deleted + 1)
      baseAtLeastTwo QPositive rPositive
  · exact sEqualsQCandidateState_delete_zero base Q r deleted
      baseAtLeastTwo QPositive rPositive dTwoQ dr

theorem candidateMarkerAboveQ_step
    (base source target Q r s : Nat) (baseAtLeastTwo : 2 ≤ base)
    (QPositive : 0 < Q) (QBelowS : Q < s) (sBelowR : s < r) :
    SameLine
      ((markerOneExit source target).act base
        (phaseAffine source (candidateState base Q r s (Q - 1))))
      (phaseAffine target (generalFirstOutputState base Q r s 0)) := by
  apply TwoProjectionModule.markerOneExit_affine_step base source target
    (candidateState base Q r s (Q - 1))
    (generalFirstOutputState base Q r s 0) baseAtLeastTwo
  · exact candidateState_local base Q r s (Q - 1) baseAtLeastTwo
      QPositive (by omega) (by omega)
  · exact generalFirstOutputState_local base Q r s 0 baseAtLeastTwo
      QPositive (by omega) (by omega)
  · exact candidateState_delete_marker_above_Q base Q r s baseAtLeastTwo
      QPositive QBelowS sBelowR

theorem sEqualsQCandidateMarker_step
    (base source target Q r : Nat) (baseAtLeastTwo : 2 ≤ base)
    (QPositive : 0 < Q) (twoQBelowR : 2 * Q < r)
    (rBelowThreeQ : r < 3 * Q) :
    SameLine
      ((markerOneExit source target).act base
        (phaseAffine source
          (sEqualsQCandidateState base Q r (2 * Q - 1))))
      (phaseAffine target (sEqualsQFirstOutputState base Q r 0)) := by
  apply TwoProjectionModule.markerOneExit_affine_step base source target
    (sEqualsQCandidateState base Q r (2 * Q - 1))
    (sEqualsQFirstOutputState base Q r 0) baseAtLeastTwo
  · exact sEqualsQCandidateState_local base Q r (2 * Q - 1)
      baseAtLeastTwo QPositive (by omega)
  · exact sEqualsQFirstOutputState_local base Q r 0 baseAtLeastTwo
      QPositive (by omega)
  · exact sEqualsQCandidateState_delete_marker base Q r baseAtLeastTwo
      QPositive twoQBelowR rBelowThreeQ

theorem generalFirstOutputZero_step
    (base phase Q r s deleted : Nat) (baseAtLeastTwo : 2 ≤ base)
    (QPositive : 0 < Q) (rPositive : 0 < r) (sPositive : 0 < s)
    (d1 : deleted < Q - 1) (d2 : deleted < 2 * Q - 1)
    (d3 : deleted < 3 * Q - 1) (drq : deleted < r - Q - 1)
    (dsq : deleted < s - Q - 1) (dr : deleted < r - 1)
    (ds : deleted < s - 1) :
    SameLine
      ((zeroLoop phase).act base
        (phaseAffine phase
          (generalFirstOutputState base Q r s deleted)))
      (phaseAffine phase
        (generalFirstOutputState base Q r s (deleted + 1))) := by
  apply TwoProjectionModule.zeroLoop_affine_step base phase
    (generalFirstOutputState base Q r s deleted)
    (generalFirstOutputState base Q r s (deleted + 1)) baseAtLeastTwo
  · exact generalFirstOutputState_local base Q r s deleted baseAtLeastTwo
      QPositive rPositive sPositive
  · exact generalFirstOutputState_local base Q r s (deleted + 1)
      baseAtLeastTwo QPositive rPositive sPositive
  · exact generalFirstOutputState_delete_zero base Q r s deleted
      baseAtLeastTwo QPositive rPositive sPositive d1 d2 d3 drq dsq dr ds

theorem generalFirstOutputMarkerS2_step
    (base source target Q r : Nat) (baseAtLeastTwo : 2 ≤ base)
    (QPositive : 0 < Q) (twoQBelowR : 2 * Q < r) :
    SameLine
      ((markerOneExit source target).act base
        (phaseAffine source
          (generalFirstOutputState base Q r (2 * Q) (Q - 1))))
      (phaseAffine target
        (sEqualsTwoQSecondOutputState base Q r 0)) := by
  apply TwoProjectionModule.markerOneExit_affine_step base source target
    (generalFirstOutputState base Q r (2 * Q) (Q - 1))
    (sEqualsTwoQSecondOutputState base Q r 0) baseAtLeastTwo
  · exact generalFirstOutputState_local base Q r (2 * Q) (Q - 1)
      baseAtLeastTwo QPositive (by omega) (by omega)
  · exact sEqualsTwoQSecondOutputState_local base Q r 0 baseAtLeastTwo
      QPositive (by omega)
  · exact generalFirstOutputState_delete_marker_s_eq_twoQ base Q r
      baseAtLeastTwo QPositive twoQBelowR

theorem sEqualsQFirstOutputZero_step
    (base phase Q r deleted : Nat) (baseAtLeastTwo : 2 ≤ base)
    (QPositive : 0 < Q) (rPositive : 0 < r)
    (d1 : deleted < Q - 1) (d2 : deleted < 2 * Q - 1)
    (d3 : deleted < 3 * Q - 1) (dr2 : deleted < r - 2 * Q - 1)
    (dr : deleted < r - 1) :
    SameLine
      ((zeroLoop phase).act base
        (phaseAffine phase
          (sEqualsQFirstOutputState base Q r deleted)))
      (phaseAffine phase
        (sEqualsQFirstOutputState base Q r (deleted + 1))) := by
  apply TwoProjectionModule.zeroLoop_affine_step base phase
    (sEqualsQFirstOutputState base Q r deleted)
    (sEqualsQFirstOutputState base Q r (deleted + 1)) baseAtLeastTwo
  · exact sEqualsQFirstOutputState_local base Q r deleted baseAtLeastTwo
      QPositive rPositive
  · exact sEqualsQFirstOutputState_local base Q r (deleted + 1)
      baseAtLeastTwo QPositive rPositive
  · exact sEqualsQFirstOutputState_delete_zero base Q r deleted
      baseAtLeastTwo QPositive rPositive d1 d2 d3 dr2 dr

theorem sEqualsTwoQSecondOutputZero_step
    (base phase Q r deleted : Nat) (baseAtLeastTwo : 2 ≤ base)
    (QPositive : 0 < Q) (rPositive : 0 < r)
    (d1 : deleted < Q - 1) (d2 : deleted < 2 * Q - 1)
    (d3 : deleted < 3 * Q - 1) (dr2 : deleted < r - 2 * Q - 1)
    (drq : deleted < r - Q - 1) (dr : deleted < r - 1) :
    SameLine
      ((zeroLoop phase).act base
        (phaseAffine phase
          (sEqualsTwoQSecondOutputState base Q r deleted)))
      (phaseAffine phase
        (sEqualsTwoQSecondOutputState base Q r (deleted + 1))) := by
  apply TwoProjectionModule.zeroLoop_affine_step base phase
    (sEqualsTwoQSecondOutputState base Q r deleted)
    (sEqualsTwoQSecondOutputState base Q r (deleted + 1)) baseAtLeastTwo
  · exact sEqualsTwoQSecondOutputState_local base Q r deleted
      baseAtLeastTwo QPositive rPositive
  · exact sEqualsTwoQSecondOutputState_local base Q r (deleted + 1)
      baseAtLeastTwo QPositive rPositive
  · exact sEqualsTwoQSecondOutputState_delete_zero base Q r deleted
      baseAtLeastTwo QPositive rPositive d1 d2 d3 dr2 drq dr

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

theorem sourceTail_forced_prefix_to_endpoint
    {prime phaseCount source target firstGuess secondGuess negativePhase
      firstValidator secondValidator thirdValidator endpointPhase : Nat}
    {endpointDigit : Int} {endpoint : Vec2}
    (primeProperty : IsPrime prime) (primeBound : 6 * phaseCount < prime)
    (layout : PhaseLayout phaseCount source firstGuess secondGuess
      negativePhase firstValidator secondValidator thirdValidator)
    (endpointBound : endpointPhase < phaseCount)
    (sourceEndpointDistinct : source ≠ endpointPhase)
    (endpointMembership : InPhaseAt prime endpointPhase endpointDigit endpoint)
    {first deleted remaining : Nat} (sumEq : deleted + remaining = first)
    {word : List PhysicalTemplate}
    (wordOver : WordOver
      (alphabet source target firstGuess secondGuess negativePhase
        firstValidator secondValidator thirdValidator) word)
    (allLocal : AllStatesLocal prime word
      (phaseAffine source (sourceScanState prime first deleted)))
    (completeRun : SameLine
      (physicalWordAction prime word
        (phaseAffine source (sourceScanState prime first deleted))) endpoint) :
    ∃ suffix,
      word = List.replicate remaining (zeroLoop source) ++
          [markerOneExit source firstGuess] ++ suffix ∧
      WordOver
        (alphabet source target firstGuess secondGuess negativePhase
          firstValidator secondValidator thirdValidator) suffix ∧
      AllStatesLocal prime suffix
        (phaseAffine firstGuess (threeProjectionFirstState prime first)) ∧
      SameLine
        (physicalWordAction prime suffix
          (phaseAffine firstGuess (threeProjectionFirstState prime first)))
        endpoint := by
  have nextLocal' : LocalAt prime
      (phaseAffine firstGuess (threeProjectionFirstState prime first)) := by
    apply TwoProjectionModule.phase_local (phase := firstGuess)
    rw [← firstScan_rotated prime first primeProperty.1]
    exact periodicCode_local_affine prime
      (List.replicate (3 * first + 2) 0 ++ [-1] ++
        List.replicate first 0 ++ [1]) primeProperty.1 (by simp)
  have parsed := forcedScanPrefixToEndpoint
    (Certificate := True) (primeProperty := primeProperty)
    (primeBound := primeBound) (currentBound := layout.sourceBound)
    (endpointBound := endpointBound) (phaseDistinct := sourceEndpointDistinct)
    (endpointMembership := endpointMembership)
    (beforeMembership := fun position positionBelow =>
      MutatingScan.zeroState_inPhaseAt_before prime source first 1
        (List.replicate (3 * first + 2) 0 ++ [-1]) position
        primeProperty.1 positionBelow)
    (markerMembership := MutatingScan.zeroState_inPhaseAt_marker prime source
      first 1 (List.replicate (3 * first + 2) 0 ++ [-1]) primeProperty.1
      (by simp [ReservedDigit]))
    (stateLocal := fun position _ =>
      MutatingScan.phaseZeroState_local prime source first 1
        (List.replicate (3 * first + 2) 0 ++ [-1]) position
        primeProperty.1)
    (nextLocal := nextLocal')
    (forceLoop := fun position positionBelow {letter} letterMem outputLocal =>
      by
        rcases source_letter primeProperty primeBound layout
            (MutatingScan.zeroState_inPhaseAt_before prime source first 1
              (List.replicate (3 * first + 2) 0 ++ [-1]) position
              primeProperty.1 positionBelow) letterMem outputLocal with
          ⟨_, letterEq⟩ | ⟨digitEq, _⟩
        · exact letterEq
        · omega)
    (forceExit := fun {letter} letterMem outputLocal => by
      rcases source_letter primeProperty primeBound layout
          (MutatingScan.zeroState_inPhaseAt_marker prime source first 1
            (List.replicate (3 * first + 2) 0 ++ [-1]) primeProperty.1
            (by simp [ReservedDigit])) letterMem outputLocal with
        ⟨digitEq, _⟩ | ⟨_, letterEq⟩
      · omega
      · exact ⟨True.intro, letterEq⟩)
    (loopStep := fun position positionBelow =>
      sourceZero_step prime source first position primeProperty.1
        positionBelow)
    (exitStep := fun _ => sourceMarker_step prime source firstGuess first
      primeProperty.1)
    sumEq wordOver allLocal completeRun
  rcases parsed with ⟨suffix, _, wordEq, suffixOver, suffixLocal, suffixRun⟩
  exact ⟨suffix, wordEq, suffixOver, suffixLocal, suffixRun⟩

theorem firstGuess_marker_rejects
    {prime phaseCount source target firstGuess secondGuess negativePhase
      firstValidator secondValidator thirdValidator first : Nat}
    (primeProperty : IsPrime prime) (primeBound : 6 * phaseCount < prime)
    (layout : PhaseLayout phaseCount source firstGuess secondGuess
      negativePhase firstValidator secondValidator thirdValidator)
    {letter : PhysicalTemplate}
    (letterMem : letter ∈ alphabet source target firstGuess secondGuess
      negativePhase firstValidator secondValidator thirdValidator) :
    ¬LocalAt prime
      (letter.act prime
        (phaseAffine firstGuess
          (firstGuessState prime first (3 * first + 2)))) := by
  intro outputLocal
  have membership : InPhaseAt prime firstGuess (-1)
      (phaseAffine firstGuess
        (firstGuessState prime first (3 * first + 2))) := by
    unfold firstGuessState
    exact MutatingScan.zeroState_inPhaseAt_marker prime firstGuess
      (3 * first + 2) (-1) (List.replicate first 0 ++ [1])
      primeProperty.1 (by simp [ReservedDigit])
  have classified := first_guess_letter primeProperty primeBound layout
    membership letterMem outputLocal
  omega

theorem firstGuessTail_forced_exit_to_endpoint
    {prime phaseCount source target firstGuess secondGuess negativePhase
      firstValidator secondValidator thirdValidator endpointPhase : Nat}
    {endpointDigit : Int} {endpoint : Vec2}
    (primeProperty : IsPrime prime) (primeBound : 6 * phaseCount < prime)
    (layout : PhaseLayout phaseCount source firstGuess secondGuess
      negativePhase firstValidator secondValidator thirdValidator)
    (endpointBound : endpointPhase < phaseCount)
    (guessEndpointDistinct : firstGuess ≠ endpointPhase)
    (endpointMembership : InPhaseAt prime endpointPhase endpointDigit endpoint)
    {first deleted remaining : Nat}
    (sumEq : deleted + remaining = 3 * first + 2)
    {word : List PhysicalTemplate}
    (wordOver : WordOver
      (alphabet source target firstGuess secondGuess negativePhase
        firstValidator secondValidator thirdValidator) word)
    (allLocal : AllStatesLocal prime word
      (phaseAffine firstGuess (firstGuessState prime first deleted)))
    (completeRun : SameLine
      (physicalWordAction prime word
        (phaseAffine firstGuess (firstGuessState prime first deleted)))
      endpoint) :
    ∃ guess suffix,
      deleted < guess ∧ guess ≤ 3 * first + 2 ∧
      word = List.replicate (guess - deleted - 1) (zeroLoop firstGuess) ++
          [inverseTZeroExit firstGuess secondGuess] ++ suffix ∧
      WordOver
        (alphabet source target firstGuess secondGuess negativePhase
          firstValidator secondValidator thirdValidator) suffix ∧
      AllStatesLocal prime suffix
        (phaseAffine secondGuess
          (secondGuessState prime (first + 1)
            (3 * (first + 1) - guess) 0)) ∧
      SameLine
        (physicalWordAction prime suffix
          (phaseAffine secondGuess
            (secondGuessState prime (first + 1)
              (3 * (first + 1) - guess) 0))) endpoint := by
  induction remaining generalizing deleted word with
  | zero =>
      have deletedEq : deleted = 3 * first + 2 := by omega
      have membership : InPhaseAt prime firstGuess (-1)
          (phaseAffine firstGuess (firstGuessState prime first deleted)) := by
        rw [deletedEq]
        unfold firstGuessState
        exact MutatingScan.zeroState_inPhaseAt_marker prime firstGuess
          (3 * first + 2) (-1) (List.replicate first 0 ++ [1])
          primeProperty.1 (by simp [ReservedDigit])
      have wordNonempty := word_nonempty_of_endpoint_phase_ne primeProperty
        primeBound layout.firstGuessBound endpointBound guessEndpointDistinct
        membership endpointMembership completeRun
      cases word with
      | nil => exact False.elim (wordNonempty rfl)
      | cons letter tail =>
          have letterMem := wordOver letter (by simp)
          exact False.elim (firstGuess_marker_rejects primeProperty primeBound
            layout letterMem (by simpa only [deletedEq] using
              allLocal.2.start))
  | succ remaining inductionHypothesis =>
      have deletedBelow : deleted < 3 * first + 2 := by omega
      have membership : InPhaseAt prime firstGuess 0
          (phaseAffine firstGuess (firstGuessState prime first deleted)) := by
        unfold firstGuessState
        exact MutatingScan.zeroState_inPhaseAt_before prime firstGuess
          (3 * first + 2) (-1) (List.replicate first 0 ++ [1]) deleted
          primeProperty.1 deletedBelow
      have wordNonempty := word_nonempty_of_endpoint_phase_ne primeProperty
        primeBound layout.firstGuessBound endpointBound guessEndpointDistinct
        membership endpointMembership completeRun
      cases word with
      | nil => exact False.elim (wordNonempty rfl)
      | cons letter tail =>
          have letterMem := wordOver letter (by simp)
          have tailOver : WordOver
              (alphabet source target firstGuess secondGuess negativePhase
                firstValidator secondValidator thirdValidator) tail := by
            intro candidate candidateMem
            exact wordOver candidate (by simp [candidateMem])
          obtain ⟨_, letterEq | letterEq⟩ := first_guess_letter
            primeProperty primeBound layout membership letterMem
              allLocal.2.start
          · subst letter
            have firstStep := firstGuessZero_step prime firstGuess first
              deleted primeProperty.1 deletedBelow
            have nextLocal := MutatingScan.phaseZeroState_local prime
              firstGuess (3 * first + 2) (-1)
              (List.replicate first 0 ++ [1]) (deleted + 1)
              primeProperty.1
            have tailLocal : AllStatesLocal prime tail
                (phaseAffine firstGuess
                  (firstGuessState prime first (deleted + 1))) := by
              apply AllStatesLocal.of_sameLine
                (primePositive := by have := primeProperty.1; omega)
                allLocal.2 nextLocal.1
              simpa [firstGuessState] using firstStep.symm
            have tailRun : SameLine
                (physicalWordAction prime tail
                  (phaseAffine firstGuess
                    (firstGuessState prime first (deleted + 1)))) endpoint := by
              apply physicalWordAction_tail_sameLine prime
                (zeroLoop firstGuess) tail (completeRun := completeRun)
              exact firstStep
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
            let Q := first + 1
            let r := 3 * Q - guess
            have guessBound : guess ≤ 3 * first + 2 := by
              unfold guess; omega
            have rPositive : 0 < r := by unfold r Q guess; omega
            have firstStep := firstGuessExit_step prime firstGuess
              secondGuess first deleted primeProperty.1 deletedBelow
            dsimp at firstStep
            have rEq : 3 * (first + 1) - (deleted + 1) = r := by
              unfold r Q guess
              rfl
            rw [rEq] at firstStep
            have rawLocal := powerZeroState_local prime r 0
              (firstGuessDenominator prime Q r)
              (firstGuessDenominator_not_dvd prime Q r primeProperty.1
                (by unfold Q; omega) rPositive)
            have nextLocal := TwoProjectionModule.phase_local
              (phase := secondGuess) rawLocal
            have tailLocal : AllStatesLocal prime tail
                (phaseAffine secondGuess (secondGuessState prime Q r 0)) := by
              apply AllStatesLocal.of_sameLine
                (primePositive := by have := primeProperty.1; omega)
                allLocal.2 nextLocal.1 firstStep.symm
            have tailRun : SameLine
                (physicalWordAction prime tail
                  (phaseAffine secondGuess (secondGuessState prime Q r 0)))
                endpoint := by
              apply physicalWordAction_tail_sameLine prime
                (inverseTZeroExit firstGuess secondGuess) tail
                (completeRun := completeRun)
              exact firstStep
            exact ⟨guess, tail, by unfold guess; omega, guessBound,
              by simp [guess], tailOver, by simpa [Q, r] using tailLocal,
              by simpa [Q, r] using tailRun⟩

theorem secondGuess_marker_rejects
    {prime phaseCount source target firstGuess secondGuess negativePhase
      firstValidator secondValidator thirdValidator Q r : Nat}
    (primeProperty : IsPrime prime) (primeBound : 6 * phaseCount < prime)
    (layout : PhaseLayout phaseCount source firstGuess secondGuess
      negativePhase firstValidator secondValidator thirdValidator)
    (QPositive : 0 < Q) (rPositive : 0 < r)
    {letter : PhysicalTemplate}
    (letterMem : letter ∈ alphabet source target firstGuess secondGuess
      negativePhase firstValidator secondValidator thirdValidator) :
    ¬LocalAt prime
      (letter.act prime
        (phaseAffine secondGuess
          (secondGuessState prime Q r (r - 1)))) := by
  intro outputLocal
  have denominatorNotDivisible := firstGuessDenominator_not_dvd prime Q r
    primeProperty.1 QPositive rPositive
  have membership : InPhaseAt prime secondGuess (-1)
      (phaseAffine secondGuess
        (secondGuessState prime Q r (r - 1))) := by
    exact powerZeroState_inPhaseAt_marker denominatorNotDivisible
      (firstGuessDenominator_one_residue prime Q r QPositive rPositive)
  have classified := second_guess_letter primeProperty primeBound layout
    membership letterMem outputLocal
  omega

theorem secondGuessTail_forced_exit_to_endpoint
    {prime phaseCount source target firstGuess secondGuess negativePhase
      firstValidator secondValidator thirdValidator endpointPhase Q r : Nat}
    {endpointDigit : Int} {endpoint : Vec2}
    (primeProperty : IsPrime prime) (primeBound : 6 * phaseCount < prime)
    (layout : PhaseLayout phaseCount source firstGuess secondGuess
      negativePhase firstValidator secondValidator thirdValidator)
    (endpointBound : endpointPhase < phaseCount)
    (guessEndpointDistinct : secondGuess ≠ endpointPhase)
    (endpointMembership : InPhaseAt prime endpointPhase endpointDigit endpoint)
    (QPositive : 0 < Q) (rPositive : 0 < r)
    (rBelowThreeQ : r < 3 * Q)
    {deleted remaining : Nat} (sumEq : deleted + remaining = r - 1)
    {word : List PhysicalTemplate}
    (wordOver : WordOver
      (alphabet source target firstGuess secondGuess negativePhase
        firstValidator secondValidator thirdValidator) word)
    (allLocal : AllStatesLocal prime word
      (phaseAffine secondGuess (secondGuessState prime Q r deleted)))
    (completeRun : SameLine
      (physicalWordAction prime word
        (phaseAffine secondGuess (secondGuessState prime Q r deleted)))
      endpoint) :
    ∃ s suffix,
      0 < s ∧ s < r ∧ deleted < r - s ∧
      word = List.replicate (r - s - deleted - 1) (zeroLoop secondGuess) ++
          [inverseTZeroExit secondGuess negativePhase] ++ suffix ∧
      WordOver
        (alphabet source target firstGuess secondGuess negativePhase
          firstValidator secondValidator thirdValidator) suffix ∧
      AllStatesLocal prime suffix
        (phaseAffine negativePhase (negativeState prime Q r s 0)) ∧
      SameLine
        (physicalWordAction prime suffix
          (phaseAffine negativePhase (negativeState prime Q r s 0)))
        endpoint := by
  have denominatorNotDivisible := firstGuessDenominator_not_dvd prime Q r
    primeProperty.1 QPositive rPositive
  induction remaining generalizing deleted word with
  | zero =>
      have deletedEq : deleted = r - 1 := by omega
      have membership : InPhaseAt prime secondGuess (-1)
          (phaseAffine secondGuess
            (secondGuessState prime Q r deleted)) := by
        rw [deletedEq]
        exact powerZeroState_inPhaseAt_marker denominatorNotDivisible
          (firstGuessDenominator_one_residue prime Q r QPositive rPositive)
      have wordNonempty := word_nonempty_of_endpoint_phase_ne primeProperty
        primeBound layout.secondGuessBound endpointBound guessEndpointDistinct
        membership endpointMembership completeRun
      cases word with
      | nil => exact False.elim (wordNonempty rfl)
      | cons letter tail =>
          have letterMem := wordOver letter (by simp)
          exact False.elim (secondGuess_marker_rejects primeProperty
            primeBound layout QPositive rPositive letterMem (by
              simpa only [deletedEq] using allLocal.2.start))
  | succ remaining inductionHypothesis =>
      have deletedBelow : deleted < r - 1 := by omega
      have membership : InPhaseAt prime secondGuess 0
          (phaseAffine secondGuess
            (secondGuessState prime Q r deleted)) :=
        powerZeroState_inPhaseAt_before denominatorNotDivisible deletedBelow
      have wordNonempty := word_nonempty_of_endpoint_phase_ne primeProperty
        primeBound layout.secondGuessBound endpointBound guessEndpointDistinct
        membership endpointMembership completeRun
      cases word with
      | nil => exact False.elim (wordNonempty rfl)
      | cons letter tail =>
          have letterMem := wordOver letter (by simp)
          have tailOver : WordOver
              (alphabet source target firstGuess secondGuess negativePhase
                firstValidator secondValidator thirdValidator) tail := by
            intro candidate candidateMem
            exact wordOver candidate (by simp [candidateMem])
          obtain ⟨_, letterEq | letterEq⟩ := second_guess_letter
            primeProperty primeBound layout membership letterMem
              allLocal.2.start
          · subst letter
            have firstStep := secondGuessZero_step prime secondGuess Q r
              deleted primeProperty.1 QPositive rPositive deletedBelow
            have rawNextLocal := powerZeroState_local prime r (deleted + 1)
              (firstGuessDenominator prime Q r) denominatorNotDivisible
            have nextLocal := TwoProjectionModule.phase_local
              (phase := secondGuess) rawNextLocal
            have tailLocal : AllStatesLocal prime tail
                (phaseAffine secondGuess
                  (secondGuessState prime Q r (deleted + 1))) := by
              apply AllStatesLocal.of_sameLine
                (primePositive := by have := primeProperty.1; omega)
                allLocal.2 nextLocal.1 firstStep.symm
            have tailRun : SameLine
                (physicalWordAction prime tail
                  (phaseAffine secondGuess
                    (secondGuessState prime Q r (deleted + 1)))) endpoint := by
              apply physicalWordAction_tail_sameLine prime
                (zeroLoop secondGuess) tail (completeRun := completeRun)
              exact firstStep
            obtain ⟨s, suffix, sPositive, sBelowR, deletedBelowExit,
                tailEq, suffixOver, suffixLocal, suffixRun⟩ :=
              inductionHypothesis (deleted := deleted + 1) (by omega)
                tailOver tailLocal tailRun
            refine ⟨s, suffix, sPositive, sBelowR, by omega, ?_,
              suffixOver, suffixLocal, suffixRun⟩
            rw [tailEq]
            have countEq : r - s - deleted - 1 =
                (r - s - (deleted + 1) - 1) + 1 := by omega
            rw [countEq, List.replicate_succ]
            simp
          · subst letter
            let s := r - (deleted + 1)
            have sPositive : 0 < s := by unfold s; omega
            have sBelowR : s < r := by unfold s; omega
            have firstStep := secondGuessExit_step prime secondGuess
              negativePhase Q r deleted primeProperty.1 QPositive rPositive
              rBelowThreeQ deletedBelow
            dsimp at firstStep
            have sEq : r - (deleted + 1) = s := by rfl
            rw [sEq] at firstStep
            have rawNextLocal := powerZeroState_local prime s 0
              (secondGuessDenominator prime Q r s)
              (secondGuessDenominator_not_dvd prime Q r s primeProperty.1
                QPositive rPositive sPositive)
            have nextLocal := TwoProjectionModule.phase_local
              (phase := negativePhase) rawNextLocal
            have tailLocal : AllStatesLocal prime tail
                (phaseAffine negativePhase (negativeState prime Q r s 0)) := by
              apply AllStatesLocal.of_sameLine
                (primePositive := by have := primeProperty.1; omega)
                allLocal.2 nextLocal.1 firstStep.symm
            have tailRun : SameLine
                (physicalWordAction prime tail
                  (phaseAffine negativePhase
                    (negativeState prime Q r s 0))) endpoint := by
              apply physicalWordAction_tail_sameLine prime
                (inverseTZeroExit secondGuess negativePhase) tail
                (completeRun := completeRun)
              exact firstStep
            refine ⟨s, tail, sPositive, sBelowR, by unfold s; omega, ?_,
              tailOver, tailLocal, tailRun⟩
            have countZero : r - s - deleted - 1 = 0 := by unfold s; omega
            rw [countZero]
            simp

theorem negativeTail_forced_prefix_to_endpoint
    {prime phaseCount source target firstGuess secondGuess negativePhase
      firstValidator secondValidator thirdValidator endpointPhase Q r s : Nat}
    {endpointDigit : Int} {endpoint : Vec2}
    (primeProperty : IsPrime prime) (primeBound : 6 * phaseCount < prime)
    (layout : PhaseLayout phaseCount source firstGuess secondGuess
      negativePhase firstValidator secondValidator thirdValidator)
    (endpointBound : endpointPhase < phaseCount)
    (negativeEndpointDistinct : negativePhase ≠ endpointPhase)
    (endpointMembership : InPhaseAt prime endpointPhase endpointDigit endpoint)
    (QPositive : 0 < Q) (sPositive : 0 < s)
    (sBelowR : s < r) (rBelowThreeQ : r < 3 * Q)
    {deleted remaining : Nat} (sumEq : deleted + remaining = s - 1)
    {word : List PhysicalTemplate}
    (wordOver : WordOver
      (alphabet source target firstGuess secondGuess negativePhase
        firstValidator secondValidator thirdValidator) word)
    (allLocal : AllStatesLocal prime word
      (phaseAffine negativePhase (negativeState prime Q r s deleted)))
    (completeRun : SameLine
      (physicalWordAction prime word
        (phaseAffine negativePhase (negativeState prime Q r s deleted)))
      endpoint) :
    ∃ suffix,
      word = List.replicate remaining (zeroLoop negativePhase) ++
          [inverseFNegativeExit negativePhase firstValidator] ++ suffix ∧
      WordOver
        (alphabet source target firstGuess secondGuess negativePhase
          firstValidator secondValidator thirdValidator) suffix ∧
      AllStatesLocal prime suffix
        (phaseAffine firstValidator (candidateState prime Q r s 0)) ∧
      SameLine
        (physicalWordAction prime suffix
          (phaseAffine firstValidator (candidateState prime Q r s 0)))
        endpoint := by
  have rPositive : 0 < r := by omega
  have denominatorNotDivisible := secondGuessDenominator_not_dvd prime Q r s
    primeProperty.1 QPositive rPositive sPositive
  have parsed := forcedScanPrefixToEndpoint
    (Certificate := True) (primeProperty := primeProperty)
    (primeBound := primeBound) (currentBound := layout.negativeBound)
    (endpointBound := endpointBound)
    (phaseDistinct := negativeEndpointDistinct)
    (endpointMembership := endpointMembership)
    (beforeMembership := fun position positionBelow =>
      powerZeroState_inPhaseAt_before denominatorNotDivisible positionBelow)
    (markerMembership := powerZeroState_inPhaseAt_marker
      denominatorNotDivisible
      (secondGuessDenominator_one_residue prime Q r s QPositive rPositive
        sPositive))
    (stateLocal := fun position _ =>
      TwoProjectionModule.phase_local (phase := negativePhase)
        (powerZeroState_local prime s position
          (secondGuessDenominator prime Q r s) denominatorNotDivisible))
    (nextLocal := TwoProjectionModule.phase_local (phase := firstValidator)
      (candidateState_local prime Q r s 0 primeProperty.1 QPositive
        rPositive sPositive))
    (forceLoop := fun position positionBelow {letter} letterMem outputLocal =>
      by
        rcases negative_letter primeProperty primeBound layout
            (powerZeroState_inPhaseAt_before denominatorNotDivisible
              positionBelow) letterMem outputLocal with
          ⟨_, letterEq⟩ | ⟨digitEq, _⟩
        · exact letterEq
        · omega)
    (forceExit := fun {letter} letterMem outputLocal => by
      rcases negative_letter primeProperty primeBound layout
          (powerZeroState_inPhaseAt_marker denominatorNotDivisible
            (secondGuessDenominator_one_residue prime Q r s QPositive
              rPositive sPositive)) letterMem outputLocal with
        ⟨digitEq, _⟩ | ⟨_, letterEq⟩
      · omega
      · exact ⟨True.intro, letterEq⟩)
    (loopStep := fun position positionBelow =>
      negativeZero_step prime negativePhase Q r s position primeProperty.1
        QPositive rPositive sPositive positionBelow)
    (exitStep := fun _ => negativeMarker_step prime negativePhase
      firstValidator Q r s primeProperty.1 QPositive sPositive sBelowR
      rBelowThreeQ)
    sumEq wordOver allLocal completeRun
  rcases parsed with ⟨suffix, _, wordEq, suffixOver, suffixLocal, suffixRun⟩
  exact ⟨suffix, wordEq, suffixOver, suffixLocal, suffixRun⟩

theorem first_validator_rejects_forbidden
    {prime phaseCount source target firstGuess secondGuess negativePhase
      firstValidator secondValidator thirdValidator : Nat}
    {digit : Int} {state : Vec2}
    (primeProperty : IsPrime prime) (primeBound : 6 * phaseCount < prime)
    (layout : PhaseLayout phaseCount source firstGuess secondGuess
      negativePhase firstValidator secondValidator thirdValidator)
    (digitNeZero : digit ≠ 0) (digitNeOne : digit ≠ 1)
    (membership : InPhaseAt prime firstValidator digit state)
    {letter : PhysicalTemplate}
    (letterMem : letter ∈ alphabet source target firstGuess secondGuess
      negativePhase firstValidator secondValidator thirdValidator) :
    ¬LocalAt prime (letter.act prime state) := by
  intro outputLocal
  rcases first_validator_letter primeProperty primeBound layout membership
      letterMem outputLocal with ⟨digitZero, _⟩ | ⟨digitOne, _⟩
  · exact digitNeZero digitZero
  · exact digitNeOne digitOne

theorem second_validator_rejects_forbidden
    {prime phaseCount source target firstGuess secondGuess negativePhase
      firstValidator secondValidator thirdValidator : Nat}
    {digit : Int} {state : Vec2}
    (primeProperty : IsPrime prime) (primeBound : 6 * phaseCount < prime)
    (layout : PhaseLayout phaseCount source firstGuess secondGuess
      negativePhase firstValidator secondValidator thirdValidator)
    (digitNeZero : digit ≠ 0) (digitNeOne : digit ≠ 1)
    (membership : InPhaseAt prime secondValidator digit state)
    {letter : PhysicalTemplate}
    (letterMem : letter ∈ alphabet source target firstGuess secondGuess
      negativePhase firstValidator secondValidator thirdValidator) :
    ¬LocalAt prime (letter.act prime state) := by
  intro outputLocal
  rcases second_validator_letter primeProperty primeBound layout membership
      letterMem outputLocal with ⟨digitZero, _⟩ | ⟨digitOne, _⟩
  · exact digitNeZero digitZero
  · exact digitNeOne digitOne

theorem third_validator_rejects_forbidden
    {prime phaseCount source target firstGuess secondGuess negativePhase
      firstValidator secondValidator thirdValidator : Nat}
    {digit : Int} {state : Vec2}
    (primeProperty : IsPrime prime) (primeBound : 6 * phaseCount < prime)
    (layout : PhaseLayout phaseCount source firstGuess secondGuess
      negativePhase firstValidator secondValidator thirdValidator)
    (digitNeZero : digit ≠ 0) (digitNeOne : digit ≠ 1)
    (membership : InPhaseAt prime thirdValidator digit state)
    {letter : PhysicalTemplate}
    (letterMem : letter ∈ alphabet source target firstGuess secondGuess
      negativePhase firstValidator secondValidator thirdValidator) :
    ¬LocalAt prime (letter.act prime state) := by
  intro outputLocal
  rcases third_validator_letter primeProperty primeBound layout membership
      letterMem outputLocal with ⟨digitZero, _⟩ | ⟨digitOne, _⟩
  · exact digitNeZero digitZero
  · exact digitNeOne digitOne

theorem candidateBelowQ_rejects_to_endpoint
    {prime phaseCount source target firstGuess secondGuess negativePhase
      firstValidator secondValidator thirdValidator endpointPhase Q r s : Nat}
    {endpointDigit : Int} {endpoint : Vec2}
    (primeProperty : IsPrime prime) (primeBound : 6 * phaseCount < prime)
    (layout : PhaseLayout phaseCount source firstGuess secondGuess
      negativePhase firstValidator secondValidator thirdValidator)
    (endpointBound : endpointPhase < phaseCount)
    (validatorEndpointDistinct : firstValidator ≠ endpointPhase)
    (endpointMembership : InPhaseAt prime endpointPhase endpointDigit endpoint)
    (QPositive : 0 < Q) (sPositive : 0 < s)
    (sBelowQ : s < Q) (sBelowR : s < r)
    {deleted remaining : Nat} (sumEq : deleted + remaining = s - 1)
    {word : List PhysicalTemplate}
    (wordOver : WordOver
      (alphabet source target firstGuess secondGuess negativePhase
        firstValidator secondValidator thirdValidator) word)
    (allLocal : AllStatesLocal prime word
      (phaseAffine firstValidator (candidateState prime Q r s deleted)))
    (completeRun : SameLine
      (physicalWordAction prime word
        (phaseAffine firstValidator (candidateState prime Q r s deleted)))
      endpoint) :
    False := by
  have rPositive : 0 < r := by omega
  apply forcedScanRejectsAtMarker
    (markerDigit := -1) (limit := s - 1)
    (state := fun position =>
      phaseAffine firstValidator (candidateState prime Q r s position))
    (loopLetter := zeroLoop firstValidator)
    (primeProperty := primeProperty) (primeBound := primeBound)
    (currentBound := layout.firstValidatorBound)
    (endpointBound := endpointBound)
    (phaseDistinct := validatorEndpointDistinct)
    (endpointMembership := endpointMembership)
    (beforeMembership := fun position positionBelow =>
      candidateState_inPhaseAt (digit := 0) primeProperty QPositive
        rPositive sPositive
        (by simp [ReservedDigit]) (by
          simpa only [Int.zero_mul, Int.sub_zero] using
            candidate_zero_residue prime Q r s position (by omega)
              (by omega) positionBelow))
    (markerMembership := candidateState_inPhaseAt (digit := -1)
      primeProperty QPositive rPositive sPositive (by simp [ReservedDigit])
      (first_marker_s_below_Q prime Q r s QPositive sPositive sBelowQ
        sBelowR))
    (stateLocal := fun position _ =>
      TwoProjectionModule.phase_local (phase := firstValidator)
        (candidateState_local prime Q r s position primeProperty.1 QPositive
          rPositive sPositive))
    (forceLoop := fun position positionBelow {letter} letterMem outputLocal =>
      by
        rcases first_validator_letter primeProperty primeBound layout
            (candidateState_inPhaseAt (digit := 0) primeProperty QPositive
              rPositive sPositive (by simp [ReservedDigit]) (by
                simpa only [Int.zero_mul, Int.sub_zero] using
                  candidate_zero_residue prime Q r s position (by omega)
                    (by omega) positionBelow)) letterMem outputLocal with
          ⟨_, letterEq⟩ | ⟨digitEq, _⟩
        · exact letterEq
        · omega)
    (rejectMarker := fun {letter} letterMem =>
      first_validator_rejects_forbidden primeProperty primeBound layout
        (by omega) (by omega)
        (candidateState_inPhaseAt (digit := -1) primeProperty QPositive
          rPositive sPositive (by simp [ReservedDigit])
          (first_marker_s_below_Q prime Q r s QPositive sPositive sBelowQ
            sBelowR)) letterMem)
    (loopStep := fun position positionBelow =>
      candidateZero_step prime firstValidator Q r s position primeProperty.1
        QPositive rPositive sPositive (by omega) (by omega) positionBelow)
    sumEq wordOver allLocal completeRun

theorem candidateSEqQBelowTwoQ_rejects_to_endpoint
    {prime phaseCount source target firstGuess secondGuess negativePhase
      firstValidator secondValidator thirdValidator endpointPhase Q r : Nat}
    {endpointDigit : Int} {endpoint : Vec2}
    (primeProperty : IsPrime prime) (primeBound : 6 * phaseCount < prime)
    (layout : PhaseLayout phaseCount source firstGuess secondGuess
      negativePhase firstValidator secondValidator thirdValidator)
    (endpointBound : endpointPhase < phaseCount)
    (validatorEndpointDistinct : firstValidator ≠ endpointPhase)
    (endpointMembership : InPhaseAt prime endpointPhase endpointDigit endpoint)
    (QPositive : 0 < Q) (QBelowR : Q < r) (rBelowTwoQ : r < 2 * Q)
    {deleted remaining : Nat} (sumEq : deleted + remaining = r - 1)
    {word : List PhysicalTemplate}
    (wordOver : WordOver
      (alphabet source target firstGuess secondGuess negativePhase
        firstValidator secondValidator thirdValidator) word)
    (allLocal : AllStatesLocal prime word
      (phaseAffine firstValidator
        (sEqualsQCandidateState prime Q r deleted)))
    (completeRun : SameLine
      (physicalWordAction prime word
        (phaseAffine firstValidator
          (sEqualsQCandidateState prime Q r deleted))) endpoint) :
    False := by
  apply forcedScanRejectsAtMarker
    (markerDigit := -1) (limit := r - 1)
    (state := fun position =>
      phaseAffine firstValidator (sEqualsQCandidateState prime Q r position))
    (loopLetter := zeroLoop firstValidator)
    (primeProperty := primeProperty) (primeBound := primeBound)
    (currentBound := layout.firstValidatorBound)
    (endpointBound := endpointBound)
    (phaseDistinct := validatorEndpointDistinct)
    (endpointMembership := endpointMembership)
    (beforeMembership := fun position positionBelow =>
      sEqualsQCandidateState_inPhaseAt (digit := 0) primeProperty QPositive
        (by omega)
        (by simp [ReservedDigit]) (by
          simpa only [Int.zero_mul, Int.sub_zero] using
            sEqualsQCandidate_zero_residue prime Q r position (by omega)
              positionBelow))
    (markerMembership := sEqualsQCandidateState_inPhaseAt (digit := -1)
      primeProperty QPositive (by omega) (by simp [ReservedDigit]) (by
        have residue := first_marker_s_eq_Q_r_below_twoQ prime Q r QPositive
          QBelowR rBelowTwoQ
        have numeratorEq :
            sEqualsQCandidateNumerator prime Q r (r - 1) =
              candidateNumerator prime Q r Q (r - 1) := by
          unfold sEqualsQCandidateNumerator candidateNumerator
          grind
        rw [numeratorEq]
        simpa using residue))
    (stateLocal := fun position _ =>
      TwoProjectionModule.phase_local (phase := firstValidator)
        (sEqualsQCandidateState_local prime Q r position primeProperty.1
          QPositive (by omega)))
    (forceLoop := fun position positionBelow {letter} letterMem outputLocal =>
      by
        rcases first_validator_letter primeProperty primeBound layout
            (sEqualsQCandidateState_inPhaseAt (digit := 0) primeProperty
              QPositive
              (by omega) (by simp [ReservedDigit]) (by
                simpa only [Int.zero_mul, Int.sub_zero] using
                  sEqualsQCandidate_zero_residue prime Q r position
                    (by omega) positionBelow)) letterMem outputLocal with
          ⟨_, letterEq⟩ | ⟨digitEq, _⟩
        · exact letterEq
        · omega)
    (rejectMarker := fun {letter} letterMem =>
      first_validator_rejects_forbidden primeProperty primeBound layout
        (by omega) (by omega)
        (sEqualsQCandidateState_inPhaseAt (digit := -1) primeProperty
          QPositive (by omega)
          (by simp [ReservedDigit]) (by
            have residue := first_marker_s_eq_Q_r_below_twoQ prime Q r
              QPositive QBelowR rBelowTwoQ
            have numeratorEq :
                sEqualsQCandidateNumerator prime Q r (r - 1) =
                  candidateNumerator prime Q r Q (r - 1) := by
              unfold sEqualsQCandidateNumerator candidateNumerator
              grind
            rw [numeratorEq]
            simpa using residue)) letterMem)
    (loopStep := fun position positionBelow =>
      sEqualsQCandidateZero_step prime firstValidator Q r position
        primeProperty.1 QPositive (by omega) (by omega) positionBelow)
    sumEq wordOver allLocal completeRun

theorem candidateAboveQTail_forced_prefix_to_endpoint
    {prime phaseCount source target firstGuess secondGuess negativePhase
      firstValidator secondValidator thirdValidator endpointPhase Q r s : Nat}
    {endpointDigit : Int} {endpoint : Vec2}
    (primeProperty : IsPrime prime) (primeBound : 6 * phaseCount < prime)
    (layout : PhaseLayout phaseCount source firstGuess secondGuess
      negativePhase firstValidator secondValidator thirdValidator)
    (endpointBound : endpointPhase < phaseCount)
    (validatorEndpointDistinct : firstValidator ≠ endpointPhase)
    (endpointMembership : InPhaseAt prime endpointPhase endpointDigit endpoint)
    (QPositive : 0 < Q) (QBelowS : Q < s) (sBelowR : s < r)
    {deleted remaining : Nat} (sumEq : deleted + remaining = Q - 1)
    {word : List PhysicalTemplate}
    (wordOver : WordOver
      (alphabet source target firstGuess secondGuess negativePhase
        firstValidator secondValidator thirdValidator) word)
    (allLocal : AllStatesLocal prime word
      (phaseAffine firstValidator (candidateState prime Q r s deleted)))
    (completeRun : SameLine
      (physicalWordAction prime word
        (phaseAffine firstValidator (candidateState prime Q r s deleted)))
      endpoint) :
    ∃ suffix,
      word = List.replicate remaining (zeroLoop firstValidator) ++
          [markerOneExit firstValidator secondValidator] ++ suffix ∧
      WordOver
        (alphabet source target firstGuess secondGuess negativePhase
          firstValidator secondValidator thirdValidator) suffix ∧
      AllStatesLocal prime suffix
        (phaseAffine secondValidator
          (generalFirstOutputState prime Q r s 0)) ∧
      SameLine
        (physicalWordAction prime suffix
          (phaseAffine secondValidator
            (generalFirstOutputState prime Q r s 0))) endpoint := by
  have rPositive : 0 < r := by omega
  have sPositive : 0 < s := by omega
  have parsed := forcedScanPrefixToEndpoint
    (Certificate := True) (markerDigit := 1) (limit := Q - 1)
    (state := fun position =>
      phaseAffine firstValidator (candidateState prime Q r s position))
    (loopLetter := zeroLoop firstValidator)
    (exitLetter := markerOneExit firstValidator secondValidator)
    (primeProperty := primeProperty) (primeBound := primeBound)
    (currentBound := layout.firstValidatorBound)
    (endpointBound := endpointBound)
    (phaseDistinct := validatorEndpointDistinct)
    (endpointMembership := endpointMembership)
    (beforeMembership := fun position positionBelow =>
      candidateState_inPhaseAt (digit := 0) primeProperty QPositive
        rPositive sPositive (by simp [ReservedDigit]) (by
          simpa only [Int.zero_mul, Int.sub_zero] using
            candidate_zero_residue prime Q r s position positionBelow
              (by omega) (by omega)))
    (markerMembership := candidateState_inPhaseAt (digit := 1)
      primeProperty QPositive rPositive sPositive
      (by simp [ReservedDigit]) (by
        simpa only [Int.one_mul] using
          first_marker_s_above_Q prime Q r s QPositive QBelowS sBelowR))
    (stateLocal := fun position _ =>
      TwoProjectionModule.phase_local (phase := firstValidator)
        (candidateState_local prime Q r s position primeProperty.1 QPositive
          rPositive sPositive))
    (nextLocal := TwoProjectionModule.phase_local (phase := secondValidator)
      (generalFirstOutputState_local prime Q r s 0 primeProperty.1 QPositive
        rPositive sPositive))
    (forceLoop := fun position positionBelow {letter} letterMem outputLocal =>
      by
        rcases first_validator_letter primeProperty primeBound layout
            (candidateState_inPhaseAt (digit := 0) primeProperty QPositive
              rPositive sPositive (by simp [ReservedDigit]) (by
                simpa only [Int.zero_mul, Int.sub_zero] using
                  candidate_zero_residue prime Q r s position positionBelow
                    (by omega) (by omega))) letterMem outputLocal with
          ⟨_, letterEq⟩ | ⟨digitEq, _⟩
        · exact letterEq
        · omega)
    (forceExit := fun {letter} letterMem outputLocal => by
      rcases first_validator_letter primeProperty primeBound layout
          (candidateState_inPhaseAt (digit := 1) primeProperty QPositive
            rPositive sPositive (by simp [ReservedDigit]) (by
              simpa only [Int.one_mul] using
                first_marker_s_above_Q prime Q r s QPositive QBelowS
                  sBelowR)) letterMem outputLocal with
        ⟨digitEq, _⟩ | ⟨_, letterEq⟩
      · omega
      · exact ⟨True.intro, letterEq⟩)
    (loopStep := fun position positionBelow =>
      candidateZero_step prime firstValidator Q r s position primeProperty.1
        QPositive rPositive sPositive positionBelow (by omega) (by omega))
    (exitStep := fun _ => candidateMarkerAboveQ_step prime firstValidator
      secondValidator Q r s primeProperty.1 QPositive QBelowS sBelowR)
    sumEq wordOver allLocal completeRun
  rcases parsed with ⟨suffix, _, wordEq, suffixOver, suffixLocal, suffixRun⟩
  exact ⟨suffix, wordEq, suffixOver, suffixLocal, suffixRun⟩

theorem generalFirstOutput_rejects_to_endpoint
    {prime phaseCount source target firstGuess secondGuess negativePhase
      firstValidator secondValidator thirdValidator endpointPhase Q r s
      limit : Nat}
    {markerDigit endpointDigit : Int} {endpoint : Vec2}
    (primeProperty : IsPrime prime) (primeBound : 6 * phaseCount < prime)
    (layout : PhaseLayout phaseCount source firstGuess secondGuess
      negativePhase firstValidator secondValidator thirdValidator)
    (endpointBound : endpointPhase < phaseCount)
    (validatorEndpointDistinct : secondValidator ≠ endpointPhase)
    (endpointMembership : InPhaseAt prime endpointPhase endpointDigit endpoint)
    (QPositive : 0 < Q) (rPositive : 0 < r) (sPositive : 0 < s)
    (markerReserved : ReservedDigit markerDigit)
    (markerNeZero : markerDigit ≠ 0) (markerNeOne : markerDigit ≠ 1)
    (beforeResidue : ∀ position, position < limit →
      (prime : Int) ∣ generalFirstOutputNumerator prime Q r s position)
    (markerResidue : (prime : Int) ∣
      generalFirstOutputNumerator prime Q r s limit -
        markerDigit * candidateDenominator prime Q r s)
    (loopStep : ∀ position, position < limit →
      SameLine
        ((zeroLoop secondValidator).act prime
          (phaseAffine secondValidator
            (generalFirstOutputState prime Q r s position)))
        (phaseAffine secondValidator
          (generalFirstOutputState prime Q r s (position + 1))))
    {deleted remaining : Nat} (sumEq : deleted + remaining = limit)
    {word : List PhysicalTemplate}
    (wordOver : WordOver
      (alphabet source target firstGuess secondGuess negativePhase
        firstValidator secondValidator thirdValidator) word)
    (allLocal : AllStatesLocal prime word
      (phaseAffine secondValidator
        (generalFirstOutputState prime Q r s deleted)))
    (completeRun : SameLine
      (physicalWordAction prime word
        (phaseAffine secondValidator
          (generalFirstOutputState prime Q r s deleted))) endpoint) :
    False := by
  apply forcedScanRejectsAtMarker
    (markerDigit := markerDigit) (limit := limit)
    (state := fun position => phaseAffine secondValidator
      (generalFirstOutputState prime Q r s position))
    (loopLetter := zeroLoop secondValidator)
    (primeProperty := primeProperty) (primeBound := primeBound)
    (currentBound := layout.secondValidatorBound)
    (endpointBound := endpointBound)
    (phaseDistinct := validatorEndpointDistinct)
    (endpointMembership := endpointMembership)
    (beforeMembership := fun position positionBelow =>
      generalFirstOutputState_inPhaseAt (digit := 0) primeProperty QPositive
        rPositive sPositive (by simp [ReservedDigit]) (by
          simpa only [Int.zero_mul, Int.sub_zero] using
            beforeResidue position positionBelow))
    (markerMembership := generalFirstOutputState_inPhaseAt
      (digit := markerDigit) primeProperty QPositive rPositive sPositive
      markerReserved markerResidue)
    (stateLocal := fun position _ =>
      TwoProjectionModule.phase_local (phase := secondValidator)
        (generalFirstOutputState_local prime Q r s position primeProperty.1
          QPositive rPositive sPositive))
    (forceLoop := fun position positionBelow {letter} letterMem outputLocal =>
      by
        rcases second_validator_letter primeProperty primeBound layout
            (generalFirstOutputState_inPhaseAt (digit := 0) primeProperty
              QPositive rPositive sPositive (by simp [ReservedDigit]) (by
                simpa only [Int.zero_mul, Int.sub_zero] using
                  beforeResidue position positionBelow)) letterMem
            outputLocal with
          ⟨_, letterEq⟩ | ⟨digitEq, _⟩
        · exact letterEq
        · omega)
    (rejectMarker := fun {letter} letterMem =>
      second_validator_rejects_forbidden primeProperty primeBound layout
        markerNeZero markerNeOne
        (generalFirstOutputState_inPhaseAt (digit := markerDigit)
          primeProperty QPositive rPositive sPositive markerReserved
          markerResidue) letterMem)
    loopStep sumEq wordOver allLocal completeRun

theorem candidateSEqQAboveTwoQTail_forced_prefix_to_endpoint
    {prime phaseCount source target firstGuess secondGuess negativePhase
      firstValidator secondValidator thirdValidator endpointPhase Q r : Nat}
    {endpointDigit : Int} {endpoint : Vec2}
    (primeProperty : IsPrime prime) (primeBound : 6 * phaseCount < prime)
    (layout : PhaseLayout phaseCount source firstGuess secondGuess
      negativePhase firstValidator secondValidator thirdValidator)
    (endpointBound : endpointPhase < phaseCount)
    (validatorEndpointDistinct : firstValidator ≠ endpointPhase)
    (endpointMembership : InPhaseAt prime endpointPhase endpointDigit endpoint)
    (QPositive : 0 < Q) (twoQBelowR : 2 * Q < r)
    (rBelowThreeQ : r < 3 * Q)
    {deleted remaining : Nat} (sumEq : deleted + remaining = 2 * Q - 1)
    {word : List PhysicalTemplate}
    (wordOver : WordOver
      (alphabet source target firstGuess secondGuess negativePhase
        firstValidator secondValidator thirdValidator) word)
    (allLocal : AllStatesLocal prime word
      (phaseAffine firstValidator
        (sEqualsQCandidateState prime Q r deleted)))
    (completeRun : SameLine
      (physicalWordAction prime word
        (phaseAffine firstValidator
          (sEqualsQCandidateState prime Q r deleted))) endpoint) :
    ∃ suffix,
      word = List.replicate remaining (zeroLoop firstValidator) ++
          [markerOneExit firstValidator secondValidator] ++ suffix ∧
      WordOver
        (alphabet source target firstGuess secondGuess negativePhase
          firstValidator secondValidator thirdValidator) suffix ∧
      AllStatesLocal prime suffix
        (phaseAffine secondValidator
          (sEqualsQFirstOutputState prime Q r 0)) ∧
      SameLine
        (physicalWordAction prime suffix
          (phaseAffine secondValidator
            (sEqualsQFirstOutputState prime Q r 0))) endpoint := by
  have parsed := forcedScanPrefixToEndpoint
    (Certificate := True) (markerDigit := 1) (limit := 2 * Q - 1)
    (state := fun position => phaseAffine firstValidator
      (sEqualsQCandidateState prime Q r position))
    (loopLetter := zeroLoop firstValidator)
    (exitLetter := markerOneExit firstValidator secondValidator)
    (primeProperty := primeProperty) (primeBound := primeBound)
    (currentBound := layout.firstValidatorBound)
    (endpointBound := endpointBound)
    (phaseDistinct := validatorEndpointDistinct)
    (endpointMembership := endpointMembership)
    (beforeMembership := fun position positionBelow =>
      sEqualsQCandidateState_inPhaseAt (digit := 0) primeProperty QPositive
        (by omega) (by simp [ReservedDigit]) (by
          simpa only [Int.zero_mul, Int.sub_zero] using
            sEqualsQCandidate_zero_residue prime Q r position positionBelow
              (by omega)))
    (markerMembership := sEqualsQCandidateState_inPhaseAt (digit := 1)
      primeProperty QPositive (by omega) (by simp [ReservedDigit]) (by
        have residue := first_marker_s_eq_Q_r_above_twoQ prime Q r QPositive
          twoQBelowR rBelowThreeQ
        have numeratorEq :
            sEqualsQCandidateNumerator prime Q r (2 * Q - 1) =
              candidateNumerator prime Q r Q (2 * Q - 1) := by
          unfold sEqualsQCandidateNumerator candidateNumerator
          grind
        rw [numeratorEq]
        simpa only [Int.one_mul] using residue))
    (stateLocal := fun position _ =>
      TwoProjectionModule.phase_local (phase := firstValidator)
        (sEqualsQCandidateState_local prime Q r position primeProperty.1
          QPositive (by omega)))
    (nextLocal := TwoProjectionModule.phase_local (phase := secondValidator)
      (sEqualsQFirstOutputState_local prime Q r 0 primeProperty.1 QPositive
        (by omega)))
    (forceLoop := fun position positionBelow {letter} letterMem outputLocal =>
      by
        rcases first_validator_letter primeProperty primeBound layout
            (sEqualsQCandidateState_inPhaseAt (digit := 0) primeProperty
              QPositive (by omega) (by simp [ReservedDigit]) (by
                simpa only [Int.zero_mul, Int.sub_zero] using
                  sEqualsQCandidate_zero_residue prime Q r position
                    positionBelow (by omega))) letterMem outputLocal with
          ⟨_, letterEq⟩ | ⟨digitEq, _⟩
        · exact letterEq
        · omega)
    (forceExit := fun {letter} letterMem outputLocal => by
      rcases first_validator_letter primeProperty primeBound layout
          (sEqualsQCandidateState_inPhaseAt (digit := 1) primeProperty
            QPositive (by omega) (by simp [ReservedDigit]) (by
              have residue := first_marker_s_eq_Q_r_above_twoQ prime Q r
                QPositive twoQBelowR rBelowThreeQ
              have numeratorEq :
                  sEqualsQCandidateNumerator prime Q r (2 * Q - 1) =
                    candidateNumerator prime Q r Q (2 * Q - 1) := by
                unfold sEqualsQCandidateNumerator candidateNumerator
                grind
              rw [numeratorEq]
              simpa only [Int.one_mul] using residue)) letterMem outputLocal
          with
        ⟨digitEq, _⟩ | ⟨_, letterEq⟩
      · omega
      · exact ⟨True.intro, letterEq⟩)
    (loopStep := fun position positionBelow =>
      sEqualsQCandidateZero_step prime firstValidator Q r position
        primeProperty.1 QPositive (by omega) positionBelow (by omega))
    (exitStep := fun _ => sEqualsQCandidateMarker_step prime firstValidator
      secondValidator Q r primeProperty.1 QPositive twoQBelowR
      rBelowThreeQ)
    sumEq wordOver allLocal completeRun
  rcases parsed with ⟨suffix, _, wordEq, suffixOver, suffixLocal, suffixRun⟩
  exact ⟨suffix, wordEq, suffixOver, suffixLocal, suffixRun⟩

theorem sEqualsQFirstOutput_rejects_to_endpoint
    {prime phaseCount source target firstGuess secondGuess negativePhase
      firstValidator secondValidator thirdValidator endpointPhase Q r : Nat}
    {endpointDigit : Int} {endpoint : Vec2}
    (primeProperty : IsPrime prime) (primeBound : 6 * phaseCount < prime)
    (layout : PhaseLayout phaseCount source firstGuess secondGuess
      negativePhase firstValidator secondValidator thirdValidator)
    (endpointBound : endpointPhase < phaseCount)
    (validatorEndpointDistinct : secondValidator ≠ endpointPhase)
    (endpointMembership : InPhaseAt prime endpointPhase endpointDigit endpoint)
    (QPositive : 0 < Q) (twoQBelowR : 2 * Q < r)
    (rBelowThreeQ : r < 3 * Q)
    {deleted remaining : Nat}
    (sumEq : deleted + remaining = r - 2 * Q - 1)
    {word : List PhysicalTemplate}
    (wordOver : WordOver
      (alphabet source target firstGuess secondGuess negativePhase
        firstValidator secondValidator thirdValidator) word)
    (allLocal : AllStatesLocal prime word
      (phaseAffine secondValidator
        (sEqualsQFirstOutputState prime Q r deleted)))
    (completeRun : SameLine
      (physicalWordAction prime word
        (phaseAffine secondValidator
          (sEqualsQFirstOutputState prime Q r deleted))) endpoint) :
    False := by
  apply forcedScanRejectsAtMarker
    (markerDigit := -1) (limit := r - 2 * Q - 1)
    (state := fun position => phaseAffine secondValidator
      (sEqualsQFirstOutputState prime Q r position))
    (loopLetter := zeroLoop secondValidator)
    (primeProperty := primeProperty) (primeBound := primeBound)
    (currentBound := layout.secondValidatorBound)
    (endpointBound := endpointBound)
    (phaseDistinct := validatorEndpointDistinct)
    (endpointMembership := endpointMembership)
    (beforeMembership := fun position positionBelow =>
      sEqualsQFirstOutputState_inPhaseAt (digit := 0) primeProperty
        QPositive (by omega) (by simp [ReservedDigit]) (by
          simpa only [Int.zero_mul, Int.sub_zero] using
            sEqualsQFirstOutput_zero_residue prime Q r position (by omega)
              positionBelow))
    (markerMembership := sEqualsQFirstOutputState_inPhaseAt (digit := -1)
      primeProperty QPositive (by omega) (by simp [ReservedDigit])
      (second_marker_s_eq_Q_r_above_twoQ prime Q r QPositive twoQBelowR
        rBelowThreeQ))
    (stateLocal := fun position _ =>
      TwoProjectionModule.phase_local (phase := secondValidator)
        (sEqualsQFirstOutputState_local prime Q r position primeProperty.1
          QPositive (by omega)))
    (forceLoop := fun position positionBelow {letter} letterMem outputLocal =>
      by
        rcases second_validator_letter primeProperty primeBound layout
            (sEqualsQFirstOutputState_inPhaseAt (digit := 0) primeProperty
              QPositive (by omega) (by simp [ReservedDigit]) (by
                simpa only [Int.zero_mul, Int.sub_zero] using
                  sEqualsQFirstOutput_zero_residue prime Q r position
                    (by omega) positionBelow)) letterMem outputLocal with
          ⟨_, letterEq⟩ | ⟨digitEq, _⟩
        · exact letterEq
        · omega)
    (rejectMarker := fun {letter} letterMem =>
      second_validator_rejects_forbidden primeProperty primeBound layout
        (by omega) (by omega)
        (sEqualsQFirstOutputState_inPhaseAt (digit := -1) primeProperty
          QPositive (by omega) (by simp [ReservedDigit])
          (second_marker_s_eq_Q_r_above_twoQ prime Q r QPositive
            twoQBelowR rBelowThreeQ)) letterMem)
    (loopStep := fun position positionBelow =>
      sEqualsQFirstOutputZero_step prime secondValidator Q r position
        primeProperty.1 QPositive (by omega) (by omega) (by omega)
        (by omega) positionBelow (by omega))
    sumEq wordOver allLocal completeRun

theorem generalFirstOutputS2Tail_forced_prefix_to_endpoint
    {prime phaseCount source target firstGuess secondGuess negativePhase
      firstValidator secondValidator thirdValidator endpointPhase Q r : Nat}
    {endpointDigit : Int} {endpoint : Vec2}
    (primeProperty : IsPrime prime) (primeBound : 6 * phaseCount < prime)
    (layout : PhaseLayout phaseCount source firstGuess secondGuess
      negativePhase firstValidator secondValidator thirdValidator)
    (endpointBound : endpointPhase < phaseCount)
    (validatorEndpointDistinct : secondValidator ≠ endpointPhase)
    (endpointMembership : InPhaseAt prime endpointPhase endpointDigit endpoint)
    (QPositive : 0 < Q) (twoQBelowR : 2 * Q < r)
    {deleted remaining : Nat} (sumEq : deleted + remaining = Q - 1)
    {word : List PhysicalTemplate}
    (wordOver : WordOver
      (alphabet source target firstGuess secondGuess negativePhase
        firstValidator secondValidator thirdValidator) word)
    (allLocal : AllStatesLocal prime word
      (phaseAffine secondValidator
        (generalFirstOutputState prime Q r (2 * Q) deleted)))
    (completeRun : SameLine
      (physicalWordAction prime word
        (phaseAffine secondValidator
          (generalFirstOutputState prime Q r (2 * Q) deleted))) endpoint) :
    ∃ suffix,
      word = List.replicate remaining (zeroLoop secondValidator) ++
          [markerOneExit secondValidator thirdValidator] ++ suffix ∧
      WordOver
        (alphabet source target firstGuess secondGuess negativePhase
          firstValidator secondValidator thirdValidator) suffix ∧
      AllStatesLocal prime suffix
        (phaseAffine thirdValidator
          (sEqualsTwoQSecondOutputState prime Q r 0)) ∧
      SameLine
        (physicalWordAction prime suffix
          (phaseAffine thirdValidator
            (sEqualsTwoQSecondOutputState prime Q r 0))) endpoint := by
  have parsed := forcedScanPrefixToEndpoint
    (Certificate := True) (markerDigit := 1) (limit := Q - 1)
    (state := fun position => phaseAffine secondValidator
      (generalFirstOutputState prime Q r (2 * Q) position))
    (loopLetter := zeroLoop secondValidator)
    (exitLetter := markerOneExit secondValidator thirdValidator)
    (primeProperty := primeProperty) (primeBound := primeBound)
    (currentBound := layout.secondValidatorBound)
    (endpointBound := endpointBound)
    (phaseDistinct := validatorEndpointDistinct)
    (endpointMembership := endpointMembership)
    (beforeMembership := fun position positionBelow =>
      generalFirstOutputState_inPhaseAt (digit := 0) primeProperty QPositive
        (by omega) (by omega) (by simp [ReservedDigit]) (by
          simpa only [Int.zero_mul, Int.sub_zero] using
            generalFirstOutput_zero_residue prime Q r (2 * Q) position
              positionBelow (by omega) (by omega)))
    (markerMembership := generalFirstOutputState_inPhaseAt (digit := 1)
      primeProperty QPositive (by omega) (by omega)
      (by simp [ReservedDigit]) (by
        simpa only [Int.one_mul] using
          second_marker_s_eq_twoQ prime Q r QPositive twoQBelowR))
    (stateLocal := fun position _ =>
      TwoProjectionModule.phase_local (phase := secondValidator)
        (generalFirstOutputState_local prime Q r (2 * Q) position
          primeProperty.1 QPositive (by omega) (by omega)))
    (nextLocal := TwoProjectionModule.phase_local (phase := thirdValidator)
      (sEqualsTwoQSecondOutputState_local prime Q r 0 primeProperty.1
        QPositive (by omega)))
    (forceLoop := fun position positionBelow {letter} letterMem outputLocal =>
      by
        rcases second_validator_letter primeProperty primeBound layout
            (generalFirstOutputState_inPhaseAt (digit := 0) primeProperty
              QPositive (by omega) (by omega) (by simp [ReservedDigit]) (by
                simpa only [Int.zero_mul, Int.sub_zero] using
                  generalFirstOutput_zero_residue prime Q r (2 * Q) position
                    positionBelow (by omega) (by omega))) letterMem
            outputLocal with
          ⟨_, letterEq⟩ | ⟨digitEq, _⟩
        · exact letterEq
        · omega)
    (forceExit := fun {letter} letterMem outputLocal => by
      rcases second_validator_letter primeProperty primeBound layout
          (generalFirstOutputState_inPhaseAt (digit := 1) primeProperty
            QPositive (by omega) (by omega) (by simp [ReservedDigit]) (by
              simpa only [Int.one_mul] using
                second_marker_s_eq_twoQ prime Q r QPositive twoQBelowR))
          letterMem outputLocal with
        ⟨digitEq, _⟩ | ⟨_, letterEq⟩
      · omega
      · exact ⟨True.intro, letterEq⟩)
    (loopStep := fun position positionBelow =>
      generalFirstOutputZero_step prime secondValidator Q r (2 * Q)
        position primeProperty.1 QPositive (by omega) (by omega)
        positionBelow (by omega) (by omega) (by omega) (by omega)
        (by omega) (by omega))
    (exitStep := fun _ => generalFirstOutputMarkerS2_step prime
      secondValidator thirdValidator Q r primeProperty.1 QPositive
      twoQBelowR)
    sumEq wordOver allLocal completeRun
  rcases parsed with ⟨suffix, _, wordEq, suffixOver, suffixLocal, suffixRun⟩
  exact ⟨suffix, wordEq, suffixOver, suffixLocal, suffixRun⟩

theorem sEqualsTwoQSecondOutput_rejects_to_endpoint
    {prime phaseCount source target firstGuess secondGuess negativePhase
      firstValidator secondValidator thirdValidator endpointPhase Q r : Nat}
    {endpointDigit : Int} {endpoint : Vec2}
    (primeProperty : IsPrime prime) (primeBound : 6 * phaseCount < prime)
    (layout : PhaseLayout phaseCount source firstGuess secondGuess
      negativePhase firstValidator secondValidator thirdValidator)
    (endpointBound : endpointPhase < phaseCount)
    (validatorEndpointDistinct : thirdValidator ≠ endpointPhase)
    (endpointMembership : InPhaseAt prime endpointPhase endpointDigit endpoint)
    (QPositive : 0 < Q) (twoQBelowR : 2 * Q < r)
    (rBelowThreeQ : r < 3 * Q)
    {deleted remaining : Nat}
    (sumEq : deleted + remaining = r - 2 * Q - 1)
    {word : List PhysicalTemplate}
    (wordOver : WordOver
      (alphabet source target firstGuess secondGuess negativePhase
        firstValidator secondValidator thirdValidator) word)
    (allLocal : AllStatesLocal prime word
      (phaseAffine thirdValidator
        (sEqualsTwoQSecondOutputState prime Q r deleted)))
    (completeRun : SameLine
      (physicalWordAction prime word
        (phaseAffine thirdValidator
          (sEqualsTwoQSecondOutputState prime Q r deleted))) endpoint) :
    False := by
  apply forcedScanRejectsAtMarker
    (markerDigit := -1) (limit := r - 2 * Q - 1)
    (state := fun position => phaseAffine thirdValidator
      (sEqualsTwoQSecondOutputState prime Q r position))
    (loopLetter := zeroLoop thirdValidator)
    (primeProperty := primeProperty) (primeBound := primeBound)
    (currentBound := layout.thirdValidatorBound)
    (endpointBound := endpointBound)
    (phaseDistinct := validatorEndpointDistinct)
    (endpointMembership := endpointMembership)
    (beforeMembership := fun position positionBelow =>
      sEqualsTwoQSecondOutputState_inPhaseAt (digit := 0) primeProperty
        QPositive (by omega) (by simp [ReservedDigit]) (by
          simpa only [Int.zero_mul, Int.sub_zero] using
            sEqualsTwoQSecondOutput_zero_residue prime Q r position
              (by omega) positionBelow))
    (markerMembership := sEqualsTwoQSecondOutputState_inPhaseAt
      (digit := -1) primeProperty QPositive (by omega)
      (by simp [ReservedDigit])
      (third_marker_s_eq_twoQ prime Q r QPositive twoQBelowR
        rBelowThreeQ))
    (stateLocal := fun position _ =>
      TwoProjectionModule.phase_local (phase := thirdValidator)
        (sEqualsTwoQSecondOutputState_local prime Q r position
          primeProperty.1 QPositive (by omega)))
    (forceLoop := fun position positionBelow {letter} letterMem outputLocal =>
      by
        rcases third_validator_letter primeProperty primeBound layout
            (sEqualsTwoQSecondOutputState_inPhaseAt (digit := 0)
              primeProperty QPositive (by omega) (by simp [ReservedDigit])
              (by
                simpa only [Int.zero_mul, Int.sub_zero] using
                  sEqualsTwoQSecondOutput_zero_residue prime Q r position
                    (by omega) positionBelow)) letterMem outputLocal with
          ⟨_, letterEq⟩ | ⟨digitEq, _⟩
        · exact letterEq
        · omega)
    (rejectMarker := fun {letter} letterMem =>
      third_validator_rejects_forbidden primeProperty primeBound layout
        (by omega) (by omega)
        (sEqualsTwoQSecondOutputState_inPhaseAt (digit := -1)
          primeProperty QPositive (by omega) (by simp [ReservedDigit])
          (third_marker_s_eq_twoQ prime Q r QPositive twoQBelowR
            rBelowThreeQ)) letterMem)
    (loopStep := fun position positionBelow =>
      sEqualsTwoQSecondOutputZero_step prime thirdValidator Q r position
        primeProperty.1 QPositive (by omega) (by omega) (by omega)
        (by omega) positionBelow (by omega) (by omega))
    sumEq wordOver allLocal completeRun

theorem acceptedCandidateValidators_forced_prefix_to_endpoint
    {prime phaseCount source target firstGuess secondGuess negativePhase
      firstValidator secondValidator thirdValidator endpointPhase Q : Nat}
    {endpointDigit : Int} {endpoint : Vec2}
    (primeProperty : IsPrime prime) (primeBound : 6 * phaseCount < prime)
    (layout : PhaseLayout phaseCount source firstGuess secondGuess
      negativePhase firstValidator secondValidator thirdValidator)
    (endpointBound : endpointPhase < phaseCount)
    (firstEndpointDistinct : firstValidator ≠ endpointPhase)
    (secondEndpointDistinct : secondValidator ≠ endpointPhase)
    (thirdEndpointDistinct : thirdValidator ≠ endpointPhase)
    (endpointMembership : InPhaseAt prime endpointPhase endpointDigit endpoint)
    (QPositive : 0 < Q)
    {word : List PhysicalTemplate}
    (wordOver : WordOver
      (alphabet source target firstGuess secondGuess negativePhase
        firstValidator secondValidator thirdValidator) word)
    (allLocal : AllStatesLocal prime word
      (phaseAffine firstValidator
        (candidateState prime Q (2 * Q) Q 0)))
    (completeRun : SameLine
      (physicalWordAction prime word
        (phaseAffine firstValidator
          (candidateState prime Q (2 * Q) Q 0))) endpoint) :
    ∃ suffix,
      word = validatorWord firstValidator secondValidator (3 * Q - 1) ++
          validatorWord secondValidator thirdValidator (3 * Q - 1) ++
          validatorWord thirdValidator target (3 * Q - 1) ++ suffix ∧
      WordOver
        (alphabet source target firstGuess secondGuess negativePhase
          firstValidator secondValidator thirdValidator) suffix ∧
      AllStatesLocal prime suffix
        (phaseAffine target (unaryCode prime (3 * Q - 1))) ∧
      SameLine
        (physicalWordAction prime suffix
          (phaseAffine target (unaryCode prime (3 * Q - 1)))) endpoint := by
  have startEq :
      phaseAffine firstValidator (candidateState prime Q (2 * Q) Q 0) =
        phaseAffine firstValidator
          (TwoProjectionModule.validatorState prime (3 * Q - 1) 0) := by
    rw [accepted_candidate_state prime Q QPositive,
      TwoProjectionModule.validatorState_zero]
  rw [startEq] at allLocal completeRun
  obtain ⟨afterFirst, firstEq, afterFirstOver, afterFirstLocal,
      afterFirstRun⟩ :=
    TwoProjectionModule.validatorTail_forced_prefix_to_endpoint
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
      (sumEq := show 0 + (3 * Q - 1) = 3 * Q - 1 by omega)
      wordOver allLocal completeRun
  have afterFirstStart :
      phaseAffine secondValidator (unaryCode prime (3 * Q - 1)) =
        phaseAffine secondValidator
          (TwoProjectionModule.validatorState prime (3 * Q - 1) 0) := by
    rw [TwoProjectionModule.validatorState_zero]
  rw [afterFirstStart] at afterFirstLocal afterFirstRun
  obtain ⟨afterSecond, secondEq, afterSecondOver, afterSecondLocal,
      afterSecondRun⟩ :=
    TwoProjectionModule.validatorTail_forced_prefix_to_endpoint
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
      (sumEq := show 0 + (3 * Q - 1) = 3 * Q - 1 by omega)
      afterFirstOver afterFirstLocal afterFirstRun
  have afterSecondStart :
      phaseAffine thirdValidator (unaryCode prime (3 * Q - 1)) =
        phaseAffine thirdValidator
          (TwoProjectionModule.validatorState prime (3 * Q - 1) 0) := by
    rw [TwoProjectionModule.validatorState_zero]
  rw [afterSecondStart] at afterSecondLocal afterSecondRun
  obtain ⟨suffix, thirdEq, suffixOver, suffixLocal, suffixRun⟩ :=
    TwoProjectionModule.validatorTail_forced_prefix_to_endpoint
      (primeProperty := primeProperty) (primeBound := primeBound)
      (currentBound := layout.thirdValidatorBound)
      (endpointBound := endpointBound)
      (currentEndpointDistinct := thirdEndpointDistinct)
      (endpointMembership := endpointMembership)
      (forceZero := fun {state} {letter} membership letterMem outputLocal => by
        rcases third_validator_letter primeProperty primeBound layout
            membership letterMem outputLocal with
          ⟨_, letterEq⟩ | ⟨digitEq, _⟩
        · exact letterEq
        · omega)
      (forceMarker := fun {state} {letter} membership letterMem outputLocal =>
        by
          rcases third_validator_letter primeProperty primeBound layout
              membership letterMem outputLocal with
            ⟨digitEq, _⟩ | ⟨_, letterEq⟩
          · omega
          · exact letterEq)
      (sumEq := show 0 + (3 * Q - 1) = 3 * Q - 1 by omega)
      afterSecondOver afterSecondLocal afterSecondRun
  rw [thirdEq] at secondEq
  rw [secondEq] at firstEq
  refine ⟨suffix, ?_, suffixOver, suffixLocal, suffixRun⟩
  simpa [validatorWord, TwoProjectionModule.validatorWord,
    MutatingScan.word, List.append_assoc] using firstEq

/-- Every completed local path through the fourteen-letter alphabet starts
with the unique accepted two-guess projection block. -/
theorem completedPath_forces_accepted_prefix
    {prime phaseCount source target firstGuess secondGuess negativePhase
      firstValidator secondValidator thirdValidator endpointPhase first : Nat}
    {endpointDigit : Int} {endpoint : Vec2}
    (primeProperty : IsPrime prime) (primeBound : 6 * phaseCount < prime)
    (layout : PhaseLayout phaseCount source firstGuess secondGuess
      negativePhase firstValidator secondValidator thirdValidator)
    (endpointBound : endpointPhase < phaseCount)
    (sourceEndpointDistinct : source ≠ endpointPhase)
    (firstGuessEndpointDistinct : firstGuess ≠ endpointPhase)
    (secondGuessEndpointDistinct : secondGuess ≠ endpointPhase)
    (negativeEndpointDistinct : negativePhase ≠ endpointPhase)
    (firstValidatorEndpointDistinct : firstValidator ≠ endpointPhase)
    (secondValidatorEndpointDistinct : secondValidator ≠ endpointPhase)
    (thirdValidatorEndpointDistinct : thirdValidator ≠ endpointPhase)
    (endpointMembership : InPhaseAt prime endpointPhase endpointDigit endpoint)
    {word : List PhysicalTemplate}
    (wordOver : WordOver
      (alphabet source target firstGuess secondGuess negativePhase
        firstValidator secondValidator thirdValidator) word)
    (allLocal : AllStatesLocal prime word
      (phaseAffine source
        (twoFieldCode prime first (3 * first + 2))))
    (completeRun : SameLine
      (physicalWordAction prime word
        (phaseAffine source
          (twoFieldCode prime first (3 * first + 2)))) endpoint) :
    ∃ suffix,
      word = acceptedWord source target firstGuess secondGuess negativePhase
          firstValidator secondValidator thirdValidator first ++ suffix ∧
      WordOver
        (alphabet source target firstGuess secondGuess negativePhase
          firstValidator secondValidator thirdValidator) suffix ∧
      AllStatesLocal prime suffix
        (phaseAffine target (unaryCode prime (3 * first + 2))) ∧
      SameLine
        (physicalWordAction prime suffix
          (phaseAffine target (unaryCode prime (3 * first + 2)))) endpoint := by
  rw [← sourceScanState_zero prime first] at allLocal completeRun
  obtain ⟨afterSource, sourceEq, afterSourceOver, afterSourceLocal,
      afterSourceRun⟩ :=
    sourceTail_forced_prefix_to_endpoint primeProperty primeBound layout
      endpointBound sourceEndpointDistinct endpointMembership
      (show 0 + first = first by omega) wordOver allLocal completeRun
  rw [← firstGuessState_zero prime first primeProperty.1] at afterSourceLocal afterSourceRun
  obtain ⟨guess, afterFirstGuess, guessPositive, guessBound, firstGuessEq,
      afterFirstGuessOver, afterFirstGuessLocal, afterFirstGuessRun⟩ :=
    firstGuessTail_forced_exit_to_endpoint primeProperty primeBound layout
      endpointBound firstGuessEndpointDistinct endpointMembership
      (show 0 + (3 * first + 2) = 3 * first + 2 by omega)
      afterSourceOver afterSourceLocal afterSourceRun
  let Q := first + 1
  let r := 3 * Q - guess
  have QPositive : 0 < Q := by simp [Q]
  have rPositive : 0 < r := by dsimp [r, Q]; omega
  have rBelowThreeQ : r < 3 * Q := by dsimp [r]; omega
  have firstGuessStartEq :
      phaseAffine secondGuess
          (secondGuessState prime (first + 1)
            (3 * (first + 1) - guess) 0) =
        phaseAffine secondGuess (secondGuessState prime Q r 0) := by
    rfl
  rw [firstGuessStartEq] at afterFirstGuessLocal afterFirstGuessRun
  obtain ⟨s, afterSecondGuess, sPositive, sBelowR, _, secondGuessEq,
      afterSecondGuessOver, afterSecondGuessLocal, afterSecondGuessRun⟩ :=
    secondGuessTail_forced_exit_to_endpoint primeProperty primeBound layout
      endpointBound secondGuessEndpointDistinct endpointMembership QPositive
      rPositive rBelowThreeQ (show 0 + (r - 1) = r - 1 by omega)
      afterFirstGuessOver afterFirstGuessLocal afterFirstGuessRun
  obtain ⟨afterNegative, negativeEq, afterNegativeOver, afterNegativeLocal,
      afterNegativeRun⟩ :=
    negativeTail_forced_prefix_to_endpoint primeProperty primeBound layout
      endpointBound negativeEndpointDistinct endpointMembership QPositive
      sPositive sBelowR rBelowThreeQ
      (show 0 + (s - 1) = s - 1 by omega) afterSecondGuessOver
      afterSecondGuessLocal afterSecondGuessRun
  cases exhaustive_projection_outcome prime Q r s QPositive sPositive
      sBelowR rBelowThreeQ with
  | firstRejectBelow sBelowQ residue =>
      exact False.elim (candidateBelowQ_rejects_to_endpoint primeProperty
        primeBound layout endpointBound firstValidatorEndpointDistinct
        endpointMembership QPositive sPositive sBelowQ sBelowR
        (show 0 + (s - 1) = s - 1 by omega) afterNegativeOver
        afterNegativeLocal afterNegativeRun)
  | firstRejectAtQ sEqQ rBelowTwoQ residue =>
      have QBelowR : Q < r := by omega
      rw [sEqQ, ← sEqualsQCandidateState_eq prime Q r 0] at afterNegativeLocal afterNegativeRun
      exact False.elim
        (candidateSEqQBelowTwoQ_rejects_to_endpoint primeProperty primeBound
          layout endpointBound firstValidatorEndpointDistinct
          endpointMembership QPositive QBelowR rBelowTwoQ
          (show 0 + (r - 1) = r - 1 by omega) afterNegativeOver
          afterNegativeLocal afterNegativeRun)
  | accepted sEqQ rEqTwoQ numeratorEq denominatorEq =>
      have acceptedGuess : guess = Q := by
        dsimp [r] at rEqTwoQ
        omega
      rw [sEqQ, rEqTwoQ] at afterNegativeLocal afterNegativeRun
      obtain ⟨suffix, validatorsEq, suffixOver, suffixLocal, suffixRun⟩ :=
        acceptedCandidateValidators_forced_prefix_to_endpoint primeProperty
          primeBound layout endpointBound firstValidatorEndpointDistinct
          secondValidatorEndpointDistinct thirdValidatorEndpointDistinct
          endpointMembership QPositive afterNegativeOver afterNegativeLocal
          afterNegativeRun
      rw [validatorsEq] at negativeEq
      rw [negativeEq] at secondGuessEq
      rw [secondGuessEq] at firstGuessEq
      rw [firstGuessEq] at sourceEq
      have firstGuessLength : guess - 1 = first := by
        dsimp [Q] at acceptedGuess
        omega
      have secondGuessLength : r - s - 1 = first := by
        dsimp [Q] at sEqQ rEqTwoQ
        omega
      have negativeLength : s - 1 = first := by
        dsimp [Q] at sEqQ
        omega
      have counterEq : 3 * Q - 1 = 3 * first + 2 := by
        unfold Q
        omega
      have counterAfterSubstitution :
          3 * (first + 1) - 1 = 3 * first + 2 := by omega
      refine ⟨suffix, ?_, suffixOver, ?_, ?_⟩
      · simpa [acceptedWord, sourceWord, guessWord, negativeWord,
          validatorWord, MutatingScan.word, zeroLoop, markerOneExit,
          inverseTZeroExit, inverseFNegativeExit, firstGuessLength,
          secondGuessLength, negativeLength, acceptedGuess, Q,
          counterAfterSubstitution, List.append_assoc] using sourceEq
      · simpa [counterEq] using suffixLocal
      · simpa [counterEq] using suffixRun
  | secondRejectAtQ sEqQ twoQBelowR residue =>
      rw [sEqQ, ← sEqualsQCandidateState_eq prime Q r 0] at afterNegativeLocal afterNegativeRun
      obtain ⟨afterFirstValidator, firstValidatorEq,
          afterFirstValidatorOver, afterFirstValidatorLocal,
          afterFirstValidatorRun⟩ :=
        candidateSEqQAboveTwoQTail_forced_prefix_to_endpoint primeProperty
          primeBound layout endpointBound firstValidatorEndpointDistinct
          endpointMembership QPositive twoQBelowR rBelowThreeQ
          (show 0 + (2 * Q - 1) = 2 * Q - 1 by omega)
          afterNegativeOver afterNegativeLocal afterNegativeRun
      exact False.elim (sEqualsQFirstOutput_rejects_to_endpoint primeProperty
        primeBound layout endpointBound secondValidatorEndpointDistinct
        endpointMembership QPositive twoQBelowR rBelowThreeQ
        (show 0 + (r - 2 * Q - 1) = r - 2 * Q - 1 by omega)
        afterFirstValidatorOver afterFirstValidatorLocal
        afterFirstValidatorRun)
  | secondRejectBetween QBelowS sBelowTwoQ residue =>
      obtain ⟨afterFirstValidator, firstValidatorEq,
          afterFirstValidatorOver, afterFirstValidatorLocal,
          afterFirstValidatorRun⟩ :=
        candidateAboveQTail_forced_prefix_to_endpoint primeProperty
          primeBound layout endpointBound firstValidatorEndpointDistinct
          endpointMembership QPositive QBelowS sBelowR
          (show 0 + (Q - 1) = Q - 1 by omega) afterNegativeOver
          afterNegativeLocal afterNegativeRun
      exact False.elim (generalFirstOutput_rejects_to_endpoint primeProperty
        primeBound layout endpointBound secondValidatorEndpointDistinct
        endpointMembership QPositive (by omega) sPositive
        (by simp [ReservedDigit]) (by omega) (by omega)
        (fun position positionBelow =>
          generalFirstOutput_zero_residue prime Q r s position (by omega)
            (by omega) positionBelow)
        (second_marker_s_between_Q_twoQ prime Q r s QPositive QBelowS
          sBelowTwoQ sBelowR)
        (fun position positionBelow =>
          generalFirstOutputZero_step prime secondValidator Q r s position
            primeProperty.1 QPositive (by omega) sPositive (by omega)
            (by omega) (by omega) (by omega) positionBelow (by omega)
            (by omega))
        (show 0 + (s - Q - 1) = s - Q - 1 by omega)
        afterFirstValidatorOver afterFirstValidatorLocal
        afterFirstValidatorRun)
  | thirdRejectAtTwoQ sEqTwoQ residue =>
      subst s
      obtain ⟨afterFirstValidator, firstValidatorEq,
          afterFirstValidatorOver, afterFirstValidatorLocal,
          afterFirstValidatorRun⟩ :=
        candidateAboveQTail_forced_prefix_to_endpoint primeProperty
          primeBound layout endpointBound firstValidatorEndpointDistinct
          endpointMembership QPositive (by omega) (by omega)
          (show 0 + (Q - 1) = Q - 1 by omega) afterNegativeOver
          afterNegativeLocal afterNegativeRun
      obtain ⟨afterSecondValidator, secondValidatorEq,
          afterSecondValidatorOver, afterSecondValidatorLocal,
          afterSecondValidatorRun⟩ :=
        generalFirstOutputS2Tail_forced_prefix_to_endpoint primeProperty
          primeBound layout endpointBound secondValidatorEndpointDistinct
          endpointMembership QPositive (by omega)
          (show 0 + (Q - 1) = Q - 1 by omega) afterFirstValidatorOver
          afterFirstValidatorLocal afterFirstValidatorRun
      exact False.elim
        (sEqualsTwoQSecondOutput_rejects_to_endpoint primeProperty primeBound
          layout endpointBound thirdValidatorEndpointDistinct
          endpointMembership QPositive (by omega) rBelowThreeQ
          (show 0 + (r - 2 * Q - 1) = r - 2 * Q - 1 by omega)
          afterSecondValidatorOver afterSecondValidatorLocal
          afterSecondValidatorRun)
  | secondRejectAbove twoQBelowS residue =>
      obtain ⟨afterFirstValidator, firstValidatorEq,
          afterFirstValidatorOver, afterFirstValidatorLocal,
          afterFirstValidatorRun⟩ :=
        candidateAboveQTail_forced_prefix_to_endpoint primeProperty
          primeBound layout endpointBound firstValidatorEndpointDistinct
          endpointMembership QPositive (by omega) sBelowR
          (show 0 + (Q - 1) = Q - 1 by omega) afterNegativeOver
          afterNegativeLocal afterNegativeRun
      exact False.elim (generalFirstOutput_rejects_to_endpoint primeProperty
        primeBound layout endpointBound secondValidatorEndpointDistinct
        endpointMembership QPositive (by omega) sPositive
        (by simp [ReservedDigit]) (by omega) (by omega)
        (fun position positionBelow =>
          generalFirstOutput_zero_residue prime Q r s position positionBelow
            (by omega) (by omega))
        (second_marker_s_above_twoQ prime Q r s QPositive twoQBelowS sBelowR)
        (fun position positionBelow =>
          generalFirstOutputZero_step prime secondValidator Q r s position
            primeProperty.1 QPositive (by omega) sPositive positionBelow
            (by omega) (by omega) (by omega) (by omega) (by omega)
            (by omega))
        (show 0 + (Q - 1) = Q - 1 by omega) afterFirstValidatorOver
        afterFirstValidatorLocal afterFirstValidatorRun)

theorem no_letter_from_target
    {prime phaseCount source target firstGuess secondGuess negativePhase
      firstValidator secondValidator thirdValidator : Nat}
    {digit : Int} {state : Vec2} {letter : PhysicalTemplate}
    (primeProperty : IsPrime prime) (primeBound : 6 * phaseCount < prime)
    (layout : PhaseLayout phaseCount source firstGuess secondGuess
      negativePhase firstValidator secondValidator thirdValidator)
    (targetBound : target < phaseCount)
    (targetNotActive : target ∉
      [source, firstGuess, secondGuess, negativePhase, firstValidator,
        secondValidator, thirdValidator])
    (membership : InPhaseAt prime target digit state)
    (letterMem : letter ∈ alphabet source target firstGuess secondGuess
      negativePhase firstValidator secondValidator thirdValidator)
    (outputLocal : LocalAt prime (letter.act prime state)) : False := by
  have forced := membership.physicalLetter_source_digit_unique primeProperty
    primeBound targetBound (letter_source_bound layout letterMem)
    (letter_reserved letterMem)
    (by simpa [PhysicalTemplate.act, PhysicalTemplate.matrix] using outputLocal)
  apply targetNotActive
  rw [forced.1]
  exact letter_source_mem_active letterMem

theorem word_from_target_eq_nil
    {prime phaseCount source target firstGuess secondGuess negativePhase
      firstValidator secondValidator thirdValidator : Nat}
    {digit : Int} {state : Vec2}
    (primeProperty : IsPrime prime) (primeBound : 6 * phaseCount < prime)
    (layout : PhaseLayout phaseCount source firstGuess secondGuess
      negativePhase firstValidator secondValidator thirdValidator)
    (targetBound : target < phaseCount)
    (targetNotActive : target ∉
      [source, firstGuess, secondGuess, negativePhase, firstValidator,
        secondValidator, thirdValidator])
    (membership : InPhaseAt prime target digit state)
    {word : List PhysicalTemplate}
    (wordOver : WordOver
      (alphabet source target firstGuess secondGuess negativePhase
        firstValidator secondValidator thirdValidator) word)
    (allLocal : AllStatesLocal prime word state) : word = [] := by
  cases word with
  | nil => rfl
  | cons letter tail =>
      exact False.elim (no_letter_from_target primeProperty primeBound layout
        targetBound targetNotActive membership (wordOver letter (by simp))
        allLocal.2.start)

private theorem active_ne_endpoint
    {source firstGuess secondGuess negativePhase firstValidator
      secondValidator thirdValidator endpointPhase : Nat}
    (endpointNotActive : endpointPhase ∉
      [source, firstGuess, secondGuess, negativePhase, firstValidator,
        secondValidator, thirdValidator])
    {phase : Nat}
    (phaseActive : phase ∈
      [source, firstGuess, secondGuess, negativePhase, firstValidator,
        secondValidator, thirdValidator]) :
    phase ≠ endpointPhase := by
  intro phaseEq
  apply endpointNotActive
  simpa [phaseEq] using phaseActive

/-- Exact unrestricted-word converse for the fourteen-letter projection
module. -/
theorem completedPath_unique
    {prime phaseCount source target firstGuess secondGuess negativePhase
      firstValidator secondValidator thirdValidator first : Nat}
    {endpointDigit : Int} {endpoint : Vec2}
    (primeProperty : IsPrime prime) (primeBound : 6 * phaseCount < prime)
    (layout : PhaseLayout phaseCount source firstGuess secondGuess
      negativePhase firstValidator secondValidator thirdValidator)
    (targetBound : target < phaseCount)
    (targetNotActive : target ∉
      [source, firstGuess, secondGuess, negativePhase, firstValidator,
        secondValidator, thirdValidator])
    (endpointMembership : InPhaseAt prime target endpointDigit endpoint)
    {word : List PhysicalTemplate}
    (wordOver : WordOver
      (alphabet source target firstGuess secondGuess negativePhase
        firstValidator secondValidator thirdValidator) word)
    (allLocal : AllStatesLocal prime word
      (phaseAffine source (twoFieldCode prime first (3 * first + 2))))
    (completeRun : SameLine
      (physicalWordAction prime word
        (phaseAffine source (twoFieldCode prime first (3 * first + 2))))
      endpoint) :
    word = acceptedWord source target firstGuess secondGuess negativePhase
      firstValidator secondValidator thirdValidator first := by
  obtain ⟨suffix, wordEq, suffixOver, suffixLocal, _⟩ :=
    completedPath_forces_accepted_prefix primeProperty primeBound layout
      targetBound
      (active_ne_endpoint targetNotActive (by simp))
      (active_ne_endpoint targetNotActive (by simp))
      (active_ne_endpoint targetNotActive (by simp))
      (active_ne_endpoint targetNotActive (by simp))
      (active_ne_endpoint targetNotActive (by simp))
      (active_ne_endpoint targetNotActive (by simp))
      (active_ne_endpoint targetNotActive (by simp))
      endpointMembership wordOver allLocal completeRun
  obtain ⟨targetDigit, targetMembership⟩ := unaryCode_inPhaseAt
    (phase := target) (counter := 3 * first + 2) primeProperty.1
  have suffixEq := word_from_target_eq_nil primeProperty primeBound layout
    targetBound targetNotActive targetMembership suffixOver suffixLocal
  subst suffix
  simpa using wordEq

/-- A projection-only word cannot end in a guarded phase outside both its
active controls and its declared target. -/
theorem completedPath_cannot_reach_foreign_phase
    {prime phaseCount source target firstGuess secondGuess negativePhase
      firstValidator secondValidator thirdValidator endpointPhase first : Nat}
    {endpointDigit : Int} {endpoint : Vec2}
    (primeProperty : IsPrime prime) (primeBound : 6 * phaseCount < prime)
    (layout : PhaseLayout phaseCount source firstGuess secondGuess
      negativePhase firstValidator secondValidator thirdValidator)
    (targetBound : target < phaseCount)
    (endpointBound : endpointPhase < phaseCount)
    (targetNotActive : target ∉
      [source, firstGuess, secondGuess, negativePhase, firstValidator,
        secondValidator, thirdValidator])
    (endpointNotActive : endpointPhase ∉
      [source, firstGuess, secondGuess, negativePhase, firstValidator,
        secondValidator, thirdValidator])
    (targetEndpointDistinct : target ≠ endpointPhase)
    (endpointMembership : InPhaseAt prime endpointPhase endpointDigit endpoint)
    {word : List PhysicalTemplate}
    (wordOver : WordOver
      (alphabet source target firstGuess secondGuess negativePhase
        firstValidator secondValidator thirdValidator) word)
    (allLocal : AllStatesLocal prime word
      (phaseAffine source (twoFieldCode prime first (3 * first + 2))))
    (completeRun : SameLine
      (physicalWordAction prime word
        (phaseAffine source (twoFieldCode prime first (3 * first + 2))))
      endpoint) : False := by
  obtain ⟨suffix, _, suffixOver, suffixLocal, suffixRun⟩ :=
    completedPath_forces_accepted_prefix primeProperty primeBound layout
      endpointBound
      (active_ne_endpoint endpointNotActive (by simp))
      (active_ne_endpoint endpointNotActive (by simp))
      (active_ne_endpoint endpointNotActive (by simp))
      (active_ne_endpoint endpointNotActive (by simp))
      (active_ne_endpoint endpointNotActive (by simp))
      (active_ne_endpoint endpointNotActive (by simp))
      (active_ne_endpoint endpointNotActive (by simp))
      endpointMembership wordOver allLocal completeRun
  obtain ⟨targetDigit, targetMembership⟩ := unaryCode_inPhaseAt
    (phase := target) (counter := 3 * first + 2) primeProperty.1
  have suffixEq := word_from_target_eq_nil primeProperty primeBound layout
    targetBound targetNotActive targetMembership suffixOver suffixLocal
  subst suffix
  have phaseEq := (targetMembership.unique primeProperty primeBound
    targetBound endpointBound endpointMembership (by
      simpa [physicalWordAction] using suffixRun)).1
  exact targetEndpointDistinct phaseEq

end Mortality.Compiler.ThreeProjectionModule
