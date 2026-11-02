import Mortality.Compiler.FivefoldFrontArithmetic
import Mortality.Compiler.IntegerFraction
import Mortality.Compiler.TernaryFrontArithmetic

/-!
# Exhaustive arithmetic for the fivefold front

For a unary input split as `n = first + guess`, put `Q = first + 1`.
The first two positive scans are the scans from `OddHalvingArithmetic`, and
the third and fourth use the numerator families from
`TernaryFrontArithmetic`.  This file continues that calculation through the
fifth positive scan, the marker-two scan, and the first subtraction scan.
-/

namespace Mortality.Compiler.FivefoldFrontClassification

open Mortality.Compiler
open Mortality.PeriodicCode
open Mortality.Compiler.UnaryArithmetic
open Mortality.Compiler.OddHalvingArithmetic
open Mortality.Compiler.TernaryFrontArithmetic
open Mortality.Compiler.IntegerFraction
open Mortality.Compiler.ContractionArithmetic

private theorem rat_pow_two_block (value : Rat) (exponent : Nat) :
    value ^ (2 * exponent) = (value ^ exponent) ^ 2 := by
  rw [show 2 * exponent = exponent + exponent by omega,
    Lean.Grind.Semiring.pow_add]
  grind

private theorem rat_pow_three_block (value : Rat) (exponent : Nat) :
    value ^ (3 * exponent) = (value ^ exponent) ^ 3 := by
  rw [show 3 * exponent = exponent + exponent + exponent by omega]
  repeat' rw [Lean.Grind.Semiring.pow_add]
  grind

private theorem rat_pow_four_block (value : Rat) (exponent : Nat) :
    value ^ (4 * exponent) = (value ^ exponent) ^ 4 := by
  rw [show 4 * exponent =
    exponent + exponent + exponent + exponent by omega]
  repeat' rw [Lean.Grind.Semiring.pow_add]
  grind

def fourthNumerator (base first guess deleted : Nat) : Int :=
  ternaryValidatorNumerator base first guess deleted

def fourthState (base first guess deleted : Nat) : Rat :=
  state (fourthNumerator base first guess deleted)
    (halfIntegerDenominator base first guess)

def fourthZeroCount (first guess : Nat) : Nat :=
  ternaryValidatorLength first guess

def fourthMarkerDigit (first guess : Nat) : Int :=
  ternaryValidatorMarkerDigit first guess

theorem fourthState_zero (base first guess : Nat) :
    fourthState base first guess 0 = thirdScanOutput base first guess := by
  simp [fourthState, fourthNumerator, thirdScanOutput, state]

theorem fourthState_local (base first guess deleted : Nat)
    (baseAtLeastTwo : 2 ≤ base) :
    LocalAt base (Vec2.affine (fourthState base first guess deleted)) := by
  exact state_local
    (halfIntegerDenominator_not_dvd base first guess baseAtLeastTwo)

theorem fourthState_sameLine_integer
    (base first guess deleted : Nat) (baseAtLeastTwo : 2 ≤ base) :
    SameLine (Vec2.affine (fourthState base first guess deleted))
      (integerVector (fourthNumerator base first guess deleted)
        (halfIntegerDenominator base first guess)) := by
  exact sameLine_integer (denominator_nonzero_of_not_dvd
    (halfIntegerDenominator_not_dvd base first guess baseAtLeastTwo))

theorem fourthNumerator_step
    (base first guess deleted : Nat)
    (deletedBelow : deleted < fourthZeroCount first guess) :
    fourthNumerator base first guess deleted =
      (base : Int) * fourthNumerator base first guess (deleted + 1) := by
  unfold fourthZeroCount ternaryValidatorLength at deletedBelow
  unfold fourthNumerator ternaryValidatorNumerator
  by_cases longCase : first < guess - 1
  · simp only [if_pos longCase] at deletedBelow ⊢
    have belowFirst : deleted < first := Nat.lt_of_lt_of_le deletedBelow
      (Nat.min_le_left _ _)
    have belowGap : deleted < guess - first - 2 :=
      Nat.lt_of_lt_of_le deletedBelow (Nat.min_le_right _ _)
    have gapExponent : guess - first - 2 - deleted =
        guess - first - 2 - (deleted + 1) + 1 := by omega
    have guessExponent : guess - 1 - deleted =
        guess - 1 - (deleted + 1) + 1 := by omega
    have combinedExponent : first + guess - deleted =
        first + guess - (deleted + 1) + 1 := by omega
    have firstExponent : first - deleted =
        first - (deleted + 1) + 1 := by omega
    rw [gapExponent, guessExponent, combinedExponent, firstExponent]
    simp only [Int.pow_succ]
    grind
  · simp only [if_neg longCase] at deletedBelow ⊢
    have belowDifference : deleted < first - guess := deletedBelow
    have firstExponent : first - deleted =
        first - (deleted + 1) + 1 := by omega
    have differenceExponent : first - guess - deleted =
        first - guess - (deleted + 1) + 1 := by omega
    have combinedExponent : first + guess - deleted =
        first + guess - (deleted + 1) + 1 := by omega
    rw [firstExponent, differenceExponent, combinedExponent]
    simp only [Int.pow_succ]
    grind

theorem fourthState_delete_zero
    (base first guess deleted : Nat) (baseAtLeastTwo : 2 ≤ base)
    (deletedBelow : deleted < fourthZeroCount first guess) :
    deleteDigit (base : Rat) 0 (fourthState base first guess deleted) =
      fourthState base first guess (deleted + 1) := by
  apply deleteZero_eq base _ _ _ (by omega)
    (denominator_nonzero_of_not_dvd
      (halfIntegerDenominator_not_dvd base first guess baseAtLeastTwo))
  exact fourthNumerator_step base first guess deleted deletedBelow

theorem fourthState_zero_residue
    (base first guess deleted : Nat)
    (deletedBelow : deleted < fourthZeroCount first guess) :
    (base : Int) ∣ fourthNumerator base first guess deleted := by
  exact ⟨fourthNumerator base first guess (deleted + 1),
    fourthNumerator_step base first guess deleted deletedBelow⟩

theorem fourthState_marker_residue
    (base first guess : Nat) (guessPositive : 0 < guess)
    (thirdMarkerAccepted : first ≠ guess - 1) :
    (base : Int) ∣
      fourthNumerator base first guess (fourthZeroCount first guess) -
        fourthMarkerDigit first guess *
          halfIntegerDenominator base first guess := by
  have old := ternaryValidatorState_marker_residue base first guess
    guessPositive thirdMarkerAccepted
  rcases old with ⟨factor, factorEq⟩
  refine ⟨factor + fourthMarkerDigit first guess *
      ternaryCandidateNumerator base first guess, ?_⟩
  unfold fourthNumerator fourthZeroCount fourthMarkerDigit
  unfold ternaryCandidateDenominator at factorEq
  calc
    ternaryValidatorNumerator base first guess
          (ternaryValidatorLength first guess) -
        ternaryValidatorMarkerDigit first guess *
          halfIntegerDenominator base first guess =
      (ternaryValidatorNumerator base first guess
          (ternaryValidatorLength first guess) -
        ternaryValidatorMarkerDigit first guess *
          (halfIntegerDenominator base first guess +
            (base : Int) * ternaryCandidateNumerator base first guess)) +
        ternaryValidatorMarkerDigit first guess *
          ((base : Int) * ternaryCandidateNumerator base first guess) := by
            grind
    _ = (base : Int) * factor +
        ternaryValidatorMarkerDigit first guess *
          ((base : Int) * ternaryCandidateNumerator base first guess) := by
      rw [factorEq]
    _ = (base : Int) *
        (factor + ternaryValidatorMarkerDigit first guess *
          ternaryCandidateNumerator base first guess) := by grind

theorem fourthMarkerDigit_eq_two_iff (first guess : Nat) :
    fourthMarkerDigit first guess = 2 ↔
      guess = 2 * (first + 1) := by
  simp [fourthMarkerDigit, ternaryValidatorMarkerDigit]
  omega

def smallFourthOutputNumerator (base first guess : Nat) : Int :=
  (base : Int) ^ first + 2 * (base : Int) ^ (guess - 1) +
    (base : Int) ^ (2 * guess - 1) +
    (base : Int) ^ (first + guess)

def middleFourthOutputNumerator (base first guess : Nat) : Int :=
  (base : Int) ^ (2 * (first + 1) - guess - 1) +
    2 * (base : Int) ^ first +
    (base : Int) ^ (2 * (first + 1) - 1) +
    (base : Int) ^ (first + guess)

def largeFourthOutputNumerator (base first guess : Nat) : Int :=
  (base : Int) ^ first +
    (base : Int) ^ (guess - 2 * (first + 1) - 1) +
    (base : Int) ^ (guess - (first + 1) - 1) +
    (base : Int) ^ (guess - 1) +
    (base : Int) ^ (first + guess)

def smallFourthOutput (base first guess : Nat) : Rat :=
  state (smallFourthOutputNumerator base first guess)
    (halfIntegerDenominator base first guess)

def middleFourthOutput (base first guess : Nat) : Rat :=
  state (middleFourthOutputNumerator base first guess)
    (halfIntegerDenominator base first guess)

def largeFourthOutput (base first guess : Nat) : Rat :=
  state (largeFourthOutputNumerator base first guess)
    (halfIntegerDenominator base first guess)

theorem fourth_small_marker_difference
    (base first guess : Nat) (guessPositive : 0 < guess)
    (guessBelowQ : guess < first + 1) :
    fourthNumerator base first guess (fourthZeroCount first guess) -
        halfIntegerDenominator base first guess =
      (base : Int) * smallFourthOutputNumerator base first guess := by
  have shortCase : ¬ first < guess - 1 := by omega
  have countEq : fourthZeroCount first guess = first - guess := by
    simp [fourthZeroCount, ternaryValidatorLength, shortCase]
  have firstPower : (base : Int) ^ (first + 1) =
      (base : Int) ^ first * (base : Int) := by rw [Int.pow_succ]
  have guessPower : (base : Int) ^ guess =
      (base : Int) ^ (guess - 1) * (base : Int) := by
    calc
      (base : Int) ^ guess = (base : Int) ^ (guess - 1 + 1) := by
        congr 1 <;> omega
      _ = _ := by rw [Int.pow_succ]
  have twiceGuessPower : (base : Int) ^ (2 * guess) =
      (base : Int) ^ (2 * guess - 1) * (base : Int) := by
    calc
      (base : Int) ^ (2 * guess) =
          (base : Int) ^ (2 * guess - 1 + 1) := by congr 1 <;> omega
      _ = _ := by rw [Int.pow_succ]
  have combinedPower : (base : Int) ^ (first + guess + 1) =
      (base : Int) ^ (first + guess) * (base : Int) := by
    rw [Int.pow_succ]
  unfold fourthNumerator ternaryValidatorNumerator
    halfIntegerDenominator smallFourthOutputNumerator
  rw [if_neg shortCase, countEq]
  rw [show first - (first - guess) = guess by omega,
    show first - guess - (first - guess) = 0 by omega,
    show first + guess - (first - guess) = 2 * guess by omega]
  simp only [Int.pow_zero]
  rw [firstPower, guessPower, twiceGuessPower, combinedPower]
  grind

theorem fourth_middle_marker_difference
    (base first guess : Nat) (QBelowGuess : first + 1 < guess)
    (guessBelowTwoQ : guess < 2 * (first + 1)) :
    fourthNumerator base first guess (fourthZeroCount first guess) -
        halfIntegerDenominator base first guess =
      (base : Int) * middleFourthOutputNumerator base first guess := by
  have longCase : first < guess - 1 := by omega
  have gapBelow : guess - first - 2 < first := by omega
  have countEq : fourthZeroCount first guess = guess - first - 2 := by
    simp [fourthZeroCount, ternaryValidatorLength, longCase,
      Nat.min_eq_right (Nat.le_of_lt gapBelow)]
  have firstPower : (base : Int) ^ (first + 1) =
      (base : Int) ^ first * (base : Int) := by rw [Int.pow_succ]
  have leadingPower : (base : Int) ^ (2 * (first + 1) - guess) =
      (base : Int) ^ (2 * (first + 1) - guess - 1) *
        (base : Int) := by
    calc
      (base : Int) ^ (2 * (first + 1) - guess) =
          (base : Int) ^ (2 * (first + 1) - guess - 1 + 1) := by
            congr 1 <;> omega
      _ = _ := by rw [Int.pow_succ]
  have twiceQPower : (base : Int) ^ (2 * (first + 1)) =
      (base : Int) ^ (2 * (first + 1) - 1) * (base : Int) := by
    calc
      (base : Int) ^ (2 * (first + 1)) =
          (base : Int) ^ (2 * (first + 1) - 1 + 1) := by
            congr 1 <;> omega
      _ = _ := by rw [Int.pow_succ]
  have combinedPower : (base : Int) ^ (first + guess + 1) =
      (base : Int) ^ (first + guess) * (base : Int) := by
    rw [Int.pow_succ]
  unfold fourthNumerator ternaryValidatorNumerator
    halfIntegerDenominator middleFourthOutputNumerator
  rw [if_pos longCase, countEq]
  rw [show guess - first - 2 - (guess - first - 2) = 0 by omega,
    show guess - 1 - (guess - first - 2) = first + 1 by omega,
    show first + guess - (guess - first - 2) = 2 * (first + 1) by omega,
    show first - (guess - first - 2) = 2 * (first + 1) - guess by omega]
  simp only [Int.pow_zero]
  rw [firstPower, leadingPower, twiceQPower, combinedPower]
  grind

theorem fourth_large_marker_difference
    (base first guess : Nat) (twoQBelowGuess : 2 * (first + 1) < guess) :
    fourthNumerator base first guess (fourthZeroCount first guess) -
        halfIntegerDenominator base first guess =
      (base : Int) * largeFourthOutputNumerator base first guess := by
  have longCase : first < guess - 1 := by omega
  have firstBelowGap : first < guess - first - 2 := by omega
  have countEq : fourthZeroCount first guess = first := by
    simp [fourthZeroCount, ternaryValidatorLength, longCase,
      Nat.min_eq_left (Nat.le_of_lt firstBelowGap)]
  have firstPower : (base : Int) ^ (first + 1) =
      (base : Int) ^ first * (base : Int) := by rw [Int.pow_succ]
  have firstGapPower : (base : Int) ^ (guess - 2 * (first + 1)) =
      (base : Int) ^ (guess - 2 * (first + 1) - 1) *
        (base : Int) := by
    calc
      (base : Int) ^ (guess - 2 * (first + 1)) =
          (base : Int) ^ (guess - 2 * (first + 1) - 1 + 1) := by
            congr 1 <;> omega
      _ = _ := by rw [Int.pow_succ]
  have secondGapPower : (base : Int) ^ (guess - (first + 1)) =
      (base : Int) ^ (guess - (first + 1) - 1) *
        (base : Int) := by
    calc
      (base : Int) ^ (guess - (first + 1)) =
          (base : Int) ^ (guess - (first + 1) - 1 + 1) := by
            congr 1 <;> omega
      _ = _ := by rw [Int.pow_succ]
  have guessPower : (base : Int) ^ guess =
      (base : Int) ^ (guess - 1) * (base : Int) := by
    calc
      (base : Int) ^ guess = (base : Int) ^ (guess - 1 + 1) := by
        congr 1 <;> omega
      _ = _ := by rw [Int.pow_succ]
  have combinedPower : (base : Int) ^ (first + guess + 1) =
      (base : Int) ^ (first + guess) * (base : Int) := by
    rw [Int.pow_succ]
  unfold fourthNumerator ternaryValidatorNumerator
    halfIntegerDenominator largeFourthOutputNumerator
  rw [if_pos longCase, countEq]
  rw [show guess - first - 2 - first = guess - 2 * (first + 1) by omega,
    show guess - 1 - first = guess - (first + 1) by omega,
    show first + guess - first = guess by omega, Nat.sub_self]
  simp only [Int.pow_zero]
  rw [firstPower, firstGapPower, secondGapPower, guessPower,
    combinedPower]
  grind

theorem fourth_small_delete_marker
    (base first guess : Nat) (baseAtLeastTwo : 2 ≤ base)
    (guessPositive : 0 < guess) (guessBelowQ : guess < first + 1) :
    deleteDigit (base : Rat) 1
        (fourthState base first guess (fourthZeroCount first guess)) =
      smallFourthOutput base first guess := by
  exact deleteDigit_eq base 1 _ _ _ (by omega)
    (denominator_nonzero_of_not_dvd
      (halfIntegerDenominator_not_dvd base first guess baseAtLeastTwo))
    (by simpa using (fourth_small_marker_difference base first guess
      guessPositive guessBelowQ))

theorem fourth_middle_delete_marker
    (base first guess : Nat) (baseAtLeastTwo : 2 ≤ base)
    (QBelowGuess : first + 1 < guess)
    (guessBelowTwoQ : guess < 2 * (first + 1)) :
    deleteDigit (base : Rat) 1
        (fourthState base first guess (fourthZeroCount first guess)) =
      middleFourthOutput base first guess := by
  exact deleteDigit_eq base 1 _ _ _ (by omega)
    (denominator_nonzero_of_not_dvd
      (halfIntegerDenominator_not_dvd base first guess baseAtLeastTwo))
    (by simpa using (fourth_middle_marker_difference base first guess
      QBelowGuess guessBelowTwoQ))

theorem fourth_large_delete_marker
    (base first guess : Nat) (baseAtLeastTwo : 2 ≤ base)
    (twoQBelowGuess : 2 * (first + 1) < guess) :
    deleteDigit (base : Rat) 1
        (fourthState base first guess (fourthZeroCount first guess)) =
      largeFourthOutput base first guess := by
  exact deleteDigit_eq base 1 _ _ _ (by omega)
    (denominator_nonzero_of_not_dvd
      (halfIntegerDenominator_not_dvd base first guess baseAtLeastTwo))
    (by simpa using (fourth_large_marker_difference base first guess
      twoQBelowGuess))

def smallFifthNumerator (base first guess deleted : Nat) : Int :=
  (base : Int) ^ (first - deleted) +
    2 * (base : Int) ^ (guess - 1 - deleted) +
    (base : Int) ^ (2 * guess - 1 - deleted) +
    (base : Int) ^ (first + guess - deleted)

def middleFifthNumerator (base first guess deleted : Nat) : Int :=
  (base : Int) ^ (2 * (first + 1) - guess - 1 - deleted) +
    2 * (base : Int) ^ (first - deleted) +
    (base : Int) ^ (2 * (first + 1) - 1 - deleted) +
    (base : Int) ^ (first + guess - deleted)

def largeFifthNumerator (base first guess deleted : Nat) : Int :=
  (base : Int) ^ (first - deleted) +
    (base : Int) ^ (guess - 2 * (first + 1) - 1 - deleted) +
    (base : Int) ^ (guess - (first + 1) - 1 - deleted) +
    (base : Int) ^ (guess - 1 - deleted) +
    (base : Int) ^ (first + guess - deleted)

def smallFifthState (base first guess deleted : Nat) : Rat :=
  state (smallFifthNumerator base first guess deleted)
    (halfIntegerDenominator base first guess)

def middleFifthState (base first guess deleted : Nat) : Rat :=
  state (middleFifthNumerator base first guess deleted)
    (halfIntegerDenominator base first guess)

def largeFifthState (base first guess deleted : Nat) : Rat :=
  state (largeFifthNumerator base first guess deleted)
    (halfIntegerDenominator base first guess)

def smallFifthZeroCount (_first guess : Nat) : Nat := guess - 1

def middleFifthZeroCount (first guess : Nat) : Nat :=
  2 * (first + 1) - guess - 1

def largeFifthZeroCount (first guess : Nat) : Nat :=
  min first (guess - 2 * (first + 1) - 1)

def largeFifthMarkerDigit (first guess : Nat) : Int :=
  if guess = 3 * (first + 1) then 2 else 1

theorem smallFifthState_zero (base first guess : Nat) :
    smallFifthState base first guess 0 =
      smallFourthOutput base first guess := by
  simp [smallFifthState, smallFifthNumerator, smallFourthOutput,
    smallFourthOutputNumerator]

theorem middleFifthState_zero (base first guess : Nat) :
    middleFifthState base first guess 0 =
      middleFourthOutput base first guess := by
  simp [middleFifthState, middleFifthNumerator, middleFourthOutput,
    middleFourthOutputNumerator]

theorem largeFifthState_zero (base first guess : Nat) :
    largeFifthState base first guess 0 =
      largeFourthOutput base first guess := by
  simp [largeFifthState, largeFifthNumerator, largeFourthOutput,
    largeFourthOutputNumerator]

theorem smallFifthState_local (base first guess deleted : Nat)
    (baseAtLeastTwo : 2 ≤ base) :
    LocalAt base
      (Vec2.affine (smallFifthState base first guess deleted)) := by
  exact state_local
    (halfIntegerDenominator_not_dvd base first guess baseAtLeastTwo)

theorem middleFifthState_local (base first guess deleted : Nat)
    (baseAtLeastTwo : 2 ≤ base) :
    LocalAt base
      (Vec2.affine (middleFifthState base first guess deleted)) := by
  exact state_local
    (halfIntegerDenominator_not_dvd base first guess baseAtLeastTwo)

theorem largeFifthState_local (base first guess deleted : Nat)
    (baseAtLeastTwo : 2 ≤ base) :
    LocalAt base
      (Vec2.affine (largeFifthState base first guess deleted)) := by
  exact state_local
    (halfIntegerDenominator_not_dvd base first guess baseAtLeastTwo)

theorem smallFifthState_sameLine_integer
    (base first guess deleted : Nat) (baseAtLeastTwo : 2 ≤ base) :
    SameLine (Vec2.affine (smallFifthState base first guess deleted))
      (integerVector (smallFifthNumerator base first guess deleted)
        (halfIntegerDenominator base first guess)) := by
  exact sameLine_integer (denominator_nonzero_of_not_dvd
    (halfIntegerDenominator_not_dvd base first guess baseAtLeastTwo))

theorem middleFifthState_sameLine_integer
    (base first guess deleted : Nat) (baseAtLeastTwo : 2 ≤ base) :
    SameLine (Vec2.affine (middleFifthState base first guess deleted))
      (integerVector (middleFifthNumerator base first guess deleted)
        (halfIntegerDenominator base first guess)) := by
  exact sameLine_integer (denominator_nonzero_of_not_dvd
    (halfIntegerDenominator_not_dvd base first guess baseAtLeastTwo))

theorem largeFifthState_sameLine_integer
    (base first guess deleted : Nat) (baseAtLeastTwo : 2 ≤ base) :
    SameLine (Vec2.affine (largeFifthState base first guess deleted))
      (integerVector (largeFifthNumerator base first guess deleted)
        (halfIntegerDenominator base first guess)) := by
  exact sameLine_integer (denominator_nonzero_of_not_dvd
    (halfIntegerDenominator_not_dvd base first guess baseAtLeastTwo))

theorem smallFifthNumerator_step
    (base first guess deleted : Nat) (guessPositive : 0 < guess)
    (guessBelowQ : guess < first + 1)
    (deletedBelow : deleted < smallFifthZeroCount first guess) :
    smallFifthNumerator base first guess deleted =
      (base : Int) * smallFifthNumerator base first guess (deleted + 1) := by
  have firstExponent : first - deleted =
      first - (deleted + 1) + 1 := by
    unfold smallFifthZeroCount at deletedBelow
    omega
  have guessExponent : guess - 1 - deleted =
      guess - 1 - (deleted + 1) + 1 := by
    unfold smallFifthZeroCount at deletedBelow
    omega
  have twiceGuessExponent : 2 * guess - 1 - deleted =
      2 * guess - 1 - (deleted + 1) + 1 := by
    unfold smallFifthZeroCount at deletedBelow
    omega
  have combinedExponent : first + guess - deleted =
      first + guess - (deleted + 1) + 1 := by
    unfold smallFifthZeroCount at deletedBelow
    omega
  unfold smallFifthNumerator
  rw [firstExponent, guessExponent, twiceGuessExponent, combinedExponent]
  simp only [Int.pow_succ]
  grind

theorem middleFifthNumerator_step
    (base first guess deleted : Nat)
    (QBelowGuess : first + 1 < guess)
    (guessBelowTwoQ : guess < 2 * (first + 1))
    (deletedBelow : deleted < middleFifthZeroCount first guess) :
    middleFifthNumerator base first guess deleted =
      (base : Int) * middleFifthNumerator base first guess (deleted + 1) := by
  have leadingExponent : 2 * (first + 1) - guess - 1 - deleted =
      2 * (first + 1) - guess - 1 - (deleted + 1) + 1 := by
    unfold middleFifthZeroCount at deletedBelow
    omega
  have firstExponent : first - deleted =
      first - (deleted + 1) + 1 := by
    unfold middleFifthZeroCount at deletedBelow
    omega
  have twiceQExponent : 2 * (first + 1) - 1 - deleted =
      2 * (first + 1) - 1 - (deleted + 1) + 1 := by
    unfold middleFifthZeroCount at deletedBelow
    omega
  have combinedExponent : first + guess - deleted =
      first + guess - (deleted + 1) + 1 := by
    unfold middleFifthZeroCount at deletedBelow
    omega
  unfold middleFifthNumerator
  rw [leadingExponent, firstExponent, twiceQExponent, combinedExponent]
  simp only [Int.pow_succ]
  grind

theorem largeFifthNumerator_step
    (base first guess deleted : Nat)
    (twoQBelowGuess : 2 * (first + 1) < guess)
    (deletedBelow : deleted < largeFifthZeroCount first guess) :
    largeFifthNumerator base first guess deleted =
      (base : Int) * largeFifthNumerator base first guess (deleted + 1) := by
  have belowFirst : deleted < first := Nat.lt_of_lt_of_le deletedBelow
    (Nat.min_le_left _ _)
  have belowGap : deleted < guess - 2 * (first + 1) - 1 :=
    Nat.lt_of_lt_of_le deletedBelow (Nat.min_le_right _ _)
  have firstExponent : first - deleted =
      first - (deleted + 1) + 1 := by omega
  have firstGapExponent : guess - 2 * (first + 1) - 1 - deleted =
      guess - 2 * (first + 1) - 1 - (deleted + 1) + 1 := by omega
  have secondGapExponent : guess - (first + 1) - 1 - deleted =
      guess - (first + 1) - 1 - (deleted + 1) + 1 := by omega
  have guessExponent : guess - 1 - deleted =
      guess - 1 - (deleted + 1) + 1 := by omega
  have combinedExponent : first + guess - deleted =
      first + guess - (deleted + 1) + 1 := by omega
  unfold largeFifthNumerator
  rw [firstExponent, firstGapExponent, secondGapExponent, guessExponent,
    combinedExponent]
  simp only [Int.pow_succ]
  grind

theorem smallFifthState_delete_zero
    (base first guess deleted : Nat) (baseAtLeastTwo : 2 ≤ base)
    (guessPositive : 0 < guess) (guessBelowQ : guess < first + 1)
    (deletedBelow : deleted < smallFifthZeroCount first guess) :
    deleteDigit (base : Rat) 0 (smallFifthState base first guess deleted) =
      smallFifthState base first guess (deleted + 1) := by
  apply deleteZero_eq base _ _ _ (by omega)
    (denominator_nonzero_of_not_dvd
      (halfIntegerDenominator_not_dvd base first guess baseAtLeastTwo))
  exact smallFifthNumerator_step base first guess deleted guessPositive
    guessBelowQ deletedBelow

theorem middleFifthState_delete_zero
    (base first guess deleted : Nat) (baseAtLeastTwo : 2 ≤ base)
    (QBelowGuess : first + 1 < guess)
    (guessBelowTwoQ : guess < 2 * (first + 1))
    (deletedBelow : deleted < middleFifthZeroCount first guess) :
    deleteDigit (base : Rat) 0 (middleFifthState base first guess deleted) =
      middleFifthState base first guess (deleted + 1) := by
  apply deleteZero_eq base _ _ _ (by omega)
    (denominator_nonzero_of_not_dvd
      (halfIntegerDenominator_not_dvd base first guess baseAtLeastTwo))
  exact middleFifthNumerator_step base first guess deleted QBelowGuess
    guessBelowTwoQ deletedBelow

theorem largeFifthState_delete_zero
    (base first guess deleted : Nat) (baseAtLeastTwo : 2 ≤ base)
    (twoQBelowGuess : 2 * (first + 1) < guess)
    (deletedBelow : deleted < largeFifthZeroCount first guess) :
    deleteDigit (base : Rat) 0 (largeFifthState base first guess deleted) =
      largeFifthState base first guess (deleted + 1) := by
  apply deleteZero_eq base _ _ _ (by omega)
    (denominator_nonzero_of_not_dvd
      (halfIntegerDenominator_not_dvd base first guess baseAtLeastTwo))
  exact largeFifthNumerator_step base first guess deleted twoQBelowGuess
    deletedBelow

theorem halfIntegerDenominator_one_residue
    (base first guess : Nat) :
    (base : Int) ∣ 1 - halfIntegerDenominator base first guess := by
  rcases base_dvd_positive_power base (first + guess + 1) (by omega) with
    ⟨combinedFactor, combinedEq⟩
  rcases base_dvd_positive_power base (first + 1) (by omega) with
    ⟨firstFactor, firstEq⟩
  refine ⟨combinedFactor + firstFactor, ?_⟩
  unfold halfIntegerDenominator
  rw [combinedEq, firstEq]
  grind

theorem smallFifth_marker_residue_two
    (base first guess : Nat) (guessPositive : 0 < guess)
    (guessBelowQ : guess < first + 1) :
    (base : Int) ∣
      smallFifthNumerator base first guess
          (smallFifthZeroCount first guess) -
        2 * halfIntegerDenominator base first guess := by
  have firstExponent : 0 < first - (guess - 1) := by omega
  have twiceGuessExponent : 0 < 2 * guess - 1 - (guess - 1) := by omega
  have combinedExponent : 0 < first + guess - (guess - 1) := by omega
  rcases base_dvd_positive_power base (first - (guess - 1)) firstExponent
      with ⟨firstFactor, firstEq⟩
  rcases base_dvd_positive_power base
      (2 * guess - 1 - (guess - 1)) twiceGuessExponent with
    ⟨twiceGuessFactor, twiceGuessEq⟩
  rcases base_dvd_positive_power base
      (first + guess - (guess - 1)) combinedExponent with
    ⟨combinedFactor, combinedEq⟩
  rcases halfIntegerDenominator_one_residue base first guess with
    ⟨denominatorFactor, denominatorEq⟩
  refine ⟨firstFactor + twiceGuessFactor + combinedFactor +
      2 * denominatorFactor, ?_⟩
  unfold smallFifthZeroCount smallFifthNumerator
  rw [show guess - 1 - (guess - 1) = 0 by omega]
  simp only [Int.pow_zero]
  rw [firstEq, twiceGuessEq, combinedEq]
  calc
    (base : Int) * firstFactor + 2 +
          (base : Int) * twiceGuessFactor +
          (base : Int) * combinedFactor -
        2 * halfIntegerDenominator base first guess =
      (base : Int) * firstFactor +
          (base : Int) * twiceGuessFactor +
          (base : Int) * combinedFactor +
        2 * (1 - halfIntegerDenominator base first guess) := by grind
    _ = _ := by rw [denominatorEq]; grind

theorem middleFifth_marker_residue_one
    (base first guess : Nat) (QBelowGuess : first + 1 < guess)
    (guessBelowTwoQ : guess < 2 * (first + 1)) :
    (base : Int) ∣
      middleFifthNumerator base first guess
          (middleFifthZeroCount first guess) -
        halfIntegerDenominator base first guess := by
  let count := middleFifthZeroCount first guess
  have firstExponent : 0 < first - count := by
    dsimp [count, middleFifthZeroCount]
    omega
  have twiceQExponent : 0 < 2 * (first + 1) - 1 - count := by
    dsimp [count, middleFifthZeroCount]
    omega
  have combinedExponent : 0 < first + guess - count := by
    dsimp [count, middleFifthZeroCount]
    omega
  rcases base_dvd_positive_power base (first - count) firstExponent with
    ⟨firstFactor, firstEq⟩
  rcases base_dvd_positive_power base
      (2 * (first + 1) - 1 - count) twiceQExponent with
    ⟨twiceQFactor, twiceQEq⟩
  rcases base_dvd_positive_power base
      (first + guess - count) combinedExponent with
    ⟨combinedFactor, combinedEq⟩
  rcases halfIntegerDenominator_one_residue base first guess with
    ⟨denominatorFactor, denominatorEq⟩
  refine ⟨2 * firstFactor + twiceQFactor + combinedFactor +
      denominatorFactor, ?_⟩
  have leadingZero :
      2 * (first + 1) - guess - 1 - count = 0 := by
    dsimp [count, middleFifthZeroCount]
    omega
  unfold middleFifthNumerator
  rw [leadingZero]
  simp only [Int.pow_zero]
  rw [firstEq, twiceQEq, combinedEq]
  calc
    1 + 2 * ((base : Int) * firstFactor) +
          (base : Int) * twiceQFactor + (base : Int) * combinedFactor -
        halfIntegerDenominator base first guess =
      2 * ((base : Int) * firstFactor) +
          (base : Int) * twiceQFactor + (base : Int) * combinedFactor +
        (1 - halfIntegerDenominator base first guess) := by grind
    _ = _ := by rw [denominatorEq]; grind

theorem largeFifth_marker_residue
    (base first guess : Nat) (twoQBelowGuess : 2 * (first + 1) < guess) :
    (base : Int) ∣
      largeFifthNumerator base first guess
          (largeFifthZeroCount first guess) -
        largeFifthMarkerDigit first guess *
          halfIntegerDenominator base first guess := by
  let gap := guess - 2 * (first + 1) - 1
  have countEq : largeFifthZeroCount first guess = min first gap := rfl
  by_cases equalLeads : first = gap
  · have guessEq : guess = 3 * (first + 1) := by
      dsimp [gap] at equalLeads
      omega
    have countFirst : largeFifthZeroCount first guess = first := by
      rw [countEq, equalLeads, Nat.min_self]
    have secondGapPositive : 0 < guess - (first + 1) - 1 - first := by omega
    have guessPositive : 0 < guess - 1 - first := by omega
    have combinedPositive : 0 < first + guess - first := by omega
    rcases base_dvd_positive_power base
        (guess - (first + 1) - 1 - first) secondGapPositive with
      ⟨secondGapFactor, secondGapEq⟩
    rcases base_dvd_positive_power base (guess - 1 - first) guessPositive
        with ⟨guessFactor, guessPowerEq⟩
    rcases base_dvd_positive_power base (first + guess - first)
        combinedPositive with ⟨combinedFactor, combinedEq⟩
    rcases halfIntegerDenominator_one_residue base first guess with
      ⟨denominatorFactor, denominatorEq⟩
    refine ⟨secondGapFactor + guessFactor + combinedFactor +
        2 * denominatorFactor, ?_⟩
    unfold largeFifthNumerator largeFifthMarkerDigit
    rw [if_pos guessEq, countFirst, Nat.sub_self]
    have firstGapZero :
        guess - 2 * (first + 1) - 1 - first = 0 := by omega
    rw [firstGapZero]
    simp only [Int.pow_zero]
    rw [secondGapEq, guessPowerEq, combinedEq]
    calc
      1 + 1 + (base : Int) * secondGapFactor +
            (base : Int) * guessFactor + (base : Int) * combinedFactor -
          2 * halfIntegerDenominator base first guess =
        (base : Int) * secondGapFactor +
            (base : Int) * guessFactor + (base : Int) * combinedFactor +
          2 * (1 - halfIntegerDenominator base first guess) := by grind
      _ = _ := by rw [denominatorEq]; grind
  · have guessNe : guess ≠ 3 * (first + 1) := by
      intro guessEq
      apply equalLeads
      dsimp [gap]
      omega
    rcases Nat.lt_or_gt_of_ne equalLeads with firstBelow | gapBelow
    · have countFirst : largeFifthZeroCount first guess = first := by
        rw [countEq, Nat.min_eq_left (Nat.le_of_lt firstBelow)]
      have firstGapPositive :
          0 < guess - 2 * (first + 1) - 1 - first := by
        dsimp [gap] at firstBelow
        omega
      have secondGapPositive :
          0 < guess - (first + 1) - 1 - first := by omega
      have guessPositive : 0 < guess - 1 - first := by omega
      have combinedPositive : 0 < first + guess - first := by omega
      rcases base_dvd_positive_power base _ firstGapPositive with
        ⟨firstGapFactor, firstGapEq⟩
      rcases base_dvd_positive_power base _ secondGapPositive with
        ⟨secondGapFactor, secondGapEq⟩
      rcases base_dvd_positive_power base _ guessPositive with
        ⟨guessFactor, guessPowerEq⟩
      rcases base_dvd_positive_power base _ combinedPositive with
        ⟨combinedFactor, combinedEq⟩
      rcases halfIntegerDenominator_one_residue base first guess with
        ⟨denominatorFactor, denominatorEq⟩
      refine ⟨firstGapFactor + secondGapFactor + guessFactor +
          combinedFactor + denominatorFactor, ?_⟩
      unfold largeFifthNumerator largeFifthMarkerDigit
      rw [if_neg guessNe, countFirst, Nat.sub_self]
      simp only [Int.pow_zero]
      rw [firstGapEq, secondGapEq, guessPowerEq, combinedEq]
      simp only [Int.one_mul]
      calc
        1 + (base : Int) * firstGapFactor +
              (base : Int) * secondGapFactor +
              (base : Int) * guessFactor +
              (base : Int) * combinedFactor -
            halfIntegerDenominator base first guess =
          (base : Int) * firstGapFactor +
              (base : Int) * secondGapFactor +
              (base : Int) * guessFactor +
              (base : Int) * combinedFactor +
            (1 - halfIntegerDenominator base first guess) := by grind
        _ = _ := by rw [denominatorEq]; grind
    · have countGap : largeFifthZeroCount first guess = gap := by
        rw [countEq, Nat.min_eq_right (Nat.le_of_lt gapBelow)]
      have firstPositive : 0 < first - gap := by omega
      have secondGapPositive :
          0 < guess - (first + 1) - 1 - gap := by
        dsimp [gap]
        omega
      have guessPositive : 0 < guess - 1 - gap := by
        dsimp [gap]
        omega
      have combinedPositive : 0 < first + guess - gap := by
        dsimp [gap]
        omega
      rcases base_dvd_positive_power base _ firstPositive with
        ⟨firstFactor, firstEq⟩
      rcases base_dvd_positive_power base _ secondGapPositive with
        ⟨secondGapFactor, secondGapEq⟩
      rcases base_dvd_positive_power base _ guessPositive with
        ⟨guessFactor, guessPowerEq⟩
      rcases base_dvd_positive_power base _ combinedPositive with
        ⟨combinedFactor, combinedEq⟩
      rcases halfIntegerDenominator_one_residue base first guess with
        ⟨denominatorFactor, denominatorEq⟩
      refine ⟨firstFactor + secondGapFactor + guessFactor +
          combinedFactor + denominatorFactor, ?_⟩
      unfold largeFifthNumerator largeFifthMarkerDigit
      rw [if_neg guessNe, countGap]
      have gapZero : guess - 2 * (first + 1) - 1 - gap = 0 := by
        dsimp [gap]
        omega
      rw [gapZero]
      simp only [Int.pow_zero]
      rw [firstEq, secondGapEq, guessPowerEq, combinedEq]
      simp only [Int.one_mul]
      calc
        (base : Int) * firstFactor + 1 +
              (base : Int) * secondGapFactor +
              (base : Int) * guessFactor +
              (base : Int) * combinedFactor -
            halfIntegerDenominator base first guess =
          (base : Int) * firstFactor +
              (base : Int) * secondGapFactor +
              (base : Int) * guessFactor +
              (base : Int) * combinedFactor +
            (1 - halfIntegerDenominator base first guess) := by grind
        _ = _ := by rw [denominatorEq]; grind

theorem largeFifthMarkerDigit_eq_two_iff (first guess : Nat) :
    largeFifthMarkerDigit first guess = 2 ↔
      guess = 3 * (first + 1) := by
  simp [largeFifthMarkerDigit]

def falseFifthOutputNumerator (base first guess : Nat) : Int :=
  (base : Int) ^ first +
    2 * (base : Int) ^ (guess - (first + 1) - 1) +
    (base : Int) ^ (guess - 1) +
    (base : Int) ^ (2 * guess - (first + 1) - 1) +
    (base : Int) ^ (first + guess)

def belowThreeFifthOutputNumerator (base first guess : Nat) : Int :=
  (base : Int) ^ (3 * (first + 1) - guess - 1) +
    2 * (base : Int) ^ first +
    (base : Int) ^ (2 * (first + 1) - 1) +
    (base : Int) ^ (3 * (first + 1) - 1) +
    (base : Int) ^ (first + guess)

def aboveThreeFifthOutputNumerator (base first guess : Nat) : Int :=
  (base : Int) ^ first +
    (base : Int) ^ (guess - 3 * (first + 1) - 1) +
    (base : Int) ^ (guess - 2 * (first + 1) - 1) +
    (base : Int) ^ (guess - (first + 1) - 1) +
    (base : Int) ^ (guess - 1) +
    (base : Int) ^ (first + guess)

def falseFifthOutput (base first guess : Nat) : Rat :=
  state (falseFifthOutputNumerator base first guess)
    (halfIntegerDenominator base first guess)

def belowThreeFifthOutput (base first guess : Nat) : Rat :=
  state (belowThreeFifthOutputNumerator base first guess)
    (halfIntegerDenominator base first guess)

def aboveThreeFifthOutput (base first guess : Nat) : Rat :=
  state (aboveThreeFifthOutputNumerator base first guess)
    (halfIntegerDenominator base first guess)

theorem middleFifth_marker_difference
    (base first guess : Nat) (QBelowGuess : first + 1 < guess)
    (guessBelowTwoQ : guess < 2 * (first + 1)) :
    middleFifthNumerator base first guess
          (middleFifthZeroCount first guess) -
        halfIntegerDenominator base first guess =
      (base : Int) * falseFifthOutputNumerator base first guess := by
  let count := middleFifthZeroCount first guess
  have countEq : count = 2 * (first + 1) - guess - 1 := rfl
  have firstEq : first - count = guess - first - 1 := by
    dsimp [count, middleFifthZeroCount]
    omega
  have twiceQEq : 2 * (first + 1) - 1 - count = guess := by
    dsimp [count, middleFifthZeroCount]
    omega
  have combinedEq : first + guess - count = 2 * guess - first - 1 := by
    dsimp [count, middleFifthZeroCount]
    omega
  have firstPower : (base : Int) ^ (first + 1) =
      (base : Int) ^ first * (base : Int) := by rw [Int.pow_succ]
  have gapPower : (base : Int) ^ (guess - first - 1) =
      (base : Int) ^ (guess - (first + 1) - 1) * (base : Int) := by
    calc
      (base : Int) ^ (guess - first - 1) =
          (base : Int) ^ (guess - (first + 1) - 1 + 1) := by
            congr 1 <;> omega
      _ = _ := by rw [Int.pow_succ]
  have guessPower : (base : Int) ^ guess =
      (base : Int) ^ (guess - 1) * (base : Int) := by
    calc
      (base : Int) ^ guess = (base : Int) ^ (guess - 1 + 1) := by
        congr 1 <;> omega
      _ = _ := by rw [Int.pow_succ]
  have twiceGuessPower : (base : Int) ^ (2 * guess - first - 1) =
      (base : Int) ^ (2 * guess - (first + 1) - 1) *
        (base : Int) := by
    calc
      (base : Int) ^ (2 * guess - first - 1) =
          (base : Int) ^ (2 * guess - (first + 1) - 1 + 1) := by
            congr 1 <;> omega
      _ = _ := by rw [Int.pow_succ]
  have combinedPower : (base : Int) ^ (first + guess + 1) =
      (base : Int) ^ (first + guess) * (base : Int) := by
    rw [Int.pow_succ]
  have leadingZero :
      2 * (first + 1) - guess - 1 - count = 0 := by
    dsimp [count, middleFifthZeroCount]
    omega
  unfold middleFifthNumerator halfIntegerDenominator
    falseFifthOutputNumerator
  rw [leadingZero, firstEq, twiceQEq, combinedEq]
  simp only [Int.pow_zero]
  rw [firstPower, gapPower, guessPower, twiceGuessPower, combinedPower]
  grind

theorem belowThreeFifth_marker_difference
    (base first guess : Nat)
    (_twoQBelowGuess : 2 * (first + 1) < guess)
    (_guessBelowThreeQ : guess < 3 * (first + 1)) :
    largeFifthNumerator base first guess
          (largeFifthZeroCount first guess) -
        halfIntegerDenominator base first guess =
      (base : Int) * belowThreeFifthOutputNumerator base first guess := by
  let count := guess - 2 * (first + 1) - 1
  have countBelowFirst : count < first := by dsimp [count]; omega
  have countEq : largeFifthZeroCount first guess = count := by
    simp [largeFifthZeroCount, count,
      Nat.min_eq_right (Nat.le_of_lt countBelowFirst)]
  have firstEq : first - count = 3 * (first + 1) - guess := by
    dsimp [count]
    omega
  have secondGapEq : guess - (first + 1) - 1 - count = first + 1 := by
    dsimp [count]
    omega
  have guessEq : guess - 1 - count = 2 * (first + 1) := by
    dsimp [count]
    omega
  have combinedEq : first + guess - count = 3 * (first + 1) := by
    dsimp [count]
    omega
  have leadingPower : (base : Int) ^ (3 * (first + 1) - guess) =
      (base : Int) ^ (3 * (first + 1) - guess - 1) *
        (base : Int) := by
    calc
      (base : Int) ^ (3 * (first + 1) - guess) =
          (base : Int) ^ (3 * (first + 1) - guess - 1 + 1) := by
            congr 1 <;> omega
      _ = _ := by rw [Int.pow_succ]
  have firstPower : (base : Int) ^ (first + 1) =
      (base : Int) ^ first * (base : Int) := by rw [Int.pow_succ]
  have twiceQPower : (base : Int) ^ (2 * (first + 1)) =
      (base : Int) ^ (2 * (first + 1) - 1) * (base : Int) := by
    calc
      (base : Int) ^ (2 * (first + 1)) =
          (base : Int) ^ (2 * (first + 1) - 1 + 1) := by
            congr 1 <;> omega
      _ = _ := by rw [Int.pow_succ]
  have threeQPower : (base : Int) ^ (3 * (first + 1)) =
      (base : Int) ^ (3 * (first + 1) - 1) * (base : Int) := by
    calc
      (base : Int) ^ (3 * (first + 1)) =
          (base : Int) ^ (3 * (first + 1) - 1 + 1) := by
            congr 1 <;> omega
      _ = _ := by rw [Int.pow_succ]
  have combinedPower : (base : Int) ^ (first + guess + 1) =
      (base : Int) ^ (first + guess) * (base : Int) := by
    rw [Int.pow_succ]
  have gapZero :
      guess - 2 * (first + 1) - 1 - count = 0 := by
    dsimp [count]
    omega
  unfold largeFifthNumerator halfIntegerDenominator
    belowThreeFifthOutputNumerator
  rw [countEq, firstEq, gapZero, secondGapEq, guessEq, combinedEq]
  simp only [Int.pow_zero]
  rw [leadingPower, firstPower, twiceQPower, threeQPower, combinedPower]
  grind

theorem aboveThreeFifth_marker_difference
    (base first guess : Nat)
    (_threeQBelowGuess : 3 * (first + 1) < guess) :
    largeFifthNumerator base first guess
          (largeFifthZeroCount first guess) -
        halfIntegerDenominator base first guess =
      (base : Int) * aboveThreeFifthOutputNumerator base first guess := by
  have gapAboveFirst : first < guess - 2 * (first + 1) - 1 := by omega
  have countEq : largeFifthZeroCount first guess = first := by
    simp [largeFifthZeroCount,
      Nat.min_eq_left (Nat.le_of_lt gapAboveFirst)]
  have firstGapEq : guess - 2 * (first + 1) - 1 - first =
      guess - 3 * (first + 1) := by omega
  have secondGapEq : guess - (first + 1) - 1 - first =
      guess - 2 * (first + 1) := by omega
  have guessEq : guess - 1 - first = guess - (first + 1) := by omega
  have combinedEq : first + guess - first = guess := by omega
  have firstPower : (base : Int) ^ (first + 1) =
      (base : Int) ^ first * (base : Int) := by rw [Int.pow_succ]
  have firstGapPower : (base : Int) ^ (guess - 3 * (first + 1)) =
      (base : Int) ^ (guess - 3 * (first + 1) - 1) *
        (base : Int) := by
    calc
      (base : Int) ^ (guess - 3 * (first + 1)) =
          (base : Int) ^ (guess - 3 * (first + 1) - 1 + 1) := by
            congr 1 <;> omega
      _ = _ := by rw [Int.pow_succ]
  have secondGapPower : (base : Int) ^ (guess - 2 * (first + 1)) =
      (base : Int) ^ (guess - 2 * (first + 1) - 1) *
        (base : Int) := by
    calc
      (base : Int) ^ (guess - 2 * (first + 1)) =
          (base : Int) ^ (guess - 2 * (first + 1) - 1 + 1) := by
            congr 1 <;> omega
      _ = _ := by rw [Int.pow_succ]
  have thirdGapPower : (base : Int) ^ (guess - (first + 1)) =
      (base : Int) ^ (guess - (first + 1) - 1) *
        (base : Int) := by
    calc
      (base : Int) ^ (guess - (first + 1)) =
          (base : Int) ^ (guess - (first + 1) - 1 + 1) := by
            congr 1 <;> omega
      _ = _ := by rw [Int.pow_succ]
  have guessPower : (base : Int) ^ guess =
      (base : Int) ^ (guess - 1) * (base : Int) := by
    calc
      (base : Int) ^ guess = (base : Int) ^ (guess - 1 + 1) := by
        congr 1 <;> omega
      _ = _ := by rw [Int.pow_succ]
  have combinedPower : (base : Int) ^ (first + guess + 1) =
      (base : Int) ^ (first + guess) * (base : Int) := by
    rw [Int.pow_succ]
  unfold largeFifthNumerator halfIntegerDenominator
    aboveThreeFifthOutputNumerator
  rw [countEq, Nat.sub_self, firstGapEq, secondGapEq, guessEq, combinedEq]
  simp only [Int.pow_zero]
  rw [firstPower, firstGapPower, secondGapPower, thirdGapPower, guessPower,
    combinedPower]
  grind

theorem middleFifth_delete_marker
    (base first guess : Nat) (baseAtLeastTwo : 2 ≤ base)
    (QBelowGuess : first + 1 < guess)
    (guessBelowTwoQ : guess < 2 * (first + 1)) :
    deleteDigit (base : Rat) 1
        (middleFifthState base first guess
          (middleFifthZeroCount first guess)) =
      falseFifthOutput base first guess := by
  exact deleteDigit_eq base 1 _ _ _ (by omega)
    (denominator_nonzero_of_not_dvd
      (halfIntegerDenominator_not_dvd base first guess baseAtLeastTwo))
    (by simpa using (middleFifth_marker_difference base first guess
      QBelowGuess guessBelowTwoQ))

theorem belowThreeFifth_delete_marker
    (base first guess : Nat) (baseAtLeastTwo : 2 ≤ base)
    (twoQBelowGuess : 2 * (first + 1) < guess)
    (guessBelowThreeQ : guess < 3 * (first + 1)) :
    deleteDigit (base : Rat) 1
        (largeFifthState base first guess
          (largeFifthZeroCount first guess)) =
      belowThreeFifthOutput base first guess := by
  exact deleteDigit_eq base 1 _ _ _ (by omega)
    (denominator_nonzero_of_not_dvd
      (halfIntegerDenominator_not_dvd base first guess baseAtLeastTwo))
    (by simpa using (belowThreeFifth_marker_difference base first guess
      twoQBelowGuess guessBelowThreeQ))

theorem aboveThreeFifth_delete_marker
    (base first guess : Nat) (baseAtLeastTwo : 2 ≤ base)
    (threeQBelowGuess : 3 * (first + 1) < guess) :
    deleteDigit (base : Rat) 1
        (largeFifthState base first guess
          (largeFifthZeroCount first guess)) =
      aboveThreeFifthOutput base first guess := by
  exact deleteDigit_eq base 1 _ _ _ (by omega)
    (denominator_nonzero_of_not_dvd
      (halfIntegerDenominator_not_dvd base first guess baseAtLeastTwo))
    (by simpa using (aboveThreeFifth_marker_difference base first guess
      threeQBelowGuess))

def markerTwoDenominator
    (base first guess : Nat) (numerator : Nat → Int) : Int :=
  halfIntegerDenominator base first guess + (base : Int) * numerator 0

def falseMarkerTwoNumerator (base first guess deleted : Nat) : Int :=
  (base : Int) ^ (first - deleted) +
    2 * (base : Int) ^ (guess - (first + 1) - 1 - deleted) +
    (base : Int) ^ (guess - 1 - deleted) +
    (base : Int) ^ (2 * guess - (first + 1) - 1 - deleted) +
    (base : Int) ^ (first + guess - deleted)

def belowThreeMarkerTwoNumerator
    (base first guess deleted : Nat) : Int :=
  (base : Int) ^ (3 * (first + 1) - guess - 1 - deleted) +
    2 * (base : Int) ^ (first - deleted) +
    (base : Int) ^ (2 * (first + 1) - 1 - deleted) +
    (base : Int) ^ (3 * (first + 1) - 1 - deleted) +
    (base : Int) ^ (first + guess - deleted)

def aboveThreeMarkerTwoNumerator
    (base first guess deleted : Nat) : Int :=
  (base : Int) ^ (first - deleted) +
    (base : Int) ^ (guess - 3 * (first + 1) - 1 - deleted) +
    (base : Int) ^ (guess - 2 * (first + 1) - 1 - deleted) +
    (base : Int) ^ (guess - (first + 1) - 1 - deleted) +
    (base : Int) ^ (guess - 1 - deleted) +
    (base : Int) ^ (first + guess - deleted)

def falseMarkerTwoState (base first guess deleted : Nat) : Rat :=
  state (falseMarkerTwoNumerator base first guess deleted)
    (markerTwoDenominator base first guess
      (falseMarkerTwoNumerator base first guess))

def belowThreeMarkerTwoState (base first guess deleted : Nat) : Rat :=
  state (belowThreeMarkerTwoNumerator base first guess deleted)
    (markerTwoDenominator base first guess
      (belowThreeMarkerTwoNumerator base first guess))

def aboveThreeMarkerTwoState (base first guess deleted : Nat) : Rat :=
  state (aboveThreeMarkerTwoNumerator base first guess deleted)
    (markerTwoDenominator base first guess
      (aboveThreeMarkerTwoNumerator base first guess))

def falseMarkerTwoZeroCount (first guess : Nat) : Nat :=
  guess - (first + 1) - 1

def belowThreeMarkerTwoZeroCount (first guess : Nat) : Nat :=
  3 * (first + 1) - guess - 1

def aboveThreeMarkerTwoZeroCount (first guess : Nat) : Nat :=
  min first (guess - 3 * (first + 1) - 1)

def aboveThreeMarkerTwoDigit (first guess : Nat) : Int :=
  if guess = 4 * (first + 1) then 2 else 1

theorem markerTwoDenominator_not_dvd
    (base first guess : Nat) (numerator : Nat → Int)
    (baseAtLeastTwo : 2 ≤ base) :
    ¬(base : Int) ∣ markerTwoDenominator base first guess numerator := by
  intro sumDivisible
  have productDivisible : (base : Int) ∣
      (base : Int) * numerator 0 := ⟨numerator 0, rfl⟩
  have denominatorDivisible := Int.dvd_sub sumDivisible productDivisible
  exact halfIntegerDenominator_not_dvd base first guess baseAtLeastTwo
    (by simpa [markerTwoDenominator] using denominatorDivisible)

theorem falseMarkerTwoState_local
    (base first guess deleted : Nat) (baseAtLeastTwo : 2 ≤ base) :
    LocalAt base
      (Vec2.affine (falseMarkerTwoState base first guess deleted)) := by
  exact state_local
    (markerTwoDenominator_not_dvd base first guess _ baseAtLeastTwo)

theorem belowThreeMarkerTwoState_local
    (base first guess deleted : Nat) (baseAtLeastTwo : 2 ≤ base) :
    LocalAt base
      (Vec2.affine (belowThreeMarkerTwoState base first guess deleted)) := by
  exact state_local
    (markerTwoDenominator_not_dvd base first guess _ baseAtLeastTwo)

theorem aboveThreeMarkerTwoState_local
    (base first guess deleted : Nat) (baseAtLeastTwo : 2 ≤ base) :
    LocalAt base
      (Vec2.affine (aboveThreeMarkerTwoState base first guess deleted)) := by
  exact state_local
    (markerTwoDenominator_not_dvd base first guess _ baseAtLeastTwo)

theorem falseMarkerTwoState_sameLine_integer
    (base first guess deleted : Nat) (baseAtLeastTwo : 2 ≤ base) :
    SameLine (Vec2.affine (falseMarkerTwoState base first guess deleted))
      (integerVector (falseMarkerTwoNumerator base first guess deleted)
        (markerTwoDenominator base first guess
          (falseMarkerTwoNumerator base first guess))) := by
  exact sameLine_integer (denominator_nonzero_of_not_dvd
    (markerTwoDenominator_not_dvd base first guess _ baseAtLeastTwo))

theorem belowThreeMarkerTwoState_sameLine_integer
    (base first guess deleted : Nat) (baseAtLeastTwo : 2 ≤ base) :
    SameLine
      (Vec2.affine (belowThreeMarkerTwoState base first guess deleted))
      (integerVector (belowThreeMarkerTwoNumerator base first guess deleted)
        (markerTwoDenominator base first guess
          (belowThreeMarkerTwoNumerator base first guess))) := by
  exact sameLine_integer (denominator_nonzero_of_not_dvd
    (markerTwoDenominator_not_dvd base first guess _ baseAtLeastTwo))

theorem aboveThreeMarkerTwoState_sameLine_integer
    (base first guess deleted : Nat) (baseAtLeastTwo : 2 ≤ base) :
    SameLine
      (Vec2.affine (aboveThreeMarkerTwoState base first guess deleted))
      (integerVector (aboveThreeMarkerTwoNumerator base first guess deleted)
        (markerTwoDenominator base first guess
          (aboveThreeMarkerTwoNumerator base first guess))) := by
  exact sameLine_integer (denominator_nonzero_of_not_dvd
    (markerTwoDenominator_not_dvd base first guess _ baseAtLeastTwo))

theorem falseMarkerTwoState_zero
    (base first guess : Nat) (baseAtLeastTwo : 2 ≤ base)
    (_QBelowGuess : first + 1 < guess)
    (_guessBelowTwoQ : guess < 2 * (first + 1)) :
    Tinv base (falseFifthOutput base first guess) =
      falseMarkerTwoState base first guess 0 := by
  have numeratorEq : falseMarkerTwoNumerator base first guess 0 =
      falseFifthOutputNumerator base first guess := by
    simp [falseMarkerTwoNumerator, falseFifthOutputNumerator]
  rw [falseFifthOutput, ← numeratorEq]
  apply Tinv_state
  · exact denominator_nonzero_of_not_dvd
      (halfIntegerDenominator_not_dvd base first guess baseAtLeastTwo)
  · exact denominator_nonzero_of_not_dvd
      (markerTwoDenominator_not_dvd base first guess _ baseAtLeastTwo)

theorem belowThreeMarkerTwoState_zero
    (base first guess : Nat) (baseAtLeastTwo : 2 ≤ base)
    (_twoQBelowGuess : 2 * (first + 1) < guess)
    (_guessBelowThreeQ : guess < 3 * (first + 1)) :
    Tinv base (belowThreeFifthOutput base first guess) =
      belowThreeMarkerTwoState base first guess 0 := by
  have numeratorEq : belowThreeMarkerTwoNumerator base first guess 0 =
      belowThreeFifthOutputNumerator base first guess := by
    simp [belowThreeMarkerTwoNumerator, belowThreeFifthOutputNumerator]
  rw [belowThreeFifthOutput, ← numeratorEq]
  apply Tinv_state
  · exact denominator_nonzero_of_not_dvd
      (halfIntegerDenominator_not_dvd base first guess baseAtLeastTwo)
  · exact denominator_nonzero_of_not_dvd
      (markerTwoDenominator_not_dvd base first guess _ baseAtLeastTwo)

theorem aboveThreeMarkerTwoState_zero
    (base first guess : Nat) (baseAtLeastTwo : 2 ≤ base)
    (_threeQBelowGuess : 3 * (first + 1) < guess) :
    Tinv base (aboveThreeFifthOutput base first guess) =
      aboveThreeMarkerTwoState base first guess 0 := by
  have numeratorEq : aboveThreeMarkerTwoNumerator base first guess 0 =
      aboveThreeFifthOutputNumerator base first guess := by
    simp [aboveThreeMarkerTwoNumerator, aboveThreeFifthOutputNumerator]
  rw [aboveThreeFifthOutput, ← numeratorEq]
  apply Tinv_state
  · exact denominator_nonzero_of_not_dvd
      (halfIntegerDenominator_not_dvd base first guess baseAtLeastTwo)
  · exact denominator_nonzero_of_not_dvd
      (markerTwoDenominator_not_dvd base first guess _ baseAtLeastTwo)

theorem falseMarkerTwoNumerator_step
    (base first guess deleted : Nat)
    (QBelowGuess : first + 1 < guess)
    (guessBelowTwoQ : guess < 2 * (first + 1))
    (deletedBelow : deleted < falseMarkerTwoZeroCount first guess) :
    falseMarkerTwoNumerator base first guess deleted =
      (base : Int) *
        falseMarkerTwoNumerator base first guess (deleted + 1) := by
  have firstExponent : first - deleted =
      first - (deleted + 1) + 1 := by
    unfold falseMarkerTwoZeroCount at deletedBelow
    omega
  have leadingExponent : guess - (first + 1) - 1 - deleted =
      guess - (first + 1) - 1 - (deleted + 1) + 1 := by
    unfold falseMarkerTwoZeroCount at deletedBelow
    omega
  have guessExponent : guess - 1 - deleted =
      guess - 1 - (deleted + 1) + 1 := by
    unfold falseMarkerTwoZeroCount at deletedBelow
    omega
  have twiceGuessExponent : 2 * guess - (first + 1) - 1 - deleted =
      2 * guess - (first + 1) - 1 - (deleted + 1) + 1 := by
    unfold falseMarkerTwoZeroCount at deletedBelow
    omega
  have combinedExponent : first + guess - deleted =
      first + guess - (deleted + 1) + 1 := by
    unfold falseMarkerTwoZeroCount at deletedBelow
    omega
  unfold falseMarkerTwoNumerator
  rw [firstExponent, leadingExponent, guessExponent, twiceGuessExponent,
    combinedExponent]
  simp only [Int.pow_succ]
  grind

theorem belowThreeMarkerTwoNumerator_step
    (base first guess deleted : Nat)
    (twoQBelowGuess : 2 * (first + 1) < guess)
    (guessBelowThreeQ : guess < 3 * (first + 1))
    (deletedBelow : deleted < belowThreeMarkerTwoZeroCount first guess) :
    belowThreeMarkerTwoNumerator base first guess deleted =
      (base : Int) *
        belowThreeMarkerTwoNumerator base first guess (deleted + 1) := by
  have leadingExponent : 3 * (first + 1) - guess - 1 - deleted =
      3 * (first + 1) - guess - 1 - (deleted + 1) + 1 := by
    unfold belowThreeMarkerTwoZeroCount at deletedBelow
    omega
  have firstExponent : first - deleted =
      first - (deleted + 1) + 1 := by
    unfold belowThreeMarkerTwoZeroCount at deletedBelow
    omega
  have twiceQExponent : 2 * (first + 1) - 1 - deleted =
      2 * (first + 1) - 1 - (deleted + 1) + 1 := by
    unfold belowThreeMarkerTwoZeroCount at deletedBelow
    omega
  have threeQExponent : 3 * (first + 1) - 1 - deleted =
      3 * (first + 1) - 1 - (deleted + 1) + 1 := by
    unfold belowThreeMarkerTwoZeroCount at deletedBelow
    omega
  have combinedExponent : first + guess - deleted =
      first + guess - (deleted + 1) + 1 := by
    unfold belowThreeMarkerTwoZeroCount at deletedBelow
    omega
  unfold belowThreeMarkerTwoNumerator
  rw [leadingExponent, firstExponent, twiceQExponent, threeQExponent,
    combinedExponent]
  simp only [Int.pow_succ]
  grind

theorem aboveThreeMarkerTwoNumerator_step
    (base first guess deleted : Nat)
    (threeQBelowGuess : 3 * (first + 1) < guess)
    (deletedBelow : deleted < aboveThreeMarkerTwoZeroCount first guess) :
    aboveThreeMarkerTwoNumerator base first guess deleted =
      (base : Int) *
        aboveThreeMarkerTwoNumerator base first guess (deleted + 1) := by
  have belowFirst : deleted < first := Nat.lt_of_lt_of_le deletedBelow
    (Nat.min_le_left _ _)
  have belowGap : deleted < guess - 3 * (first + 1) - 1 :=
    Nat.lt_of_lt_of_le deletedBelow (Nat.min_le_right _ _)
  have firstExponent : first - deleted =
      first - (deleted + 1) + 1 := by omega
  have firstGapExponent : guess - 3 * (first + 1) - 1 - deleted =
      guess - 3 * (first + 1) - 1 - (deleted + 1) + 1 := by omega
  have secondGapExponent : guess - 2 * (first + 1) - 1 - deleted =
      guess - 2 * (first + 1) - 1 - (deleted + 1) + 1 := by omega
  have thirdGapExponent : guess - (first + 1) - 1 - deleted =
      guess - (first + 1) - 1 - (deleted + 1) + 1 := by omega
  have guessExponent : guess - 1 - deleted =
      guess - 1 - (deleted + 1) + 1 := by omega
  have combinedExponent : first + guess - deleted =
      first + guess - (deleted + 1) + 1 := by omega
  unfold aboveThreeMarkerTwoNumerator
  rw [firstExponent, firstGapExponent, secondGapExponent,
    thirdGapExponent, guessExponent, combinedExponent]
  simp only [Int.pow_succ]
  grind

theorem falseMarkerTwoState_delete_zero
    (base first guess deleted : Nat) (baseAtLeastTwo : 2 ≤ base)
    (QBelowGuess : first + 1 < guess)
    (guessBelowTwoQ : guess < 2 * (first + 1))
    (deletedBelow : deleted < falseMarkerTwoZeroCount first guess) :
    deleteDigit (base : Rat) 0
        (falseMarkerTwoState base first guess deleted) =
      falseMarkerTwoState base first guess (deleted + 1) := by
  apply deleteZero_eq base _ _ _ (by omega)
    (denominator_nonzero_of_not_dvd
      (markerTwoDenominator_not_dvd base first guess _ baseAtLeastTwo))
  exact falseMarkerTwoNumerator_step base first guess deleted QBelowGuess
    guessBelowTwoQ deletedBelow

theorem belowThreeMarkerTwoState_delete_zero
    (base first guess deleted : Nat) (baseAtLeastTwo : 2 ≤ base)
    (twoQBelowGuess : 2 * (first + 1) < guess)
    (guessBelowThreeQ : guess < 3 * (first + 1))
    (deletedBelow : deleted < belowThreeMarkerTwoZeroCount first guess) :
    deleteDigit (base : Rat) 0
        (belowThreeMarkerTwoState base first guess deleted) =
      belowThreeMarkerTwoState base first guess (deleted + 1) := by
  apply deleteZero_eq base _ _ _ (by omega)
    (denominator_nonzero_of_not_dvd
      (markerTwoDenominator_not_dvd base first guess _ baseAtLeastTwo))
  exact belowThreeMarkerTwoNumerator_step base first guess deleted
    twoQBelowGuess guessBelowThreeQ deletedBelow

theorem aboveThreeMarkerTwoState_delete_zero
    (base first guess deleted : Nat) (baseAtLeastTwo : 2 ≤ base)
    (threeQBelowGuess : 3 * (first + 1) < guess)
    (deletedBelow : deleted < aboveThreeMarkerTwoZeroCount first guess) :
    deleteDigit (base : Rat) 0
        (aboveThreeMarkerTwoState base first guess deleted) =
      aboveThreeMarkerTwoState base first guess (deleted + 1) := by
  apply deleteZero_eq base _ _ _ (by omega)
    (denominator_nonzero_of_not_dvd
      (markerTwoDenominator_not_dvd base first guess _ baseAtLeastTwo))
  exact aboveThreeMarkerTwoNumerator_step base first guess deleted
    threeQBelowGuess deletedBelow

theorem markerTwoDenominator_one_residue
    (base first guess : Nat) (numerator : Nat → Int) :
    (base : Int) ∣
      1 - markerTwoDenominator base first guess numerator := by
  rcases halfIntegerDenominator_one_residue base first guess with
    ⟨factor, factorEq⟩
  refine ⟨factor - numerator 0, ?_⟩
  unfold markerTwoDenominator
  calc
    1 - (halfIntegerDenominator base first guess +
        (base : Int) * numerator 0) =
      (1 - halfIntegerDenominator base first guess) -
        (base : Int) * numerator 0 := by grind
    _ = (base : Int) * factor - (base : Int) * numerator 0 := by
      rw [factorEq]
    _ = (base : Int) * (factor - numerator 0) := by grind

theorem falseMarkerTwo_marker_residue_two
    (base first guess : Nat) (QBelowGuess : first + 1 < guess)
    (guessBelowTwoQ : guess < 2 * (first + 1)) :
    (base : Int) ∣
      falseMarkerTwoNumerator base first guess
          (falseMarkerTwoZeroCount first guess) -
        2 * markerTwoDenominator base first guess
          (falseMarkerTwoNumerator base first guess) := by
  let count := falseMarkerTwoZeroCount first guess
  have firstPositive : 0 < first - count := by
    dsimp [count, falseMarkerTwoZeroCount]
    omega
  have guessPositive : 0 < guess - 1 - count := by
    dsimp [count, falseMarkerTwoZeroCount]
    omega
  have twiceGuessPositive :
      0 < 2 * guess - (first + 1) - 1 - count := by
    dsimp [count, falseMarkerTwoZeroCount]
    omega
  have combinedPositive : 0 < first + guess - count := by
    dsimp [count, falseMarkerTwoZeroCount]
    omega
  rcases base_dvd_positive_power base (first - count) firstPositive with
    ⟨firstFactor, firstEq⟩
  rcases base_dvd_positive_power base (guess - 1 - count) guessPositive with
    ⟨guessFactor, guessEq⟩
  rcases base_dvd_positive_power base
      (2 * guess - (first + 1) - 1 - count) twiceGuessPositive with
    ⟨twiceGuessFactor, twiceGuessEq⟩
  rcases base_dvd_positive_power base (first + guess - count)
      combinedPositive with ⟨combinedFactor, combinedEq⟩
  rcases markerTwoDenominator_one_residue base first guess
      (falseMarkerTwoNumerator base first guess) with
    ⟨denominatorFactor, denominatorEq⟩
  refine ⟨firstFactor + guessFactor + twiceGuessFactor + combinedFactor +
      2 * denominatorFactor, ?_⟩
  have leadingZero : guess - (first + 1) - 1 - count = 0 := by
    dsimp [count, falseMarkerTwoZeroCount]
    omega
  have numeratorAt :
      falseMarkerTwoNumerator base first guess count =
        (base : Int) * firstFactor + 2 + (base : Int) * guessFactor +
          (base : Int) * twiceGuessFactor +
          (base : Int) * combinedFactor := by
    unfold falseMarkerTwoNumerator
    rw [leadingZero]
    simp only [Int.pow_zero, Int.mul_one]
    rw [firstEq, guessEq, twiceGuessEq, combinedEq]
  change
    falseMarkerTwoNumerator base first guess count -
        2 * markerTwoDenominator base first guess
          (falseMarkerTwoNumerator base first guess) = _
  rw [numeratorAt]
  calc
    (base : Int) * firstFactor + 2 + (base : Int) * guessFactor +
          (base : Int) * twiceGuessFactor +
          (base : Int) * combinedFactor -
        2 * markerTwoDenominator base first guess
          (falseMarkerTwoNumerator base first guess) =
      (base : Int) * firstFactor + (base : Int) * guessFactor +
          (base : Int) * twiceGuessFactor +
          (base : Int) * combinedFactor +
        2 * (1 - markerTwoDenominator base first guess
          (falseMarkerTwoNumerator base first guess)) := by grind
    _ = _ := by rw [denominatorEq]; grind

theorem belowThreeMarkerTwo_marker_residue_one
    (base first guess : Nat)
    (twoQBelowGuess : 2 * (first + 1) < guess)
    (guessBelowThreeQ : guess < 3 * (first + 1)) :
    (base : Int) ∣
      belowThreeMarkerTwoNumerator base first guess
          (belowThreeMarkerTwoZeroCount first guess) -
        markerTwoDenominator base first guess
          (belowThreeMarkerTwoNumerator base first guess) := by
  let count := belowThreeMarkerTwoZeroCount first guess
  have firstPositive : 0 < first - count := by
    dsimp [count, belowThreeMarkerTwoZeroCount]
    omega
  have twiceQPositive : 0 < 2 * (first + 1) - 1 - count := by
    dsimp [count, belowThreeMarkerTwoZeroCount]
    omega
  have threeQPositive : 0 < 3 * (first + 1) - 1 - count := by
    dsimp [count, belowThreeMarkerTwoZeroCount]
    omega
  have combinedPositive : 0 < first + guess - count := by
    dsimp [count, belowThreeMarkerTwoZeroCount]
    omega
  rcases base_dvd_positive_power base (first - count) firstPositive with
    ⟨firstFactor, firstEq⟩
  rcases base_dvd_positive_power base
      (2 * (first + 1) - 1 - count) twiceQPositive with
    ⟨twiceQFactor, twiceQEq⟩
  rcases base_dvd_positive_power base
      (3 * (first + 1) - 1 - count) threeQPositive with
    ⟨threeQFactor, threeQEq⟩
  rcases base_dvd_positive_power base (first + guess - count)
      combinedPositive with ⟨combinedFactor, combinedEq⟩
  rcases markerTwoDenominator_one_residue base first guess
      (belowThreeMarkerTwoNumerator base first guess) with
    ⟨denominatorFactor, denominatorEq⟩
  refine ⟨2 * firstFactor + twiceQFactor + threeQFactor +
      combinedFactor + denominatorFactor, ?_⟩
  have leadingZero : 3 * (first + 1) - guess - 1 - count = 0 := by
    dsimp [count, belowThreeMarkerTwoZeroCount]
    omega
  unfold belowThreeMarkerTwoNumerator
  rw [leadingZero]
  simp only [Int.pow_zero]
  rw [firstEq, twiceQEq, threeQEq, combinedEq]
  change
    1 + 2 * ((base : Int) * firstFactor) +
          (base : Int) * twiceQFactor + (base : Int) * threeQFactor +
          (base : Int) * combinedFactor -
        markerTwoDenominator base first guess
          (belowThreeMarkerTwoNumerator base first guess) = _
  calc
    1 + 2 * ((base : Int) * firstFactor) +
          (base : Int) * twiceQFactor + (base : Int) * threeQFactor +
          (base : Int) * combinedFactor -
        markerTwoDenominator base first guess
          (belowThreeMarkerTwoNumerator base first guess) =
      2 * ((base : Int) * firstFactor) +
          (base : Int) * twiceQFactor + (base : Int) * threeQFactor +
          (base : Int) * combinedFactor +
        (1 - markerTwoDenominator base first guess
          (belowThreeMarkerTwoNumerator base first guess)) := by grind
    _ = _ := by rw [denominatorEq]; grind

theorem aboveThreeMarkerTwo_marker_residue
    (base first guess : Nat)
    (threeQBelowGuess : 3 * (first + 1) < guess) :
    (base : Int) ∣
      aboveThreeMarkerTwoNumerator base first guess
          (aboveThreeMarkerTwoZeroCount first guess) -
        aboveThreeMarkerTwoDigit first guess *
          markerTwoDenominator base first guess
            (aboveThreeMarkerTwoNumerator base first guess) := by
  let gap := guess - 3 * (first + 1) - 1
  have countEq : aboveThreeMarkerTwoZeroCount first guess =
      min first gap := rfl
  by_cases equalLeads : first = gap
  · have guessEq : guess = 4 * (first + 1) := by
      dsimp [gap] at equalLeads
      omega
    have countFirst : aboveThreeMarkerTwoZeroCount first guess = first := by
      rw [countEq, equalLeads, Nat.min_self]
    have secondGapPositive :
        0 < guess - 2 * (first + 1) - 1 - first := by omega
    have thirdGapPositive :
        0 < guess - (first + 1) - 1 - first := by omega
    have guessPositive : 0 < guess - 1 - first := by omega
    have combinedPositive : 0 < first + guess - first := by omega
    rcases base_dvd_positive_power base _ secondGapPositive with
      ⟨secondGapFactor, secondGapEq⟩
    rcases base_dvd_positive_power base _ thirdGapPositive with
      ⟨thirdGapFactor, thirdGapEq⟩
    rcases base_dvd_positive_power base _ guessPositive with
      ⟨guessFactor, guessPowerEq⟩
    rcases base_dvd_positive_power base _ combinedPositive with
      ⟨combinedFactor, combinedEq⟩
    rcases markerTwoDenominator_one_residue base first guess
        (aboveThreeMarkerTwoNumerator base first guess) with
      ⟨denominatorFactor, denominatorEq⟩
    refine ⟨secondGapFactor + thirdGapFactor + guessFactor +
        combinedFactor + 2 * denominatorFactor, ?_⟩
    unfold aboveThreeMarkerTwoNumerator aboveThreeMarkerTwoDigit
    rw [if_pos guessEq, countFirst, Nat.sub_self]
    have firstGapZero :
        guess - 3 * (first + 1) - 1 - first = 0 := by omega
    rw [firstGapZero]
    simp only [Int.pow_zero]
    rw [secondGapEq, thirdGapEq, guessPowerEq, combinedEq]
    change
      1 + 1 + (base : Int) * secondGapFactor +
            (base : Int) * thirdGapFactor + (base : Int) * guessFactor +
            (base : Int) * combinedFactor -
          2 * markerTwoDenominator base first guess
            (aboveThreeMarkerTwoNumerator base first guess) = _
    calc
      1 + 1 + (base : Int) * secondGapFactor +
            (base : Int) * thirdGapFactor + (base : Int) * guessFactor +
            (base : Int) * combinedFactor -
          2 * markerTwoDenominator base first guess
            (aboveThreeMarkerTwoNumerator base first guess) =
        (base : Int) * secondGapFactor +
            (base : Int) * thirdGapFactor + (base : Int) * guessFactor +
            (base : Int) * combinedFactor +
          2 * (1 - markerTwoDenominator base first guess
            (aboveThreeMarkerTwoNumerator base first guess)) := by grind
      _ = _ := by rw [denominatorEq]; grind
  · have guessNe : guess ≠ 4 * (first + 1) := by
      intro guessEq
      apply equalLeads
      dsimp [gap]
      omega
    rcases Nat.lt_or_gt_of_ne equalLeads with firstBelow | gapBelow
    · have countFirst : aboveThreeMarkerTwoZeroCount first guess =
          first := by
        rw [countEq, Nat.min_eq_left (Nat.le_of_lt firstBelow)]
      have firstGapPositive :
          0 < guess - 3 * (first + 1) - 1 - first := by
        dsimp [gap] at firstBelow
        omega
      have secondGapPositive :
          0 < guess - 2 * (first + 1) - 1 - first := by omega
      have thirdGapPositive :
          0 < guess - (first + 1) - 1 - first := by omega
      have guessPositive : 0 < guess - 1 - first := by omega
      have combinedPositive : 0 < first + guess - first := by omega
      rcases base_dvd_positive_power base _ firstGapPositive with
        ⟨firstGapFactor, firstGapEq⟩
      rcases base_dvd_positive_power base _ secondGapPositive with
        ⟨secondGapFactor, secondGapEq⟩
      rcases base_dvd_positive_power base _ thirdGapPositive with
        ⟨thirdGapFactor, thirdGapEq⟩
      rcases base_dvd_positive_power base _ guessPositive with
        ⟨guessFactor, guessPowerEq⟩
      rcases base_dvd_positive_power base _ combinedPositive with
        ⟨combinedFactor, combinedEq⟩
      rcases markerTwoDenominator_one_residue base first guess
          (aboveThreeMarkerTwoNumerator base first guess) with
        ⟨denominatorFactor, denominatorEq⟩
      refine ⟨firstGapFactor + secondGapFactor + thirdGapFactor +
          guessFactor + combinedFactor + denominatorFactor, ?_⟩
      unfold aboveThreeMarkerTwoNumerator aboveThreeMarkerTwoDigit
      rw [if_neg guessNe, countFirst, Nat.sub_self]
      simp only [Int.pow_zero, Int.one_mul]
      rw [firstGapEq, secondGapEq, thirdGapEq, guessPowerEq, combinedEq]
      change
        1 + (base : Int) * firstGapFactor +
              (base : Int) * secondGapFactor +
              (base : Int) * thirdGapFactor + (base : Int) * guessFactor +
              (base : Int) * combinedFactor -
            markerTwoDenominator base first guess
              (aboveThreeMarkerTwoNumerator base first guess) = _
      calc
        1 + (base : Int) * firstGapFactor +
              (base : Int) * secondGapFactor +
              (base : Int) * thirdGapFactor + (base : Int) * guessFactor +
              (base : Int) * combinedFactor -
            markerTwoDenominator base first guess
              (aboveThreeMarkerTwoNumerator base first guess) =
          (base : Int) * firstGapFactor +
              (base : Int) * secondGapFactor +
              (base : Int) * thirdGapFactor + (base : Int) * guessFactor +
              (base : Int) * combinedFactor +
            (1 - markerTwoDenominator base first guess
              (aboveThreeMarkerTwoNumerator base first guess)) := by grind
        _ = _ := by rw [denominatorEq]; grind
    · have countGap : aboveThreeMarkerTwoZeroCount first guess = gap := by
        rw [countEq, Nat.min_eq_right (Nat.le_of_lt gapBelow)]
      have firstPositive : 0 < first - gap := by omega
      have secondGapPositive :
          0 < guess - 2 * (first + 1) - 1 - gap := by
        dsimp [gap]
        omega
      have thirdGapPositive :
          0 < guess - (first + 1) - 1 - gap := by
        dsimp [gap]
        omega
      have guessPositive : 0 < guess - 1 - gap := by
        dsimp [gap]
        omega
      have combinedPositive : 0 < first + guess - gap := by
        dsimp [gap]
        omega
      rcases base_dvd_positive_power base _ firstPositive with
        ⟨firstFactor, firstEq⟩
      rcases base_dvd_positive_power base _ secondGapPositive with
        ⟨secondGapFactor, secondGapEq⟩
      rcases base_dvd_positive_power base _ thirdGapPositive with
        ⟨thirdGapFactor, thirdGapEq⟩
      rcases base_dvd_positive_power base _ guessPositive with
        ⟨guessFactor, guessPowerEq⟩
      rcases base_dvd_positive_power base _ combinedPositive with
        ⟨combinedFactor, combinedEq⟩
      rcases markerTwoDenominator_one_residue base first guess
          (aboveThreeMarkerTwoNumerator base first guess) with
        ⟨denominatorFactor, denominatorEq⟩
      refine ⟨firstFactor + secondGapFactor + thirdGapFactor +
          guessFactor + combinedFactor + denominatorFactor, ?_⟩
      unfold aboveThreeMarkerTwoNumerator aboveThreeMarkerTwoDigit
      rw [if_neg guessNe, countGap]
      have gapZero : guess - 3 * (first + 1) - 1 - gap = 0 := by
        dsimp [gap]
        omega
      rw [gapZero]
      simp only [Int.pow_zero, Int.one_mul]
      rw [firstEq, secondGapEq, thirdGapEq, guessPowerEq, combinedEq]
      change
        (base : Int) * firstFactor + 1 +
              (base : Int) * secondGapFactor +
              (base : Int) * thirdGapFactor + (base : Int) * guessFactor +
              (base : Int) * combinedFactor -
            markerTwoDenominator base first guess
              (aboveThreeMarkerTwoNumerator base first guess) = _
      calc
        (base : Int) * firstFactor + 1 +
              (base : Int) * secondGapFactor +
              (base : Int) * thirdGapFactor + (base : Int) * guessFactor +
              (base : Int) * combinedFactor -
            markerTwoDenominator base first guess
              (aboveThreeMarkerTwoNumerator base first guess) =
          (base : Int) * firstFactor +
              (base : Int) * secondGapFactor +
              (base : Int) * thirdGapFactor + (base : Int) * guessFactor +
              (base : Int) * combinedFactor +
            (1 - markerTwoDenominator base first guess
              (aboveThreeMarkerTwoNumerator base first guess)) := by grind
        _ = _ := by rw [denominatorEq]; grind

theorem aboveThreeMarkerTwoDigit_eq_two_iff (first guess : Nat) :
    aboveThreeMarkerTwoDigit first guess = 2 ↔
      guess = 4 * (first + 1) := by
  simp [aboveThreeMarkerTwoDigit]

def falseHandoffNumerator
    (base first guess deleted : Nat) : Int :=
  4 * (base : Int) ^ (guess - (first + 1) - 1 - deleted) +
    (base : Int) ^ (guess - 1 - deleted) +
    2 * (base : Int) ^ (2 * guess - (first + 1) - 1 - deleted) -
    (base : Int) ^ (2 * (first + 1) - guess - 1 - deleted) -
    (base : Int) ^ (first - deleted) -
    (base : Int) ^ (2 * (first + 1) - 1 - deleted)

def falseHandoffDenominator (base first guess : Nat) : Int :=
  markerTwoDenominator base first guess
      (falseMarkerTwoNumerator base first guess) -
    (base : Int) * falseHandoffNumerator base first guess 0

def falseHandoffState (base first guess deleted : Nat) : Rat :=
  state (falseHandoffNumerator base first guess deleted)
    (falseHandoffDenominator base first guess)

def falseHandoffZeroCount (first guess : Nat) : Nat :=
  min (guess - (first + 1) - 1)
    (2 * (first + 1) - guess - 1)

theorem falseHandoffDenominator_not_dvd
    (base first guess : Nat) (baseAtLeastTwo : 2 ≤ base) :
    ¬(base : Int) ∣ falseHandoffDenominator base first guess := by
  intro differenceDivisible
  have productDivisible : (base : Int) ∣
      (base : Int) * falseHandoffNumerator base first guess 0 :=
    ⟨falseHandoffNumerator base first guess 0, rfl⟩
  have sumDivisible := Int.dvd_add differenceDivisible productDivisible
  exact markerTwoDenominator_not_dvd base first guess _ baseAtLeastTwo
    (by simpa [falseHandoffDenominator] using sumDivisible)

theorem falseHandoffState_local
    (base first guess deleted : Nat) (baseAtLeastTwo : 2 ≤ base) :
    LocalAt base (Vec2.affine
      (falseHandoffState base first guess deleted)) := by
  exact state_local
    (falseHandoffDenominator_not_dvd base first guess baseAtLeastTwo)

theorem false_markerTwo_difference
    (base first guess : Nat) (QBelowGuess : first + 1 < guess)
    (guessBelowTwoQ : guess < 2 * (first + 1)) :
    falseMarkerTwoNumerator base first guess
          (falseMarkerTwoZeroCount first guess) -
        2 * markerTwoDenominator base first guess
          (falseMarkerTwoNumerator base first guess) =
      (base : Int) *
        (-falseHandoffNumerator base first guess 0) := by
  let count := falseMarkerTwoZeroCount first guess
  have countEq : count = guess - (first + 1) - 1 := rfl
  have firstEq : first - count = 2 * (first + 1) - guess := by
    dsimp [count, falseMarkerTwoZeroCount]
    omega
  have guessEq : guess - 1 - count = first + 1 := by
    dsimp [count, falseMarkerTwoZeroCount]
    omega
  have twiceGuessEq : 2 * guess - (first + 1) - 1 - count = guess := by
    dsimp [count, falseMarkerTwoZeroCount]
    omega
  have combinedEq : first + guess - count = 2 * (first + 1) := by
    dsimp [count, falseMarkerTwoZeroCount]
    omega
  have firstPower : (base : Int) ^ (first + 1) =
      (base : Int) ^ first * (base : Int) := by rw [Int.pow_succ]
  have leftGapPower : (base : Int) ^ (2 * (first + 1) - guess) =
      (base : Int) ^ (2 * (first + 1) - guess - 1) *
        (base : Int) := by
    calc
      (base : Int) ^ (2 * (first + 1) - guess) =
          (base : Int) ^ (2 * (first + 1) - guess - 1 + 1) := by
            congr 1 <;> omega
      _ = _ := by rw [Int.pow_succ]
  have rightGapPower : (base : Int) ^ (guess - (first + 1)) =
      (base : Int) ^ (guess - (first + 1) - 1) *
        (base : Int) := by
    calc
      (base : Int) ^ (guess - (first + 1)) =
          (base : Int) ^ (guess - (first + 1) - 1 + 1) := by
            congr 1 <;> omega
      _ = _ := by rw [Int.pow_succ]
  have guessPower : (base : Int) ^ guess =
      (base : Int) ^ (guess - 1) * (base : Int) := by
    calc
      (base : Int) ^ guess = (base : Int) ^ (guess - 1 + 1) := by
        congr 1 <;> omega
      _ = _ := by rw [Int.pow_succ]
  have twiceQPower : (base : Int) ^ (2 * (first + 1)) =
      (base : Int) ^ (2 * (first + 1) - 1) * (base : Int) := by
    calc
      (base : Int) ^ (2 * (first + 1)) =
          (base : Int) ^ (2 * (first + 1) - 1 + 1) := by
            congr 1 <;> omega
      _ = _ := by rw [Int.pow_succ]
  have twiceGuessGapPower :
      (base : Int) ^ (2 * guess - (first + 1)) =
        (base : Int) ^ (2 * guess - (first + 1) - 1) *
          (base : Int) := by
    calc
      (base : Int) ^ (2 * guess - (first + 1)) =
          (base : Int) ^ (2 * guess - (first + 1) - 1 + 1) := by
            congr 1 <;> omega
      _ = _ := by rw [Int.pow_succ]
  have combinedPower : (base : Int) ^ (first + guess + 1) =
      (base : Int) ^ (first + guess) * (base : Int) := by
    rw [Int.pow_succ]
  have terminalNumerator :
      falseMarkerTwoNumerator base first guess count =
        (base : Int) ^ (2 * (first + 1) - guess) + 2 +
          (base : Int) ^ (first + 1) + (base : Int) ^ guess +
          (base : Int) ^ (2 * (first + 1)) := by
    unfold falseMarkerTwoNumerator
    rw [show guess - (first + 1) - 1 - count = 0 by
      dsimp [count, falseMarkerTwoZeroCount]; omega]
    simp only [Int.pow_zero, Int.mul_one]
    rw [firstEq, guessEq, twiceGuessEq, combinedEq]
  have denominatorExpanded :
      markerTwoDenominator base first guess
          (falseMarkerTwoNumerator base first guess) =
        1 + 2 * (base : Int) ^ (guess - (first + 1)) +
          (base : Int) ^ guess +
          (base : Int) ^ (2 * guess - (first + 1)) := by
    unfold markerTwoDenominator halfIntegerDenominator
      falseMarkerTwoNumerator
    simp only [Nat.sub_zero]
    rw [firstPower, rightGapPower, guessPower, twiceGuessGapPower,
      combinedPower]
    grind
  rw [terminalNumerator, denominatorExpanded]
  unfold falseHandoffNumerator
  simp only [Nat.sub_zero]
  rw [leftGapPower, firstPower, rightGapPower, guessPower, twiceQPower,
    twiceGuessGapPower]
  grind

theorem false_markerTwo_to_handoff
    (base first guess : Nat) (baseAtLeastTwo : 2 ≤ base)
    (QBelowGuess : first + 1 < guess)
    (guessBelowTwoQ : guess < 2 * (first + 1)) :
    mutationMap base .negative 1
        (deleteDigit (base : Rat) 2
          (falseMarkerTwoState base first guess
            (falseMarkerTwoZeroCount first guess))) =
      falseHandoffState base first guess 0 := by
  let markerDenominator := markerTwoDenominator base first guess
    (falseMarkerTwoNumerator base first guess)
  let handoffNumerator := falseHandoffNumerator base first guess 0
  have markerDenominatorNotDivisible := markerTwoDenominator_not_dvd base
    first guess (falseMarkerTwoNumerator base first guess) baseAtLeastTwo
  have markerDenominatorNonzero := denominator_nonzero_of_not_dvd
    markerDenominatorNotDivisible
  have deleteEq := deleteDigit_eq base 2
    (falseMarkerTwoNumerator base first guess
      (falseMarkerTwoZeroCount first guess)) markerDenominator
    (-handoffNumerator) (by omega) markerDenominatorNonzero
    (by simpa [markerDenominator, handoffNumerator] using
      (false_markerTwo_difference base first guess QBelowGuess
        guessBelowTwoQ))
  rw [falseMarkerTwoState, deleteEq]
  have outputDenominatorEq :
      markerDenominator + (base : Int) * (-handoffNumerator) =
        falseHandoffDenominator base first guess := by
    dsimp [markerDenominator, handoffNumerator]
    unfold falseHandoffDenominator
    grind
  have outputDenominatorNonzero :
      markerDenominator + (base : Int) * (-handoffNumerator) ≠ 0 := by
    rw [outputDenominatorEq]
    exact denominator_nonzero_of_not_dvd
      (falseHandoffDenominator_not_dvd base first guess baseAtLeastTwo)
  have mutationEq := negativeOneMutation_state base (-handoffNumerator)
    markerDenominator markerDenominatorNonzero outputDenominatorNonzero
  rw [mutationEq]
  rw [outputDenominatorEq]
  simp [falseHandoffState, handoffNumerator]

theorem falseHandoffNumerator_step
    (base first guess deleted : Nat)
    (QBelowGuess : first + 1 < guess)
    (guessBelowTwoQ : guess < 2 * (first + 1))
    (deletedBelow : deleted < falseHandoffZeroCount first guess) :
    falseHandoffNumerator base first guess deleted =
      (base : Int) *
        falseHandoffNumerator base first guess (deleted + 1) := by
  have belowLeft : deleted < guess - (first + 1) - 1 :=
    Nat.lt_of_lt_of_le deletedBelow (Nat.min_le_left _ _)
  have belowRight : deleted < 2 * (first + 1) - guess - 1 :=
    Nat.lt_of_lt_of_le deletedBelow (Nat.min_le_right _ _)
  have leftExponent : guess - (first + 1) - 1 - deleted =
      guess - (first + 1) - 1 - (deleted + 1) + 1 := by omega
  have guessExponent : guess - 1 - deleted =
      guess - 1 - (deleted + 1) + 1 := by omega
  have twiceGuessExponent : 2 * guess - (first + 1) - 1 - deleted =
      2 * guess - (first + 1) - 1 - (deleted + 1) + 1 := by omega
  have rightExponent : 2 * (first + 1) - guess - 1 - deleted =
      2 * (first + 1) - guess - 1 - (deleted + 1) + 1 := by omega
  have firstExponent : first - deleted =
      first - (deleted + 1) + 1 := by omega
  have twiceQExponent : 2 * (first + 1) - 1 - deleted =
      2 * (first + 1) - 1 - (deleted + 1) + 1 := by omega
  unfold falseHandoffNumerator
  rw [leftExponent, guessExponent, twiceGuessExponent, rightExponent,
    firstExponent, twiceQExponent]
  simp only [Int.pow_succ]
  grind

theorem falseHandoffState_delete_zero
    (base first guess deleted : Nat) (baseAtLeastTwo : 2 ≤ base)
    (QBelowGuess : first + 1 < guess)
    (guessBelowTwoQ : guess < 2 * (first + 1))
    (deletedBelow : deleted < falseHandoffZeroCount first guess) :
    deleteDigit (base : Rat) 0
        (falseHandoffState base first guess deleted) =
      falseHandoffState base first guess (deleted + 1) := by
  apply deleteZero_eq base _ _ _ (by omega)
    (denominator_nonzero_of_not_dvd
      (falseHandoffDenominator_not_dvd base first guess baseAtLeastTwo))
  exact falseHandoffNumerator_step base first guess deleted QBelowGuess
    guessBelowTwoQ deletedBelow

theorem falseHandoffState_sameLine_integer
    (base first guess deleted : Nat) (baseAtLeastTwo : 2 ≤ base) :
    SameLine (Vec2.affine (falseHandoffState base first guess deleted))
      (integerVector (falseHandoffNumerator base first guess deleted)
        (falseHandoffDenominator base first guess)) := by
  exact sameLine_integer (denominator_nonzero_of_not_dvd
    (falseHandoffDenominator_not_dvd base first guess baseAtLeastTwo))

theorem falseHandoffDenominator_one_residue
    (base first guess : Nat) :
    (base : Int) ∣ 1 - falseHandoffDenominator base first guess := by
  rcases markerTwoDenominator_one_residue base first guess
      (falseMarkerTwoNumerator base first guess) with
    ⟨factor, factorEq⟩
  refine ⟨factor + falseHandoffNumerator base first guess 0, ?_⟩
  unfold falseHandoffDenominator
  calc
    1 - (markerTwoDenominator base first guess
          (falseMarkerTwoNumerator base first guess) -
        (base : Int) * falseHandoffNumerator base first guess 0) =
      (1 - markerTwoDenominator base first guess
          (falseMarkerTwoNumerator base first guess)) +
        (base : Int) * falseHandoffNumerator base first guess 0 := by grind
    _ = (base : Int) * factor +
        (base : Int) * falseHandoffNumerator base first guess 0 := by
      rw [factorEq]
    _ = _ := by grind

theorem falseHandoff_marker_residue_four
    (base first guess : Nat) (QBelowGuess : first + 1 < guess)
    (twoGuessBelowThreeQ : 2 * guess < 3 * (first + 1)) :
    (base : Int) ∣
      falseHandoffNumerator base first guess
          (falseHandoffZeroCount first guess) -
        4 * falseHandoffDenominator base first guess := by
  have leftBelowRight : guess - (first + 1) - 1 <
      2 * (first + 1) - guess - 1 := by omega
  have countEq : falseHandoffZeroCount first guess =
      guess - (first + 1) - 1 := by
    simp [falseHandoffZeroCount,
      Nat.min_eq_left (Nat.le_of_lt leftBelowRight)]
  let count := falseHandoffZeroCount first guess
  have guessPositive : 0 < guess - 1 - count := by
    dsimp [count]
    omega
  have twiceGuessPositive :
      0 < 2 * guess - (first + 1) - 1 - count := by
    dsimp [count]
    omega
  have rightPositive :
      0 < 2 * (first + 1) - guess - 1 - count := by
    dsimp [count]
    omega
  have firstPositive : 0 < first - count := by
    dsimp [count]
    omega
  have twiceQPositive : 0 < 2 * (first + 1) - 1 - count := by
    dsimp [count]
    omega
  rcases base_dvd_positive_power base _ guessPositive with
    ⟨guessFactor, guessEq⟩
  rcases base_dvd_positive_power base _ twiceGuessPositive with
    ⟨twiceGuessFactor, twiceGuessEq⟩
  rcases base_dvd_positive_power base _ rightPositive with
    ⟨rightFactor, rightEq⟩
  rcases base_dvd_positive_power base _ firstPositive with
    ⟨firstFactor, firstEq⟩
  rcases base_dvd_positive_power base _ twiceQPositive with
    ⟨twiceQFactor, twiceQEq⟩
  rcases falseHandoffDenominator_one_residue base first guess with
    ⟨denominatorFactor, denominatorEq⟩
  refine ⟨guessFactor + 2 * twiceGuessFactor - rightFactor -
      firstFactor - twiceQFactor + 4 * denominatorFactor, ?_⟩
  have leftZero :
      guess - (first + 1) - 1 - count = 0 := by
    dsimp [count]
    omega
  unfold falseHandoffNumerator
  rw [leftZero]
  simp only [Int.pow_zero, Int.mul_one]
  rw [guessEq, twiceGuessEq, rightEq, firstEq, twiceQEq]
  calc
    4 + (base : Int) * guessFactor +
          2 * ((base : Int) * twiceGuessFactor) -
          (base : Int) * rightFactor - (base : Int) * firstFactor -
          (base : Int) * twiceQFactor -
        4 * falseHandoffDenominator base first guess =
      (base : Int) * guessFactor +
          2 * ((base : Int) * twiceGuessFactor) -
          (base : Int) * rightFactor - (base : Int) * firstFactor -
          (base : Int) * twiceQFactor +
        4 * (1 - falseHandoffDenominator base first guess) := by grind
    _ = _ := by rw [denominatorEq]; grind

theorem falseHandoff_marker_residue_three
    (base first guess : Nat) (_QBelowGuess : first + 1 < guess)
    (twoGuessEqThreeQ : 2 * guess = 3 * (first + 1)) :
    (base : Int) ∣
      falseHandoffNumerator base first guess
          (falseHandoffZeroCount first guess) -
        3 * falseHandoffDenominator base first guess := by
  have leadsEq : guess - (first + 1) - 1 =
      2 * (first + 1) - guess - 1 := by omega
  have countEq : falseHandoffZeroCount first guess =
      guess - (first + 1) - 1 := by
    simp [falseHandoffZeroCount, leadsEq]
  let count := falseHandoffZeroCount first guess
  have guessPositive : 0 < guess - 1 - count := by
    dsimp [count]
    omega
  have twiceGuessPositive :
      0 < 2 * guess - (first + 1) - 1 - count := by
    dsimp [count]
    omega
  have firstPositive : 0 < first - count := by
    dsimp [count]
    omega
  have twiceQPositive : 0 < 2 * (first + 1) - 1 - count := by
    dsimp [count]
    omega
  rcases base_dvd_positive_power base _ guessPositive with
    ⟨guessFactor, guessEq⟩
  rcases base_dvd_positive_power base _ twiceGuessPositive with
    ⟨twiceGuessFactor, twiceGuessEq⟩
  rcases base_dvd_positive_power base _ firstPositive with
    ⟨firstFactor, firstEq⟩
  rcases base_dvd_positive_power base _ twiceQPositive with
    ⟨twiceQFactor, twiceQEq⟩
  rcases falseHandoffDenominator_one_residue base first guess with
    ⟨denominatorFactor, denominatorEq⟩
  refine ⟨guessFactor + 2 * twiceGuessFactor - firstFactor -
      twiceQFactor + 3 * denominatorFactor, ?_⟩
  have leftZero : guess - (first + 1) - 1 - count = 0 := by
    dsimp [count]
    omega
  have rightZero : 2 * (first + 1) - guess - 1 - count = 0 := by
    dsimp [count]
    omega
  unfold falseHandoffNumerator
  rw [leftZero, rightZero]
  simp only [Int.pow_zero, Int.mul_one]
  rw [guessEq, twiceGuessEq, firstEq, twiceQEq]
  calc
    4 + (base : Int) * guessFactor +
          2 * ((base : Int) * twiceGuessFactor) - 1 -
          (base : Int) * firstFactor - (base : Int) * twiceQFactor -
        3 * falseHandoffDenominator base first guess =
      (base : Int) * guessFactor +
          2 * ((base : Int) * twiceGuessFactor) -
          (base : Int) * firstFactor - (base : Int) * twiceQFactor +
        3 * (1 - falseHandoffDenominator base first guess) := by grind
    _ = _ := by rw [denominatorEq]; grind

theorem falseHandoff_marker_residue_negative_one
    (base first guess : Nat)
    (twoGuessAboveThreeQ : 3 * (first + 1) < 2 * guess)
    (guessBelowTwoQ : guess < 2 * (first + 1)) :
    (base : Int) ∣
      falseHandoffNumerator base first guess
          (falseHandoffZeroCount first guess) -
        (-1) * falseHandoffDenominator base first guess := by
  have rightBelowLeft : 2 * (first + 1) - guess - 1 <
      guess - (first + 1) - 1 := by omega
  have countEq : falseHandoffZeroCount first guess =
      2 * (first + 1) - guess - 1 := by
    simp [falseHandoffZeroCount,
      Nat.min_eq_right (Nat.le_of_lt rightBelowLeft)]
  let count := falseHandoffZeroCount first guess
  have leftPositive : 0 < guess - (first + 1) - 1 - count := by
    dsimp [count]
    omega
  have guessPositive : 0 < guess - 1 - count := by
    dsimp [count]
    omega
  have twiceGuessPositive :
      0 < 2 * guess - (first + 1) - 1 - count := by
    dsimp [count]
    omega
  have firstPositive : 0 < first - count := by
    dsimp [count]
    omega
  have twiceQPositive : 0 < 2 * (first + 1) - 1 - count := by
    dsimp [count]
    omega
  rcases base_dvd_positive_power base _ leftPositive with
    ⟨leftFactor, leftEq⟩
  rcases base_dvd_positive_power base _ guessPositive with
    ⟨guessFactor, guessEq⟩
  rcases base_dvd_positive_power base _ twiceGuessPositive with
    ⟨twiceGuessFactor, twiceGuessEq⟩
  rcases base_dvd_positive_power base _ firstPositive with
    ⟨firstFactor, firstEq⟩
  rcases base_dvd_positive_power base _ twiceQPositive with
    ⟨twiceQFactor, twiceQEq⟩
  rcases falseHandoffDenominator_one_residue base first guess with
    ⟨denominatorFactor, denominatorEq⟩
  refine ⟨4 * leftFactor + guessFactor + 2 * twiceGuessFactor -
      firstFactor - twiceQFactor - denominatorFactor, ?_⟩
  have rightZero : 2 * (first + 1) - guess - 1 - count = 0 := by
    dsimp [count]
    omega
  unfold falseHandoffNumerator
  rw [rightZero]
  simp only [Int.pow_zero]
  rw [leftEq, guessEq, twiceGuessEq, firstEq, twiceQEq]
  simp only [Int.neg_one_mul]
  calc
    4 * ((base : Int) * leftFactor) + (base : Int) * guessFactor +
          2 * ((base : Int) * twiceGuessFactor) - 1 -
          (base : Int) * firstFactor - (base : Int) * twiceQFactor -
        (-falseHandoffDenominator base first guess) =
      4 * ((base : Int) * leftFactor) + (base : Int) * guessFactor +
          2 * ((base : Int) * twiceGuessFactor) -
          (base : Int) * firstFactor - (base : Int) * twiceQFactor -
        (1 - falseHandoffDenominator base first guess) := by grind
    _ = _ := by rw [denominatorEq]; grind

def acceptedHandoffNumerator (base first : Nat) : Int :=
  (base : Int) ^ first +
    (base : Int) ^ (2 * (first + 1) - 1) +
    (base : Int) ^ (3 * (first + 1) - 1) +
    (base : Int) ^ (4 * (first + 1) - 1)

def acceptedMarkerDenominator (base first : Nat) : Int :=
  markerTwoDenominator base first (4 * (first + 1))
    (aboveThreeMarkerTwoNumerator base first (4 * (first + 1)))

def acceptedHandoffDenominator (base first : Nat) : Int :=
  acceptedMarkerDenominator base first -
    (base : Int) * acceptedHandoffNumerator base first

def acceptedHandoffState (base first : Nat) : Rat :=
  state (acceptedHandoffNumerator base first)
    (acceptedHandoffDenominator base first)

theorem acceptedMarkerDenominator_eq (base first : Nat) :
    let q : Int := (base : Int) ^ (first + 1)
    acceptedMarkerDenominator base first =
      1 + q + q ^ 2 + q ^ 3 + q ^ 4 := by
  dsimp
  let Q := first + 1
  let q : Int := (base : Int) ^ Q
  have firstSucc : (base : Int) ^ (first + 1) =
      (base : Int) ^ first * (base : Int) := by rw [Int.pow_succ]
  have twiceSucc : (base : Int) ^ (2 * Q) =
      (base : Int) ^ (2 * Q - 1) * (base : Int) := by
    calc
      (base : Int) ^ (2 * Q) =
          (base : Int) ^ (2 * Q - 1 + 1) := by congr 1 <;> omega
      _ = _ := by rw [Int.pow_succ]
  have threeSucc : (base : Int) ^ (3 * Q) =
      (base : Int) ^ (3 * Q - 1) * (base : Int) := by
    calc
      (base : Int) ^ (3 * Q) =
          (base : Int) ^ (3 * Q - 1 + 1) := by congr 1 <;> omega
      _ = _ := by rw [Int.pow_succ]
  have fourSucc : (base : Int) ^ (4 * Q) =
      (base : Int) ^ (4 * Q - 1) * (base : Int) := by
    calc
      (base : Int) ^ (4 * Q) =
          (base : Int) ^ (4 * Q - 1 + 1) := by congr 1 <;> omega
      _ = _ := by rw [Int.pow_succ]
  have fivePower : (base : Int) ^ (5 * Q) = q ^ 5 := by
    rw [show 5 * Q = Q + Q + Q + Q + Q by omega]
    repeat' rw [Lean.Grind.Semiring.pow_add]
    grind
  have twicePower : (base : Int) ^ (2 * Q) = q ^ 2 := by
    rw [show 2 * Q = Q + Q by omega, Lean.Grind.Semiring.pow_add]
    grind
  have threePower : (base : Int) ^ (3 * Q) = q ^ 3 := by
    rw [show 3 * Q = Q + Q + Q by omega]
    repeat' rw [Lean.Grind.Semiring.pow_add]
    grind
  have fourPower : (base : Int) ^ (4 * Q) = q ^ 4 := by
    rw [show 4 * Q = Q + Q + Q + Q by omega]
    repeat' rw [Lean.Grind.Semiring.pow_add]
    grind
  unfold acceptedMarkerDenominator markerTwoDenominator
    halfIntegerDenominator aboveThreeMarkerTwoNumerator
  simp only [Nat.sub_zero]
  rw [show first + 4 * (first + 1) + 1 = 5 * Q by omega,
    show 4 * (first + 1) - 3 * (first + 1) - 1 = first by omega,
    show 4 * (first + 1) - 2 * (first + 1) - 1 =
      2 * Q - 1 by omega,
    show 4 * (first + 1) - (first + 1) - 1 =
      3 * Q - 1 by omega,
    show 4 * (first + 1) - 1 = 4 * Q - 1 by omega,
    show first + 4 * (first + 1) = 5 * Q - 1 by omega]
  have fiveSucc : (base : Int) ^ (5 * Q) =
      (base : Int) ^ (5 * Q - 1) * (base : Int) := by
    calc
      (base : Int) ^ (5 * Q) =
          (base : Int) ^ (5 * Q - 1 + 1) := by congr 1 <;> omega
      _ = _ := by rw [Int.pow_succ]
  have firstProduct : (base : Int) * (base : Int) ^ first = q := by
    rw [Int.mul_comm]
    simpa [q, Q] using firstSucc.symm
  have twiceProduct :
      (base : Int) * (base : Int) ^ (2 * Q - 1) = q ^ 2 := by
    rw [Int.mul_comm, ← twiceSucc, twicePower]
  have threeProduct :
      (base : Int) * (base : Int) ^ (3 * Q - 1) = q ^ 3 := by
    rw [Int.mul_comm, ← threeSucc, threePower]
  have fourProduct :
      (base : Int) * (base : Int) ^ (4 * Q - 1) = q ^ 4 := by
    rw [Int.mul_comm, ← fourSucc, fourPower]
  have fiveProduct :
      (base : Int) * (base : Int) ^ (5 * Q - 1) = q ^ 5 := by
    rw [Int.mul_comm, ← fiveSucc, fivePower]
  have qEq : (base : Int) ^ (first + 1) = q := by rfl
  rw [fivePower, qEq]
  grind

theorem accepted_markerTwo_difference (base first : Nat) :
    aboveThreeMarkerTwoNumerator base first (4 * (first + 1)) first -
        2 * acceptedMarkerDenominator base first =
      (base : Int) * (-acceptedHandoffNumerator base first) := by
  let Q := first + 1
  let q : Int := (base : Int) ^ Q
  have firstSucc : (base : Int) ^ (first + 1) =
      (base : Int) ^ first * (base : Int) := by rw [Int.pow_succ]
  have twiceSucc : (base : Int) ^ (2 * Q) =
      (base : Int) ^ (2 * Q - 1) * (base : Int) := by
    calc
      (base : Int) ^ (2 * Q) =
          (base : Int) ^ (2 * Q - 1 + 1) := by congr 1 <;> omega
      _ = _ := by rw [Int.pow_succ]
  have threeSucc : (base : Int) ^ (3 * Q) =
      (base : Int) ^ (3 * Q - 1) * (base : Int) := by
    calc
      (base : Int) ^ (3 * Q) =
          (base : Int) ^ (3 * Q - 1 + 1) := by congr 1 <;> omega
      _ = _ := by rw [Int.pow_succ]
  have fourSucc : (base : Int) ^ (4 * Q) =
      (base : Int) ^ (4 * Q - 1) * (base : Int) := by
    calc
      (base : Int) ^ (4 * Q) =
          (base : Int) ^ (4 * Q - 1 + 1) := by congr 1 <;> omega
      _ = _ := by rw [Int.pow_succ]
  have firstProduct : (base : Int) * (base : Int) ^ first = q := by
    rw [Int.mul_comm]
    simpa [q, Q] using firstSucc.symm
  have twiceProduct :
      (base : Int) * (base : Int) ^ (2 * Q - 1) =
        (base : Int) ^ (2 * Q) := by
    rw [Int.mul_comm, ← twiceSucc]
  have threeProduct :
      (base : Int) * (base : Int) ^ (3 * Q - 1) =
        (base : Int) ^ (3 * Q) := by
    rw [Int.mul_comm, ← threeSucc]
  have fourProduct :
      (base : Int) * (base : Int) ^ (4 * Q - 1) =
        (base : Int) ^ (4 * Q) := by
    rw [Int.mul_comm, ← fourSucc]
  have twicePower : (base : Int) ^ (2 * Q) = q ^ 2 := by
    rw [show 2 * Q = Q + Q by omega, Lean.Grind.Semiring.pow_add]
    grind
  have threePower : (base : Int) ^ (3 * Q) = q ^ 3 := by
    rw [show 3 * Q = Q + Q + Q by omega]
    repeat' rw [Lean.Grind.Semiring.pow_add]
    grind
  have fourPower : (base : Int) ^ (4 * Q) = q ^ 4 := by
    rw [show 4 * Q = Q + Q + Q + Q by omega]
    repeat' rw [Lean.Grind.Semiring.pow_add]
    grind
  have scaledHandoff :
      (base : Int) * acceptedHandoffNumerator base first =
        q + q ^ 2 + q ^ 3 + q ^ 4 := by
    unfold acceptedHandoffNumerator
    rw [Int.mul_add, Int.mul_add, Int.mul_add]
    rw [firstProduct, twiceProduct, threeProduct, fourProduct,
      twicePower, threePower, fourPower]
  have denominatorEq := acceptedMarkerDenominator_eq base first
  dsimp only at denominatorEq
  change acceptedMarkerDenominator base first =
    1 + q + q ^ 2 + q ^ 3 + q ^ 4 at denominatorEq
  unfold aboveThreeMarkerTwoNumerator
  rw [show 4 * (first + 1) - 3 * (first + 1) - 1 - first = 0 by omega,
    show 4 * (first + 1) - 2 * (first + 1) - 1 - first = Q by omega,
    show 4 * (first + 1) - (first + 1) - 1 - first = 2 * Q by omega,
    show 4 * (first + 1) - 1 - first = 3 * Q by omega,
    show first + 4 * (first + 1) - first = 4 * Q by omega]
  simp only [Nat.sub_self, Int.pow_zero]
  rw [denominatorEq]
  rw [show (base : Int) ^ Q = q by rfl, twicePower, threePower, fourPower]
  rw [Int.mul_neg, scaledHandoff]
  grind

theorem acceptedHandoffCoordinate_eq
    (base first : Nat) (baseAtLeastTwo : 2 ≤ base) :
    state (acceptedHandoffNumerator base first)
        (acceptedMarkerDenominator base first) =
      twoFieldCode base first (4 * first + 3) := by
  let Q := first + 1
  let q : Rat := (base : Rat) ^ Q
  have firstSucc : (base : Int) ^ (first + 1) =
      (base : Int) ^ first * (base : Int) := by rw [Int.pow_succ]
  have twiceSucc : (base : Int) ^ (2 * Q) =
      (base : Int) ^ (2 * Q - 1) * (base : Int) := by
    calc
      (base : Int) ^ (2 * Q) =
          (base : Int) ^ (2 * Q - 1 + 1) := by congr 1 <;> omega
      _ = _ := by rw [Int.pow_succ]
  have threeSucc : (base : Int) ^ (3 * Q) =
      (base : Int) ^ (3 * Q - 1) * (base : Int) := by
    calc
      (base : Int) ^ (3 * Q) =
          (base : Int) ^ (3 * Q - 1 + 1) := by congr 1 <;> omega
      _ = _ := by rw [Int.pow_succ]
  have fourSucc : (base : Int) ^ (4 * Q) =
      (base : Int) ^ (4 * Q - 1) * (base : Int) := by
    calc
      (base : Int) ^ (4 * Q) =
          (base : Int) ^ (4 * Q - 1 + 1) := by congr 1 <;> omega
      _ = _ := by rw [Int.pow_succ]
  have scaledNumeratorInt :
      (base : Int) * acceptedHandoffNumerator base first =
        (base : Int) ^ Q + (base : Int) ^ (2 * Q) +
          (base : Int) ^ (3 * Q) + (base : Int) ^ (4 * Q) := by
    unfold acceptedHandoffNumerator
    rw [Int.mul_add, Int.mul_add, Int.mul_add]
    rw [Int.mul_comm (base : Int) ((base : Int) ^ first), ← firstSucc,
      Int.mul_comm (base : Int) ((base : Int) ^ (2 * Q - 1)),
      ← twiceSucc,
      Int.mul_comm (base : Int) ((base : Int) ^ (3 * Q - 1)),
      ← threeSucc,
      Int.mul_comm (base : Int) ((base : Int) ^ (4 * Q - 1)),
      ← fourSucc]
  have scaledNumeratorRat :
      (base : Rat) * (acceptedHandoffNumerator base first : Rat) =
        q + q ^ 2 + q ^ 3 + q ^ 4 := by
    have castEq :
        (((base : Int) * acceptedHandoffNumerator base first : Int) : Rat) =
          (((base : Int) ^ Q + (base : Int) ^ (2 * Q) +
            (base : Int) ^ (3 * Q) + (base : Int) ^ (4 * Q) : Int) : Rat) :=
      congrArg (fun value : Int => (value : Rat)) scaledNumeratorInt
    have raw :
        (base : Rat) * (acceptedHandoffNumerator base first : Rat) =
          (base : Rat) ^ Q + (base : Rat) ^ (2 * Q) +
            (base : Rat) ^ (3 * Q) + (base : Rat) ^ (4 * Q) := by
      simpa [Rat.intCast_mul, Rat.intCast_add, Rat.intCast_pow,
        Rat.intCast_natCast] using castEq
    have twicePower : (base : Rat) ^ (2 * Q) = q ^ 2 := by
      simpa [q] using rat_pow_two_block (base : Rat) Q
    have threePower : (base : Rat) ^ (3 * Q) = q ^ 3 := by
      simpa [q] using rat_pow_three_block (base : Rat) Q
    have fourPower : (base : Rat) ^ (4 * Q) = q ^ 4 := by
      simpa [q] using rat_pow_four_block (base : Rat) Q
    rw [show (base : Rat) ^ Q = q by rfl, twicePower, threePower,
      fourPower] at raw
    exact raw
  have denominatorEqInt := acceptedMarkerDenominator_eq base first
  dsimp only at denominatorEqInt
  have denominatorEqRat :
      (acceptedMarkerDenominator base first : Rat) =
        1 + q + q ^ 2 + q ^ 3 + q ^ 4 := by
    have castEq := congrArg (fun value : Int => (value : Rat))
      denominatorEqInt
    simpa [q, Q, Rat.intCast_add, Rat.intCast_pow,
      Rat.intCast_natCast] using castEq
  have scaledState :
      (base : Rat) *
          state (acceptedHandoffNumerator base first)
            (acceptedMarkerDenominator base first) =
        (q + q ^ 2 + q ^ 3 + q ^ 4) /
          (1 + q + q ^ 2 + q ^ 3 + q ^ 4) := by
    unfold state
    rw [denominatorEqRat]
    simp only [Rat.div_def]
    rw [← Rat.mul_assoc, scaledNumeratorRat]
  have coordinate := accepted_front_coordinate_eq_twoFieldCode base first
    baseAtLeastTwo
  dsimp only at coordinate
  have productEq :
      (base : Rat) *
          state (acceptedHandoffNumerator base first)
            (acceptedMarkerDenominator base first) =
        (base : Rat) * twoFieldCode base first (4 * first + 3) := by
    rw [scaledState]
    simpa [q, Q] using coordinate
  have baseNonzero : (base : Rat) ≠ 0 := by
    simpa using (show base ≠ 0 by omega)
  calc
    state (acceptedHandoffNumerator base first)
        (acceptedMarkerDenominator base first) =
      ((base : Rat)⁻¹ * (base : Rat)) *
        state (acceptedHandoffNumerator base first)
          (acceptedMarkerDenominator base first) := by
            rw [Rat.inv_mul_cancel (base : Rat) baseNonzero, Rat.one_mul]
    _ = (base : Rat)⁻¹ *
        ((base : Rat) * state (acceptedHandoffNumerator base first)
          (acceptedMarkerDenominator base first)) := by rw [Rat.mul_assoc]
    _ = (base : Rat)⁻¹ *
        ((base : Rat) * twoFieldCode base first (4 * first + 3)) := by
          rw [productEq]
    _ = ((base : Rat)⁻¹ * (base : Rat)) *
        twoFieldCode base first (4 * first + 3) := by rw [Rat.mul_assoc]
    _ = twoFieldCode base first (4 * first + 3) := by
      rw [Rat.inv_mul_cancel (base : Rat) baseNonzero, Rat.one_mul]

theorem acceptedHandoffDenominator_not_dvd
    (base first : Nat) (baseAtLeastTwo : 2 ≤ base) :
    ¬(base : Int) ∣ acceptedHandoffDenominator base first := by
  intro differenceDivisible
  have productDivisible : (base : Int) ∣
      (base : Int) * acceptedHandoffNumerator base first :=
    ⟨acceptedHandoffNumerator base first, rfl⟩
  have sumDivisible := Int.dvd_add differenceDivisible productDivisible
  exact markerTwoDenominator_not_dvd base first (4 * (first + 1)) _
    baseAtLeastTwo (by
      simpa [acceptedHandoffDenominator, acceptedMarkerDenominator] using
        sumDivisible)

theorem acceptedHandoffState_local
    (base first : Nat) (baseAtLeastTwo : 2 ≤ base) :
    LocalAt base (Vec2.affine (acceptedHandoffState base first)) := by
  exact state_local
    (acceptedHandoffDenominator_not_dvd base first baseAtLeastTwo)

theorem acceptedHandoffState_eq
    (base first : Nat) (baseAtLeastTwo : 2 ≤ base) :
    acceptedHandoffState base first =
      T base (twoFieldCode base first (4 * first + 3)) := by
  have markerNonzero := denominator_nonzero_of_not_dvd
    (markerTwoDenominator_not_dvd base first (4 * (first + 1))
      (aboveThreeMarkerTwoNumerator base first (4 * (first + 1)))
      baseAtLeastTwo)
  have handoffNonzero := denominator_nonzero_of_not_dvd
    (acceptedHandoffDenominator_not_dvd base first baseAtLeastTwo)
  have transformed := T_state base (acceptedHandoffNumerator base first)
    (acceptedMarkerDenominator base first) markerNonzero handoffNonzero
  rw [acceptedHandoffCoordinate_eq base first baseAtLeastTwo] at transformed
  simpa [acceptedHandoffState, acceptedHandoffDenominator] using
    transformed.symm

theorem accepted_markerTwo_to_handoff
    (base first : Nat) (baseAtLeastTwo : 2 ≤ base) :
    mutationMap base .negative 1
        (deleteDigit (base : Rat) 2
          (aboveThreeMarkerTwoState base first (4 * (first + 1)) first)) =
      acceptedHandoffState base first := by
  let markerDenominator := acceptedMarkerDenominator base first
  let handoffNumerator := acceptedHandoffNumerator base first
  have markerDenominatorNonzero := denominator_nonzero_of_not_dvd
    (markerTwoDenominator_not_dvd base first (4 * (first + 1))
      (aboveThreeMarkerTwoNumerator base first (4 * (first + 1)))
      baseAtLeastTwo)
  have deleteEq := deleteDigit_eq base 2
    (aboveThreeMarkerTwoNumerator base first (4 * (first + 1)) first)
    markerDenominator (-handoffNumerator) (by omega)
    markerDenominatorNonzero (by
      simpa [markerDenominator, handoffNumerator,
        acceptedMarkerDenominator] using
        (accepted_markerTwo_difference base first))
  change mutationMap base .negative 1
      (deleteDigit (base : Rat) 2
        (state
          (aboveThreeMarkerTwoNumerator base first (4 * (first + 1)) first)
          markerDenominator)) = acceptedHandoffState base first
  rw [deleteEq]
  have outputDenominatorEq :
      markerDenominator + (base : Int) * (-handoffNumerator) =
        acceptedHandoffDenominator base first := by
    dsimp [markerDenominator, handoffNumerator]
    unfold acceptedHandoffDenominator
    grind
  have outputDenominatorNonzero :
      markerDenominator + (base : Int) * (-handoffNumerator) ≠ 0 := by
    rw [outputDenominatorEq]
    exact denominator_nonzero_of_not_dvd
      (acceptedHandoffDenominator_not_dvd base first baseAtLeastTwo)
  have mutationEq := negativeOneMutation_state base (-handoffNumerator)
    markerDenominator markerDenominatorNonzero outputDenominatorNonzero
  rw [mutationEq, outputDenominatorEq]
  simp [acceptedHandoffState, handoffNumerator]

inductive FivefoldOutcome (first guess : Nat) : Prop where
  | fifthRejectSmall
      (guessBelowQ : guess < first + 1) : FivefoldOutcome first guess
  | thirdRejectAtQ
      (guessEqQ : guess = first + 1) : FivefoldOutcome first guess
  | falseSurvivor
      (QBelowGuess : first + 1 < guess)
      (guessBelowTwoQ : guess < 2 * (first + 1)) :
      FivefoldOutcome first guess
  | fourthRejectAtTwoQ
      (guessEqTwoQ : guess = 2 * (first + 1)) :
      FivefoldOutcome first guess
  | markerTwoRejectMiddle
      (twoQBelowGuess : 2 * (first + 1) < guess)
      (guessBelowThreeQ : guess < 3 * (first + 1)) :
      FivefoldOutcome first guess
  | fifthRejectAtThreeQ
      (guessEqThreeQ : guess = 3 * (first + 1)) :
      FivefoldOutcome first guess
  | accepted
      (guessEqFourQ : guess = 4 * (first + 1)) :
      FivefoldOutcome first guess
  | markerTwoRejectHigh
      (threeQBelowGuess : 3 * (first + 1) < guess)
      (guessNeFourQ : guess ≠ 4 * (first + 1)) :
      FivefoldOutcome first guess

theorem exhaustive_fivefold_outcome (first guess : Nat)
    (_guessPositive : 0 < guess) : FivefoldOutcome first guess := by
  by_cases guessBelowQ : guess < first + 1
  · exact .fifthRejectSmall guessBelowQ
  by_cases guessEqQ : guess = first + 1
  · exact .thirdRejectAtQ guessEqQ
  have QBelowGuess : first + 1 < guess := by omega
  by_cases guessBelowTwoQ : guess < 2 * (first + 1)
  · exact .falseSurvivor QBelowGuess guessBelowTwoQ
  by_cases guessEqTwoQ : guess = 2 * (first + 1)
  · exact .fourthRejectAtTwoQ guessEqTwoQ
  have twoQBelowGuess : 2 * (first + 1) < guess := by omega
  by_cases guessBelowThreeQ : guess < 3 * (first + 1)
  · exact .markerTwoRejectMiddle twoQBelowGuess guessBelowThreeQ
  by_cases guessEqThreeQ : guess = 3 * (first + 1)
  · exact .fifthRejectAtThreeQ guessEqThreeQ
  have threeQBelowGuess : 3 * (first + 1) < guess := by omega
  by_cases guessEqFourQ : guess = 4 * (first + 1)
  · exact .accepted guessEqFourQ
  · exact .markerTwoRejectHigh threeQBelowGuess guessEqFourQ

end Mortality.Compiler.FivefoldFrontClassification
