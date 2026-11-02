import Mortality.Compiler.OddHalvingArithmetic

/-!
# Arithmetic core of the ternary front end

The ternary front end shares its guessed prefix and first two
marker-one scans with odd halving.  Its third scan starts from the same
three-term numerator as the odd-halving validator, but retains the
earlier denominator.  This file formalizes that state and its complete
first-nonzero-digit classification, including the shortened scan on a
small guess.
-/

namespace Mortality.Compiler.TernaryFrontArithmetic

open Mortality.PeriodicCode
open Mortality.Compiler.UnaryArithmetic
open Mortality.Compiler.OddHalvingArithmetic

/-- State after `deleted` zero deletions in the third marker-one scan. -/
def thirdAutomaticState (base first guess deleted : Nat) : Rat :=
  ((base : Rat) ^ (guess - 1 - deleted) +
      (base : Rat) ^ (first + guess - deleted) +
      (base : Rat) ^ (first - deleted)) /
    halfDenominator base first guess

/-- The third scan stops at the smaller of the two potentially leading
exponents. -/
def thirdScanLength (first guess : Nat) : Nat :=
  min first (guess - 1)

/-- Its first nonzero digit is two only in the exceptional middle split
`first = guess - 1`; it is one in both strict cases. -/
def thirdMarkerDigit (first guess : Nat) : Int :=
  if first = guess - 1 then 2 else 1

theorem thirdAutomaticState_zero (base first guess : Nat) :
    thirdAutomaticState base first guess 0 =
      secondScanOutput base first guess := by
  simp [thirdAutomaticState, secondScanOutput]

theorem thirdAutomaticState_local (base first guess deleted : Nat)
    (baseAtLeastTwo : 2 ≤ base) :
    LocalAt base (Vec2.affine
      (thirdAutomaticState base first guess deleted)) := by
  have denominatorNotDivisible := halfIntegerDenominator_not_dvd base
    first guess baseAtLeastTwo
  have localFraction := local_affine_integer_div
    (prime := base)
    (numerator := validatorIntegerNumerator base first guess deleted)
    (denominator := halfIntegerDenominator base first guess)
    denominatorNotDivisible
  simpa [thirdAutomaticState, validatorIntegerNumerator, halfDenominator,
    halfIntegerDenominator, Rat.intCast_pow, Rat.intCast_natCast,
    Rat.intCast_add, Rat.intCast_sub] using localFraction

theorem thirdAutomaticState_sameLine_integer
    (base first guess deleted : Nat) (baseAtLeastTwo : 2 ≤ base) :
    SameLine (Vec2.affine
      (thirdAutomaticState base first guess deleted))
      (integerVector (validatorIntegerNumerator base first guess deleted)
        (halfIntegerDenominator base first guess)) := by
  have denominatorNotDivisible := halfIntegerDenominator_not_dvd base
    first guess baseAtLeastTwo
  have denominatorNonzero : halfIntegerDenominator base first guess ≠ 0 :=
    fun denominatorZero => denominatorNotDivisible (by
      rw [denominatorZero]
      exact Int.dvd_zero _)
  have same := affine_div_sameLine_integerVector
    (numerator := validatorIntegerNumerator base first guess deleted)
    (denominator := halfIntegerDenominator base first guess)
    denominatorNonzero
  simpa [thirdAutomaticState, validatorIntegerNumerator, halfDenominator,
    halfIntegerDenominator, Rat.intCast_pow, Rat.intCast_natCast,
    Rat.intCast_add, Rat.intCast_sub] using same

theorem thirdAutomaticState_delete_zero
    (base first guess deleted : Nat) (baseAtLeastTwo : 2 ≤ base)
    (deletedBelow : deleted < thirdScanLength first guess) :
    deleteDigit (base : Rat) 0
        (thirdAutomaticState base first guess deleted) =
      thirdAutomaticState base first guess (deleted + 1) := by
  have belowFirst : deleted < first := Nat.lt_of_lt_of_le deletedBelow
    (Nat.min_le_left _ _)
  have belowGuess : deleted < guess - 1 := Nat.lt_of_lt_of_le deletedBelow
    (Nat.min_le_right _ _)
  have belowCombined : deleted < first + guess := by omega
  have firstExponent : first - deleted = first - (deleted + 1) + 1 := by
    omega
  have guessExponent : guess - 1 - deleted =
      guess - 1 - (deleted + 1) + 1 := by omega
  have combinedExponent : first + guess - deleted =
      first + guess - (deleted + 1) + 1 := by omega
  have firstPower : (base : Rat) ^ (first - deleted) =
      (base : Rat) ^ (first - (deleted + 1)) * (base : Rat) := by
    rw [firstExponent, Rat.pow_succ]
  have guessPower : (base : Rat) ^ (guess - 1 - deleted) =
      (base : Rat) ^ (guess - 1 - (deleted + 1)) * (base : Rat) := by
    rw [guessExponent, Rat.pow_succ]
  have combinedPower : (base : Rat) ^ (first + guess - deleted) =
      (base : Rat) ^ (first + guess - (deleted + 1)) *
        (base : Rat) := by
    rw [combinedExponent, Rat.pow_succ]
  have baseNonzero : (base : Rat) ≠ 0 := by
    simpa using (show base ≠ 0 by omega)
  have denominatorNonzero := halfDenominator_nonzero base first guess
    baseAtLeastTwo
  unfold deleteDigit thirdAutomaticState
  rw [Rat.intCast_zero, Rat.div_def, Rat.div_def, Rat.div_def]
  have baseCancel := Rat.mul_inv_cancel (base : Rat) baseNonzero
  have denominatorCancel := Rat.mul_inv_cancel
    (halfDenominator base first guess) denominatorNonzero
  grind

theorem thirdAutomaticState_zero_residue
    (base first guess deleted : Nat)
    (deletedBelow : deleted < thirdScanLength first guess) :
    (base : Int) ∣ validatorIntegerNumerator base first guess deleted := by
  have belowFirst : deleted < first := Nat.lt_of_lt_of_le deletedBelow
    (Nat.min_le_left _ _)
  have belowGuess : deleted < guess - 1 := Nat.lt_of_lt_of_le deletedBelow
    (Nat.min_le_right _ _)
  have belowCombined : deleted < first + guess := by omega
  rcases base_dvd_positive_power base (guess - 1 - deleted) (by omega) with
    ⟨guessFactor, guessEq⟩
  rcases base_dvd_positive_power base (first + guess - deleted) (by omega) with
    ⟨combinedFactor, combinedEq⟩
  rcases base_dvd_positive_power base (first - deleted) (by omega) with
    ⟨firstFactor, firstEq⟩
  refine ⟨guessFactor + combinedFactor + firstFactor, ?_⟩
  unfold validatorIntegerNumerator
  rw [guessEq, combinedEq, firstEq]
  grind

/-- Complete first-nonzero-digit classification of the third scan.  In
particular, the equality split exposes digit two and therefore cannot
take its marker-one exit. -/
theorem thirdAutomaticState_marker_residue
    (base first guess : Nat) (guessPositive : 0 < guess) :
    (base : Int) ∣
      validatorIntegerNumerator base first guess
          (thirdScanLength first guess) -
        thirdMarkerDigit first guess *
          halfIntegerDenominator base first guess := by
  have oldResidue := validatorState_marker_residue base first guess
    guessPositive
  have guessPower := base_dvd_positive_power base guess guessPositive
  have combinedPower := base_dvd_positive_power base (first + guess + 1)
    (by omega)
  have firstPower := base_dvd_positive_power base (first + 1) (by omega)
  rcases oldResidue with ⟨oldFactor, oldEq⟩
  rcases guessPower with ⟨guessFactor, guessEq⟩
  rcases combinedPower with ⟨combinedFactor, combinedEq⟩
  rcases firstPower with ⟨firstFactor, firstEq⟩
  refine ⟨oldFactor + thirdMarkerDigit first guess *
      (guessFactor + combinedFactor + firstFactor), ?_⟩
  unfold thirdScanLength thirdMarkerDigit
  unfold validatorMarkerDigit at oldEq
  unfold validatorLength at oldEq
  unfold validatorIntegerDenominator at oldEq
  unfold halfIntegerDenominator
  calc
    validatorIntegerNumerator base first guess (min first (guess - 1)) -
          (if first = guess - 1 then 2 else 1) *
            (1 - (base : Int) ^ (first + guess + 1) -
              (base : Int) ^ (first + 1)) =
        (validatorIntegerNumerator base first guess (min first (guess - 1)) -
          (if first = guess - 1 then 2 else 1) *
            (1 + (base : Int) ^ guess)) +
          (if first = guess - 1 then 2 else 1) *
            ((base : Int) ^ guess +
              (base : Int) ^ (first + guess + 1) +
              (base : Int) ^ (first + 1)) := by grind
    _ = (base : Int) * oldFactor +
          (if first = guess - 1 then 2 else 1) *
            ((base : Int) * guessFactor +
              (base : Int) * combinedFactor +
              (base : Int) * firstFactor) := by
      rw [oldEq, guessEq, combinedEq, firstEq]
    _ = (base : Int) *
          (oldFactor + (if first = guess - 1 then 2 else 1) *
            (guessFactor + combinedFactor + firstFactor)) := by grind

/-- Numerator after the third marker-one deletion.  The first branch is
the long-third-scan case `first < guess - 1`; the second is the shortened
case.  The equality case never reaches this state. -/
def ternaryCandidateNumerator (base first guess : Nat) : Int :=
  if first < guess - 1 then
    (base : Int) ^ (guess - first - 2) +
      (base : Int) ^ (guess - 1) +
      (base : Int) ^ (first + guess) +
      (base : Int) ^ first
  else
    2 * (base : Int) ^ first +
      (base : Int) ^ (first - guess) +
      (base : Int) ^ (first + guess)

/-- Denominator after applying `T⁻¹` to the third scan output. -/
def ternaryCandidateDenominator (base first guess : Nat) : Int :=
  halfIntegerDenominator base first guess +
    (base : Int) * ternaryCandidateNumerator base first guess

def ternaryValidatorLength (first guess : Nat) : Nat :=
  if first < guess - 1 then min first (guess - first - 2)
  else first - guess

def ternaryValidatorMarkerDigit (first guess : Nat) : Int :=
  if guess = 2 * first + 2 then 2 else 1

def ternaryValidatorNumerator
    (base first guess deleted : Nat) : Int :=
  if first < guess - 1 then
    (base : Int) ^ (guess - first - 2 - deleted) +
      (base : Int) ^ (guess - 1 - deleted) +
      (base : Int) ^ (first + guess - deleted) +
      (base : Int) ^ (first - deleted)
  else
    2 * (base : Int) ^ (first - deleted) +
      (base : Int) ^ (first - guess - deleted) +
      (base : Int) ^ (first + guess - deleted)

def ternaryValidatorState
    (base first guess deleted : Nat) : Rat :=
  (ternaryValidatorNumerator base first guess deleted : Rat) /
    (ternaryCandidateDenominator base first guess : Rat)

@[simp] theorem ternaryValidatorNumerator_zero
    (base first guess : Nat) :
    ternaryValidatorNumerator base first guess 0 =
      ternaryCandidateNumerator base first guess := by
  simp [ternaryValidatorNumerator, ternaryCandidateNumerator]

theorem ternaryCandidateDenominator_not_dvd
    (base first guess : Nat) (baseAtLeastTwo : 2 ≤ base) :
    ¬(base : Int) ∣ ternaryCandidateDenominator base first guess := by
  intro candidateDivisible
  have productDivisible : (base : Int) ∣
      (base : Int) * ternaryCandidateNumerator base first guess := by
    exact ⟨ternaryCandidateNumerator base first guess, rfl⟩
  have halfDivisible := Int.dvd_sub candidateDivisible productDivisible
  exact halfIntegerDenominator_not_dvd base first guess baseAtLeastTwo
    (by simpa [ternaryCandidateDenominator] using halfDivisible)

theorem ternaryValidatorState_local
    (base first guess deleted : Nat) (baseAtLeastTwo : 2 ≤ base) :
    LocalAt base
      (Vec2.affine (ternaryValidatorState base first guess deleted)) := by
  have localFraction := local_affine_integer_div
    (prime := base)
    (numerator := ternaryValidatorNumerator base first guess deleted)
    (denominator := ternaryCandidateDenominator base first guess)
    (ternaryCandidateDenominator_not_dvd base first guess baseAtLeastTwo)
  simpa [ternaryValidatorState] using localFraction

theorem ternaryValidatorState_sameLine_integer
    (base first guess deleted : Nat) (baseAtLeastTwo : 2 ≤ base) :
    SameLine (Vec2.affine
      (ternaryValidatorState base first guess deleted))
      (integerVector (ternaryValidatorNumerator base first guess deleted)
        (ternaryCandidateDenominator base first guess)) := by
  have denominatorNotDivisible := ternaryCandidateDenominator_not_dvd base
    first guess baseAtLeastTwo
  have denominatorNonzero : ternaryCandidateDenominator base first guess ≠
      0 := fun denominatorZero => denominatorNotDivisible (by
    rw [denominatorZero]
    exact Int.dvd_zero _)
  exact affine_div_sameLine_integerVector denominatorNonzero

theorem ternaryValidatorState_delete_zero
    (base first guess deleted : Nat) (baseAtLeastTwo : 2 ≤ base)
    (deletedBelow : deleted < ternaryValidatorLength first guess) :
    deleteDigit (base : Rat) 0
        (ternaryValidatorState base first guess deleted) =
      ternaryValidatorState base first guess (deleted + 1) := by
  have baseNonzero : (base : Rat) ≠ 0 := by
    simpa using (show base ≠ 0 by omega)
  have denominatorNotDivisible := ternaryCandidateDenominator_not_dvd base
    first guess baseAtLeastTwo
  have denominatorNonzeroInt :
      ternaryCandidateDenominator base first guess ≠ 0 :=
    fun denominatorZero => denominatorNotDivisible (by
      rw [denominatorZero]
      exact Int.dvd_zero _)
  have denominatorNonzero :
      (ternaryCandidateDenominator base first guess : Rat) ≠ 0 := by
    exact_mod_cast denominatorNonzeroInt
  unfold ternaryValidatorLength at deletedBelow
  unfold ternaryValidatorState ternaryValidatorNumerator
  by_cases longCase : first < guess - 1
  · simp only [if_pos longCase] at deletedBelow ⊢
    have belowFirst : deleted < first := Nat.lt_of_lt_of_le deletedBelow
      (Nat.min_le_left _ _)
    have belowGap : deleted < guess - first - 2 :=
      Nat.lt_of_lt_of_le deletedBelow (Nat.min_le_right _ _)
    have belowGuess : deleted < guess - 1 := by omega
    have belowCombined : deleted < first + guess := by omega
    have gapExponent : guess - first - 2 - deleted =
        guess - first - 2 - (deleted + 1) + 1 := by omega
    have guessExponent : guess - 1 - deleted =
        guess - 1 - (deleted + 1) + 1 := by omega
    have combinedExponent : first + guess - deleted =
        first + guess - (deleted + 1) + 1 := by omega
    have firstExponent : first - deleted =
        first - (deleted + 1) + 1 := by omega
    rw [gapExponent, guessExponent, combinedExponent, firstExponent]
    simp only [Rat.intCast_add, Rat.intCast_pow, Rat.intCast_natCast,
      Rat.pow_succ]
    unfold deleteDigit
    rw [Rat.div_def, Rat.div_def, Rat.div_def]
    have baseCancel := Rat.mul_inv_cancel (base : Rat) baseNonzero
    have denominatorCancel := Rat.mul_inv_cancel
      (ternaryCandidateDenominator base first guess : Rat)
      denominatorNonzero
    grind
  · simp only [if_neg longCase] at deletedBelow ⊢
    have belowDifference : deleted < first - guess := by
      exact deletedBelow
    have belowFirst : deleted < first := by omega
    have belowCombined : deleted < first + guess := by omega
    have firstExponent : first - deleted =
        first - (deleted + 1) + 1 := by omega
    have differenceExponent : first - guess - deleted =
        first - guess - (deleted + 1) + 1 := by omega
    have combinedExponent : first + guess - deleted =
        first + guess - (deleted + 1) + 1 := by omega
    rw [firstExponent, differenceExponent, combinedExponent]
    simp only [Rat.intCast_add, Rat.intCast_mul, Rat.intCast_ofNat,
      Rat.intCast_pow, Rat.intCast_natCast, Rat.pow_succ]
    unfold deleteDigit
    rw [Rat.div_def, Rat.div_def, Rat.div_def]
    have baseCancel := Rat.mul_inv_cancel (base : Rat) baseNonzero
    have denominatorCancel := Rat.mul_inv_cancel
      (ternaryCandidateDenominator base first guess : Rat)
      denominatorNonzero
    grind

theorem ternaryValidatorState_zero_residue
    (base first guess deleted : Nat)
    (deletedBelow : deleted < ternaryValidatorLength first guess) :
    (base : Int) ∣ ternaryValidatorNumerator base first guess deleted := by
  unfold ternaryValidatorLength at deletedBelow
  unfold ternaryValidatorNumerator
  by_cases longCase : first < guess - 1
  · simp only [if_pos longCase] at deletedBelow ⊢
    have belowFirst : deleted < first := Nat.lt_of_lt_of_le deletedBelow
      (Nat.min_le_left _ _)
    have belowGap : deleted < guess - first - 2 :=
      Nat.lt_of_lt_of_le deletedBelow (Nat.min_le_right _ _)
    rcases base_dvd_positive_power base (guess - first - 2 - deleted)
        (by omega) with ⟨gapFactor, gapEq⟩
    rcases base_dvd_positive_power base (guess - 1 - deleted) (by omega) with
      ⟨guessFactor, guessEq⟩
    rcases base_dvd_positive_power base (first + guess - deleted) (by omega)
      with ⟨combinedFactor, combinedEq⟩
    rcases base_dvd_positive_power base (first - deleted) (by omega) with
      ⟨firstFactor, firstEq⟩
    refine ⟨gapFactor + guessFactor + combinedFactor + firstFactor, ?_⟩
    rw [gapEq, guessEq, combinedEq, firstEq]
    grind
  · simp only [if_neg longCase] at deletedBelow ⊢
    rcases base_dvd_positive_power base (first - deleted) (by omega) with
      ⟨firstFactor, firstEq⟩
    rcases base_dvd_positive_power base (first - guess - deleted) (by omega)
      with ⟨differenceFactor, differenceEq⟩
    rcases base_dvd_positive_power base (first + guess - deleted) (by omega)
      with ⟨combinedFactor, combinedEq⟩
    refine ⟨2 * firstFactor + differenceFactor + combinedFactor, ?_⟩
    rw [firstEq, differenceEq, combinedEq]
    grind

theorem ternaryCandidateDenominator_one_residue
    (base first guess : Nat) :
    (base : Int) ∣
      1 - ternaryCandidateDenominator base first guess := by
  rcases base_dvd_positive_power base (first + guess + 1) (by omega) with
    ⟨combinedFactor, combinedEq⟩
  rcases base_dvd_positive_power base (first + 1) (by omega) with
    ⟨firstFactor, firstEq⟩
  refine ⟨combinedFactor + firstFactor -
      ternaryCandidateNumerator base first guess, ?_⟩
  unfold ternaryCandidateDenominator halfIntegerDenominator
  rw [combinedEq, firstEq]
  grind

/-- The final marker-two validator accepts exactly `guess = 2*first+2`.
Both strict wrong-split cases expose digit one, including the shortened
third scan. -/
theorem ternaryValidatorState_marker_residue
    (base first guess : Nat) (guessPositive : 0 < guess)
    (middleRejected : first ≠ guess - 1) :
    (base : Int) ∣
      ternaryValidatorNumerator base first guess
          (ternaryValidatorLength first guess) -
        ternaryValidatorMarkerDigit first guess *
          ternaryCandidateDenominator base first guess := by
  have denominatorResidue := ternaryCandidateDenominator_one_residue base
    first guess
  rcases denominatorResidue with ⟨denominatorFactor, denominatorEq⟩
  have numeratorResidue : (base : Int) ∣
      ternaryValidatorNumerator base first guess
          (ternaryValidatorLength first guess) -
        ternaryValidatorMarkerDigit first guess := by
    by_cases accepted : guess = 2 * first + 2
    · have longCase : first < guess - 1 := by omega
      have lengthEq : ternaryValidatorLength first guess = first := by
        unfold ternaryValidatorLength
        rw [if_pos longCase]
        apply Nat.min_eq_left
        omega
      have gapExponent : guess - first - 2 - first = 0 := by omega
      have guessExponent : guess - 1 - first = first + 1 := by omega
      have combinedExponent : first + guess - first = guess := by omega
      rcases base_dvd_positive_power base (first + 1) (by omega) with
        ⟨nextFactor, nextEq⟩
      rcases base_dvd_positive_power base guess guessPositive with
        ⟨guessFactor, guessEq⟩
      refine ⟨nextFactor + guessFactor, ?_⟩
      rw [lengthEq]
      unfold ternaryValidatorNumerator
      rw [if_pos longCase, gapExponent, guessExponent, combinedExponent,
        Nat.sub_self]
      simp only [Int.pow_zero]
      unfold ternaryValidatorMarkerDigit
      rw [if_pos accepted]
      rw [nextEq, guessEq]
      grind
    · by_cases longCase : first < guess - 1
      · have unequalLeads : first ≠ guess - first - 2 := by
          intro equalLeads
          apply accepted
          omega
        rcases Nat.lt_or_gt_of_ne unequalLeads with firstBelow | gapBelow
        · have lengthEq : ternaryValidatorLength first guess = first := by
            unfold ternaryValidatorLength
            rw [if_pos longCase]
            exact Nat.min_eq_left (Nat.le_of_lt firstBelow)
          have gapExponent : 0 < guess - first - 2 - first := by omega
          have guessExponent : 0 < guess - 1 - first := by omega
          have combinedExponent : first + guess - first = guess := by omega
          rcases base_dvd_positive_power base
              (guess - first - 2 - first) gapExponent with
            ⟨gapFactor, gapEq⟩
          rcases base_dvd_positive_power base (guess - 1 - first)
              guessExponent
            with ⟨guessFactor, guessEq⟩
          rcases base_dvd_positive_power base guess guessPositive with
            ⟨combinedFactor, combinedEq⟩
          refine ⟨gapFactor + guessFactor + combinedFactor, ?_⟩
          rw [lengthEq]
          unfold ternaryValidatorNumerator
          rw [if_pos longCase, combinedExponent, Nat.sub_self]
          simp only [Int.pow_zero]
          unfold ternaryValidatorMarkerDigit
          rw [if_neg accepted]
          rw [gapEq, guessEq, combinedEq]
          grind
        · have lengthEq : ternaryValidatorLength first guess =
              guess - first - 2 := by
            unfold ternaryValidatorLength
            rw [if_pos longCase]
            exact Nat.min_eq_right (Nat.le_of_lt gapBelow)
          have guessExponent : 0 <
              guess - 1 - (guess - first - 2) := by omega
          have combinedExponent : 0 <
              first + guess - (guess - first - 2) := by omega
          have firstExponent : 0 <
              first - (guess - first - 2) := by omega
          rcases base_dvd_positive_power base
              (guess - 1 - (guess - first - 2)) guessExponent with
            ⟨guessFactor, guessEq⟩
          rcases base_dvd_positive_power base
              (first + guess - (guess - first - 2)) combinedExponent with
            ⟨combinedFactor, combinedEq⟩
          rcases base_dvd_positive_power base
              (first - (guess - first - 2)) firstExponent with
            ⟨firstFactor, firstEq⟩
          refine ⟨guessFactor + combinedFactor + firstFactor, ?_⟩
          rw [lengthEq]
          unfold ternaryValidatorNumerator
          rw [if_pos longCase, Nat.sub_self]
          simp only [Int.pow_zero]
          unfold ternaryValidatorMarkerDigit
          rw [if_neg accepted]
          rw [guessEq, combinedEq, firstEq]
          grind
      · have shortCase : guess ≤ first := by omega
        have lengthEq : ternaryValidatorLength first guess = first - guess :=
          by simp [ternaryValidatorLength, longCase]
        have firstExponent : first - (first - guess) = guess := by omega
        have differenceExponent : first - guess - (first - guess) = 0 := by
          omega
        have combinedExponent : first + guess - (first - guess) =
            2 * guess := by omega
        rcases base_dvd_positive_power base guess guessPositive with
          ⟨firstFactor, firstEq⟩
        rcases base_dvd_positive_power base (2 * guess) (by omega) with
          ⟨combinedFactor, combinedEq⟩
        refine ⟨2 * firstFactor + combinedFactor, ?_⟩
        rw [lengthEq]
        unfold ternaryValidatorNumerator
        rw [if_neg longCase, firstExponent, differenceExponent,
          combinedExponent]
        simp only [Int.pow_zero]
        unfold ternaryValidatorMarkerDigit
        rw [if_neg accepted]
        rw [firstEq, combinedEq]
        grind
  rcases numeratorResidue with ⟨numeratorFactor, numeratorEq⟩
  refine ⟨numeratorFactor +
      ternaryValidatorMarkerDigit first guess * denominatorFactor, ?_⟩
  calc
    ternaryValidatorNumerator base first guess
          (ternaryValidatorLength first guess) -
        ternaryValidatorMarkerDigit first guess *
          ternaryCandidateDenominator base first guess =
      (ternaryValidatorNumerator base first guess
          (ternaryValidatorLength first guess) -
        ternaryValidatorMarkerDigit first guess) +
      ternaryValidatorMarkerDigit first guess *
        (1 - ternaryCandidateDenominator base first guess) := by grind
    _ = (base : Int) * numeratorFactor +
        ternaryValidatorMarkerDigit first guess *
          ((base : Int) * denominatorFactor) := by
      rw [numeratorEq, denominatorEq]
    _ = (base : Int) *
        (numeratorFactor +
          ternaryValidatorMarkerDigit first guess * denominatorFactor) := by
      grind

theorem thirdMarker_difference
    (base first guess : Nat) (guessPositive : 0 < guess)
    (middleRejected : first ≠ guess - 1) :
    validatorIntegerNumerator base first guess
          (thirdScanLength first guess) -
        halfIntegerDenominator base first guess =
      (base : Int) * ternaryCandidateNumerator base first guess := by
  by_cases longCase : first < guess - 1
  · have lengthEq : thirdScanLength first guess = first := by
      exact Nat.min_eq_left (Nat.le_of_lt longCase)
    have gapPower : (base : Int) ^ (guess - 1 - first) =
        (base : Int) ^ (guess - first - 2) * (base : Int) := by
      rw [show guess - 1 - first = guess - first - 2 + 1 by omega,
        Int.pow_succ]
    have guessPower : (base : Int) ^ guess =
        (base : Int) ^ (guess - 1) * (base : Int) := by
      calc
        (base : Int) ^ guess =
            (base : Int) ^ ((guess - 1) + 1) := by congr 1 <;> omega
        _ = (base : Int) ^ (guess - 1) * (base : Int) := by
          rw [Int.pow_succ]
    have combinedPower : (base : Int) ^ (first + guess + 1) =
        (base : Int) ^ (first + guess) * (base : Int) := by
      rw [Int.pow_succ]
    have firstPower : (base : Int) ^ (first + 1) =
        (base : Int) ^ first * (base : Int) := by
      rw [Int.pow_succ]
    unfold validatorIntegerNumerator halfIntegerDenominator
      ternaryCandidateNumerator
    rw [if_pos longCase, lengthEq]
    simp only [Nat.sub_self, Int.pow_zero]
    rw [show first + guess - first = guess by omega, gapPower, guessPower,
      combinedPower, firstPower]
    grind
  · have shortCase : guess - 1 < first := by omega
    have lengthEq : thirdScanLength first guess = guess - 1 := by
      exact Nat.min_eq_right (Nat.le_of_lt shortCase)
    have firstDifference : first - (guess - 1) = first - guess + 1 := by
      omega
    have combinedDifference : first + guess - (guess - 1) = first + 1 := by
      omega
    have differencePower : (base : Int) ^ (first - guess + 1) =
        (base : Int) ^ (first - guess) * (base : Int) := by
      rw [Int.pow_succ]
    have firstPower : (base : Int) ^ (first + 1) =
        (base : Int) ^ first * (base : Int) := by
      rw [Int.pow_succ]
    have combinedPower : (base : Int) ^ (first + guess + 1) =
        (base : Int) ^ (first + guess) * (base : Int) := by
      rw [Int.pow_succ]
    unfold validatorIntegerNumerator halfIntegerDenominator
      ternaryCandidateNumerator
    rw [if_neg longCase, lengthEq]
    rw [show guess - 1 - (guess - 1) = 0 by omega,
      firstDifference, combinedDifference]
    simp only [Int.pow_zero]
    rw [differencePower, firstPower, combinedPower]
    grind

def thirdScanOutput (base first guess : Nat) : Rat :=
  (ternaryCandidateNumerator base first guess : Rat) /
    (halfIntegerDenominator base first guess : Rat)

theorem thirdScanOutput_local (base first guess : Nat)
    (baseAtLeastTwo : 2 ≤ base) :
    LocalAt base (Vec2.affine (thirdScanOutput base first guess)) := by
  have localFraction := local_affine_integer_div
    (prime := base)
    (numerator := ternaryCandidateNumerator base first guess)
    (denominator := halfIntegerDenominator base first guess)
    (halfIntegerDenominator_not_dvd base first guess baseAtLeastTwo)
  simpa [thirdScanOutput] using localFraction

private theorem delete_one_integer_fraction
    (base : Nat) (numerator denominator quotient : Int)
    (basePositive : 0 < base) (denominatorNonzero : denominator ≠ 0)
    (differenceEq : numerator - denominator = (base : Int) * quotient) :
    deleteDigit (base : Rat) 1
        ((numerator : Rat) / (denominator : Rat)) =
      (quotient : Rat) / (denominator : Rat) := by
  have baseNonzero : (base : Rat) ≠ 0 := by
    simpa using (show base ≠ 0 by omega)
  have denominatorNonzeroRat : (denominator : Rat) ≠ 0 := by
    exact_mod_cast denominatorNonzero
  have differenceRat : (numerator : Rat) - (denominator : Rat) =
      (base : Rat) * (quotient : Rat) := by
    exact_mod_cast differenceEq
  unfold deleteDigit
  rw [Rat.div_def, Rat.div_def, Rat.div_def]
  have baseCancel := Rat.mul_inv_cancel (base : Rat) baseNonzero
  have denominatorCancel := Rat.mul_inv_cancel (denominator : Rat)
    denominatorNonzeroRat
  grind

theorem thirdAutomaticState_delete_marker
    (base first guess : Nat) (baseAtLeastTwo : 2 ≤ base)
    (guessPositive : 0 < guess) (middleRejected : first ≠ guess - 1) :
    deleteDigit (base : Rat) 1
        (thirdAutomaticState base first guess
          (thirdScanLength first guess)) =
      thirdScanOutput base first guess := by
  let numerator := validatorIntegerNumerator base first guess
    (thirdScanLength first guess)
  let denominator := halfIntegerDenominator base first guess
  let quotient := ternaryCandidateNumerator base first guess
  have denominatorNotDivisible := halfIntegerDenominator_not_dvd base first
    guess baseAtLeastTwo
  have denominatorNonzero : denominator ≠ 0 :=
    fun denominatorZero => denominatorNotDivisible (by
      rw [show halfIntegerDenominator base first guess = 0 by
        exact denominatorZero]
      exact Int.dvd_zero _)
  have differenceEq : numerator - denominator = (base : Int) * quotient :=
    thirdMarker_difference base first guess guessPositive middleRejected
  have deleted := delete_one_integer_fraction base numerator denominator
    quotient (by omega) denominatorNonzero differenceEq
  have stateEq : thirdAutomaticState base first guess
        (thirdScanLength first guess) =
      (numerator : Rat) / (denominator : Rat) := by
    simp [thirdAutomaticState, numerator, denominator,
      validatorIntegerNumerator, halfDenominator, halfIntegerDenominator,
      Rat.intCast_pow, Rat.intCast_natCast, Rat.intCast_add,
      Rat.intCast_sub]
  rw [stateEq, deleted]
  rfl

theorem ternaryCandidateDenominator_eq_markerNumerator
    (base first guess : Nat) (guessPositive : 0 < guess)
    (middleRejected : first ≠ guess - 1) :
    ternaryCandidateDenominator base first guess =
      validatorIntegerNumerator base first guess
        (thirdScanLength first guess) := by
  have difference := thirdMarker_difference base first guess guessPositive
    middleRejected
  unfold ternaryCandidateDenominator
  grind

private theorem Tinv_delete_one_integer_fraction
    (base : Nat) (numerator denominator quotient : Int)
    (basePositive : 0 < base) (denominatorNonzero : denominator ≠ 0)
    (numeratorNonzero : numerator ≠ 0)
    (differenceEq : numerator - denominator = (base : Int) * quotient) :
    Tinv base
        (deleteDigit (base : Rat) 1
          ((numerator : Rat) / (denominator : Rat))) =
      (quotient : Rat) / (numerator : Rat) := by
  have baseNonzero : (base : Rat) ≠ 0 := by
    simpa using (show base ≠ 0 by omega)
  have denominatorNonzeroRat : (denominator : Rat) ≠ 0 := by
    exact_mod_cast denominatorNonzero
  have numeratorNonzeroRat : (numerator : Rat) ≠ 0 := by
    exact_mod_cast numeratorNonzero
  have differenceRat : (numerator : Rat) - (denominator : Rat) =
      (base : Rat) * (quotient : Rat) := by
    exact_mod_cast differenceEq
  unfold Tinv deleteDigit
  rw [Rat.div_def, Rat.div_def, Rat.div_def]
  have baseCancel := Rat.mul_inv_cancel (base : Rat) baseNonzero
  have denominatorCancel := Rat.mul_inv_cancel (denominator : Rat)
    denominatorNonzeroRat
  have numeratorCancel := Rat.mul_inv_cancel (numerator : Rat)
    numeratorNonzeroRat
  grind

/-- Exact rational state after the third marker-one deletion and its
fused `T⁻¹` mutation. -/
theorem thirdMarker_to_validator
    (base first guess : Nat) (baseAtLeastTwo : 2 ≤ base)
    (guessPositive : 0 < guess) (middleRejected : first ≠ guess - 1) :
    Tinv base
        (deleteDigit (base : Rat) 1
          (thirdAutomaticState base first guess
            (thirdScanLength first guess))) =
      ternaryValidatorState base first guess 0 := by
  let numerator := validatorIntegerNumerator base first guess
    (thirdScanLength first guess)
  let denominator := halfIntegerDenominator base first guess
  let quotient := ternaryCandidateNumerator base first guess
  have differenceEq : numerator - denominator = (base : Int) * quotient :=
    thirdMarker_difference base first guess guessPositive middleRejected
  have denominatorNotDivisible := halfIntegerDenominator_not_dvd base first
    guess baseAtLeastTwo
  have denominatorNonzero : denominator ≠ 0 :=
    fun denominatorZero => denominatorNotDivisible (by
      rw [show halfIntegerDenominator base first guess = 0 by
        exact denominatorZero]
      exact Int.dvd_zero _)
  have numeratorEq : ternaryCandidateDenominator base first guess =
      numerator := ternaryCandidateDenominator_eq_markerNumerator base first
        guess guessPositive middleRejected
  have numeratorNotDivisible := ternaryCandidateDenominator_not_dvd base
    first guess baseAtLeastTwo
  have numeratorNonzero : numerator ≠ 0 := fun numeratorZero =>
    numeratorNotDivisible (by rw [numeratorEq, numeratorZero]; exact Int.dvd_zero _)
  have action := Tinv_delete_one_integer_fraction base numerator denominator
    quotient (by omega) denominatorNonzero numeratorNonzero differenceEq
  have stateEq : thirdAutomaticState base first guess
        (thirdScanLength first guess) =
      (numerator : Rat) / (denominator : Rat) := by
    simp [thirdAutomaticState, numerator, denominator,
      validatorIntegerNumerator, halfDenominator, halfIntegerDenominator,
      Rat.intCast_pow, Rat.intCast_natCast, Rat.intCast_add,
      Rat.intCast_sub]
  rw [stateEq, action]
  simp [ternaryValidatorState, quotient, numerator, numeratorEq]

theorem Tinv_thirdScanOutput
    (base first guess : Nat) (baseAtLeastTwo : 2 ≤ base)
    (guessPositive : 0 < guess) (middleRejected : first ≠ guess - 1) :
    Tinv base (thirdScanOutput base first guess) =
      ternaryValidatorState base first guess 0 := by
  rw [← thirdAutomaticState_delete_marker base first guess baseAtLeastTwo
    guessPositive middleRejected]
  exact thirdMarker_to_validator base first guess baseAtLeastTwo guessPositive
    middleRejected

theorem acceptedTernaryValidatorNumerator (base first : Nat) :
    ternaryValidatorNumerator base first (2 * first + 2) first =
      2 + (base : Int) ^ (first + 1) +
        (base : Int) ^ (2 * first + 2) := by
  have longCase : first < 2 * first + 2 - 1 := by omega
  unfold ternaryValidatorNumerator
  rw [if_pos longCase]
  rw [show 2 * first + 2 - first - 2 - first = 0 by omega,
    show 2 * first + 2 - 1 - first = first + 1 by omega,
    show first + (2 * first + 2) - first = 2 * first + 2 by omega,
    Nat.sub_self]
  simp only [Int.pow_zero]
  grind

theorem acceptedTernaryCandidateDenominator (base first : Nat) :
    ternaryCandidateDenominator base first (2 * first + 2) =
      1 + (base : Int) ^ (first + 1) +
        (base : Int) ^ (2 * first + 2) := by
  rw [ternaryCandidateDenominator_eq_markerNumerator base first
    (2 * first + 2) (by omega) (by omega)]
  have lengthEq : thirdScanLength first (2 * first + 2) = first := by
    exact Nat.min_eq_left (by omega)
  unfold validatorIntegerNumerator
  rw [lengthEq]
  rw [show 2 * first + 2 - 1 - first = first + 1 by omega,
    show first + (2 * first + 2) - first = 2 * first + 2 by omega,
    Nat.sub_self]
  simp only [Int.pow_zero]
  grind

/-- On the accepted split, the marker-two deletion produces the
negative two-field code claimed by the ternary front end. -/
theorem accepted_ternary_validator_delete_marker
    (base first : Nat) (baseAtLeastTwo : 2 ≤ base) :
    deleteDigit (base : Rat) 2
        (ternaryValidatorState base first (2 * first + 2) first) =
      -(twoFieldCode base first (2 * first + 1)) := by
  have baseNonzero : (base : Rat) ≠ 0 := by
    simpa using (show base ≠ 0 by omega)
  have candidateNonzeroInt :
      ternaryCandidateDenominator base first (2 * first + 2) ≠ 0 :=
    fun denominatorZero =>
      ternaryCandidateDenominator_not_dvd base first (2 * first + 2)
        baseAtLeastTwo (by rw [denominatorZero]; exact Int.dvd_zero _)
  have candidateNonzero :
      (ternaryCandidateDenominator base first (2 * first + 2) : Rat) ≠
        0 := by
    exact_mod_cast candidateNonzeroInt
  have candidateExpressionNonzero :
      (1 : Rat) + (base : Rat) ^ (first + 1) +
        (base : Rat) ^ (2 * first + 2) ≠ 0 := by
    have candidateExpressionNonzeroInt :
        (1 : Int) + (base : Int) ^ (first + 1) +
          (base : Int) ^ (2 * first + 2) ≠ 0 := by
      rw [← acceptedTernaryCandidateDenominator base first]
      exact candidateNonzeroInt
    exact_mod_cast candidateExpressionNonzeroInt
  have targetNonzero := one_sub_pow_ne_zero base (3 * first + 3)
    baseAtLeastTwo (by omega)
  have firstPower : (base : Rat) ^ (first + 1) =
      (base : Rat) ^ first * (base : Rat) := by
    rw [Rat.pow_succ]
  have squarePower : (base : Rat) ^ (2 * first + 2) =
      (base : Rat) ^ (first + 1) * (base : Rat) ^ (first + 1) := by
    rw [show 2 * first + 2 = (first + 1) + (first + 1) by omega]
    exact Lean.Grind.Semiring.pow_add _ _ _
  have cubePower : (base : Rat) ^ (3 * first + 3) =
      (base : Rat) ^ (first + 1) *
        (base : Rat) ^ (2 * first + 2) := by
    rw [show 3 * first + 3 = (first + 1) + (2 * first + 2) by omega]
    exact Lean.Grind.Semiring.pow_add _ _ _
  unfold ternaryValidatorState
  rw [acceptedTernaryValidatorNumerator,
    acceptedTernaryCandidateDenominator base first,
    twoFieldCode_eq]
  simp only [Rat.intCast_add, Rat.intCast_ofNat, Rat.intCast_pow,
    Rat.intCast_natCast]
  rw [show first + (2 * first + 1) + 2 = 3 * first + 3 by omega]
  unfold deleteDigit
  rw [Rat.div_def, Rat.div_def, Rat.div_def]
  have candidateCancel := Rat.mul_inv_cancel
    ((1 : Rat) + (base : Rat) ^ (first + 1) +
      (base : Rat) ^ (2 * first + 2)) candidateExpressionNonzero
  have baseCancel := Rat.mul_inv_cancel (base : Rat) baseNonzero
  have targetCancel := Rat.mul_inv_cancel
    ((1 : Rat) - (base : Rat) ^ (3 * first + 3)) targetNonzero
  grind

theorem accepted_ternary_front_output
    (base first : Nat) (baseAtLeastTwo : 2 ≤ base) :
    mutationMap base .negative 0
        (deleteDigit (base : Rat) 2
          (ternaryValidatorState base first (2 * first + 2) first)) =
      twoFieldCode base first (2 * first + 1) := by
  rw [accepted_ternary_validator_delete_marker base first baseAtLeastTwo]
  simp [mutationMap, mutationDenominator, Sign.value, Rat.div_def]
  grind

end Mortality.Compiler.TernaryFrontArithmetic
