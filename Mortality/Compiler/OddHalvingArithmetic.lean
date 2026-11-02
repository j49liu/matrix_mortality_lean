import Mortality.Compiler.PrefixGuessModule

/-!
# Arithmetic core of odd halving

For a guessed nonempty guess of length `b`, write the remaining unary
length as `a`.  This file checks the two marker-one scans and the
marker-two equality validator from Lemma 5.5.
-/

namespace Mortality.Compiler.OddHalvingArithmetic

open Mortality.PeriodicCode
open Mortality.Compiler.UnaryArithmetic
open Mortality.Compiler.PrefixGuessModule

private theorem div_div_same_den (numerator denominator target : Rat)
    (denominatorNonzero : denominator ≠ 0) :
    (numerator / denominator) / (target / denominator) =
      numerator / target := by
  simp only [Rat.div_def, Rat.inv_mul_rev, Rat.inv_inv]
  rw [Rat.mul_assoc numerator denominator⁻¹ (denominator * target⁻¹),
    ← Rat.mul_assoc denominator⁻¹ denominator target⁻¹,
    Rat.inv_mul_cancel _ denominatorNonzero, Rat.one_mul]

private theorem one_add_power_nonzero (base exponent : Nat) :
    (1 : Rat) + (base : Rat) ^ exponent ≠ 0 := by
  intro sumZero
  have castZero : ((1 + base ^ exponent : Nat) : Rat) = 0 := by
    simpa [Rat.natCast_add, Rat.natCast_pow] using sumZero
  have naturalZero : 1 + base ^ exponent = 0 := Rat.natCast_inj.mp castZero
  omega

def halfDenominator (base first guess : Nat) : Rat :=
  1 - (base : Rat) ^ (first + guess + 1) -
    (base : Rat) ^ (first + 1)

def firstScanOutput (base first guess : Nat) : Rat :=
  (base : Rat) ^ first * (1 + (base : Rat) ^ guess) /
    halfDenominator base first guess

def secondScanOutput (base first guess : Nat) : Rat :=
  ((base : Rat) ^ (guess - 1) +
      (base : Rat) ^ (first + guess) + (base : Rat) ^ first) /
    halfDenominator base first guess

def validatorInput (base first guess : Nat) : Rat :=
  ((base : Rat) ^ (guess - 1) +
      (base : Rat) ^ (first + guess) + (base : Rat) ^ first) /
    (1 + (base : Rat) ^ guess)

theorem halfDenominator_nonzero (base first guess : Nat)
    (baseAtLeastTwo : 2 ≤ base) :
    halfDenominator base first guess ≠ 0 := by
  have firstPowerAtLeastOne :
      (1 : Rat) ≤ (base : Rat) ^ (first + guess + 1) := by
    rw [← Rat.natCast_pow]
    exact_mod_cast Nat.one_le_pow (first + guess + 1) base (by omega)
  have secondPowerAtLeastOne :
      (1 : Rat) ≤ (base : Rat) ^ (first + 1) := by
    rw [← Rat.natCast_pow]
    exact_mod_cast Nat.one_le_pow (first + 1) base (by omega)
  unfold halfDenominator
  grind

theorem prefixState_split (base first guess : Nat) :
    prefixState base (first + guess) guess =
      (base : Rat) ^ first /
        (1 - (base : Rat) ^ (first + guess + 1)) := by
  simp [prefixState]

theorem T_after_prefix (base first guess : Nat)
    (baseAtLeastTwo : 2 ≤ base) :
    T base (prefixState base (first + guess) guess) =
      (base : Rat) ^ first / halfDenominator base first guess := by
  rw [prefixState_split]
  have oldDenominatorNonzero := one_sub_pow_ne_zero base
    (first + guess + 1) baseAtLeastTwo (by omega)
  have firstSucc : (base : Rat) ^ (first + 1) =
      (base : Rat) ^ first * (base : Rat) := by
    rw [Rat.pow_succ]
  unfold T halfDenominator
  rw [Rat.div_def, Rat.div_def]
  have oldCancel := Rat.mul_inv_cancel
    ((1 : Rat) - (base : Rat) ^ (first + guess + 1))
    oldDenominatorNonzero
  grind

theorem first_marker_scan (base first guess : Nat)
    (baseAtLeastTwo : 2 ≤ base) :
    scanDigits (base : Rat) (unaryDigits first)
        (T base (prefixState base (first + guess) guess)) =
      firstScanOutput base first guess := by
  rw [scanDigits_eq]
  · rw [T_after_prefix base first guess baseAtLeastTwo,
      digitPolynomial_unaryDigits, unaryDigits_length]
    have baseNonzero : (base : Rat) ≠ 0 := by
      simpa using (show base ≠ 0 by omega)
    have scanPowerNonzero := pow_ne_zero baseNonzero (first + 1)
    have oldDenominatorNonzero := one_sub_pow_ne_zero base
      (first + guess + 1) baseAtLeastTwo (by omega)
    have halfNonzero := halfDenominator_nonzero base first guess
      baseAtLeastTwo
    have firstSucc : (base : Rat) ^ (first + 1) =
        (base : Rat) ^ first * (base : Rat) := by
      rw [Rat.pow_succ]
    have splitPower : (base : Rat) ^ (first + guess + 1) =
        (base : Rat) ^ (first + 1) * (base : Rat) ^ guess := by
      rw [show first + guess + 1 = (first + 1) + guess by omega]
      exact Lean.Grind.Semiring.pow_add _ _ _
    unfold firstScanOutput halfDenominator
    rw [Rat.div_def, Rat.div_def, Rat.div_def]
    have scanCancel := Rat.mul_inv_cancel
      ((base : Rat) ^ (first + 1)) scanPowerNonzero
    have denominatorCancel := Rat.mul_inv_cancel
      ((1 : Rat) - (base : Rat) ^ (first + guess + 1) -
        (base : Rat) ^ (first + 1)) halfNonzero
    grind
  · simpa using (show base ≠ 0 by omega)

theorem second_marker_scan (base first guess : Nat)
    (baseAtLeastTwo : 2 ≤ base) (prefixPositive : 0 < guess) :
    scanDigits (base : Rat) (unaryDigits first)
        (firstScanOutput base first guess) =
      secondScanOutput base first guess := by
  rw [scanDigits_eq]
  · rw [digitPolynomial_unaryDigits, unaryDigits_length]
    have baseNonzero : (base : Rat) ≠ 0 := by
      simpa using (show base ≠ 0 by omega)
    have scanPowerNonzero := pow_ne_zero baseNonzero (first + 1)
    have prefixSucc : guess = (guess - 1) + 1 := by omega
    have prefixPower : (base : Rat) ^ guess =
        (base : Rat) ^ (guess - 1) * (base : Rat) := by
      calc
        (base : Rat) ^ guess =
            (base : Rat) ^ ((guess - 1) + 1) := by congr 1
        _ = (base : Rat) ^ (guess - 1) * (base : Rat) := by
          rw [Rat.pow_succ]
    have firstSucc : (base : Rat) ^ (first + 1) =
        (base : Rat) ^ first * (base : Rat) := by
      rw [Rat.pow_succ]
    have combinedSucc : (base : Rat) ^ (first + guess + 1) =
        (base : Rat) ^ (first + guess) * (base : Rat) := by
      rw [Rat.pow_succ]
    have halfNonzero := halfDenominator_nonzero base first guess
      baseAtLeastTwo
    unfold firstScanOutput secondScanOutput halfDenominator
    rw [Rat.div_def, Rat.div_def, Rat.div_def]
    have scanCancel := Rat.mul_inv_cancel
      ((base : Rat) ^ (first + 1)) scanPowerNonzero
    have denominatorCancel := Rat.mul_inv_cancel
      ((1 : Rat) - (base : Rat) ^ (first + guess + 1) -
        (base : Rat) ^ (first + 1)) halfNonzero
    grind
  · simpa using (show base ≠ 0 by omega)

theorem validator_input_formula (base first guess : Nat)
    (baseAtLeastTwo : 2 ≤ base) (prefixPositive : 0 < guess) :
    Tinv base (secondScanOutput base first guess) =
      validatorInput base first guess := by
  let numerator : Rat :=
    (base : Rat) ^ (guess - 1) +
      (base : Rat) ^ (first + guess) + (base : Rat) ^ first
  let denominator : Rat := halfDenominator base first guess
  have denominatorNonzero : denominator ≠ 0 := by
    exact halfDenominator_nonzero base first guess baseAtLeastTwo
  have denominatorIdentity :
      denominator + (base : Rat) * numerator =
        1 + (base : Rat) ^ guess := by
    have prefixSucc : guess = (guess - 1) + 1 := by omega
    have prefixPower : (base : Rat) ^ guess =
        (base : Rat) ^ (guess - 1) * (base : Rat) := by
      calc
        (base : Rat) ^ guess =
            (base : Rat) ^ ((guess - 1) + 1) := by congr 1
        _ = (base : Rat) ^ (guess - 1) * (base : Rat) := by
          rw [Rat.pow_succ]
    have firstSucc : (base : Rat) ^ (first + 1) =
        (base : Rat) ^ first * (base : Rat) := by
      rw [Rat.pow_succ]
    have combinedSucc : (base : Rat) ^ (first + guess + 1) =
        (base : Rat) ^ (first + guess) * (base : Rat) := by
      rw [Rat.pow_succ]
    unfold numerator denominator halfDenominator
    grind
  change Tinv base (numerator / denominator) =
    numerator / (1 + (base : Rat) ^ guess)
  unfold Tinv
  have quotientDenominator :
      1 + (base : Rat) * (numerator / denominator) =
        (denominator + (base : Rat) * numerator) / denominator := by
    rw [Rat.div_def, Rat.div_def]
    have denominatorCancel := Rat.mul_inv_cancel denominator
      denominatorNonzero
    grind
  rw [quotientDenominator, denominatorIdentity,
    div_div_same_den numerator denominator _ denominatorNonzero]

theorem validatorInput_split (base first guess : Nat) :
    validatorInput base first guess =
      (base : Rat) ^ first +
        (base : Rat) ^ (guess - 1) /
          (1 + (base : Rat) ^ guess) := by
  have denominatorNonzero :
      (1 : Rat) + (base : Rat) ^ guess ≠ 0 := by
    exact one_add_power_nonzero base guess
  have splitPower : (base : Rat) ^ (first + guess) =
      (base : Rat) ^ first * (base : Rat) ^ guess := by
    exact Lean.Grind.Semiring.pow_add _ _ _
  unfold validatorInput
  rw [Rat.div_def, Rat.div_def]
  have denominatorCancel := Rat.mul_inv_cancel
    ((1 : Rat) + (base : Rat) ^ guess) denominatorNonzero
  grind

def validatorDigits (first : Nat) : List Int :=
  List.replicate first 0 ++ [2]

theorem digitPolynomial_validatorDigits (base first : Nat) :
    digitPolynomial (base : Rat) (validatorDigits first) =
      2 * (base : Rat) ^ first := by
  rw [validatorDigits, digitPolynomial_replicate_zero_append]
  simp [digitPolynomial]
  grind

@[simp] theorem validatorDigits_length (first : Nat) :
    (validatorDigits first).length = first + 1 := by
  simp [validatorDigits]

/-- On the accepted equality `b=a+1`, the marker-two scan has exactly
`a` leading zeros and produces the value to which `K` is applied. -/
theorem accepted_validator_scan (base first : Nat)
    (baseAtLeastTwo : 2 ≤ base) :
    scanDigits (base : Rat) (validatorDigits first)
        (validatorInput base first (first + 1)) =
      -((base : Rat) ^ first) /
        (1 + (base : Rat) ^ (first + 1)) := by
  rw [scanDigits_eq]
  · rw [digitPolynomial_validatorDigits, validatorDigits_length]
    have baseNonzero : (base : Rat) ≠ 0 := by
      simpa using (show base ≠ 0 by omega)
    have scanPowerNonzero := pow_ne_zero baseNonzero (first + 1)
    have denominatorNonzero := one_add_power_nonzero base (first + 1)
    have guessMinus : first + 1 - 1 = first := by omega
    have doubledExponent : first + (first + 1) = first + first + 1 := by
      omega
    have splitPower : (base : Rat) ^ (first + first + 1) =
        (base : Rat) ^ first * (base : Rat) ^ (first + 1) := by
      rw [show first + first + 1 = first + (first + 1) by omega]
      exact Lean.Grind.Semiring.pow_add _ _ _
    unfold validatorInput
    rw [guessMinus, doubledExponent]
    rw [Rat.div_def, Rat.div_def, Rat.div_def]
    have scanCancel := Rat.mul_inv_cancel
      ((base : Rat) ^ (first + 1)) scanPowerNonzero
    have denominatorCancel := Rat.mul_inv_cancel
      ((1 : Rat) + (base : Rat) ^ (first + 1)) denominatorNonzero
    grind
  · simpa using (show base ≠ 0 by omega)

/-- The post-validator mutation `K` regenerates the unary code. -/
theorem K_regenerates_unary (base first : Nat)
    (baseAtLeastTwo : 2 ≤ base) :
    K base
        (-((base : Rat) ^ first) /
          (1 + (base : Rat) ^ (first + 1))) =
      unaryCode base first := by
  rw [unaryCode_eq]
  have plusNonzero := one_add_power_nonzero base (first + 1)
  have minusNonzero := one_sub_pow_ne_zero base (first + 1)
    baseAtLeastTwo (by omega)
  have firstSucc : (base : Rat) ^ (first + 1) =
      (base : Rat) ^ first * (base : Rat) := by
    rw [Rat.pow_succ]
  unfold K
  rw [Rat.div_def, Rat.div_def, Rat.div_def]
  have plusCancel := Rat.mul_inv_cancel
    ((1 : Rat) + (base : Rat) ^ (first + 1)) plusNonzero
  have minusCancel := Rat.mul_inv_cancel
    ((1 : Rat) - (base : Rat) ^ (first + 1)) minusNonzero
  grind

/-- The complete accepted arithmetic chain sends `z_(2a+1)` to `z_a`. -/
theorem accepted_halving_arithmetic (base first : Nat)
    (baseAtLeastTwo : 2 ≤ base) :
    K base
      (scanDigits (base : Rat) (validatorDigits first)
        (Tinv base
          (scanDigits (base : Rat) (unaryDigits first)
            (scanDigits (base : Rat) (unaryDigits first)
              (T base
                (prefixState base (first + (first + 1)) (first + 1))))))) =
      unaryCode base first := by
  rw [first_marker_scan base first (first + 1) baseAtLeastTwo,
    second_marker_scan base first (first + 1) baseAtLeastTwo (by omega),
    validator_input_formula base first (first + 1) baseAtLeastTwo (by omega),
    accepted_validator_scan base first baseAtLeastTwo,
    K_regenerates_unary base first baseAtLeastTwo]

/-- Value during the final `0*2` validator after `deleted` zeros. -/
def validatorState (base first guess deleted : Nat) : Rat :=
  ((base : Rat) ^ (guess - 1 - deleted) +
      (base : Rat) ^ (first + guess - deleted) +
      (base : Rat) ^ (first - deleted)) /
    (1 + (base : Rat) ^ guess)

def validatorIntegerNumerator (base first guess deleted : Nat) : Int :=
  (base : Int) ^ (guess - 1 - deleted) +
    (base : Int) ^ (first + guess - deleted) +
    (base : Int) ^ (first - deleted)

def validatorIntegerDenominator (base guess : Nat) : Int :=
  1 + (base : Int) ^ guess

def validatorLength (first guess : Nat) : Nat :=
  min first (guess - 1)

def validatorMarkerDigit (first guess : Nat) : Int :=
  if first = guess - 1 then 2 else 1

theorem validatorState_zero (base first guess : Nat) :
    validatorState base first guess 0 = validatorInput base first guess := by
  simp [validatorState, validatorInput]

theorem one_add_power_not_dvd (base exponent : Nat)
    (baseAtLeastTwo : 2 ≤ base) (exponentPositive : 0 < exponent) :
    ¬(base : Int) ∣ 1 + (base : Int) ^ exponent := by
  intro sumDivisible
  have powerDivisible := base_dvd_positive_power base exponent
    exponentPositive
  rcases sumDivisible with ⟨sumFactor, sumEq⟩
  rcases powerDivisible with ⟨powerFactor, powerEq⟩
  have oneDivisible : (base : Int) ∣ 1 := by
    refine ⟨sumFactor - powerFactor, ?_⟩
    calc
      (1 : Int) = (1 + (base : Int) ^ exponent) -
          (base : Int) ^ exponent := by grind
      _ = (base : Int) * sumFactor - (base : Int) * powerFactor := by
        rw [sumEq, powerEq]
      _ = (base : Int) * (sumFactor - powerFactor) := by grind
  have naturalDivisible : base ∣ 1 := by
    simpa using (Int.ofNat_dvd.mp oneDivisible)
  have baseAtMostOne := Nat.le_of_dvd Nat.zero_lt_one naturalDivisible
  omega

theorem validatorState_local (base first guess deleted : Nat)
    (baseAtLeastTwo : 2 ≤ base) (guessPositive : 0 < guess) :
    LocalAt base (Vec2.affine (validatorState base first guess deleted)) := by
  have denominatorNotDivisible := one_add_power_not_dvd base guess
    baseAtLeastTwo guessPositive
  have localFraction := local_affine_integer_div
    (prime := base)
    (numerator := validatorIntegerNumerator base first guess deleted)
    (denominator := validatorIntegerDenominator base guess)
    denominatorNotDivisible
  simpa [validatorState, validatorIntegerNumerator,
    validatorIntegerDenominator, Rat.intCast_pow, Rat.intCast_natCast,
    Rat.intCast_add] using localFraction

theorem validatorState_sameLine_integer (base first guess deleted : Nat)
    (baseAtLeastTwo : 2 ≤ base) (guessPositive : 0 < guess) :
    SameLine (Vec2.affine (validatorState base first guess deleted))
      (integerVector (validatorIntegerNumerator base first guess deleted)
        (validatorIntegerDenominator base guess)) := by
  have denominatorNotDivisible := one_add_power_not_dvd base guess
    baseAtLeastTwo guessPositive
  have denominatorNonzero : validatorIntegerDenominator base guess ≠ 0 :=
    fun denominatorZero => denominatorNotDivisible (by
      have zeroDivisible : (base : Int) ∣
          validatorIntegerDenominator base guess := by
        rw [denominatorZero]
        exact Int.dvd_zero _
      simpa [validatorIntegerDenominator] using zeroDivisible)
  have same := affine_div_sameLine_integerVector
    (numerator := validatorIntegerNumerator base first guess deleted)
    (denominator := validatorIntegerDenominator base guess)
    denominatorNonzero
  simpa [validatorState, validatorIntegerNumerator,
    validatorIntegerDenominator, Rat.intCast_pow, Rat.intCast_natCast,
    Rat.intCast_add] using same

theorem validatorState_delete_zero
    (base first guess deleted : Nat) (baseAtLeastTwo : 2 ≤ base)
    (deletedBelow : deleted < validatorLength first guess) :
    deleteDigit (base : Rat) 0 (validatorState base first guess deleted) =
      validatorState base first guess (deleted + 1) := by
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
      (base : Rat) ^ (first + guess - (deleted + 1)) * (base : Rat) := by
    rw [combinedExponent, Rat.pow_succ]
  have baseNonzero : (base : Rat) ≠ 0 := by
    simpa using (show base ≠ 0 by omega)
  have denominatorNonzero := one_add_power_nonzero base guess
  unfold deleteDigit validatorState
  rw [Rat.intCast_zero, Rat.div_def, Rat.div_def, Rat.div_def]
  have baseCancel := Rat.mul_inv_cancel (base : Rat) baseNonzero
  have denominatorCancel := Rat.mul_inv_cancel
    ((1 : Rat) + (base : Rat) ^ guess) denominatorNonzero
  grind

theorem validatorState_zero_residue
    (base first guess deleted : Nat)
    (deletedBelow : deleted < validatorLength first guess) :
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

/-- At the first nonzero validator digit, the residue is two exactly for
the accepted equality `a=b-1`; every unequal guess exposes residue one. -/
theorem validatorState_marker_residue
    (base first guess : Nat) (guessPositive : 0 < guess) :
    (base : Int) ∣
      validatorIntegerNumerator base first guess
          (validatorLength first guess) -
        validatorMarkerDigit first guess *
          validatorIntegerDenominator base guess := by
  by_cases accepted : first = guess - 1
  · have minEq : validatorLength first guess = first := by
      simp [validatorLength, accepted]
    have firstExponent : first - first = 0 := by omega
    have guessExponent : guess - 1 - first = 0 := by omega
    have combinedExponent : first + guess - first = guess := by omega
    rcases base_dvd_positive_power base guess guessPositive with
      ⟨factor, factorEq⟩
    refine ⟨-factor, ?_⟩
    rw [show validatorMarkerDigit first guess = 2 by
      simp [validatorMarkerDigit, accepted], minEq]
    unfold validatorIntegerNumerator validatorIntegerDenominator
    rw [firstExponent, guessExponent, combinedExponent]
    simp only [Int.pow_zero]
    rw [factorEq]
    grind
  · rcases Nat.lt_or_gt_of_ne accepted with firstBelow | guessBelow
    · have minEq : validatorLength first guess = first := by
        exact Nat.min_eq_left (by omega)
      have positiveExponent : 0 < guess - 1 - first := by omega
      have firstExponent : first - first = 0 := by omega
      have combinedExponent : first + guess - first = guess := by omega
      rcases base_dvd_positive_power base (guess - 1 - first)
          positiveExponent with ⟨factor, factorEq⟩
      refine ⟨factor, ?_⟩
      rw [show validatorMarkerDigit first guess = 1 by
        simp [validatorMarkerDigit, accepted], minEq]
      unfold validatorIntegerNumerator validatorIntegerDenominator
      rw [firstExponent, combinedExponent]
      simp only [Int.pow_zero]
      rw [factorEq]
      grind
    · have minEq : validatorLength first guess = guess - 1 := by
        exact Nat.min_eq_right (by omega)
      have firstExponentPositive : 0 < first - (guess - 1) := by omega
      have guessExponent : guess - 1 - (guess - 1) = 0 := by omega
      have combinedExponent : first + guess - (guess - 1) = first + 1 := by
        omega
      rcases base_dvd_positive_power base (first - (guess - 1))
          firstExponentPositive with ⟨firstFactor, firstEq⟩
      rcases base_dvd_positive_power base (first + 1) (by omega) with
        ⟨combinedFactor, combinedEq⟩
      rcases base_dvd_positive_power base guess guessPositive with
        ⟨guessFactor, guessEq⟩
      refine ⟨combinedFactor + firstFactor - guessFactor, ?_⟩
      rw [show validatorMarkerDigit first guess = 1 by
        simp [validatorMarkerDigit, accepted], minEq]
      unfold validatorIntegerNumerator validatorIntegerDenominator
      rw [guessExponent, combinedExponent]
      simp only [Int.pow_zero]
      rw [firstEq, combinedEq, guessEq]
      grind

/-- Before its first nonzero digit, the final validator is guarded by digit
zero. -/
theorem validatorState_inPhaseAt_before
    {base phase first guess deleted : Nat} (baseAtLeastTwo : 2 ≤ base)
    (guessPositive : 0 < guess)
    (deletedBelow : deleted < validatorLength first guess) :
    InPhaseAt base phase 0
      (phaseAffine phase (validatorState base first guess deleted)) := by
  apply inPhaseAt_phaseAffine_integer
    (numerator := validatorIntegerNumerator base first guess deleted)
    (denominator := validatorIntegerDenominator base guess)
    (by simp [ReservedDigit])
    (by
      simpa [validatorIntegerDenominator] using
        one_add_power_not_dvd base guess baseAtLeastTwo guessPositive)
    (by simpa using
      (validatorState_zero_residue base first guess deleted deletedBelow))
    (validatorState_sameLine_integer base first guess deleted baseAtLeastTwo
      guessPositive)

/-- At the end of the validator, the guarded digit is two on the accepted
split and one otherwise. -/
theorem validatorState_inPhaseAt_marker
    {base phase first guess : Nat} (baseAtLeastTwo : 2 ≤ base)
    (guessPositive : 0 < guess) :
    InPhaseAt base phase (validatorMarkerDigit first guess)
      (phaseAffine phase
        (validatorState base first guess (validatorLength first guess))) := by
  apply inPhaseAt_phaseAffine_integer
    (numerator := validatorIntegerNumerator base first guess
      (validatorLength first guess))
    (denominator := validatorIntegerDenominator base guess)
    (by
      unfold validatorMarkerDigit ReservedDigit
      split <;> omega)
    (by
      simpa [validatorIntegerDenominator] using
        one_add_power_not_dvd base guess baseAtLeastTwo guessPositive)
    (validatorState_marker_residue base first guess guessPositive)
    (validatorState_sameLine_integer base first guess
      (validatorLength first guess) baseAtLeastTwo guessPositive)

def halfIntegerDenominator (base first guess : Nat) : Int :=
  1 - (base : Int) ^ (first + guess + 1) -
    (base : Int) ^ (first + 1)

theorem halfIntegerDenominator_not_dvd (base first guess : Nat)
    (baseAtLeastTwo : 2 ≤ base) :
    ¬(base : Int) ∣ halfIntegerDenominator base first guess := by
  intro denominatorDivisible
  rcases base_dvd_positive_power base (first + guess + 1) (by omega) with
    ⟨combinedFactor, combinedEq⟩
  rcases base_dvd_positive_power base (first + 1) (by omega) with
    ⟨firstFactor, firstEq⟩
  rcases denominatorDivisible with ⟨denominatorFactor, denominatorEq⟩
  have oneDivisible : (base : Int) ∣ 1 := by
    refine ⟨denominatorFactor + combinedFactor + firstFactor, ?_⟩
    calc
      (1 : Int) =
          (1 - (base : Int) ^ (first + guess + 1) -
            (base : Int) ^ (first + 1)) +
            (base : Int) ^ (first + guess + 1) +
            (base : Int) ^ (first + 1) := by grind
      _ = (base : Int) * denominatorFactor +
            (base : Int) * combinedFactor +
            (base : Int) * firstFactor := by
        rw [← halfIntegerDenominator, denominatorEq, combinedEq, firstEq]
      _ = (base : Int) *
            (denominatorFactor + combinedFactor + firstFactor) := by grind
  have naturalDivisible : base ∣ 1 := by
    simpa using (Int.ofNat_dvd.mp oneDivisible)
  have baseAtMostOne := Nat.le_of_dvd Nat.zero_lt_one naturalDivisible
  omega

def firstAutomaticState (base first guess deleted : Nat) : Rat :=
  (base : Rat) ^ (first - deleted) /
    halfDenominator base first guess

def secondAutomaticState (base first guess deleted : Nat) : Rat :=
  (base : Rat) ^ (first - deleted) *
      (1 + (base : Rat) ^ guess) /
    halfDenominator base first guess

theorem firstAutomaticState_zero (base first guess : Nat)
    (baseAtLeastTwo : 2 ≤ base) :
    firstAutomaticState base first guess 0 =
      T base (prefixState base (first + guess) guess) := by
  rw [T_after_prefix base first guess baseAtLeastTwo]
  simp [firstAutomaticState]

theorem secondAutomaticState_zero (base first guess : Nat) :
    secondAutomaticState base first guess 0 =
      firstScanOutput base first guess := by
  simp [secondAutomaticState, firstScanOutput]

theorem firstAutomaticState_local (base first guess deleted : Nat)
    (baseAtLeastTwo : 2 ≤ base) :
    LocalAt base
      (Vec2.affine (firstAutomaticState base first guess deleted)) := by
  have denominatorNotDivisible := halfIntegerDenominator_not_dvd base
    first guess baseAtLeastTwo
  have localFraction := local_affine_integer_div
    (prime := base) (numerator := (base : Int) ^ (first - deleted))
    (denominator := halfIntegerDenominator base first guess)
    denominatorNotDivisible
  simpa [firstAutomaticState, halfDenominator, halfIntegerDenominator,
    Rat.intCast_pow, Rat.intCast_natCast, Rat.intCast_sub] using localFraction

theorem secondAutomaticState_local (base first guess deleted : Nat)
    (baseAtLeastTwo : 2 ≤ base) :
    LocalAt base
      (Vec2.affine (secondAutomaticState base first guess deleted)) := by
  have denominatorNotDivisible := halfIntegerDenominator_not_dvd base
    first guess baseAtLeastTwo
  have localFraction := local_affine_integer_div
    (prime := base)
    (numerator := (base : Int) ^ (first - deleted) *
      (1 + (base : Int) ^ guess))
    (denominator := halfIntegerDenominator base first guess)
    denominatorNotDivisible
  simpa [secondAutomaticState, halfDenominator, halfIntegerDenominator,
    Rat.intCast_pow, Rat.intCast_natCast, Rat.intCast_mul, Rat.intCast_add,
    Rat.intCast_sub] using localFraction

theorem firstAutomaticState_sameLine_integer
    (base first guess deleted : Nat) (baseAtLeastTwo : 2 ≤ base) :
    SameLine (Vec2.affine (firstAutomaticState base first guess deleted))
      (integerVector ((base : Int) ^ (first - deleted))
        (halfIntegerDenominator base first guess)) := by
  have denominatorNotDivisible := halfIntegerDenominator_not_dvd base
    first guess baseAtLeastTwo
  have denominatorNonzero : halfIntegerDenominator base first guess ≠ 0 :=
    fun denominatorZero => denominatorNotDivisible (by
      rw [denominatorZero]
      exact Int.dvd_zero _)
  have same := affine_div_sameLine_integerVector
    (numerator := (base : Int) ^ (first - deleted))
    (denominator := halfIntegerDenominator base first guess)
    denominatorNonzero
  simpa [firstAutomaticState, halfDenominator, halfIntegerDenominator,
    Rat.intCast_pow, Rat.intCast_natCast, Rat.intCast_sub] using same

theorem secondAutomaticState_sameLine_integer
    (base first guess deleted : Nat) (baseAtLeastTwo : 2 ≤ base) :
    SameLine (Vec2.affine (secondAutomaticState base first guess deleted))
      (integerVector
        ((base : Int) ^ (first - deleted) *
          (1 + (base : Int) ^ guess))
        (halfIntegerDenominator base first guess)) := by
  have denominatorNotDivisible := halfIntegerDenominator_not_dvd base
    first guess baseAtLeastTwo
  have denominatorNonzero : halfIntegerDenominator base first guess ≠ 0 :=
    fun denominatorZero => denominatorNotDivisible (by
      rw [denominatorZero]
      exact Int.dvd_zero _)
  have same := affine_div_sameLine_integerVector
    (numerator := (base : Int) ^ (first - deleted) *
      (1 + (base : Int) ^ guess))
    (denominator := halfIntegerDenominator base first guess)
    denominatorNonzero
  simpa [secondAutomaticState, halfDenominator, halfIntegerDenominator,
    Rat.intCast_pow, Rat.intCast_natCast, Rat.intCast_mul, Rat.intCast_add,
    Rat.intCast_sub] using same

theorem firstAutomaticState_zero_residue
    (base first guess deleted : Nat) (deletedBelow : deleted < first) :
    (base : Int) ∣ (base : Int) ^ (first - deleted) -
      0 * halfIntegerDenominator base first guess := by
  simpa using base_dvd_positive_power base (first - deleted) (by omega)

theorem firstAutomaticState_marker_residue (base first guess : Nat) :
    (base : Int) ∣ (base : Int) ^ (first - first) -
      1 * halfIntegerDenominator base first guess := by
  rcases base_dvd_positive_power base (first + guess + 1) (by omega) with
    ⟨combinedFactor, combinedEq⟩
  rcases base_dvd_positive_power base (first + 1) (by omega) with
    ⟨firstFactor, firstEq⟩
  refine ⟨combinedFactor + firstFactor, ?_⟩
  simp only [Nat.sub_self, Int.pow_zero, Int.one_mul]
  unfold halfIntegerDenominator
  rw [combinedEq, firstEq]
  grind

theorem secondAutomaticState_zero_residue
    (base first guess deleted : Nat) (deletedBelow : deleted < first) :
    (base : Int) ∣
      (base : Int) ^ (first - deleted) * (1 + (base : Int) ^ guess) -
        0 * halfIntegerDenominator base first guess := by
  rcases base_dvd_positive_power base (first - deleted) (by omega) with
    ⟨factor, factorEq⟩
  refine ⟨factor * (1 + (base : Int) ^ guess), ?_⟩
  simp only [Int.zero_mul, Int.sub_zero]
  rw [factorEq]
  grind

theorem secondAutomaticState_marker_residue
    (base first guess : Nat) (guessPositive : 0 < guess) :
    (base : Int) ∣
      (base : Int) ^ (first - first) * (1 + (base : Int) ^ guess) -
        1 * halfIntegerDenominator base first guess := by
  rcases base_dvd_positive_power base guess guessPositive with
    ⟨guessFactor, guessEq⟩
  rcases base_dvd_positive_power base (first + guess + 1) (by omega) with
    ⟨combinedFactor, combinedEq⟩
  rcases base_dvd_positive_power base (first + 1) (by omega) with
    ⟨firstFactor, firstEq⟩
  refine ⟨guessFactor + combinedFactor + firstFactor, ?_⟩
  simp only [Nat.sub_self, Int.pow_zero, Int.one_mul]
  unfold halfIntegerDenominator
  rw [guessEq, combinedEq, firstEq]
  grind

/-- Before the marker, the first automatic scan is guarded by digit zero. -/
theorem firstAutomaticState_inPhaseAt_before
    {base phase first guess deleted : Nat} (baseAtLeastTwo : 2 ≤ base)
    (deletedBelow : deleted < first) :
    InPhaseAt base phase 0
      (phaseAffine phase
        (firstAutomaticState base first guess deleted)) := by
  apply inPhaseAt_phaseAffine_integer
    (numerator := (base : Int) ^ (first - deleted))
    (denominator := halfIntegerDenominator base first guess)
    (by simp [ReservedDigit])
    (halfIntegerDenominator_not_dvd base first guess baseAtLeastTwo)
    (firstAutomaticState_zero_residue base first guess deleted deletedBelow)
    (firstAutomaticState_sameLine_integer base first guess deleted
      baseAtLeastTwo)

/-- At its marker, the first automatic scan is guarded by digit one. -/
theorem firstAutomaticState_inPhaseAt_marker
    {base phase first guess : Nat} (baseAtLeastTwo : 2 ≤ base) :
    InPhaseAt base phase 1
      (phaseAffine phase (firstAutomaticState base first guess first)) := by
  apply inPhaseAt_phaseAffine_integer
    (numerator := (base : Int) ^ (first - first))
    (denominator := halfIntegerDenominator base first guess)
    (by simp [ReservedDigit])
    (halfIntegerDenominator_not_dvd base first guess baseAtLeastTwo)
    (firstAutomaticState_marker_residue base first guess)
    (firstAutomaticState_sameLine_integer base first guess first
      baseAtLeastTwo)

/-- Before the marker, the second automatic scan is guarded by digit zero. -/
theorem secondAutomaticState_inPhaseAt_before
    {base phase first guess deleted : Nat} (baseAtLeastTwo : 2 ≤ base)
    (deletedBelow : deleted < first) :
    InPhaseAt base phase 0
      (phaseAffine phase
        (secondAutomaticState base first guess deleted)) := by
  apply inPhaseAt_phaseAffine_integer
    (numerator := (base : Int) ^ (first - deleted) *
      (1 + (base : Int) ^ guess))
    (denominator := halfIntegerDenominator base first guess)
    (by simp [ReservedDigit])
    (halfIntegerDenominator_not_dvd base first guess baseAtLeastTwo)
    (secondAutomaticState_zero_residue base first guess deleted deletedBelow)
    (secondAutomaticState_sameLine_integer base first guess deleted
      baseAtLeastTwo)

/-- At its marker, the second automatic scan is guarded by digit one. -/
theorem secondAutomaticState_inPhaseAt_marker
    {base phase first guess : Nat} (baseAtLeastTwo : 2 ≤ base)
    (guessPositive : 0 < guess) :
    InPhaseAt base phase 1
      (phaseAffine phase (secondAutomaticState base first guess first)) := by
  apply inPhaseAt_phaseAffine_integer
    (numerator := (base : Int) ^ (first - first) *
      (1 + (base : Int) ^ guess))
    (denominator := halfIntegerDenominator base first guess)
    (by simp [ReservedDigit])
    (halfIntegerDenominator_not_dvd base first guess baseAtLeastTwo)
    (secondAutomaticState_marker_residue base first guess guessPositive)
    (secondAutomaticState_sameLine_integer base first guess first
      baseAtLeastTwo)

theorem firstScanOutput_local (base first guess : Nat)
    (baseAtLeastTwo : 2 ≤ base) :
    LocalAt base (Vec2.affine (firstScanOutput base first guess)) := by
  rw [← secondAutomaticState_zero base first guess]
  exact secondAutomaticState_local base first guess 0 baseAtLeastTwo

theorem secondScanOutput_local (base first guess : Nat)
    (baseAtLeastTwo : 2 ≤ base) :
    LocalAt base (Vec2.affine (secondScanOutput base first guess)) := by
  have denominatorNotDivisible := halfIntegerDenominator_not_dvd base
    first guess baseAtLeastTwo
  have localFraction := local_affine_integer_div
    (prime := base)
    (numerator := (base : Int) ^ (guess - 1) +
      (base : Int) ^ (first + guess) + (base : Int) ^ first)
    (denominator := halfIntegerDenominator base first guess)
    denominatorNotDivisible
  simpa [secondScanOutput, halfDenominator, halfIntegerDenominator,
    Rat.intCast_pow, Rat.intCast_natCast, Rat.intCast_add,
    Rat.intCast_sub] using localFraction

theorem acceptedValidatorDeleted_local (base first : Nat)
    (baseAtLeastTwo : 2 ≤ base) :
    LocalAt base
      (Vec2.affine
        (-((base : Rat) ^ first) /
          (1 + (base : Rat) ^ (first + 1)))) := by
  have denominatorNotDivisible := one_add_power_not_dvd base (first + 1)
    baseAtLeastTwo (by omega)
  have localFraction := local_affine_integer_div
    (prime := base) (numerator := -((base : Int) ^ first))
    (denominator := 1 + (base : Int) ^ (first + 1))
    denominatorNotDivisible
  simpa [Rat.intCast_neg, Rat.intCast_pow, Rat.intCast_natCast,
    Rat.intCast_add] using localFraction

theorem firstAutomaticState_delete_zero
    (base first guess deleted : Nat) (baseAtLeastTwo : 2 ≤ base)
    (deletedBelow : deleted < first) :
    deleteDigit (base : Rat) 0
        (firstAutomaticState base first guess deleted) =
      firstAutomaticState base first guess (deleted + 1) := by
  unfold deleteDigit firstAutomaticState
  have baseNonzero : (base : Rat) ≠ 0 := by
    simpa using (show base ≠ 0 by omega)
  have denominatorNonzero := halfDenominator_nonzero base first guess
    baseAtLeastTwo
  have exponentEq : first - deleted = first - (deleted + 1) + 1 := by
    omega
  have powerEq : (base : Rat) ^ (first - deleted) =
      (base : Rat) ^ (first - (deleted + 1)) * (base : Rat) := by
    rw [exponentEq, Rat.pow_succ]
  rw [Rat.intCast_zero, Rat.div_def, Rat.div_def, Rat.div_def]
  have baseCancel := Rat.mul_inv_cancel (base : Rat) baseNonzero
  have denominatorCancel := Rat.mul_inv_cancel
    (halfDenominator base first guess) denominatorNonzero
  grind

theorem secondAutomaticState_delete_zero
    (base first guess deleted : Nat) (baseAtLeastTwo : 2 ≤ base)
    (deletedBelow : deleted < first) :
    deleteDigit (base : Rat) 0
        (secondAutomaticState base first guess deleted) =
      secondAutomaticState base first guess (deleted + 1) := by
  unfold deleteDigit secondAutomaticState
  have baseNonzero : (base : Rat) ≠ 0 := by
    simpa using (show base ≠ 0 by omega)
  have denominatorNonzero := halfDenominator_nonzero base first guess
    baseAtLeastTwo
  have exponentEq : first - deleted = first - (deleted + 1) + 1 := by
    omega
  have powerEq : (base : Rat) ^ (first - deleted) =
      (base : Rat) ^ (first - (deleted + 1)) * (base : Rat) := by
    rw [exponentEq, Rat.pow_succ]
  rw [Rat.intCast_zero, Rat.div_def, Rat.div_def, Rat.div_def]
  have baseCancel := Rat.mul_inv_cancel (base : Rat) baseNonzero
  have denominatorCancel := Rat.mul_inv_cancel
    (halfDenominator base first guess) denominatorNonzero
  grind

theorem firstAutomaticState_delete_marker
    (base first guess : Nat) (baseAtLeastTwo : 2 ≤ base) :
    deleteDigit (base : Rat) 1
        (firstAutomaticState base first guess first) =
      firstScanOutput base first guess := by
  have baseNonzero : (base : Rat) ≠ 0 := by
    simpa using (show base ≠ 0 by omega)
  have denominatorNonzero := halfDenominator_nonzero base first guess
    baseAtLeastTwo
  have firstSucc : (base : Rat) ^ (first + 1) =
      (base : Rat) ^ first * (base : Rat) := by
    rw [Rat.pow_succ]
  have splitPower : (base : Rat) ^ (first + guess + 1) =
      (base : Rat) ^ (first + 1) * (base : Rat) ^ guess := by
    rw [show first + guess + 1 = (first + 1) + guess by omega]
    exact Lean.Grind.Semiring.pow_add _ _ _
  unfold firstAutomaticState firstScanOutput deleteDigit halfDenominator
  simp only [Nat.sub_self, Rat.pow_zero, Rat.intCast_one]
  rw [Rat.div_def, Rat.div_def, Rat.div_def]
  have baseCancel := Rat.mul_inv_cancel (base : Rat) baseNonzero
  have denominatorCancel := Rat.mul_inv_cancel
    ((1 : Rat) - (base : Rat) ^ (first + guess + 1) -
      (base : Rat) ^ (first + 1)) denominatorNonzero
  grind

theorem secondAutomaticState_delete_marker
    (base first guess : Nat) (baseAtLeastTwo : 2 ≤ base)
    (guessPositive : 0 < guess) :
    deleteDigit (base : Rat) 1
        (secondAutomaticState base first guess first) =
      secondScanOutput base first guess := by
  have baseNonzero : (base : Rat) ≠ 0 := by
    simpa using (show base ≠ 0 by omega)
  have denominatorNonzero := halfDenominator_nonzero base first guess
    baseAtLeastTwo
  have guessSucc : guess = (guess - 1) + 1 := by omega
  have guessPower : (base : Rat) ^ guess =
      (base : Rat) ^ (guess - 1) * (base : Rat) := by
    calc
      (base : Rat) ^ guess = (base : Rat) ^ ((guess - 1) + 1) := by
        congr 1
      _ = (base : Rat) ^ (guess - 1) * (base : Rat) := by
        rw [Rat.pow_succ]
  have firstSucc : (base : Rat) ^ (first + 1) =
      (base : Rat) ^ first * (base : Rat) := by
    rw [Rat.pow_succ]
  have combinedSucc : (base : Rat) ^ (first + guess + 1) =
      (base : Rat) ^ (first + guess) * (base : Rat) := by
    rw [Rat.pow_succ]
  unfold secondAutomaticState secondScanOutput deleteDigit halfDenominator
  simp only [Nat.sub_self, Rat.pow_zero, Rat.intCast_one]
  rw [Rat.div_def, Rat.div_def, Rat.div_def]
  have baseCancel := Rat.mul_inv_cancel (base : Rat) baseNonzero
  have denominatorCancel := Rat.mul_inv_cancel
    ((1 : Rat) - (base : Rat) ^ (first + guess + 1) -
      (base : Rat) ^ (first + 1)) denominatorNonzero
  grind

theorem accepted_validator_delete_marker (base first : Nat)
    (baseAtLeastTwo : 2 ≤ base) :
    deleteDigit (base : Rat) 2
        (validatorState base first (first + 1) first) =
      -((base : Rat) ^ first) /
        (1 + (base : Rat) ^ (first + 1)) := by
  have baseNonzero : (base : Rat) ≠ 0 := by
    simpa using (show base ≠ 0 by omega)
  have denominatorNonzero := one_add_power_nonzero base (first + 1)
  have firstSucc : (base : Rat) ^ (first + 1) =
      (base : Rat) ^ first * (base : Rat) := by
    rw [Rat.pow_succ]
  unfold validatorState deleteDigit
  simp only [show first + 1 - 1 - first = 0 by omega,
    show first + (first + 1) - first = first + 1 by omega,
    Nat.sub_self, Rat.pow_zero, Rat.intCast_ofNat]
  rw [Rat.div_def, Rat.div_def, Rat.div_def]
  have baseCancel := Rat.mul_inv_cancel (base : Rat) baseNonzero
  have denominatorCancel := Rat.mul_inv_cancel
    ((1 : Rat) + (base : Rat) ^ (first + 1)) denominatorNonzero
  grind

end Mortality.Compiler.OddHalvingArithmetic
