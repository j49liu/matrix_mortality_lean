import Mortality.Compiler.Enforcement
import Mortality.PeriodicCode

/-!
# Periodic codes as local projective integer pairs

The phase guard is formulated using homogeneous integer columns.  This
file connects that representation to the rational periodic codes and
proves that the first stored digit is exactly the residue recognized by
a physical letter.
-/

namespace Mortality.Compiler

open Mortality.PeriodicCode

def integerDigitPolynomial (base : Nat) : List Int → Int
  | [] => 0
  | digit :: digits => digit + (base : Int) *
      integerDigitPolynomial base digits

def periodicIntegerDenominator (base : Nat) (digits : List Int) : Int :=
  1 - (base : Int) ^ digits.length

theorem cast_integerDigitPolynomial (base : Nat) (digits : List Int) :
    (integerDigitPolynomial base digits : Rat) =
      digitPolynomial (base : Rat) digits := by
  induction digits with
  | nil => simp [integerDigitPolynomial, digitPolynomial]
  | cons digit digits inductionHypothesis =>
      simp only [integerDigitPolynomial, digitPolynomial, Rat.intCast_add,
        Rat.intCast_mul, Rat.intCast_natCast, inductionHypothesis]

theorem cast_periodicIntegerDenominator (base : Nat) (digits : List Int) :
    (periodicIntegerDenominator base digits : Rat) =
      1 - (base : Rat) ^ digits.length := by
  simp [periodicIntegerDenominator, Rat.intCast_sub, Rat.intCast_pow,
    Rat.intCast_natCast]

theorem affine_div_sameLine_integerVector {numerator denominator : Int}
    (denominatorNonzero : denominator ≠ 0) :
    SameLine
      (Vec2.affine ((numerator : Rat) / (denominator : Rat)))
      (integerVector numerator denominator) := by
  have castNonzero : (denominator : Rat) ≠ 0 := by
    simpa using denominatorNonzero
  have inverseNonzero : (denominator : Rat)⁻¹ ≠ 0 := by
    intro inverseZero
    have inverseCancel := Rat.inv_mul_cancel (denominator : Rat) castNonzero
    rw [inverseZero, Rat.zero_mul] at inverseCancel
    contradiction
  refine ⟨(denominator : Rat)⁻¹, inverseNonzero, ?_⟩
  simp only [Vec2.affine, integerVector, Vec2.scale, Rat.div_def]
  congr 1
  · exact Rat.mul_comm _ _
  · rw [Rat.inv_mul_cancel _ castNonzero]

theorem local_affine_integer_div {prime : Nat} {numerator denominator : Int}
    (denominatorNotDivisible : ¬(prime : Int) ∣ denominator) :
    LocalAt prime
      (Vec2.affine ((numerator : Rat) / (denominator : Rat))) := by
  exact ⟨Vec2.affine_nonzero _, numerator, denominator,
    denominatorNotDivisible,
    affine_div_sameLine_integerVector
      (fun denominatorZero => denominatorNotDivisible
        (denominatorZero ▸ Int.dvd_zero _))⟩

theorem periodicIntegerDenominator_nonzero (base : Nat) (digits : List Int)
    (baseAtLeastTwo : 2 ≤ base) (digitsNonempty : digits ≠ []) :
    periodicIntegerDenominator base digits ≠ 0 := by
  intro integerZero
  have castZero := congrArg (fun value : Int => (value : Rat)) integerZero
  change (periodicIntegerDenominator base digits : Rat) = 0 at castZero
  rw [cast_periodicIntegerDenominator] at castZero
  have lengthPositive : 0 < digits.length := by
    cases digits with
    | nil => contradiction
    | cons => simp
  exact one_sub_pow_ne_zero base digits.length baseAtLeastTwo lengthPositive
    castZero

/-- The affine periodic code and its integral homogeneous numerator and
denominator represent the same rational line. -/
theorem periodicCode_sameLine_integerVector (base : Nat)
    (digits : List Int) (baseAtLeastTwo : 2 ≤ base)
    (digitsNonempty : digits ≠ []) :
    SameLine (Vec2.affine (periodicCode (base : Rat) digits))
      (integerVector (integerDigitPolynomial base digits)
        (periodicIntegerDenominator base digits)) := by
  unfold periodicCode
  rw [← cast_integerDigitPolynomial,
    ← cast_periodicIntegerDenominator]
  exact affine_div_sameLine_integerVector
    (periodicIntegerDenominator_nonzero base digits baseAtLeastTwo
      digitsNonempty)

theorem base_dvd_positive_power (base exponent : Nat)
    (exponentPositive : 0 < exponent) :
    (base : Int) ∣ (base : Int) ^ exponent := by
  obtain ⟨previous, rfl⟩ := Nat.exists_eq_succ_of_ne_zero
    (by omega : exponent ≠ 0)
  refine ⟨(base : Int) ^ previous, ?_⟩
  rw [Int.pow_succ]
  grind

/-- The denominator `1-p^L` of every nonempty periodic code is a unit
modulo `p`. -/
theorem periodicIntegerDenominator_not_dvd (base : Nat)
    (digits : List Int) (baseAtLeastTwo : 2 ≤ base)
    (digitsNonempty : digits ≠ []) :
    ¬(base : Int) ∣ periodicIntegerDenominator base digits := by
  intro denominatorDivisible
  have lengthPositive : 0 < digits.length := by
    cases digits with
    | nil => contradiction
    | cons => simp
  have powerDivisible := base_dvd_positive_power base digits.length
    lengthPositive
  have oneDivisible : (base : Int) ∣ 1 := by
    have sumDivisible := Int.dvd_add denominatorDivisible powerDivisible
    have sumEq : periodicIntegerDenominator base digits +
        (base : Int) ^ digits.length = 1 := by
      unfold periodicIntegerDenominator
      grind
    rw [sumEq] at sumDivisible
    exact sumDivisible
  have naturalDivisible : base ∣ 1 := by
    simpa using (Int.ofNat_dvd.mp oneDivisible)
  have baseAtMostOne := Nat.le_of_dvd Nat.zero_lt_one naturalDivisible
  omega

theorem one_sub_power_not_dvd (base exponent : Nat)
    (baseAtLeastTwo : 2 ≤ base) (exponentPositive : 0 < exponent) :
    ¬(base : Int) ∣ 1 - (base : Int) ^ exponent := by
  let digits := List.replicate exponent (0 : Int)
  have digitsNonempty : digits ≠ [] := by
    intro digitsEmpty
    have lengthZero := congrArg List.length digitsEmpty
    simp [digits] at lengthZero
    omega
  have result := periodicIntegerDenominator_not_dvd base digits
    baseAtLeastTwo digitsNonempty
  simpa [periodicIntegerDenominator, digits] using result

/-- Every nonempty periodic code is a finite point of the local region. -/
theorem periodicCode_local_affine (base : Nat) (digits : List Int)
    (baseAtLeastTwo : 2 ≤ base) (digitsNonempty : digits ≠ []) :
    LocalAt base (Vec2.affine (periodicCode (base : Rat) digits)) := by
  exact ⟨Vec2.affine_nonzero _, integerDigitPolynomial base digits,
    periodicIntegerDenominator base digits,
    periodicIntegerDenominator_not_dvd base digits baseAtLeastTwo
      digitsNonempty,
    periodicCode_sameLine_integerVector base digits baseAtLeastTwo
      digitsNonempty⟩

/-- A correct head-digit deletion rotates a periodic code and remains
inside the local region. -/
theorem deleteDigit_periodicCode_local (base : Nat) (digit : Int)
    (digits : List Int) (baseAtLeastTwo : 2 ≤ base) :
    LocalAt base
      (Vec2.affine
        (deleteDigit (base : Rat) digit
          (periodicCode (base : Rat) (digit :: digits)))) := by
  rw [deleteDigit_periodicCode_cons base digit digits baseAtLeastTwo]
  exact periodicCode_local_affine base (digits ++ [digit]) baseAtLeastTwo
    (by simp)

/-- With identity mutations, one physical letter performs one cyclic
digit rotation and changes only the phase chart. -/
theorem physicalLetter_rotates_periodicCode
    (base sourcePhase targetPhase : Nat) (digit : Int)
    (digits : List Int) (baseAtLeastTwo : 2 ≤ base) :
    SameLine
      (Matrix2.apply
        (IntMatrix2.cast
          (physicalLetter base sourcePhase targetPhase digit 0
            .positive 0))
        (Vec2.affine
          (periodicCode (base : Rat) (digit :: digits) +
            (phaseShift sourcePhase : Rat))))
      (Vec2.affine
        (periodicCode (base : Rat) (digits ++ [digit]) +
          (phaseShift targetPhase : Rat))) := by
  have inputLocal := periodicCode_local_affine base (digit :: digits)
    baseAtLeastTwo (by simp)
  have deletedLocal := deleteDigit_periodicCode_local base digit digits
    baseAtLeastTwo
  have action := physicalLetter_affine_sameLine_of_local
    (sourcePhase := sourcePhase) (targetPhase := targetPhase)
    (digit := digit) (preCoefficient := 0) (postCoefficient := 0)
    (postSign := .positive) (primePositive := by omega)
    inputLocal (by simpa [deleteDigit] using deletedLocal)
  simp [localLetterMap] at action
  have rotation := deleteDigit_periodicCode_cons base digit digits
    baseAtLeastTwo
  unfold deleteDigit at rotation
  rw [rotation] at action
  exact action

/-- The first digit of a nonempty word is its periodic numerator modulo
the base. -/
theorem head_digit_divides (base : Nat) (digit : Int) (digits : List Int) :
    (base : Int) ∣
      integerDigitPolynomial base (digit :: digits) -
        digit * periodicIntegerDenominator base (digit :: digits) := by
  refine ⟨integerDigitPolynomial base digits +
      digit * (base : Int) ^ digits.length, ?_⟩
  simp only [integerDigitPolynomial, periodicIntegerDenominator,
    List.length_cons, Int.pow_succ]
  grind

/-- Every nonempty periodic code is local and carries its head digit as
the exact phase-guard residue. -/
theorem periodicCode_local_with_head (base : Nat) (digit : Int)
    (digits : List Int) (baseAtLeastTwo : 2 ≤ base) :
    LocalAt base
        (integerVector (integerDigitPolynomial base (digit :: digits))
          (periodicIntegerDenominator base (digit :: digits))) ∧
      (base : Int) ∣
        integerDigitPolynomial base (digit :: digits) -
          digit * periodicIntegerDenominator base (digit :: digits) := by
  constructor
  · exact local_integerVector
      (periodicIntegerDenominator_not_dvd base (digit :: digits)
        baseAtLeastTwo (by simp))
  · exact head_digit_divides base digit digits

theorem periodicCode_inPhaseAt (base phase : Nat) (digit : Int)
    (digits : List Int) (baseAtLeastTwo : 2 ≤ base)
    (reserved : ReservedDigit digit) :
    InPhaseAt base phase digit
      (phaseAffine phase
        (periodicCode (base : Rat) (digit :: digits))) := by
  apply inPhaseAt_phaseAffine_integer reserved
    (periodicIntegerDenominator_not_dvd base (digit :: digits)
      baseAtLeastTwo (by simp))
    (head_digit_divides base digit digits)
  exact periodicCode_sameLine_integerVector base (digit :: digits)
    baseAtLeastTwo (by simp)

/-- Every unary code carries its actual head digit: one for the zero counter
and zero for a positive counter. -/
theorem unaryCode_inPhaseAt
    {base phase counter : Nat} (baseAtLeastTwo : 2 ≤ base) :
    ∃ digit, InPhaseAt base phase digit
      (phaseAffine phase (unaryCode base counter)) := by
  cases counter with
  | zero =>
      refine ⟨1, ?_⟩
      simpa [unaryCode, unaryDigits] using
        (periodicCode_inPhaseAt base phase 1 [] baseAtLeastTwo
          (by simp [ReservedDigit]))
  | succ counter =>
      refine ⟨0, ?_⟩
      simpa [unaryCode, unaryDigits, List.replicate_succ,
        List.append_assoc] using
        (periodicCode_inPhaseAt base phase 0
          (List.replicate counter 0 ++ [1]) baseAtLeastTwo
          (by simp [ReservedDigit]))

/-- Specialization of phase enforcement to an arbitrary nonempty
periodic word. -/
theorem physicalLetter_periodic_source_digit_unique
    {prime phaseCount actualPhase sourcePhase targetPhase : Nat}
    {actualDigit letterDigit preCoefficient postCoefficient : Int}
    {postSign : Sign} (remainingDigits : List Int)
    (primeProperty : IsPrime prime)
    (primeBound : 6 * phaseCount < prime)
    (actualPhaseBound : actualPhase < phaseCount)
    (sourcePhaseBound : sourcePhase < phaseCount)
    (actualReserved : ReservedDigit actualDigit)
    (letterReserved : ReservedDigit letterDigit)
    (outputLocal :
      LocalAt prime
        (Matrix2.apply
          (IntMatrix2.cast
            (physicalLetter prime sourcePhase targetPhase letterDigit
              preCoefficient postSign postCoefficient))
          (phasePoint actualPhase
            (integerDigitPolynomial prime (actualDigit :: remainingDigits))
            (periodicIntegerDenominator prime
              (actualDigit :: remainingDigits))))) :
    actualPhase = sourcePhase ∧ actualDigit = letterDigit := by
  apply physicalLetter_source_digit_unique primeProperty primeBound
    actualPhaseBound sourcePhaseBound actualReserved letterReserved
  · exact periodicIntegerDenominator_not_dvd prime
      (actualDigit :: remainingDigits) primeProperty.1 (by simp)
  · exact head_digit_divides prime actualDigit remainingDigits
  · exact outputLocal

/-- Affine-coordinate version of periodic phase enforcement.  This is the
form used by the instruction modules and the final reachability statement. -/
theorem physicalLetter_periodic_affine_source_digit_unique
    {prime phaseCount actualPhase sourcePhase targetPhase : Nat}
    {actualDigit letterDigit preCoefficient postCoefficient : Int}
    {postSign : Sign} (remainingDigits : List Int)
    (primeProperty : IsPrime prime)
    (primeBound : 6 * phaseCount < prime)
    (actualPhaseBound : actualPhase < phaseCount)
    (sourcePhaseBound : sourcePhase < phaseCount)
    (actualReserved : ReservedDigit actualDigit)
    (letterReserved : ReservedDigit letterDigit)
    (outputLocal :
      LocalAt prime
        (Matrix2.apply
          (IntMatrix2.cast
            (physicalLetter prime sourcePhase targetPhase letterDigit
              preCoefficient postSign postCoefficient))
          (Vec2.affine
            (periodicCode (prime : Rat) (actualDigit :: remainingDigits) +
              (phaseShift actualPhase : Rat))))) :
    actualPhase = sourcePhase ∧ actualDigit = letterDigit := by
  let numerator := integerDigitPolynomial prime
    (actualDigit :: remainingDigits)
  let denominator := periodicIntegerDenominator prime
    (actualDigit :: remainingDigits)
  have denominatorNotDivisible := periodicIntegerDenominator_not_dvd prime
    (actualDigit :: remainingDigits) primeProperty.1 (by simp)
  have codeSame := periodicCode_sameLine_integerVector prime
    (actualDigit :: remainingDigits) primeProperty.1 (by simp)
  have chartedSame := codeSame.apply (IntMatrix2.cast (chart actualPhase))
  rw [chart_apply] at chartedSame
  change SameLine
      (Vec2.affine
        (periodicCode (prime : Rat) (actualDigit :: remainingDigits) +
          (phaseShift actualPhase : Rat)))
      (phasePoint actualPhase numerator denominator) at chartedSame
  have outputSame := chartedSame.apply
    (IntMatrix2.cast
      (physicalLetter prime sourcePhase targetPhase letterDigit
        preCoefficient postSign postCoefficient))
  have phasePointLocal :
      LocalAt prime (phasePoint actualPhase numerator denominator) := by
    apply (local_chart_iff prime actualPhase _).mpr
    exact local_integerVector denominatorNotDivisible
  have letterNonsingular :
      (physicalLetter prime sourcePhase targetPhase letterDigit
        preCoefficient postSign postCoefficient).Nonsingular :=
    physicalLetter_nonsingular
      (sourcePhase := sourcePhase) (targetPhase := targetPhase)
      (digit := letterDigit) (preCoefficient := preCoefficient)
      (postSign := postSign) (postCoefficient := postCoefficient)
      (by omega)
  have canonicalOutputNonzero := Matrix2.apply_nonzero
    (IntMatrix2.cast_nonsingular letterNonsingular)
    phasePointLocal.1
  have canonicalOutputLocal := LocalAt.of_sameLine outputLocal
    canonicalOutputNonzero outputSame.symm
  exact physicalLetter_periodic_source_digit_unique remainingDigits
    primeProperty primeBound actualPhaseBound sourcePhaseBound
    actualReserved letterReserved canonicalOutputLocal

end Mortality.Compiler
