import Mortality.Compiler.CodeRegion
import Mortality.Compiler.UnaryArithmetic

/-!
# Integer representatives for guarded scans

This file packages the elementary fraction calculation used by the longer
compiler modules.  A rational state is represented as `numerator/denominator`
with an integer denominator that is a unit modulo the coding prime.  Deleting
a digit then amounts to an exact integer division of
`numerator - digit * denominator` by the prime.
-/

namespace Mortality.Compiler.IntegerFraction

open Mortality.Compiler
open Mortality.Compiler.UnaryArithmetic
open Mortality.PeriodicCode

def state (numerator denominator : Int) : Rat :=
  (numerator : Rat) / (denominator : Rat)

theorem denominator_nonzero_of_not_dvd {prime : Nat} {denominator : Int}
    (notDivisible : ¬(prime : Int) ∣ denominator) :
    denominator ≠ 0 := by
  intro denominatorZero
  apply notDivisible
  rw [denominatorZero]
  exact Int.dvd_zero _

theorem state_local {prime : Nat} {numerator denominator : Int}
    (denominatorNotDivisible : ¬(prime : Int) ∣ denominator) :
    LocalAt prime (Vec2.affine (state numerator denominator)) := by
  exact local_affine_integer_div denominatorNotDivisible

theorem sameLine_integer {numerator denominator : Int}
    (denominatorNonzero : denominator ≠ 0) :
    SameLine (Vec2.affine (state numerator denominator))
      (integerVector numerator denominator) := by
  exact affine_div_sameLine_integerVector denominatorNonzero

theorem deleteDigit_eq
    (prime : Nat) (digit numerator denominator quotient : Int)
    (primePositive : 0 < prime) (denominatorNonzero : denominator ≠ 0)
    (differenceEq :
      numerator - digit * denominator = (prime : Int) * quotient) :
    deleteDigit (prime : Rat) digit (state numerator denominator) =
      state quotient denominator := by
  have primeNonzero : (prime : Rat) ≠ 0 := by
    simpa using (show prime ≠ 0 by omega)
  have denominatorNonzeroRat : (denominator : Rat) ≠ 0 := by
    exact_mod_cast denominatorNonzero
  have differenceRat :
      (numerator : Rat) - (digit : Rat) * (denominator : Rat) =
        (prime : Rat) * (quotient : Rat) := by
    exact_mod_cast differenceEq
  unfold deleteDigit state
  rw [Rat.div_def, Rat.div_def, Rat.div_def]
  have primeCancel := Rat.mul_inv_cancel (prime : Rat) primeNonzero
  have denominatorCancel := Rat.mul_inv_cancel (denominator : Rat)
    denominatorNonzeroRat
  grind

theorem deleteZero_eq
    (prime : Nat) (numerator denominator quotient : Int)
    (primePositive : 0 < prime) (denominatorNonzero : denominator ≠ 0)
    (numeratorEq : numerator = (prime : Int) * quotient) :
    deleteDigit (prime : Rat) 0 (state numerator denominator) =
      state quotient denominator := by
  apply deleteDigit_eq prime 0 numerator denominator quotient primePositive
    denominatorNonzero
  simpa using numeratorEq

theorem Tinv_state
    (prime : Nat) (numerator denominator : Int)
    (denominatorNonzero : denominator ≠ 0)
    (outputDenominatorNonzero :
      denominator + (prime : Int) * numerator ≠ 0) :
    Tinv prime (state numerator denominator) =
      state numerator (denominator + (prime : Int) * numerator) := by
  have denominatorNonzeroRat : (denominator : Rat) ≠ 0 := by
    exact_mod_cast denominatorNonzero
  have outputDenominatorNonzeroRat :
      (denominator : Rat) + (prime : Rat) * (numerator : Rat) ≠ 0 := by
    exact_mod_cast outputDenominatorNonzero
  unfold Tinv state
  simp only [Rat.intCast_add, Rat.intCast_mul, Rat.intCast_natCast,
    Rat.div_def]
  have denominatorCancel := Rat.mul_inv_cancel (denominator : Rat)
    denominatorNonzeroRat
  have outputCancel := Rat.mul_inv_cancel
    ((denominator : Rat) + (prime : Rat) * (numerator : Rat))
    outputDenominatorNonzeroRat
  grind

theorem negativeOneMutation_state
    (prime : Nat) (numerator denominator : Int)
    (denominatorNonzero : denominator ≠ 0)
    (outputDenominatorNonzero :
      denominator + (prime : Int) * numerator ≠ 0) :
    mutationMap prime .negative 1 (state numerator denominator) =
      state (-numerator) (denominator + (prime : Int) * numerator) := by
  have denominatorNonzeroRat : (denominator : Rat) ≠ 0 := by
    exact_mod_cast denominatorNonzero
  have outputDenominatorNonzeroRat :
      (denominator : Rat) + (prime : Rat) * (numerator : Rat) ≠ 0 := by
    exact_mod_cast outputDenominatorNonzero
  unfold mutationMap mutationDenominator state Sign.value
  simp only [Rat.intCast_one, Rat.intCast_neg, Rat.intCast_add,
    Rat.intCast_mul, Rat.intCast_natCast, Rat.div_def]
  have denominatorCancel := Rat.mul_inv_cancel (denominator : Rat)
    denominatorNonzeroRat
  have outputCancel := Rat.mul_inv_cancel
    ((denominator : Rat) + (prime : Rat) * (numerator : Rat))
    outputDenominatorNonzeroRat
  grind

theorem T_state
    (prime : Nat) (numerator denominator : Int)
    (denominatorNonzero : denominator ≠ 0)
    (outputDenominatorNonzero :
      denominator - (prime : Int) * numerator ≠ 0) :
    T prime (state numerator denominator) =
      state numerator (denominator - (prime : Int) * numerator) := by
  have denominatorNonzeroRat : (denominator : Rat) ≠ 0 := by
    exact_mod_cast denominatorNonzero
  have outputDenominatorNonzeroRat :
      (denominator : Rat) - (prime : Rat) * (numerator : Rat) ≠ 0 := by
    exact_mod_cast outputDenominatorNonzero
  unfold T state
  simp only [Rat.intCast_sub, Rat.intCast_mul, Rat.intCast_natCast,
    Rat.div_def]
  have denominatorCancel := Rat.mul_inv_cancel (denominator : Rat)
    denominatorNonzeroRat
  have outputCancel := Rat.mul_inv_cancel
    ((denominator : Rat) - (prime : Rat) * (numerator : Rat))
    outputDenominatorNonzeroRat
  grind

end Mortality.Compiler.IntegerFraction
