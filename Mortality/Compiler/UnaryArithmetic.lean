import Mortality.PeriodicCode
import Mortality.Compiler.PhysicalLetter

/-!
# Arithmetic identities for the unary instruction modules

This file formalizes the rational calculations in Section 5 of the
manuscript.  The finite-control and unrestricted-word arguments are kept
separate: the statements here say exactly what each completed local scan
does to the periodic codes.
-/

namespace Mortality.Compiler.UnaryArithmetic

open Mortality.PeriodicCode

private theorem div_div_same_den (numerator denominator target : Rat)
    (denominatorNonzero : denominator ≠ 0) :
    (numerator / denominator) / (target / denominator) =
      numerator / target := by
  simp only [Rat.div_def, Rat.inv_mul_rev, Rat.inv_inv]
  rw [Rat.mul_assoc numerator denominator⁻¹ (denominator * target⁻¹),
    ← Rat.mul_assoc denominator⁻¹ denominator target⁻¹,
    Rat.inv_mul_cancel _ denominatorNonzero, Rat.one_mul]

/-- The identity safe mutation. -/
def identityMutation (_base : Nat) (value : Rat) : Rat := value

/-- `T(z)=z/(1-pz)`. -/
def T (base : Nat) (value : Rat) : Rat :=
  value / (1 - (base : Rat) * value)

/-- `T⁻¹(z)=z/(1+pz)`. -/
def Tinv (base : Nat) (value : Rat) : Rat :=
  value / (1 + (base : Rat) * value)

/-- `ℕ(z)=-z`. -/
def negate (_base : Nat) (value : Rat) : Rat := -value

/-- The manuscript's named map `F⁻¹(z)=z/(1-2pz)`. -/
def Finv (base : Nat) (value : Rat) : Rat :=
  value / (1 - 2 * (base : Rat) * value)

/-- `S(z)=z/(1-p(p-1)z)`, used before an increment scan. -/
def S (base : Nat) (value : Rat) : Rat :=
  value / (1 - (base : Rat) * ((base : Rat) - 1) * value)

/-- The inverse of `S`. -/
def Sinv (base : Nat) (value : Rat) : Rat :=
  value / (1 + (base : Rat) * ((base : Rat) - 1) * value)

/-- `K(z)=-z/(1+2pz)`. -/
def K (base : Nat) (value : Rat) : Rat :=
  -value / (1 + 2 * (base : Rat) * value)

theorem T_eq_mutationMap (base : Nat) (value : Rat) :
    T base value = mutationMap base .positive (-1) value := by
  simp [T, mutationMap, mutationDenominator, Sign.value]
  congr 1 <;> grind

theorem Tinv_eq_mutationMap (base : Nat) (value : Rat) :
    Tinv base value = mutationMap base .positive 1 value := by
  simp [Tinv, mutationMap, mutationDenominator, Sign.value]

theorem negate_eq_mutationMap (base : Nat) (value : Rat) :
    negate base value = mutationMap base .negative 0 value := by
  simp [negate, mutationMap, mutationDenominator, Sign.value, Rat.div_def]
  grind

theorem Finv_eq_mutationMap (base : Nat) (value : Rat) :
    Finv base value = mutationMap base .positive (-2) value := by
  simp [Finv, mutationMap, mutationDenominator, Sign.value]
  congr 1 <;> grind

theorem S_eq_mutationMap (base : Nat) (value : Rat) :
    S base value =
      mutationMap base .positive (-(base : Int) + 1) value := by
  simp [S, mutationMap, mutationDenominator, Sign.value,
    Rat.intCast_add, Rat.intCast_neg, Rat.intCast_natCast]
  congr 1 <;> grind

theorem Sinv_eq_mutationMap (base : Nat) (value : Rat) :
    Sinv base value = mutationMap base .positive ((base : Int) - 1) value := by
  simp [Sinv, mutationMap, mutationDenominator, Sign.value,
    Rat.intCast_sub, Rat.intCast_natCast]

theorem K_eq_mutationMap (base : Nat) (value : Rat) :
    K base value = mutationMap base .negative 2 value := by
  simp [K, mutationMap, mutationDenominator, Sign.value]
  congr 1 <;> grind

/-- The first periodic-code identity, including the marker deletion. -/
theorem unary_period (base counter : Nat) (baseAtLeastTwo : 2 ≤ base) :
    scanDigits (base : Rat) (unaryDigits counter) (unaryCode base counter) =
      unaryCode base counter :=
  scanDigits_unaryCode base counter baseAtLeastTwo

/-- The signed two-field scan is one complete period. -/
theorem twoField_signed_period (base first second : Nat)
    (baseAtLeastTwo : 2 ≤ base) :
    scanDigits (base : Rat) (twoFieldDigits first second)
        (twoFieldCode base first second) =
      twoFieldCode base first second :=
  scanDigits_twoFieldCode base first second baseAtLeastTwo

/-- Scanning through the left field and its marker swaps the fields and
changes the sign.  This is equation (5.2) of the manuscript. -/
theorem twoField_half_period (base first second : Nat)
    (baseAtLeastTwo : 2 ≤ base) :
    scanDigits (base : Rat) (unaryDigits first)
        (twoFieldCode base first second) =
      -twoFieldCode base second first := by
  rw [scanDigits_eq]
  · rw [twoFieldCode_eq, twoFieldCode_eq,
      digitPolynomial_unaryDigits, unaryDigits_length]
    have baseNonzero : (base : Rat) ≠ 0 := by
      simpa using (show base ≠ 0 by omega)
    have scanPowerNonzero := pow_ne_zero baseNonzero (first + 1)
    have sourceDenominatorNonzero := one_sub_pow_ne_zero base
      (first + second + 2) baseAtLeastTwo (by omega)
    have targetDenominatorNonzero := one_sub_pow_ne_zero base
      (second + first + 2) baseAtLeastTwo (by omega)
    rw [Rat.div_def, Rat.div_def, Rat.div_def]
    have scanPowerCancel := Rat.mul_inv_cancel
      ((base : Rat) ^ (first + 1)) scanPowerNonzero
    have sourceCancel := Rat.mul_inv_cancel
      ((1 : Rat) - (base : Rat) ^ (first + second + 2))
      sourceDenominatorNonzero
    have targetCancel := Rat.mul_inv_cancel
      ((1 : Rat) - (base : Rat) ^ (second + first + 2))
      targetDenominatorNonzero
    have firstSucc : (base : Rat) ^ (first + 1) =
        (base : Rat) ^ first * (base : Rat) := by
      rw [Rat.pow_succ]
    have secondSucc : (base : Rat) ^ (second + 1) =
        (base : Rat) ^ second * (base : Rat) := by
      rw [Rat.pow_succ]
    have periodSplit : (base : Rat) ^ (first + second + 2) =
        (base : Rat) ^ (first + 1) *
          (base : Rat) ^ (second + 1) := by
      rw [show first + second + 2 = (first + 1) + (second + 1) by omega]
      exact Lean.Grind.Semiring.pow_add _ _ _
    have periodCommute : (base : Rat) ^ (second + first + 2) =
        (base : Rat) ^ (first + second + 2) := by
      congr 1
      omega
    grind
  · simpa using (show base ≠ 0 by omega)

/-- Applying `F⁻¹` to a diagonal two-field code recovers its unary
copy.  This is equation (5.4) of the manuscript. -/
theorem Finv_twoField_diagonal (base counter : Nat)
    (baseAtLeastTwo : 2 ≤ base) :
    Finv base (twoFieldCode base counter counter) =
      unaryCode base counter := by
  rw [twoFieldCode_eq, unaryCode_eq]
  have unaryDenominatorNonzero := one_sub_pow_ne_zero base (counter + 1)
    baseAtLeastTwo (by omega)
  have twoFieldDenominatorNonzero :=
    one_sub_pow_ne_zero base (counter + counter + 2)
      baseAtLeastTwo (by omega)
  have basePowerNonzero := pow_ne_zero
    (show (base : Rat) ≠ 0 by simpa using (show base ≠ 0 by omega)) counter
  rw [Finv, Rat.div_def, Rat.div_def, Rat.div_def]
  have unaryCancel := Rat.mul_inv_cancel
    ((1 : Rat) - (base : Rat) ^ (counter + 1)) unaryDenominatorNonzero
  have twoFieldCancel := Rat.mul_inv_cancel
    ((1 : Rat) - (base : Rat) ^ (counter + counter + 2))
    twoFieldDenominatorNonzero
  have powerSucc : (base : Rat) ^ (counter + 1) =
      (base : Rat) ^ counter * (base : Rat) := by
    rw [Rat.pow_succ]
  have powerDouble : (base : Rat) ^ (counter + counter + 2) =
      ((base : Rat) ^ (counter + 1)) *
        ((base : Rat) ^ (counter + 1)) := by
    rw [show counter + counter + 2 = (counter + 1) + (counter + 1) by omega]
    exact Lean.Grind.Semiring.pow_add _ _ _
  grind

/-- Closed form after the increment premutation `S`. -/
theorem S_unaryCode (base counter : Nat) (baseAtLeastTwo : 2 ≤ base) :
    S base (unaryCode base counter) =
      (base : Rat) ^ counter /
        (1 - (base : Rat) ^ (counter + 2)) := by
  rw [unaryCode_eq]
  have oldDenominatorNonzero := one_sub_pow_ne_zero base (counter + 1)
    baseAtLeastTwo (by omega)
  have newDenominatorNonzero := one_sub_pow_ne_zero base (counter + 2)
    baseAtLeastTwo (by omega)
  rw [S, Rat.div_def, Rat.div_def]
  have oldCancel := Rat.mul_inv_cancel
    ((1 : Rat) - (base : Rat) ^ (counter + 1)) oldDenominatorNonzero
  have newCancel := Rat.mul_inv_cancel
    ((1 : Rat) - (base : Rat) ^ (counter + 2)) newDenominatorNonzero
  have powerSucc : (base : Rat) ^ (counter + 1) =
      (base : Rat) ^ counter * (base : Rat) := by
    rw [Rat.pow_succ]
  have powerSuccTwo : (base : Rat) ^ (counter + 2) =
      (base : Rat) ^ (counter + 1) * (base : Rat) := by
    rw [Rat.pow_succ]
  grind

/-- The full increment scan maps `z_n` to `z_(n+1)`. -/
theorem increment_scan (base counter : Nat) (baseAtLeastTwo : 2 ≤ base) :
    scanDigits (base : Rat) (unaryDigits counter)
        (S base (unaryCode base counter)) =
      unaryCode base (counter + 1) := by
  rw [scanDigits_eq]
  · rw [S_unaryCode base counter baseAtLeastTwo,
      digitPolynomial_unaryDigits, unaryCode_eq]
    have oldDenominatorNonzero := one_sub_pow_ne_zero base (counter + 2)
      baseAtLeastTwo (by omega)
    have baseNonzero : (base : Rat) ≠ 0 := by
      simpa using (show base ≠ 0 by omega)
    have scanPowerNonzero := pow_ne_zero baseNonzero (counter + 1)
    rw [unaryDigits_length, Rat.div_def, Rat.div_def, Rat.div_def]
    have denominatorCancel := Rat.mul_inv_cancel
      ((1 : Rat) - (base : Rat) ^ (counter + 2)) oldDenominatorNonzero
    have scanPowerCancel := Rat.mul_inv_cancel
      ((base : Rat) ^ (counter + 1)) scanPowerNonzero
    have powerSucc : (base : Rat) ^ (counter + 1) =
        (base : Rat) ^ counter * (base : Rat) := by
      rw [Rat.pow_succ]
    grind
  · simpa using (show base ≠ 0 by omega)

/-- The local value after `deleted` zero deletions in an increment scan. -/
def incrementState (base counter deleted : Nat) : Rat :=
  (base : Rat) ^ (counter - deleted) /
    (1 - (base : Rat) ^ (counter + 2))

theorem incrementState_zero (base counter : Nat)
    (baseAtLeastTwo : 2 ≤ base) :
    incrementState base counter 0 = S base (unaryCode base counter) := by
  rw [S_unaryCode base counter baseAtLeastTwo]
  simp [incrementState]

theorem incrementState_delete_zero (base counter deleted : Nat)
    (baseAtLeastTwo : 2 ≤ base) (deletedBelow : deleted < counter) :
    deleteDigit (base : Rat) 0 (incrementState base counter deleted) =
      incrementState base counter (deleted + 1) := by
  unfold deleteDigit incrementState
  have baseNonzero : (base : Rat) ≠ 0 := by
    simpa using (show base ≠ 0 by omega)
  have denominatorNonzero := one_sub_pow_ne_zero base (counter + 2)
    baseAtLeastTwo (by omega)
  have exponentEq : counter - deleted =
      (counter - (deleted + 1)) + 1 := by omega
  have powerEq : (base : Rat) ^ (counter - deleted) =
      (base : Rat) ^ (counter - (deleted + 1)) * (base : Rat) := by
    rw [exponentEq, Rat.pow_succ]
  rw [Rat.intCast_zero, Rat.div_def, Rat.div_def, Rat.div_def]
  have baseCancel := Rat.mul_inv_cancel (base : Rat) baseNonzero
  have denominatorCancel := Rat.mul_inv_cancel
    ((1 : Rat) - (base : Rat) ^ (counter + 2)) denominatorNonzero
  grind

theorem incrementState_delete_marker (base counter : Nat)
    (baseAtLeastTwo : 2 ≤ base) :
    deleteDigit (base : Rat) 1 (incrementState base counter counter) =
      unaryCode base (counter + 1) := by
  unfold deleteDigit incrementState
  rw [unaryCode_eq]
  have baseNonzero : (base : Rat) ≠ 0 := by
    simpa using (show base ≠ 0 by omega)
  have denominatorNonzero := one_sub_pow_ne_zero base (counter + 2)
    baseAtLeastTwo (by omega)
  simp only [Nat.sub_self, Rat.pow_zero]
  rw [Rat.div_def, Rat.div_def, Rat.div_def]
  have baseCancel := Rat.mul_inv_cancel (base : Rat) baseNonzero
  have denominatorCancel := Rat.mul_inv_cancel
    ((1 : Rat) - (base : Rat) ^ (counter + 2)) denominatorNonzero
  grind

/-- A zero deletion followed by `S⁻¹` decrements a positive unary
code. -/
theorem decrement_step (base counter : Nat) (baseAtLeastTwo : 2 ≤ base) :
    Sinv base
        (deleteDigit (base : Rat) 0 (unaryCode base (counter + 1))) =
      unaryCode base counter := by
  rw [unaryCode_eq, unaryCode_eq]
  have largerDenominatorNonzero := one_sub_pow_ne_zero base (counter + 2)
    baseAtLeastTwo (by omega)
  have smallerDenominatorNonzero := one_sub_pow_ne_zero base (counter + 1)
    baseAtLeastTwo (by omega)
  have baseNonzero : (base : Rat) ≠ 0 := by
    simpa using (show base ≠ 0 by omega)
  rw [deleteDigit, Sinv, Rat.intCast_zero, Rat.div_def, Rat.div_def,
    Rat.div_def]
  have largerCancel := Rat.mul_inv_cancel
    ((1 : Rat) - (base : Rat) ^ (counter + 2)) largerDenominatorNonzero
  have smallerCancel := Rat.mul_inv_cancel
    ((1 : Rat) - (base : Rat) ^ (counter + 1)) smallerDenominatorNonzero
  have baseCancel := Rat.mul_inv_cancel (base : Rat) baseNonzero
  have powerSucc : (base : Rat) ^ (counter + 1) =
      (base : Rat) ^ counter * (base : Rat) := by
    rw [Rat.pow_succ]
  have powerSuccTwo : (base : Rat) ^ (counter + 2) =
      (base : Rat) ^ (counter + 1) * (base : Rat) := by
    rw [Rat.pow_succ]
  grind

/-- The marker-one deletion is the zero test on `z_0`. -/
theorem zero_test (base : Nat) (baseAtLeastTwo : 2 ≤ base) :
    deleteDigit (base : Rat) 1 (unaryCode base 0) = unaryCode base 0 := by
  change scanDigits (base : Rat) (unaryDigits 0) (unaryCode base 0) =
    unaryCode base 0
  exact unary_period base 0 baseAtLeastTwo

/-- The entry mutation for the typed right-subtraction scan. -/
theorem T_twoFieldCode (base first second : Nat)
    (baseAtLeastTwo : 2 ≤ base) :
    T base (twoFieldCode base first second) =
      (base : Rat) ^ first * (1 - (base : Rat) ^ (second + 1)) /
        (1 - (base : Rat) ^ (first + 1)) := by
  rw [twoFieldCode_eq]
  have sourceDenominatorNonzero := one_sub_pow_ne_zero base
    (first + second + 2) baseAtLeastTwo (by omega)
  have denominatorIdentity :
      1 - (base : Rat) *
          ((base : Rat) ^ first * (1 - (base : Rat) ^ (second + 1)) /
            (1 - (base : Rat) ^ (first + second + 2))) =
        (1 - (base : Rat) ^ (first + 1)) /
          (1 - (base : Rat) ^ (first + second + 2)) := by
    rw [Rat.div_def, Rat.div_def]
    have sourceCancel := Rat.mul_inv_cancel
      ((1 : Rat) - (base : Rat) ^ (first + second + 2))
      sourceDenominatorNonzero
    have firstSucc : (base : Rat) ^ (first + 1) =
        (base : Rat) ^ first * (base : Rat) := by
      rw [Rat.pow_succ]
    have periodSplit : (base : Rat) ^ (first + second + 2) =
        (base : Rat) ^ (first + 1) *
          (base : Rat) ^ (second + 1) := by
      rw [show first + second + 2 = (first + 1) + (second + 1) by omega]
      exact Lean.Grind.Semiring.pow_add _ _ _
    grind
  rw [T, denominatorIdentity]
  exact div_div_same_den _ _ _ sourceDenominatorNonzero

/-- The completed marker-one scan in the typed subtraction module. -/
theorem right_subtraction_middle (base first second : Nat)
    (baseAtLeastTwo : 2 ≤ base) :
    scanDigits (base : Rat) (unaryDigits first)
        (T base (twoFieldCode base first second)) =
      ((base : Rat) ^ first - (base : Rat) ^ second) /
        (1 - (base : Rat) ^ (first + 1)) := by
  rw [scanDigits_eq]
  · rw [T_twoFieldCode base first second baseAtLeastTwo,
      digitPolynomial_unaryDigits, unaryDigits_length]
    have baseNonzero : (base : Rat) ≠ 0 := by
      simpa using (show base ≠ 0 by omega)
    have scanPowerNonzero := pow_ne_zero baseNonzero (first + 1)
    have denominatorNonzero := one_sub_pow_ne_zero base (first + 1)
      baseAtLeastTwo (by omega)
    rw [Rat.div_def, Rat.div_def, Rat.div_def]
    have scanPowerCancel := Rat.mul_inv_cancel
      ((base : Rat) ^ (first + 1)) scanPowerNonzero
    have denominatorCancel := Rat.mul_inv_cancel
      ((1 : Rat) - (base : Rat) ^ (first + 1)) denominatorNonzero
    have firstSucc : (base : Rat) ^ (first + 1) =
        (base : Rat) ^ first * (base : Rat) := by
      rw [Rat.pow_succ]
    have secondSucc : (base : Rat) ^ (second + 1) =
        (base : Rat) ^ second * (base : Rat) := by
      rw [Rat.pow_succ]
    have baseCancel := Rat.mul_inv_cancel (base : Rat) baseNonzero
    grind
  · simpa using (show base ≠ 0 by omega)

/-- A typed scan subtracts the left-field length, plus its marker, from
the right-field length.  The strict inequality is exactly the module's
handoff type. -/
theorem right_subtraction (base first second : Nat)
    (baseAtLeastTwo : 2 ≤ base) (less : first < second) :
    Tinv base
        (scanDigits (base : Rat) (unaryDigits first)
          (T base (twoFieldCode base first second))) =
      twoFieldCode base first (second - first - 1) := by
  rw [right_subtraction_middle base first second baseAtLeastTwo,
    twoFieldCode_eq]
  have middleDenominatorNonzero := one_sub_pow_ne_zero base (first + 1)
    baseAtLeastTwo (by omega)
  have targetLengthPositive :
      0 < first + (second - first - 1) + 2 := by omega
  have targetDenominatorNonzero := one_sub_pow_ne_zero base
    (first + (second - first - 1) + 2) baseAtLeastTwo
    targetLengthPositive
  have firstSucc : (base : Rat) ^ (first + 1) =
      (base : Rat) ^ first * (base : Rat) := by
    rw [Rat.pow_succ]
  have secondSucc : (base : Rat) ^ (second + 1) =
      (base : Rat) ^ second * (base : Rat) := by
    rw [Rat.pow_succ]
  have gapSplit : (base : Rat) ^ second =
      (base : Rat) ^ first *
        (base : Rat) ^ (second - first) := by
    calc
      (base : Rat) ^ second =
          (base : Rat) ^ (first + (second - first)) := by
            congr 1
            omega
      _ = (base : Rat) ^ first * (base : Rat) ^ (second - first) :=
        Lean.Grind.Semiring.pow_add (base : Rat) first (second - first)
  have gapSuccessor : second - first = (second - first - 1) + 1 := by
    omega
  have gapPower : (base : Rat) ^ (second - first) =
      (base : Rat) ^ (second - first - 1) * (base : Rat) := by
    calc
      (base : Rat) ^ (second - first) =
          (base : Rat) ^ ((second - first - 1) + 1) := by
            congr 1
      _ = (base : Rat) ^ (second - first - 1) * (base : Rat) := by
        rw [Rat.pow_succ]
  have targetExponent : first + (second - first - 1) + 2 =
      second + 1 := by omega
  have denominatorIdentity :
      1 + (base : Rat) *
          (((base : Rat) ^ first - (base : Rat) ^ second) /
            (1 - (base : Rat) ^ (first + 1))) =
        (1 - (base : Rat) ^ (second + 1)) /
          (1 - (base : Rat) ^ (first + 1)) := by
    rw [Rat.div_def, Rat.div_def]
    have middleCancel := Rat.mul_inv_cancel
      ((1 : Rat) - (base : Rat) ^ (first + 1))
      middleDenominatorNonzero
    grind
  rw [Tinv, denominatorIdentity]
  rw [div_div_same_den _ _ _ middleDenominatorNonzero, targetExponent]
  congr 1
  grind

end Mortality.Compiler.UnaryArithmetic
