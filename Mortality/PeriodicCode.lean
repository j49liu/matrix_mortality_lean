import Mortality.Matrix2

/-!
# Periodic rational codes and complete deletion scans

Digits are stored least significant first, exactly as in Section 2.4 of
the manuscript.  The main theorem evaluates an arbitrary finite deletion
scan and derives the full-period identity without any positivity
assumption on the integer digits.
-/

namespace Mortality.PeriodicCode

/-- The base-`base` value of a least-significant-first integer digit word. -/
def digitPolynomial (base : Rat) : List Int → Rat
  | [] => 0
  | digit :: digits => (digit : Rat) + base * digitPolynomial base digits

/-- Delete one specified least-significant digit. -/
def deleteDigit (base : Rat) (digit : Int) (value : Rat) : Rat :=
  (value - (digit : Rat)) / base

/-- Apply the digit deletions in list order. -/
def scanDigits (base : Rat) : List Int → Rat → Rat
  | [], value => value
  | digit :: digits, value =>
      scanDigits base digits (deleteDigit base digit value)

def periodicCode (base : Rat) (digits : List Int) : Rat :=
  digitPolynomial base digits / (1 - base ^ digits.length)

theorem digitPolynomial_append (base : Rat) (first second : List Int) :
    digitPolynomial base (first ++ second) =
      digitPolynomial base first +
        base ^ first.length * digitPolynomial base second := by
  induction first with
  | nil =>
      simp [digitPolynomial]
      grind
  | cons digit first inductionHypothesis =>
      simp only [List.cons_append, digitPolynomial, List.length_cons,
        inductionHypothesis, Rat.pow_succ]
      grind

theorem pow_ne_zero {base : Rat} (baseNonzero : base ≠ 0) (power : Nat) :
    base ^ power ≠ 0 := by
  induction power with
  | zero =>
      simp only [Rat.pow_zero]
      decide
  | succ power inductionHypothesis =>
      rw [Rat.pow_succ]
      intro productZero
      rcases Rat.mul_eq_zero.mp productZero with powerZero | baseZero
      · exact inductionHypothesis powerZero
      · exact baseNonzero baseZero

/-- Deleting a whole digit word subtracts its polynomial and divides by
the corresponding power of the base. -/
theorem scanDigits_eq (base : Rat) (baseNonzero : base ≠ 0)
    (digits : List Int) (value : Rat) :
    scanDigits base digits value =
      (value - digitPolynomial base digits) / base ^ digits.length := by
  induction digits generalizing value with
  | nil =>
      simp only [scanDigits, digitPolynomial, List.length_nil, Rat.pow_zero]
      rw [Rat.div_def]
      grind
  | cons digit digits inductionHypothesis =>
      rw [scanDigits, inductionHypothesis]
      simp only [deleteDigit, digitPolynomial, List.length_cons, Rat.pow_succ]
      have powerNonzero := pow_ne_zero baseNonzero digits.length
      rw [Rat.div_def, Rat.div_def, Rat.div_def]
      have baseCancel := Rat.mul_inv_cancel base baseNonzero
      have powerCancel :=
        Rat.mul_inv_cancel (base ^ digits.length) powerNonzero
      have inverseProduct := Rat.inv_mul_rev (base ^ digits.length) base
      grind

/-- A positive-length word over a natural base at least two has a
nonzero periodic-code denominator. -/
theorem one_sub_pow_ne_zero (base length : Nat)
    (baseAtLeastTwo : 2 ≤ base) (lengthPositive : 0 < length) :
    (1 : Rat) - (base : Rat) ^ length ≠ 0 := by
  rw [← Rat.natCast_pow]
  intro differenceZero
  have castEq : ((base ^ length : Nat) : Rat) = (1 : Nat) := by
    grind
  have naturalEq : base ^ length = 1 := Rat.natCast_inj.mp castEq
  have greater : 1 < base ^ length :=
    Nat.one_lt_pow (Nat.ne_of_gt lengthPositive) (by omega)
  omega

/-- A complete period returns its periodic rational code to itself. -/
theorem scanDigits_periodicCode (base : Nat) (digits : List Int)
    (baseAtLeastTwo : 2 ≤ base) (digitsNonempty : digits ≠ []) :
    scanDigits (base : Rat) digits (periodicCode (base : Rat) digits) =
      periodicCode (base : Rat) digits := by
  rw [scanDigits_eq]
  · unfold periodicCode
    have baseNonzero : (base : Rat) ≠ 0 := by
      simpa using (show base ≠ 0 by omega)
    have powerNonzero := pow_ne_zero baseNonzero digits.length
    have lengthPositive : 0 < digits.length := by
      cases digits with
      | nil => contradiction
      | cons => simp
    have denominatorNonzero :=
      one_sub_pow_ne_zero base digits.length baseAtLeastTwo lengthPositive
    rw [Rat.div_def, Rat.div_def]
    have powerCancel :=
      Rat.mul_inv_cancel ((base : Rat) ^ digits.length) powerNonzero
    have denominatorCancel := Rat.mul_inv_cancel
      ((1 : Rat) - (base : Rat) ^ digits.length) denominatorNonzero
    grind
  · simpa using (show base ≠ 0 by omega)

/-- Deleting the head digit rotates a periodic code by one place. -/
theorem deleteDigit_periodicCode_cons (base : Nat) (digit : Int)
    (digits : List Int) (baseAtLeastTwo : 2 ≤ base) :
    deleteDigit (base : Rat) digit
        (periodicCode (base : Rat) (digit :: digits)) =
      periodicCode (base : Rat) (digits ++ [digit]) := by
  unfold deleteDigit periodicCode
  rw [digitPolynomial_append]
  simp only [digitPolynomial, List.length_cons, List.length_append]
  have baseNonzero : (base : Rat) ≠ 0 := by
    simpa using (show base ≠ 0 by omega)
  have denominatorNonzero := one_sub_pow_ne_zero base (digits.length + 1)
    baseAtLeastTwo (by omega)
  rw [Rat.div_def, Rat.div_def, Rat.div_def]
  have baseCancel := Rat.mul_inv_cancel (base : Rat) baseNonzero
  have denominatorCancel := Rat.mul_inv_cancel
    ((1 : Rat) - (base : Rat) ^ (digits.length + 1))
    denominatorNonzero
  have powerSucc : (base : Rat) ^ (digits.length + 1) =
      (base : Rat) ^ digits.length * (base : Rat) := by
    rw [Rat.pow_succ]
  grind

/-- Prefixing `count` zero digits multiplies the digit polynomial by the
corresponding power. -/
theorem digitPolynomial_replicate_zero_append (base : Rat)
    (count : Nat) (digits : List Int) :
    digitPolynomial base (List.replicate count 0 ++ digits) =
      base ^ count * digitPolynomial base digits := by
  induction count with
  | zero => simp
  | succ count inductionHypothesis =>
      simp only [List.replicate_succ, List.cons_append, digitPolynomial,
        Rat.intCast_zero, Rat.zero_add,
        inductionHypothesis, Rat.pow_succ]
      grind

def unaryDigits (counter : Nat) : List Int :=
  List.replicate counter 0 ++ [1]

def unaryCode (base : Nat) (counter : Nat) : Rat :=
  periodicCode (base : Rat) (unaryDigits counter)

theorem digitPolynomial_unaryDigits (base counter : Nat) :
    digitPolynomial (base : Rat) (unaryDigits counter) =
      (base : Rat) ^ counter := by
  rw [unaryDigits, digitPolynomial_replicate_zero_append]
  simp only [digitPolynomial, Rat.intCast_one, Rat.mul_zero]
  grind

theorem unaryDigits_length (counter : Nat) :
    (unaryDigits counter).length = counter + 1 := by
  simp [unaryDigits]

/-- Closed form for the manuscript's unary periodic code. -/
theorem unaryCode_eq (base counter : Nat) :
    unaryCode base counter =
      (base : Rat) ^ counter / (1 - (base : Rat) ^ (counter + 1)) := by
  simp [unaryCode, periodicCode, digitPolynomial_unaryDigits,
    unaryDigits_length]

theorem scanDigits_unaryCode (base counter : Nat)
    (baseAtLeastTwo : 2 ≤ base) :
    scanDigits (base : Rat) (unaryDigits counter) (unaryCode base counter) =
      unaryCode base counter := by
  apply scanDigits_periodicCode base (unaryDigits counter) baseAtLeastTwo
  simp [unaryDigits]

/-- The unary configuration code is injective. -/
theorem unaryCode_injective (base : Nat) (baseAtLeastTwo : 2 ≤ base) :
    Function.Injective (unaryCode base) := by
  intro first second codeEq
  rw [unaryCode_eq, unaryCode_eq] at codeEq
  have firstDenominatorNonzero :=
    one_sub_pow_ne_zero base (first + 1) baseAtLeastTwo (by omega)
  have secondDenominatorNonzero :=
    one_sub_pow_ne_zero base (second + 1) baseAtLeastTwo (by omega)
  rw [Rat.div_def, Rat.div_def] at codeEq
  have firstCancel := Rat.mul_inv_cancel
    ((1 : Rat) - (base : Rat) ^ (first + 1)) firstDenominatorNonzero
  have secondCancel := Rat.mul_inv_cancel
    ((1 : Rat) - (base : Rat) ^ (second + 1)) secondDenominatorNonzero
  have powerEq : (base : Rat) ^ first = (base : Rat) ^ second := by
    grind
  rw [← Rat.natCast_pow, ← Rat.natCast_pow] at powerEq
  have naturalPowerEq : base ^ first = base ^ second :=
    Rat.natCast_inj.mp powerEq
  apply Nat.le_antisymm
  · apply (Nat.pow_le_pow_iff_right (by omega : 1 < base)).mp
    omega
  · apply (Nat.pow_le_pow_iff_right (by omega : 1 < base)).mp
    omega

def twoFieldDigits (first second : Nat) : List Int :=
  List.replicate first 0 ++ [1] ++ List.replicate second 0 ++ [-1]

def twoFieldCode (base first second : Nat) : Rat :=
  periodicCode (base : Rat) (twoFieldDigits first second)

theorem digitPolynomial_twoFieldDigits (base first second : Nat) :
    digitPolynomial (base : Rat) (twoFieldDigits first second) =
      (base : Rat) ^ first * (1 - (base : Rat) ^ (second + 1)) := by
  let tail : List Int := [1] ++ List.replicate second 0 ++ [-1]
  have digitsEq : twoFieldDigits first second =
      List.replicate first 0 ++ tail := by
    simp [twoFieldDigits, tail, List.append_assoc]
  rw [digitsEq, digitPolynomial_replicate_zero_append]
  have tailEq : tail = 1 :: (List.replicate second 0 ++ [-1]) := by
    simp [tail, List.append_assoc]
  rw [tailEq]
  simp only [digitPolynomial]
  rw [digitPolynomial_replicate_zero_append]
  simp only [digitPolynomial, Rat.intCast_one, Rat.intCast_neg,
    Rat.mul_zero, Rat.pow_succ]
  grind

theorem twoFieldDigits_length (first second : Nat) :
    (twoFieldDigits first second).length = first + second + 2 := by
  simp [twoFieldDigits]
  omega

/-- Closed form for the manuscript's two-field periodic code. -/
theorem twoFieldCode_eq (base first second : Nat) :
    twoFieldCode base first second =
      (base : Rat) ^ first * (1 - (base : Rat) ^ (second + 1)) /
        (1 - (base : Rat) ^ (first + second + 2)) := by
  simp [twoFieldCode, periodicCode, digitPolynomial_twoFieldDigits,
    twoFieldDigits_length]

theorem scanDigits_twoFieldCode (base first second : Nat)
    (baseAtLeastTwo : 2 ≤ base) :
    scanDigits (base : Rat) (twoFieldDigits first second)
        (twoFieldCode base first second) =
      twoFieldCode base first second := by
  apply scanDigits_periodicCode base (twoFieldDigits first second)
    baseAtLeastTwo
  simp [twoFieldDigits]

end Mortality.PeriodicCode
