import Mortality.PeriodicCode

/-!
# Arithmetic infrastructure for the proportional contractions

The contraction proofs are most transparent in the auxiliary coordinate
`t = pz`.  A scan of `a` zeroes followed by marker `e` has total length
`a+1` and sends `t` to `t / p^(a+1) - e`.  This file proves that recurrence
from the finite digit scanner, without appealing to valuations.
-/

namespace Mortality.Compiler.ContractionArithmetic

open Mortality.PeriodicCode

def markerScanDigits (zeros : Nat) (marker : Int) : List Int :=
  List.replicate zeros 0 ++ [marker]

@[simp] theorem markerScanDigits_length (zeros : Nat) (marker : Int) :
    (markerScanDigits zeros marker).length = zeros + 1 := by
  simp [markerScanDigits]

theorem digitPolynomial_markerScanDigits
    (base : Rat) (zeros : Nat) (marker : Int) :
    digitPolynomial base (markerScanDigits zeros marker) =
      base ^ zeros * (marker : Rat) := by
  rw [markerScanDigits, digitPolynomial_replicate_zero_append]
  simp only [digitPolynomial]
  grind

/-- A complete marker scan in the auxiliary coordinate `t = pz`. -/
theorem auxiliary_marker_scan
    (base zeros : Nat) (marker : Int) (value : Rat)
    (basePositive : 0 < base) :
    (base : Rat) *
        scanDigits (base : Rat) (markerScanDigits zeros marker) value =
      ((base : Rat) * value) / (base : Rat) ^ (zeros + 1) - marker := by
  rw [scanDigits_eq]
  · rw [digitPolynomial_markerScanDigits, markerScanDigits_length]
    have baseNonzero : (base : Rat) ≠ 0 := by
      exact_mod_cast (Nat.ne_of_gt basePositive)
    have powerNonzero : (base : Rat) ^ (zeros + 1) ≠ 0 :=
      pow_ne_zero baseNonzero (zeros + 1)
    have powerSucc : (base : Rat) ^ (zeros + 1) =
        (base : Rat) ^ zeros * (base : Rat) := by
      rw [Rat.pow_succ]
    rw [Rat.div_def, Rat.div_def]
    have powerCancel := Rat.mul_inv_cancel
      ((base : Rat) ^ (zeros + 1)) powerNonzero
    grind
  · exact_mod_cast (Nat.ne_of_gt basePositive)

theorem auxiliary_positive_scan
    (base zeros : Nat) (value : Rat) (basePositive : 0 < base) :
    (base : Rat) *
        scanDigits (base : Rat) (unaryDigits zeros) value =
      ((base : Rat) * value) / (base : Rat) ^ (zeros + 1) - 1 := by
  simpa [unaryDigits, markerScanDigits] using
    auxiliary_marker_scan base zeros 1 value basePositive

theorem auxiliary_negative_scan
    (base zeros : Nat) (value : Rat) (basePositive : 0 < base) :
    (base : Rat) *
        scanDigits (base : Rat) (markerScanDigits zeros (-1)) value =
      ((base : Rat) * value) / (base : Rat) ^ (zeros + 1) + 1 := by
  have recurrence := auxiliary_marker_scan base zeros (-1) value basePositive
  rw [recurrence]
  grind

def iteratedMarkerScan (base zeros : Nat) (marker : Int) :
    Nat → Rat → Rat
  | 0, value => value
  | steps + 1, value =>
      scanDigits (base : Rat) (markerScanDigits zeros marker)
        (iteratedMarkerScan base zeros marker steps value)

def iteratedAuxiliaryStep (scale : Rat) (marker : Int) :
    Nat → Rat → Rat
  | 0, value => value
  | steps + 1, value =>
      iteratedAuxiliaryStep scale marker steps value / scale - marker

/-- Iterating physical marker scans is exactly iteration of the affine
recurrence in the auxiliary coordinate. -/
theorem auxiliary_iterated_marker_scan
    (base zeros steps : Nat) (marker : Int) (value : Rat)
    (basePositive : 0 < base) :
    (base : Rat) * iteratedMarkerScan base zeros marker steps value =
      iteratedAuxiliaryStep ((base : Rat) ^ (zeros + 1)) marker steps
        ((base : Rat) * value) := by
  induction steps with
  | zero => rfl
  | succ steps inductionHypothesis =>
      rw [iteratedMarkerScan, iteratedAuxiliaryStep,
        auxiliary_marker_scan base zeros marker _ basePositive,
        inductionHypothesis]

@[simp] theorem iteratedAuxiliaryStep_one
    (scale value : Rat) (marker : Int) :
    iteratedAuxiliaryStep scale marker 1 value = value / scale - marker := by
  rfl

@[simp] theorem iteratedAuxiliaryStep_two
    (scale value : Rat) (marker : Int) :
    iteratedAuxiliaryStep scale marker 2 value =
      (value / scale - marker) / scale - marker := by
  rfl

@[simp] theorem iteratedAuxiliaryStep_five
    (scale value : Rat) (marker : Int) :
    iteratedAuxiliaryStep scale marker 5 value =
      (((((value / scale - marker) / scale - marker) / scale - marker) /
        scale - marker) / scale - marker) := by
  rfl

/-- Closed numerator after the five positive scans on the accepted
fivefold split.  Here `q=p^(a+1)` and `D=1-q-q^5`. -/
theorem five_positive_scans_closed
    (q denominator : Rat) (qNonzero : q ≠ 0)
    (denominatorNonzero : denominator ≠ 0)
    (denominatorEq : denominator = 1 - q - q ^ 5) :
    iteratedAuxiliaryStep q 1 5 (q / denominator) =
      (2 * q + q ^ 2 + q ^ 3 + q ^ 4 + q ^ 5) / denominator := by
  rw [iteratedAuxiliaryStep_five, denominatorEq]
  simp only [Rat.intCast_one, Rat.div_def]
  have qCancel := Rat.mul_inv_cancel q qNonzero
  have denominatorCancel := Rat.mul_inv_cancel
    (1 - q - q ^ 5) (by simpa [denominatorEq] using denominatorNonzero)
  grind

/-- The accepted `T⁻¹`, marker-two scan, and negation leave the
auxiliary coordinate of `X_(a,4a+3)`. -/
theorem accepted_marker_two_closed
    (q denominator : Rat) (qNonzero : q ≠ 0)
    (denominatorNonzero : denominator ≠ 0)
    (denominatorEq : denominator = 1 - q - q ^ 5)
    (geometricSumNonzero : 1 + q + q ^ 2 + q ^ 3 + q ^ 4 ≠ 0) :
    let numerator := 2 * q + q ^ 2 + q ^ 3 + q ^ 4 + q ^ 5;
    -((numerator / denominator / (1 + numerator / denominator)) / q - 2) =
      (q + q ^ 2 + q ^ 3 + q ^ 4) /
        (1 + q + q ^ 2 + q ^ 3 + q ^ 4) := by
  dsimp
  subst denominator
  let numerator : Rat := 2 * q + q ^ 2 + q ^ 3 + q ^ 4 + q ^ 5
  let denominator : Rat := 1 - q - q ^ 5
  let geometricSum : Rat := 1 + q + q ^ 2 + q ^ 3 + q ^ 4
  change -((numerator / denominator /
      (1 + numerator / denominator)) / q - 2) =
    (q + q ^ 2 + q ^ 3 + q ^ 4) / geometricSum
  have denominatorNonzero' : denominator ≠ 0 := by
    simpa [denominator] using denominatorNonzero
  have geometricSumNonzero' : geometricSum ≠ 0 := by
    simpa [geometricSum] using geometricSumNonzero
  have onePlus : 1 + numerator / denominator =
      geometricSum / denominator := by
    simp only [Rat.div_def]
    have denominatorCancel := Rat.mul_inv_cancel denominator
      denominatorNonzero'
    unfold numerator denominator geometricSum
    grind
  have quotient :
      (numerator / denominator) / (geometricSum / denominator) =
        numerator / geometricSum := by
    simp only [Rat.div_def, Rat.inv_mul_rev, Rat.inv_inv]
    rw [Rat.mul_assoc numerator denominator⁻¹
      (denominator * geometricSum⁻¹),
      ← Rat.mul_assoc denominator⁻¹ denominator geometricSum⁻¹,
      Rat.inv_mul_cancel denominator denominatorNonzero', Rat.one_mul]
  rw [onePlus, quotient]
  simp only [Rat.div_def]
  have qCancel := Rat.mul_inv_cancel q qNonzero
  let factor : Rat := 2 + q + q ^ 2 + q ^ 3 + q ^ 4
  have numeratorFactor : numerator = q * factor := by
    unfold numerator factor
    grind
  rw [numeratorFactor]
  have cancelQ :
      q * factor * geometricSum⁻¹ * q⁻¹ = factor * geometricSum⁻¹ := by
    calc
      q * factor * geometricSum⁻¹ * q⁻¹ =
          (q * q⁻¹) * (factor * geometricSum⁻¹) := by
        rw [Rat.mul_assoc q factor geometricSum⁻¹,
          Rat.mul_assoc q (factor * geometricSum⁻¹) q⁻¹,
          Rat.mul_comm (factor * geometricSum⁻¹) q⁻¹,
          ← Rat.mul_assoc q q⁻¹ (factor * geometricSum⁻¹)]
      _ = factor * geometricSum⁻¹ := by
        rw [qCancel, Rat.one_mul]
  rw [cancelQ]
  unfold factor geometricSum
  grind

theorem correct_fivefold_denominator_nonzero
    (base first : Nat) (baseAtLeastTwo : 2 ≤ base) :
    let q : Rat := (base : Rat) ^ (first + 1)
    1 - q - q ^ 5 ≠ 0 := by
  dsimp
  have qAtLeastOne :
      (1 : Rat) ≤ (base : Rat) ^ (first + 1) := by
    rw [← Rat.natCast_pow]
    exact_mod_cast Nat.one_le_pow (first + 1) base (by omega)
  have fifthPowerAtLeastOne :
      (1 : Rat) ≤ ((base : Rat) ^ (first + 1)) ^ 5 := by
    have qNatAtLeastOne : 1 ≤ base ^ (first + 1) :=
      Nat.one_le_pow (first + 1) base (by omega)
    have naturalPowerAtLeastOne :
        1 ≤ (base ^ (first + 1)) ^ 5 :=
      Nat.one_le_pow 5 (base ^ (first + 1)) qNatAtLeastOne
    simpa [Rat.natCast_pow] using
      (show (1 : Rat) ≤ (((base ^ (first + 1)) ^ 5 : Nat) : Rat) by
        exact_mod_cast naturalPowerAtLeastOne)
  grind

theorem correct_fivefold_geometric_sum_nonzero
    (base first : Nat) :
    let q : Rat := (base : Rat) ^ (first + 1)
    1 + q + q ^ 2 + q ^ 3 + q ^ 4 ≠ 0 := by
  dsimp
  let qNat : Nat := base ^ (first + 1)
  have castIdentity :
      (((1 + qNat + qNat ^ 2 + qNat ^ 3 + qNat ^ 4 : Nat) : Rat)) =
        1 + (base : Rat) ^ (first + 1) +
          ((base : Rat) ^ (first + 1)) ^ 2 +
          ((base : Rat) ^ (first + 1)) ^ 3 +
          ((base : Rat) ^ (first + 1)) ^ 4 := by
    simp [qNat, Rat.natCast_add, Rat.natCast_pow]
  intro sumZero
  have castZero :
      (((1 + qNat + qNat ^ 2 + qNat ^ 3 + qNat ^ 4 : Nat) : Rat)) =
        0 := by
    rw [castIdentity, sumZero]
  have naturalZero : 1 + qNat + qNat ^ 2 + qNat ^ 3 + qNat ^ 4 = 0 :=
    Rat.natCast_inj.mp castZero
  omega

/-- The closed auxiliary coordinate produced by the correct fivefold split
is exactly the auxiliary coordinate of the claimed two-field code. -/
theorem accepted_front_coordinate_eq_twoFieldCode
    (base first : Nat) (baseAtLeastTwo : 2 ≤ base) :
    let q : Rat := (base : Rat) ^ (first + 1)
    (q + q ^ 2 + q ^ 3 + q ^ 4) /
        (1 + q + q ^ 2 + q ^ 3 + q ^ 4) =
      (base : Rat) * twoFieldCode base first (4 * first + 3) := by
  dsimp
  let q : Rat := (base : Rat) ^ (first + 1)
  have geometricSumNonzero :
      1 + q + q ^ 2 + q ^ 3 + q ^ 4 ≠ 0 := by
    simpa [q] using correct_fivefold_geometric_sum_nonzero base first
  have targetDenominatorNonzero :
      (1 : Rat) - (base : Rat) ^ (5 * first + 5) ≠ 0 :=
    one_sub_pow_ne_zero base (5 * first + 5) baseAtLeastTwo (by omega)
  have firstPower :
      (base : Rat) ^ (first + 1) = (base : Rat) ^ first * base := by
    rw [Rat.pow_succ]
  have fourthPower :
      (base : Rat) ^ (4 * first + 4) = q ^ 4 := by
    rw [show 4 * first + 4 =
      (first + 1) + (first + 1) + (first + 1) + (first + 1) by omega]
    unfold q
    repeat' rw [Lean.Grind.Semiring.pow_add]
    grind
  have fifthPower :
      (base : Rat) ^ (5 * first + 5) = q ^ 5 := by
    rw [show 5 * first + 5 =
      (first + 1) + (first + 1) + (first + 1) + (first + 1) +
        (first + 1) by omega]
    unfold q
    repeat' rw [Lean.Grind.Semiring.pow_add]
    grind
  rw [twoFieldCode_eq]
  rw [show first + (4 * first + 3) + 2 = 5 * first + 5 by omega,
    fourthPower, fifthPower]
  simp only [Rat.div_def]
  have geometricCancel := Rat.mul_inv_cancel
    (1 + q + q ^ 2 + q ^ 3 + q ^ 4) geometricSumNonzero
  have targetCancel := Rat.mul_inv_cancel (1 - q ^ 5)
    (by simpa [fifthPower] using targetDenominatorNonzero)
  have leadingPower : (base : Rat) * (base : Rat) ^ first = q := by
    rw [Rat.mul_comm]
    exact firstPower.symm
  change
    (q + q ^ 2 + q ^ 3 + q ^ 4) *
        (1 + q + q ^ 2 + q ^ 3 + q ^ 4)⁻¹ =
      (base : Rat) *
        ((base : Rat) ^ first * (1 - q ^ 4) * (1 - q ^ 5)⁻¹)
  have rhsLeading :
      (base : Rat) *
          ((base : Rat) ^ first * (1 - q ^ 4) * (1 - q ^ 5)⁻¹) =
        q * (1 - q ^ 4) * (1 - q ^ 5)⁻¹ := by
    rw [Rat.mul_assoc ((base : Rat) ^ first) (1 - q ^ 4)
        (1 - q ^ 5)⁻¹,
      ← Rat.mul_assoc (base : Rat) ((base : Rat) ^ first)
        ((1 - q ^ 4) * (1 - q ^ 5)⁻¹),
      ← Rat.mul_assoc ((base : Rat) * (base : Rat) ^ first)
        (1 - q ^ 4) (1 - q ^ 5)⁻¹,
      leadingPower]
  rw [rhsLeading]
  grind

/-- The complete rational calculation for the correct fivefold split.
It begins with the auxiliary coordinate after the guessed prefix and `T`,
performs the five positive scans, then `T⁻¹`, the marker-two scan, and
the final negation. -/
theorem accepted_fivefold_front_auxiliary
    (base first : Nat) (baseAtLeastTwo : 2 ≤ base) :
    let q : Rat := (base : Rat) ^ (first + 1);
    let denominator : Rat := 1 - q - q ^ 5;
    let afterFive := iteratedAuxiliaryStep q 1 5 (q / denominator);
    -((afterFive / (1 + afterFive)) / q - 2) =
      (base : Rat) * twoFieldCode base first (4 * first + 3) := by
  dsimp
  let q : Rat := (base : Rat) ^ (first + 1)
  let denominator : Rat := 1 - q - q ^ 5
  have baseNonzero : (base : Rat) ≠ 0 := by
    simpa using (show base ≠ 0 by omega)
  have qNonzero : q ≠ 0 := by
    unfold q
    exact pow_ne_zero baseNonzero (first + 1)
  have denominatorNonzero : denominator ≠ 0 := by
    simpa [q, denominator] using
      correct_fivefold_denominator_nonzero base first baseAtLeastTwo
  have geometricSumNonzero :
      1 + q + q ^ 2 + q ^ 3 + q ^ 4 ≠ 0 := by
    simpa [q] using correct_fivefold_geometric_sum_nonzero base first
  rw [five_positive_scans_closed q denominator qNonzero
    denominatorNonzero rfl]
  rw [accepted_marker_two_closed q denominator qNonzero
    denominatorNonzero rfl geometricSumNonzero]
  simpa [q] using
    accepted_front_coordinate_eq_twoFieldCode base first baseAtLeastTwo

end Mortality.Compiler.ContractionArithmetic
