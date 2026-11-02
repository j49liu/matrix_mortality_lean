import Mortality.Compiler.ContractionArithmetic
import Mortality.Compiler.PrefixGuessModule

/-!
# Operational arithmetic of the accepted fivefold front

This file connects the closed auxiliary-coordinate calculation in
`ContractionArithmetic` to the actual unary prefix, named mutations, and
finite digit scans used by the sixteen-letter fivefold front end.
-/

namespace Mortality.Compiler.FivefoldFrontArithmetic

open Mortality.PeriodicCode
open Mortality.Compiler.UnaryArithmetic
open Mortality.Compiler.PrefixGuessModule
open Mortality.Compiler.ContractionArithmetic

private theorem mul_div_assoc (left numerator denominator : Rat) :
    left * (numerator / denominator) =
      (left * numerator) / denominator := by
  simp [Rat.div_def, Rat.mul_assoc]

private theorem div_div_same_den (numerator denominator target : Rat)
    (denominatorNonzero : denominator ≠ 0) :
    (numerator / denominator) / (target / denominator) =
      numerator / target := by
  simp only [Rat.div_def, Rat.inv_mul_rev, Rat.inv_inv]
  rw [Rat.mul_assoc numerator denominator⁻¹ (denominator * target⁻¹),
    ← Rat.mul_assoc denominator⁻¹ denominator target⁻¹,
    Rat.inv_mul_cancel denominator denominatorNonzero, Rat.one_mul]

def acceptedFrontStart (base first : Nat) : Rat :=
  T base (prefixState base (5 * first + 4) (4 * first + 4))

def acceptedAfterPositiveScans (base first : Nat) : Rat :=
  iteratedMarkerScan base first 1 5 (acceptedFrontStart base first)

def acceptedAfterInverseT (base first : Nat) : Rat :=
  Tinv base (acceptedAfterPositiveScans base first)

def acceptedFrontOutput (base first : Nat) : Rat :=
  negate base
    (scanDigits (base : Rat) (markerScanDigits first 2)
      (acceptedAfterInverseT base first))

theorem auxiliary_Tinv (base : Nat) (value : Rat) :
    (base : Rat) * Tinv base value =
      ((base : Rat) * value) / (1 + (base : Rat) * value) := by
  unfold Tinv
  simp only [Rat.div_def]
  grind

theorem auxiliary_negate (base : Nat) (value : Rat) :
    (base : Rat) * negate base value = -((base : Rat) * value) := by
  unfold negate
  grind

/-- Auxiliary coordinate immediately after the correct prefix and `T`.
Here `q=p^(a+1)` and the input counter is `5a+4`. -/
theorem acceptedFrontStart_auxiliary
    (base first : Nat) (baseAtLeastTwo : 2 ≤ base) :
    let q : Rat := (base : Rat) ^ (first + 1);
    (base : Rat) * acceptedFrontStart base first =
      q / (1 - q - q ^ 5) := by
  dsimp
  let q : Rat := (base : Rat) ^ (first + 1)
  have oldDenominatorNonzero :
      (1 : Rat) - (base : Rat) ^ (5 * first + 5) ≠ 0 :=
    one_sub_pow_ne_zero base (5 * first + 5) baseAtLeastTwo (by omega)
  have newDenominatorNonzero : 1 - q - q ^ 5 ≠ 0 := by
    simpa [q] using
      correct_fivefold_denominator_nonzero base first baseAtLeastTwo
  have firstPower :
      (base : Rat) ^ (first + 1) =
        (base : Rat) ^ first * (base : Rat) := by
    rw [Rat.pow_succ]
  have fifthPower :
      (base : Rat) ^ (5 * first + 5) = q ^ 5 := by
    rw [show 5 * first + 5 =
      (first + 1) + (first + 1) + (first + 1) + (first + 1) +
        (first + 1) by omega]
    unfold q
    repeat' rw [Lean.Grind.Semiring.pow_add]
    grind
  unfold acceptedFrontStart T prefixState
  rw [show 5 * first + 4 - (4 * first + 4) = first by omega,
    show 5 * first + 4 + 1 = 5 * first + 5 by omega, fifthPower]
  simp only [Rat.div_def]
  have oldCancel := Rat.mul_inv_cancel (1 - q ^ 5)
    (by simpa [fifthPower] using oldDenominatorNonzero)
  have newCancel := Rat.mul_inv_cancel (1 - q - q ^ 5)
    newDenominatorNonzero
  change
    (base : Rat) *
        ((base : Rat) ^ first * (1 - q ^ 5)⁻¹ *
          (1 - (base : Rat) *
            ((base : Rat) ^ first * (1 - q ^ 5)⁻¹))⁻¹) =
      q * (1 - q - q ^ 5)⁻¹
  have leadingPower :
      (base : Rat) * (base : Rat) ^ first = q := by
    rw [Rat.mul_comm]
    exact firstPower.symm
  let oldDenominator : Rat := 1 - q ^ 5
  let newDenominator : Rat := 1 - q - q ^ 5
  have oldDenominatorNonzero' : oldDenominator ≠ 0 := by
    simpa [oldDenominator] using
      (show (1 : Rat) - q ^ 5 ≠ 0 by
        simpa [fifthPower] using oldDenominatorNonzero)
  have scaledNumerator :
      (base : Rat) * ((base : Rat) ^ first / oldDenominator) =
        q / oldDenominator := by
    rw [mul_div_assoc, leadingPower]
  have transformedDenominator :
      1 - q / oldDenominator = newDenominator / oldDenominator := by
    simp only [Rat.div_def]
    have oldCancel' := Rat.mul_inv_cancel oldDenominator
      oldDenominatorNonzero'
    unfold oldDenominator newDenominator
    grind
  change
    (base : Rat) *
        (((base : Rat) ^ first / oldDenominator) /
          (1 - (base : Rat) *
            ((base : Rat) ^ first / oldDenominator))) =
      q / newDenominator
  rw [mul_div_assoc, scaledNumerator, transformedDenominator]
  exact div_div_same_den q oldDenominator newDenominator
    oldDenominatorNonzero'

theorem acceptedAfterPositiveScans_auxiliary
    (base first : Nat) (baseAtLeastTwo : 2 ≤ base) :
    let q : Rat := (base : Rat) ^ (first + 1);
    let denominator : Rat := 1 - q - q ^ 5;
    (base : Rat) * acceptedAfterPositiveScans base first =
      iteratedAuxiliaryStep q 1 5 (q / denominator) := by
  dsimp
  rw [acceptedAfterPositiveScans]
  rw [auxiliary_iterated_marker_scan base first 5 1
    (acceptedFrontStart base first) (by omega)]
  rw [acceptedFrontStart_auxiliary base first baseAtLeastTwo]

theorem acceptedFrontOutput_eq
    (base first : Nat) (baseAtLeastTwo : 2 ≤ base) :
    acceptedFrontOutput base first =
      twoFieldCode base first (4 * first + 3) := by
  let q : Rat := (base : Rat) ^ (first + 1)
  let denominator : Rat := 1 - q - q ^ 5
  let afterFive : Rat := iteratedAuxiliaryStep q 1 5 (q / denominator)
  have positiveScans :
      (base : Rat) * acceptedAfterPositiveScans base first = afterFive := by
    simpa [q, denominator, afterFive] using
      acceptedAfterPositiveScans_auxiliary base first baseAtLeastTwo
  have inverseT :
      (base : Rat) * acceptedAfterInverseT base first =
        afterFive / (1 + afterFive) := by
    rw [acceptedAfterInverseT, auxiliary_Tinv, positiveScans]
  have markerScan :
      (base : Rat) *
          scanDigits (base : Rat) (markerScanDigits first 2)
            (acceptedAfterInverseT base first) =
        (afterFive / (1 + afterFive)) / q - 2 := by
    rw [auxiliary_marker_scan base first 2
      (acceptedAfterInverseT base first) (by omega), inverseT]
    simp only [Rat.intCast_ofNat]
    rfl
  have outputAuxiliary :
      (base : Rat) * acceptedFrontOutput base first =
        -((afterFive / (1 + afterFive)) / q - 2) := by
    rw [acceptedFrontOutput, auxiliary_negate, markerScan]
  have closed := accepted_fivefold_front_auxiliary base first baseAtLeastTwo
  change -((afterFive / (1 + afterFive)) / q - 2) =
      (base : Rat) * twoFieldCode base first (4 * first + 3) at closed
  have baseNonzero : (base : Rat) ≠ 0 := by
    simpa using (show base ≠ 0 by omega)
  have productEq :
      (base : Rat) * acceptedFrontOutput base first =
        (base : Rat) * twoFieldCode base first (4 * first + 3) := by
    rw [outputAuxiliary, closed]
  calc
    acceptedFrontOutput base first =
        1 * acceptedFrontOutput base first := by rw [Rat.one_mul]
    _ = ((base : Rat)⁻¹ * (base : Rat)) *
          acceptedFrontOutput base first := by
      rw [Rat.inv_mul_cancel (base : Rat) baseNonzero]
    _ = (base : Rat)⁻¹ *
          ((base : Rat) * acceptedFrontOutput base first) := by
      rw [Rat.mul_assoc]
    _ = (base : Rat)⁻¹ *
          ((base : Rat) * twoFieldCode base first (4 * first + 3)) := by
      rw [productEq]
    _ = ((base : Rat)⁻¹ * (base : Rat)) *
          twoFieldCode base first (4 * first + 3) := by
      rw [Rat.mul_assoc]
    _ = twoFieldCode base first (4 * first + 3) := by
      rw [Rat.inv_mul_cancel (base : Rat) baseNonzero, Rat.one_mul]

end Mortality.Compiler.FivefoldFrontArithmetic
