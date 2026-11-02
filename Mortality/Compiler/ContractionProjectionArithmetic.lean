import Mortality.Compiler.ContractionArithmetic
import Mortality.Compiler.UnaryArithmetic

/-!
# Arithmetic for the two proportional-contraction projections

This file begins the operational proof of the typed projections from
`X_(a,2a+1)` and `X_(a,3a+2)`.  It keeps the scan identities separate from
the later finite-control converse.
-/

namespace Mortality.Compiler.ContractionProjectionArithmetic

open Mortality.PeriodicCode
open Mortality.Compiler.UnaryArithmetic
open Mortality.Compiler.ContractionArithmetic

private theorem div_div_same_den (numerator denominator target : Rat)
    (denominatorNonzero : denominator ≠ 0) :
    (numerator / denominator) / (target / denominator) =
      numerator / target := by
  simp only [Rat.div_def, Rat.inv_mul_rev, Rat.inv_inv]
  rw [Rat.mul_assoc numerator denominator⁻¹ (denominator * target⁻¹),
    ← Rat.mul_assoc denominator⁻¹ denominator target⁻¹,
    Rat.inv_mul_cancel denominator denominatorNonzero, Rat.one_mul]

def zeroDigits (count : Nat) : List Int := List.replicate count 0

theorem digitPolynomial_zeroDigits (base : Rat) (count : Nat) :
    digitPolynomial base (zeroDigits count) = 0 := by
  unfold zeroDigits
  induction count with
  | zero => simp [digitPolynomial]
  | succ count inductionHypothesis =>
      simp [List.replicate_succ, digitPolynomial, inductionHypothesis]
      grind

theorem scan_zeroDigits
    (base count : Nat) (value : Rat) (basePositive : 0 < base) :
    scanDigits (base : Rat) (zeroDigits count) value =
      value / (base : Rat) ^ count := by
  rw [scanDigits_eq]
  · rw [digitPolynomial_zeroDigits]
    rw [show (zeroDigits count).length = count by simp [zeroDigits]]
    grind
  · simpa using (show base ≠ 0 by omega)

theorem auxiliary_scan_zeroDigits
    (base count : Nat) (value : Rat) (basePositive : 0 < base) :
    (base : Rat) * scanDigits (base : Rat) (zeroDigits count) value =
      ((base : Rat) * value) / (base : Rat) ^ count := by
  rw [scan_zeroDigits base count value basePositive]
  simp [Rat.div_def, Rat.mul_assoc]

theorem auxiliary_Tinv (base : Nat) (value : Rat) :
    (base : Rat) * Tinv base value =
      ((base : Rat) * value) / (1 + (base : Rat) * value) := by
  unfold Tinv
  simp [Rat.div_def, Rat.mul_assoc]

theorem auxiliary_Finv (base : Nat) (value : Rat) :
    (base : Rat) * Finv base value =
      ((base : Rat) * value) /
        (1 - 2 * ((base : Rat) * value)) := by
  unfold Finv
  rw [show 1 - 2 * (base : Rat) * value =
      1 - 2 * ((base : Rat) * value) by rw [Rat.mul_assoc]]
  simp [Rat.div_def, Rat.mul_assoc]

def twoProjectionFirstState (base first : Nat) : Rat :=
  scanDigits (base : Rat) (unaryDigits first)
    (twoFieldCode base first (2 * first + 1))

def twoProjectionGuessedState (base first : Nat) : Rat :=
  Tinv base
    (scanDigits (base : Rat) (zeroDigits (first + 1))
      (twoProjectionFirstState base first))

def twoProjectionNegativeState (base first : Nat) : Rat :=
  scanDigits (base : Rat) (markerScanDigits first (-1))
    (twoProjectionGuessedState base first)

def twoProjectionCandidate (base first : Nat) : Rat :=
  Finv base (twoProjectionNegativeState base first)

theorem twoProjectionFirstState_eq
    (base first : Nat) (baseAtLeastTwo : 2 ≤ base) :
    twoProjectionFirstState base first =
      -twoFieldCode base (2 * first + 1) first := by
  exact twoField_half_period base first (2 * first + 1) baseAtLeastTwo

private theorem one_add_square_nonzero (q : Nat) :
    (1 : Rat) + (q : Rat) ^ 2 ≠ 0 := by
  intro zero
  have castZero : ((1 + q ^ 2 : Nat) : Rat) = 0 := by
    simpa [Rat.natCast_add, Rat.natCast_pow] using zero
  have naturalZero : 1 + q ^ 2 = 0 := Rat.natCast_inj.mp castZero
  omega

private theorem one_add_q_add_square_nonzero (q : Nat) :
    (1 : Rat) + q + (q : Rat) ^ 2 ≠ 0 := by
  intro zero
  have castZero : ((1 + q + q ^ 2 : Nat) : Rat) = 0 := by
    simpa [Rat.natCast_add, Rat.natCast_pow] using zero
  have naturalZero : 1 + q + q ^ 2 = 0 := Rat.natCast_inj.mp castZero
  omega

/-- The first half-period scan has the auxiliary coordinate used in the
two-to-one projection calculation. -/
theorem twoProjectionFirstState_auxiliary
    (base first : Nat) (baseAtLeastTwo : 2 ≤ base) :
    let q : Rat := (base : Rat) ^ (first + 1);
    (base : Rat) * twoProjectionFirstState base first =
      -(q ^ 2 / (1 + q + q ^ 2)) := by
  dsimp
  let q : Rat := (base : Rat) ^ (first + 1)
  rw [twoProjectionFirstState_eq base first baseAtLeastTwo,
    twoFieldCode_eq]
  have targetDenominatorNonzero :
      (1 : Rat) - (base : Rat) ^ (3 * first + 3) ≠ 0 :=
    one_sub_pow_ne_zero base (3 * first + 3) baseAtLeastTwo (by omega)
  have geometricNonzero : 1 + q + q ^ 2 ≠ 0 := by
    let qNat : Nat := base ^ (first + 1)
    simpa [q, qNat, Rat.natCast_pow] using
      one_add_q_add_square_nonzero qNat
  have firstPower :
      (base : Rat) ^ (first + 1) =
        (base : Rat) ^ first * (base : Rat) := by
    rw [Rat.pow_succ]
  have squarePower :
      (base : Rat) ^ (2 * first + 2) = q ^ 2 := by
    rw [show 2 * first + 2 = (first + 1) + (first + 1) by omega]
    unfold q
    rw [Lean.Grind.Semiring.pow_add]
    simp [Rat.pow_succ]
  have cubePower :
      (base : Rat) ^ (3 * first + 3) = q ^ 3 := by
    rw [show 3 * first + 3 =
      (first + 1) + (first + 1) + (first + 1) by omega]
    unfold q
    repeat' rw [Lean.Grind.Semiring.pow_add]
    grind
  rw [show 2 * first + 1 + first + 2 = 3 * first + 3 by omega,
    cubePower]
  change
    (base : Rat) *
        -((base : Rat) ^ (2 * first + 1) * (1 - q) / (1 - q ^ 3)) =
      -(q ^ 2 / (1 + q + q ^ 2))
  simp only [Rat.div_def]
  have sourceCancel := Rat.mul_inv_cancel (1 - q ^ 3)
    (by simpa [cubePower] using targetDenominatorNonzero)
  have geometricCancel := Rat.mul_inv_cancel (1 + q + q ^ 2)
    geometricNonzero
  have leadingPower :
      (base : Rat) * (base : Rat) ^ (2 * first + 1) = q ^ 2 := by
    rw [show 2 * first + 1 = first + (first + 1) by omega,
      Lean.Grind.Semiring.pow_add]
    rw [← Rat.mul_assoc, Rat.mul_comm (base : Rat) ((base : Rat) ^ first),
      ← firstPower]
    grind
  grind

theorem twoProjectionGuessedState_auxiliary
    (base first : Nat) (baseAtLeastTwo : 2 ≤ base) :
    let q : Rat := (base : Rat) ^ (first + 1);
    (base : Rat) * twoProjectionGuessedState base first =
      -q / (1 + q ^ 2) := by
  dsimp
  let q : Rat := (base : Rat) ^ (first + 1)
  have qNonzero : q ≠ 0 := by
    unfold q
    exact pow_ne_zero
      (by simpa using (show base ≠ 0 by omega)) (first + 1)
  have geometricNonzero : 1 + q + q ^ 2 ≠ 0 := by
    let qNat : Nat := base ^ (first + 1)
    simpa [q, qNat, Rat.natCast_pow] using
      one_add_q_add_square_nonzero qNat
  have squareNonzero : 1 + q ^ 2 ≠ 0 := by
    let qNat : Nat := base ^ (first + 1)
    simpa [q, qNat, Rat.natCast_pow] using one_add_square_nonzero qNat
  unfold twoProjectionGuessedState
  rw [auxiliary_Tinv]
  rw [auxiliary_scan_zeroDigits base (first + 1)
    (twoProjectionFirstState base first) (by omega)]
  rw [twoProjectionFirstState_auxiliary base first baseAtLeastTwo]
  change
    (-(q ^ 2 / (1 + q + q ^ 2)) / q) /
        (1 + -(q ^ 2 / (1 + q + q ^ 2)) / q) =
      -q / (1 + q ^ 2)
  simp only [Rat.div_def]
  have qCancel := Rat.mul_inv_cancel q qNonzero
  have geometricCancel := Rat.mul_inv_cancel (1 + q + q ^ 2)
    geometricNonzero
  have squareCancel := Rat.mul_inv_cancel (1 + q ^ 2) squareNonzero
  grind

theorem twoProjectionNegativeState_auxiliary
    (base first : Nat) (baseAtLeastTwo : 2 ≤ base) :
    let q : Rat := (base : Rat) ^ (first + 1);
    (base : Rat) * twoProjectionNegativeState base first =
      q ^ 2 / (1 + q ^ 2) := by
  dsimp
  let q : Rat := (base : Rat) ^ (first + 1)
  unfold twoProjectionNegativeState
  rw [auxiliary_negative_scan base first
    (twoProjectionGuessedState base first) (by omega)]
  rw [twoProjectionGuessedState_auxiliary base first baseAtLeastTwo]
  change (-q / (1 + q ^ 2)) / q + 1 = q ^ 2 / (1 + q ^ 2)
  have qNonzero : q ≠ 0 := by
    unfold q
    exact pow_ne_zero
      (by simpa using (show base ≠ 0 by omega)) (first + 1)
  have squareNonzero : 1 + q ^ 2 ≠ 0 := by
    let qNat : Nat := base ^ (first + 1)
    simpa [q, qNat, Rat.natCast_pow] using one_add_square_nonzero qNat
  simp only [Rat.div_def]
  have qCancel := Rat.mul_inv_cancel q qNonzero
  have squareCancel := Rat.mul_inv_cancel (1 + q ^ 2) squareNonzero
  grind

theorem twoProjectionCandidate_eq
    (base first : Nat) (baseAtLeastTwo : 2 ≤ base) :
    twoProjectionCandidate base first = unaryCode base (2 * first + 1) := by
  let q : Rat := (base : Rat) ^ (first + 1)
  have candidateAuxiliary :
      (base : Rat) * twoProjectionCandidate base first =
        q ^ 2 / (1 - q ^ 2) := by
    unfold twoProjectionCandidate
    rw [auxiliary_Finv]
    rw [twoProjectionNegativeState_auxiliary base first baseAtLeastTwo]
    have plusNonzero : 1 + q ^ 2 ≠ 0 := by
      let qNat : Nat := base ^ (first + 1)
      simpa [q, qNat, Rat.natCast_pow] using one_add_square_nonzero qNat
    have minusNonzero : 1 - q ^ 2 ≠ 0 := by
      have target := one_sub_pow_ne_zero base (2 * first + 2)
        baseAtLeastTwo (by omega)
      have squarePower :
          (base : Rat) ^ (2 * first + 2) = q ^ 2 := by
        rw [show 2 * first + 2 = (first + 1) + (first + 1) by omega]
        unfold q
        rw [Lean.Grind.Semiring.pow_add]
        simp [Rat.pow_succ]
      simpa [squarePower] using target
    simp only [Rat.div_def]
    have plusCancel := Rat.mul_inv_cancel (1 + q ^ 2) plusNonzero
    have minusCancel := Rat.mul_inv_cancel (1 - q ^ 2) minusNonzero
    grind
  rw [unaryCode_eq]
  have squarePower :
      (base : Rat) ^ (2 * first + 2) = q ^ 2 := by
    rw [show 2 * first + 2 = (first + 1) + (first + 1) by omega]
    unfold q
    rw [Lean.Grind.Semiring.pow_add]
    simp [Rat.pow_succ]
  have firstPower :
      (base : Rat) ^ (first + 1) =
        (base : Rat) ^ first * (base : Rat) := by
    rw [Rat.pow_succ]
  have leadingPower :
      (base : Rat) * (base : Rat) ^ (2 * first + 1) = q ^ 2 := by
    rw [show 2 * first + 1 = first + (first + 1) by omega,
      Lean.Grind.Semiring.pow_add]
    rw [← Rat.mul_assoc, Rat.mul_comm (base : Rat) ((base : Rat) ^ first),
      ← firstPower]
    grind
  rw [show 2 * first + 1 + 1 = 2 * first + 2 by omega, squarePower]
  have baseNonzero : (base : Rat) ≠ 0 := by
    simpa using (show base ≠ 0 by omega)
  have productEq :
      (base : Rat) * twoProjectionCandidate base first =
        (base : Rat) *
          ((base : Rat) ^ (2 * first + 1) / (1 - q ^ 2)) := by
    rw [candidateAuxiliary]
    simp only [Rat.div_def]
    rw [← Rat.mul_assoc, leadingPower]
  calc
    twoProjectionCandidate base first =
        ((base : Rat)⁻¹ * (base : Rat)) *
          twoProjectionCandidate base first := by
      rw [Rat.inv_mul_cancel (base : Rat) baseNonzero, Rat.one_mul]
    _ = (base : Rat)⁻¹ *
          ((base : Rat) * twoProjectionCandidate base first) := by
      rw [Rat.mul_assoc]
    _ = (base : Rat)⁻¹ *
          ((base : Rat) *
            ((base : Rat) ^ (2 * first + 1) / (1 - q ^ 2))) := by
      rw [productEq]
    _ = ((base : Rat)⁻¹ * (base : Rat)) *
          ((base : Rat) ^ (2 * first + 1) / (1 - q ^ 2)) := by
      rw [Rat.mul_assoc]
    _ = (base : Rat) ^ (2 * first + 1) / (1 - q ^ 2) := by
      rw [Rat.inv_mul_cancel (base : Rat) baseNonzero, Rat.one_mul]

def twoProjectionValidatedOutput (base first : Nat) : Rat :=
  scanDigits (base : Rat) (unaryDigits (2 * first + 1))
    (scanDigits (base : Rat) (unaryDigits (2 * first + 1))
      (twoProjectionCandidate base first))

theorem twoProjectionValidatedOutput_eq
    (base first : Nat) (baseAtLeastTwo : 2 ≤ base) :
    twoProjectionValidatedOutput base first =
      unaryCode base (2 * first + 1) := by
  unfold twoProjectionValidatedOutput
  rw [twoProjectionCandidate_eq base first baseAtLeastTwo,
    scanDigits_unaryCode base (2 * first + 1) baseAtLeastTwo,
    scanDigits_unaryCode base (2 * first + 1) baseAtLeastTwo]

def twoProjectionPrefixState (base first guess : Nat) : Rat :=
  scanDigits (base : Rat) (zeroDigits guess)
    (twoProjectionFirstState base first)

def twoProjectionGeneralGuessState (base first guess : Nat) : Rat :=
  Tinv base (twoProjectionPrefixState base first guess)

def twoProjectionGeneralNegativeState
    (base first guess : Nat) : Rat :=
  let remaining := 2 * (first + 1) - guess
  scanDigits (base : Rat) (markerScanDigits (remaining - 1) (-1))
    (twoProjectionGeneralGuessState base first guess)

def twoProjectionGeneralCandidate (base first guess : Nat) : Rat :=
  Finv base (twoProjectionGeneralNegativeState base first guess)

private theorem two_projection_power_data
    (base first guess : Nat) (baseAtLeastTwo : 2 ≤ base)
    (guessPositive : 0 < guess) (guessBelow : guess < 2 * (first + 1)) :
    let Q := first + 1
    let h := 2 * Q - guess
    let q : Rat := (base : Rat) ^ Q
    let R : Rat := (base : Rat) ^ h
    q ^ 2 = (base : Rat) ^ guess * R ∧
      R < q ^ 2 ∧ 0 < h := by
  dsimp
  let Q := first + 1
  let h := 2 * Q - guess
  have hPositive : 0 < h := by dsimp [h, Q]; omega
  have exponentEq : guess + h = 2 * Q := by unfold h; omega
  have splitPower :
      (base : Rat) ^ (2 * Q) =
        (base : Rat) ^ guess * (base : Rat) ^ h := by
    rw [← exponentEq]
    exact Lean.Grind.Semiring.pow_add _ _ _
  have squarePower :
      ((base : Rat) ^ Q) ^ 2 = (base : Rat) ^ (2 * Q) := by
    calc
      ((base : Rat) ^ Q) ^ 2 =
          (base : Rat) ^ Q * (base : Rat) ^ Q := by
        rw [show (2 : Nat) = 1 + 1 by omega,
          Lean.Grind.Semiring.pow_add]
        simp only [Rat.pow_one]
      _ = (base : Rat) ^ (Q + Q) :=
        (Lean.Grind.Semiring.pow_add (base : Rat) Q Q).symm
      _ = (base : Rat) ^ (2 * Q) := by congr 1 <;> omega
  have naturalPowerLt : base ^ h < base ^ (2 * Q) :=
    Nat.pow_lt_pow_right (by omega) (by unfold h Q; omega)
  have rationalPowerLt :
      (base : Rat) ^ h < (base : Rat) ^ (2 * Q) := by
    rw [← Rat.natCast_pow, ← Rat.natCast_pow]
    exact_mod_cast naturalPowerLt
  constructor
  · rw [squarePower, splitPower]
  constructor
  · rw [squarePower]
    exact rationalPowerLt
  · exact hPositive

theorem twoProjectionPrefixState_auxiliary
    (base first guess : Nat) (baseAtLeastTwo : 2 ≤ base)
    (guessPositive : 0 < guess) (guessBelow : guess < 2 * (first + 1)) :
    let Q := first + 1;
    let h := 2 * Q - guess;
    let q : Rat := (base : Rat) ^ Q;
    let R : Rat := (base : Rat) ^ h;
    let denominator : Rat := 1 + q + q ^ 2;
    (base : Rat) * twoProjectionPrefixState base first guess =
      -(R / denominator) := by
  dsimp
  let Q := first + 1
  let h := 2 * Q - guess
  let q : Rat := (base : Rat) ^ Q
  let R : Rat := (base : Rat) ^ h
  let denominator : Rat := 1 + q + q ^ 2
  obtain ⟨squareSplit, _, hPositive⟩ := two_projection_power_data base first
    guess baseAtLeastTwo guessPositive guessBelow
  have baseNonzero : (base : Rat) ≠ 0 := by
    simpa using (show base ≠ 0 by omega)
  have guessPowerNonzero := pow_ne_zero baseNonzero guess
  have denominatorNonzero : denominator ≠ 0 := by
    let qNat : Nat := base ^ Q
    simpa [denominator, q, qNat, Rat.natCast_pow] using
      one_add_q_add_square_nonzero qNat
  unfold twoProjectionPrefixState
  rw [auxiliary_scan_zeroDigits base guess
    (twoProjectionFirstState base first) (by omega)]
  rw [twoProjectionFirstState_auxiliary base first baseAtLeastTwo]
  change (-(q ^ 2 / denominator)) / (base : Rat) ^ guess =
      -(R / denominator)
  simp only [Rat.div_def]
  have guessCancel := Rat.mul_inv_cancel ((base : Rat) ^ guess)
    guessPowerNonzero
  have denominatorCancel := Rat.mul_inv_cancel denominator
    denominatorNonzero
  grind

theorem twoProjectionGeneralGuessState_auxiliary
    (base first guess : Nat) (baseAtLeastTwo : 2 ≤ base)
    (guessPositive : 0 < guess) (guessBelow : guess < 2 * (first + 1)) :
    let Q := first + 1;
    let h := 2 * Q - guess;
    let q : Rat := (base : Rat) ^ Q;
    let R : Rat := (base : Rat) ^ h;
    let denominator : Rat := 1 + q + q ^ 2;
    (base : Rat) * twoProjectionGeneralGuessState base first guess =
      -(R / (denominator - R)) := by
  dsimp
  let Q := first + 1
  let h := 2 * Q - guess
  let q : Rat := (base : Rat) ^ Q
  let R : Rat := (base : Rat) ^ h
  let denominator : Rat := 1 + q + q ^ 2
  obtain ⟨_, RBelowSquare, _⟩ := two_projection_power_data base first guess
    baseAtLeastTwo guessPositive guessBelow
  have denominatorNonzero : denominator ≠ 0 := by
    let qNat : Nat := base ^ Q
    simpa [denominator, q, qNat, Rat.natCast_pow] using
      one_add_q_add_square_nonzero qNat
  have squareDifferencePositive : 0 < q ^ 2 - R :=
    (Rat.lt_iff_sub_pos R (q ^ 2)).mp RBelowSquare
  have qNonnegative : 0 ≤ q := by
    unfold q
    rw [← Rat.natCast_pow]
    exact_mod_cast (Nat.zero_le (base ^ Q))
  have differencePositive : 0 < denominator - R := by
    unfold denominator
    grind
  have differenceNonzero : denominator - R ≠ 0 := by grind
  unfold twoProjectionGeneralGuessState
  rw [auxiliary_Tinv]
  rw [twoProjectionPrefixState_auxiliary base first guess baseAtLeastTwo
    guessPositive guessBelow]
  have onePlus : 1 + -(R / denominator) =
      (denominator - R) / denominator := by
    simp only [Rat.div_def]
    have denominatorCancel := Rat.mul_inv_cancel denominator
      denominatorNonzero
    grind
  rw [onePlus]
  have core := div_div_same_den R denominator (denominator - R)
    denominatorNonzero
  calc
    -(R / denominator) / ((denominator - R) / denominator) =
        -((R / denominator) /
          ((denominator - R) / denominator)) := by
      simp only [Rat.div_def]
      grind
    _ = -(R / (denominator - R)) := by rw [core]

theorem twoProjectionGeneralNegativeState_auxiliary
    (base first guess : Nat) (baseAtLeastTwo : 2 ≤ base)
    (guessPositive : 0 < guess) (guessBelow : guess < 2 * (first + 1)) :
    let Q := first + 1;
    let h := 2 * Q - guess;
    let q : Rat := (base : Rat) ^ Q;
    let R : Rat := (base : Rat) ^ h;
    let polynomial : Rat := q + q ^ 2 - R;
    (base : Rat) * twoProjectionGeneralNegativeState base first guess =
      polynomial / (1 + polynomial) := by
  dsimp
  let Q := first + 1
  let h := 2 * Q - guess
  let q : Rat := (base : Rat) ^ Q
  let R : Rat := (base : Rat) ^ h
  let denominator : Rat := 1 + q + q ^ 2
  let polynomial : Rat := q + q ^ 2 - R
  obtain ⟨_, RBelowSquare, hPositive⟩ := two_projection_power_data base first
    guess baseAtLeastTwo guessPositive guessBelow
  have RNonzero : R ≠ 0 := by
    unfold R
    exact pow_ne_zero (by simpa using (show base ≠ 0 by omega)) h
  have squareDifferencePositive : 0 < q ^ 2 - R :=
    (Rat.lt_iff_sub_pos R (q ^ 2)).mp RBelowSquare
  have qNonnegative : 0 ≤ q := by
    unfold q
    rw [← Rat.natCast_pow]
    exact_mod_cast (Nat.zero_le (base ^ Q))
  have differencePositive : 0 < denominator - R := by
    unfold denominator
    grind
  have differenceNonzero : denominator - R ≠ 0 := by grind
  unfold twoProjectionGeneralNegativeState
  dsimp only
  rw [show 2 * (first + 1) - guess = h by rfl]
  rw [auxiliary_negative_scan base (h - 1)
    (twoProjectionGeneralGuessState base first guess) (by omega)]
  rw [show h - 1 + 1 = h by omega]
  rw [twoProjectionGeneralGuessState_auxiliary base first guess
    baseAtLeastTwo guessPositive guessBelow]
  change (-(R / (denominator - R))) / R + 1 =
      polynomial / (1 + polynomial)
  have denominatorEq : denominator - R = 1 + polynomial := by
    unfold denominator polynomial
    grind
  simp only [Rat.div_def]
  have RCancel := Rat.mul_inv_cancel R RNonzero
  have differenceCancel := Rat.mul_inv_cancel (denominator - R)
    differenceNonzero
  rw [denominatorEq] at differenceCancel ⊢
  unfold polynomial denominator at *
  grind

theorem twoProjectionGeneralCandidate_auxiliary
    (base first guess : Nat) (baseAtLeastTwo : 2 ≤ base)
    (guessPositive : 0 < guess) (guessBelow : guess < 2 * (first + 1)) :
    let Q := first + 1;
    let h := 2 * Q - guess;
    let q : Rat := (base : Rat) ^ Q;
    let R : Rat := (base : Rat) ^ h;
    let polynomial : Rat := q + q ^ 2 - R;
    (base : Rat) * twoProjectionGeneralCandidate base first guess =
      polynomial / (1 - polynomial) := by
  dsimp
  let Q := first + 1
  let h := 2 * Q - guess
  let q : Rat := (base : Rat) ^ Q
  let R : Rat := (base : Rat) ^ h
  let polynomial : Rat := q + q ^ 2 - R
  obtain ⟨_, RBelowSquare, _⟩ := two_projection_power_data base first guess
    baseAtLeastTwo guessPositive guessBelow
  have qGreaterOne : 1 < q := by
    have naturalGreater : 1 < base ^ Q :=
      Nat.one_lt_pow (by unfold Q; omega) (by omega)
    unfold q
    rw [← Rat.natCast_pow]
    exact_mod_cast naturalGreater
  have polynomialGreaterOne : 1 < polynomial := by
    unfold polynomial
    grind
  have targetNonzero : 1 - polynomial ≠ 0 := by grind
  unfold twoProjectionGeneralCandidate
  rw [auxiliary_Finv]
  rw [twoProjectionGeneralNegativeState_auxiliary base first guess
    baseAtLeastTwo guessPositive guessBelow]
  change (polynomial / (1 + polynomial)) /
      (1 - 2 * (polynomial / (1 + polynomial))) =
    polynomial / (1 - polynomial)
  have plusNonzero : 1 + polynomial ≠ 0 := by grind
  simp only [Rat.div_def]
  have plusCancel := Rat.mul_inv_cancel (1 + polynomial) plusNonzero
  have targetCancel := Rat.mul_inv_cancel (1 - polynomial) targetNonzero
  grind

def threeProjectionFirstState (base first : Nat) : Rat :=
  scanDigits (base : Rat) (unaryDigits first)
    (twoFieldCode base first (3 * first + 2))

def threeProjectionFirstGuess (base first : Nat) : Rat :=
  Tinv base
    (scanDigits (base : Rat) (zeroDigits (first + 1))
      (threeProjectionFirstState base first))

def threeProjectionSecondGuess (base first : Nat) : Rat :=
  Tinv base
    (scanDigits (base : Rat) (zeroDigits (first + 1))
      (threeProjectionFirstGuess base first))

def threeProjectionNegativeState (base first : Nat) : Rat :=
  scanDigits (base : Rat) (markerScanDigits first (-1))
    (threeProjectionSecondGuess base first)

def threeProjectionCandidate (base first : Nat) : Rat :=
  Finv base (threeProjectionNegativeState base first)

def threeProjectionValidatedOutput (base first : Nat) : Rat :=
  scanDigits (base : Rat) (unaryDigits (3 * first + 2))
    (scanDigits (base : Rat) (unaryDigits (3 * first + 2))
      (scanDigits (base : Rat) (unaryDigits (3 * first + 2))
        (threeProjectionCandidate base first)))

theorem threeProjectionFirstState_eq
    (base first : Nat) (baseAtLeastTwo : 2 ≤ base) :
    threeProjectionFirstState base first =
      -twoFieldCode base (3 * first + 2) first := by
  exact twoField_half_period base first (3 * first + 2) baseAtLeastTwo

private theorem one_add_cube_nonzero (q : Nat) :
    (1 : Rat) + (q : Rat) ^ 3 ≠ 0 := by
  intro zero
  have castZero : ((1 + q ^ 3 : Nat) : Rat) = 0 := by
    simpa [Rat.natCast_add, Rat.natCast_pow] using zero
  have naturalZero : 1 + q ^ 3 = 0 := Rat.natCast_inj.mp castZero
  omega

private theorem one_add_q_add_cube_nonzero (q : Nat) :
    (1 : Rat) + q + (q : Rat) ^ 3 ≠ 0 := by
  intro zero
  have castZero : ((1 + q + q ^ 3 : Nat) : Rat) = 0 := by
    simpa [Rat.natCast_add, Rat.natCast_pow] using zero
  have naturalZero : 1 + q + q ^ 3 = 0 := Rat.natCast_inj.mp castZero
  omega

private theorem geometric_four_nonzero (q : Nat) :
    (1 : Rat) + q + (q : Rat) ^ 2 + (q : Rat) ^ 3 ≠ 0 := by
  intro zero
  have castZero : ((1 + q + q ^ 2 + q ^ 3 : Nat) : Rat) = 0 := by
    simpa [Rat.natCast_add, Rat.natCast_pow] using zero
  have naturalZero : 1 + q + q ^ 2 + q ^ 3 = 0 :=
    Rat.natCast_inj.mp castZero
  omega

theorem threeProjectionFirstState_auxiliary
    (base first : Nat) (baseAtLeastTwo : 2 ≤ base) :
    let q : Rat := (base : Rat) ^ (first + 1);
    (base : Rat) * threeProjectionFirstState base first =
      -(q ^ 3 / (1 + q + q ^ 2 + q ^ 3)) := by
  dsimp
  let q : Rat := (base : Rat) ^ (first + 1)
  rw [threeProjectionFirstState_eq base first baseAtLeastTwo,
    twoFieldCode_eq]
  have targetDenominatorNonzero :
      (1 : Rat) - (base : Rat) ^ (4 * first + 4) ≠ 0 :=
    one_sub_pow_ne_zero base (4 * first + 4) baseAtLeastTwo (by omega)
  have geometricNonzero : 1 + q + q ^ 2 + q ^ 3 ≠ 0 := by
    let qNat : Nat := base ^ (first + 1)
    simpa [q, qNat, Rat.natCast_pow] using geometric_four_nonzero qNat
  have firstPower :
      (base : Rat) ^ (first + 1) =
        (base : Rat) ^ first * (base : Rat) := by
    rw [Rat.pow_succ]
  have fourthPower :
      (base : Rat) ^ (4 * first + 4) = q ^ 4 := by
    rw [show 4 * first + 4 =
      (first + 1) + (first + 1) + (first + 1) + (first + 1) by omega]
    unfold q
    repeat' rw [Lean.Grind.Semiring.pow_add]
    grind
  rw [show 3 * first + 2 + first + 2 = 4 * first + 4 by omega,
    fourthPower]
  change
    (base : Rat) *
        -((base : Rat) ^ (3 * first + 2) * (1 - q) / (1 - q ^ 4)) =
      -(q ^ 3 / (1 + q + q ^ 2 + q ^ 3))
  simp only [Rat.div_def]
  have sourceCancel := Rat.mul_inv_cancel (1 - q ^ 4)
    (by simpa [fourthPower] using targetDenominatorNonzero)
  have geometricCancel := Rat.mul_inv_cancel
    (1 + q + q ^ 2 + q ^ 3) geometricNonzero
  have leadingPower :
      (base : Rat) * (base : Rat) ^ (3 * first + 2) = q ^ 3 := by
    have cubeExponent : 3 * first + 3 =
        (first + 1) + (first + 1) + (first + 1) := by omega
    have cubePower : (base : Rat) ^ (3 * first + 3) = q ^ 3 := by
      rw [cubeExponent]
      unfold q
      repeat' rw [Lean.Grind.Semiring.pow_add]
      grind
    rw [show 3 * first + 3 = 3 * first + 2 + 1 by omega,
      Rat.pow_succ] at cubePower
    rw [Rat.mul_comm]
    exact cubePower
  grind

theorem threeProjectionFirstGuess_auxiliary
    (base first : Nat) (baseAtLeastTwo : 2 ≤ base) :
    let q : Rat := (base : Rat) ^ (first + 1);
    (base : Rat) * threeProjectionFirstGuess base first =
      -(q ^ 2 / (1 + q + q ^ 3)) := by
  dsimp
  let q : Rat := (base : Rat) ^ (first + 1)
  have qNonzero : q ≠ 0 := by
    unfold q
    exact pow_ne_zero
      (by simpa using (show base ≠ 0 by omega)) (first + 1)
  have sourceNonzero : 1 + q + q ^ 2 + q ^ 3 ≠ 0 := by
    let qNat : Nat := base ^ (first + 1)
    simpa [q, qNat, Rat.natCast_pow] using geometric_four_nonzero qNat
  have targetNonzero : 1 + q + q ^ 3 ≠ 0 := by
    let qNat : Nat := base ^ (first + 1)
    simpa [q, qNat, Rat.natCast_pow] using
      one_add_q_add_cube_nonzero qNat
  unfold threeProjectionFirstGuess
  rw [auxiliary_Tinv]
  rw [auxiliary_scan_zeroDigits base (first + 1)
    (threeProjectionFirstState base first) (by omega)]
  rw [threeProjectionFirstState_auxiliary base first baseAtLeastTwo]
  change
    (-(q ^ 3 / (1 + q + q ^ 2 + q ^ 3)) / q) /
        (1 + -(q ^ 3 / (1 + q + q ^ 2 + q ^ 3)) / q) =
      -(q ^ 2 / (1 + q + q ^ 3))
  simp only [Rat.div_def]
  have qCancel := Rat.mul_inv_cancel q qNonzero
  have sourceCancel := Rat.mul_inv_cancel (1 + q + q ^ 2 + q ^ 3)
    sourceNonzero
  have targetCancel := Rat.mul_inv_cancel (1 + q + q ^ 3)
    targetNonzero
  let source : Rat := 1 + q + q ^ 2 + q ^ 3
  let target : Rat := 1 + q + q ^ 3
  have divided : -(q ^ 3 / source) / q = -(q ^ 2 / source) := by
    simp only [Rat.div_def]
    unfold source
    grind
  have denominatorEq : 1 + -(q ^ 2 / source) = target / source := by
    simp only [Rat.div_def]
    unfold source target
    grind
  change (-(q ^ 3 / source) / q) /
      (1 + -(q ^ 3 / source) / q) = -(q ^ 2 / target)
  rw [divided, denominatorEq]
  have core := div_div_same_den (q ^ 2) source target
    (by simpa [source] using sourceNonzero)
  calc
    -(q ^ 2 / source) / (target / source) =
        -((q ^ 2 / source) / (target / source)) := by
      simp only [Rat.div_def]
      grind
    _ = -(q ^ 2 / target) := by rw [core]

theorem threeProjectionSecondGuess_auxiliary
    (base first : Nat) (baseAtLeastTwo : 2 ≤ base) :
    let q : Rat := (base : Rat) ^ (first + 1);
    (base : Rat) * threeProjectionSecondGuess base first =
      -q / (1 + q ^ 3) := by
  dsimp
  let q : Rat := (base : Rat) ^ (first + 1)
  have qNonzero : q ≠ 0 := by
    unfold q
    exact pow_ne_zero
      (by simpa using (show base ≠ 0 by omega)) (first + 1)
  have sourceNonzero : 1 + q + q ^ 3 ≠ 0 := by
    let qNat : Nat := base ^ (first + 1)
    simpa [q, qNat, Rat.natCast_pow] using
      one_add_q_add_cube_nonzero qNat
  have targetNonzero : 1 + q ^ 3 ≠ 0 := by
    let qNat : Nat := base ^ (first + 1)
    simpa [q, qNat, Rat.natCast_pow] using one_add_cube_nonzero qNat
  unfold threeProjectionSecondGuess
  rw [auxiliary_Tinv]
  rw [auxiliary_scan_zeroDigits base (first + 1)
    (threeProjectionFirstGuess base first) (by omega)]
  rw [threeProjectionFirstGuess_auxiliary base first baseAtLeastTwo]
  change
    (-(q ^ 2 / (1 + q + q ^ 3)) / q) /
        (1 + -(q ^ 2 / (1 + q + q ^ 3)) / q) =
      -q / (1 + q ^ 3)
  have qCancel := Rat.mul_inv_cancel q qNonzero
  have sourceCancel := Rat.mul_inv_cancel (1 + q + q ^ 3) sourceNonzero
  have targetCancel := Rat.mul_inv_cancel (1 + q ^ 3) targetNonzero
  have divided :
      -(q ^ 2 / (1 + q + q ^ 3)) / q =
        -(q / (1 + q + q ^ 3)) := by
    simp only [Rat.div_def]
    grind
  have denominatorEq :
      1 + -(q / (1 + q + q ^ 3)) =
        (1 + q ^ 3) / (1 + q + q ^ 3) := by
    simp only [Rat.div_def]
    grind
  rw [divided, denominatorEq]
  have core := div_div_same_den q (1 + q + q ^ 3) (1 + q ^ 3)
    sourceNonzero
  calc
    -(q / (1 + q + q ^ 3)) /
        ((1 + q ^ 3) / (1 + q + q ^ 3)) =
        -((q / (1 + q + q ^ 3)) /
          ((1 + q ^ 3) / (1 + q + q ^ 3))) := by
      simp only [Rat.div_def]
      grind
    _ = -(q / (1 + q ^ 3)) := by rw [core]
    _ = -q / (1 + q ^ 3) := by
      simp only [Rat.div_def]
      grind

theorem threeProjectionNegativeState_auxiliary
    (base first : Nat) (baseAtLeastTwo : 2 ≤ base) :
    let q : Rat := (base : Rat) ^ (first + 1);
    (base : Rat) * threeProjectionNegativeState base first =
      q ^ 3 / (1 + q ^ 3) := by
  dsimp
  let q : Rat := (base : Rat) ^ (first + 1)
  unfold threeProjectionNegativeState
  rw [auxiliary_negative_scan base first
    (threeProjectionSecondGuess base first) (by omega)]
  rw [threeProjectionSecondGuess_auxiliary base first baseAtLeastTwo]
  change (-q / (1 + q ^ 3)) / q + 1 = q ^ 3 / (1 + q ^ 3)
  have qNonzero : q ≠ 0 := by
    unfold q
    exact pow_ne_zero
      (by simpa using (show base ≠ 0 by omega)) (first + 1)
  have targetNonzero : 1 + q ^ 3 ≠ 0 := by
    let qNat : Nat := base ^ (first + 1)
    simpa [q, qNat, Rat.natCast_pow] using one_add_cube_nonzero qNat
  simp only [Rat.div_def]
  have qCancel := Rat.mul_inv_cancel q qNonzero
  have targetCancel := Rat.mul_inv_cancel (1 + q ^ 3) targetNonzero
  grind

theorem threeProjectionCandidate_eq
    (base first : Nat) (baseAtLeastTwo : 2 ≤ base) :
    threeProjectionCandidate base first = unaryCode base (3 * first + 2) := by
  let q : Rat := (base : Rat) ^ (first + 1)
  have candidateAuxiliary :
      (base : Rat) * threeProjectionCandidate base first =
        q ^ 3 / (1 - q ^ 3) := by
    unfold threeProjectionCandidate
    rw [auxiliary_Finv]
    rw [threeProjectionNegativeState_auxiliary base first baseAtLeastTwo]
    have plusNonzero : 1 + q ^ 3 ≠ 0 := by
      let qNat : Nat := base ^ (first + 1)
      simpa [q, qNat, Rat.natCast_pow] using one_add_cube_nonzero qNat
    have minusNonzero : 1 - q ^ 3 ≠ 0 := by
      have target := one_sub_pow_ne_zero base (3 * first + 3)
        baseAtLeastTwo (by omega)
      have cubePower :
          (base : Rat) ^ (3 * first + 3) = q ^ 3 := by
        rw [show 3 * first + 3 =
          (first + 1) + (first + 1) + (first + 1) by omega]
        unfold q
        repeat' rw [Lean.Grind.Semiring.pow_add]
        grind
      simpa [cubePower] using target
    simp only [Rat.div_def]
    have plusCancel := Rat.mul_inv_cancel (1 + q ^ 3) plusNonzero
    have minusCancel := Rat.mul_inv_cancel (1 - q ^ 3) minusNonzero
    grind
  rw [unaryCode_eq]
  have cubePower :
      (base : Rat) ^ (3 * first + 3) = q ^ 3 := by
    rw [show 3 * first + 3 =
      (first + 1) + (first + 1) + (first + 1) by omega]
    unfold q
    repeat' rw [Lean.Grind.Semiring.pow_add]
    grind
  rw [show 3 * first + 2 + 1 = 3 * first + 3 by omega, cubePower]
  have leadingPower :
      (base : Rat) * (base : Rat) ^ (3 * first + 2) = q ^ 3 := by
    have powerSucc :
        (base : Rat) ^ (3 * first + 3) =
          (base : Rat) ^ (3 * first + 2) * (base : Rat) := by
      rw [show 3 * first + 3 = 3 * first + 2 + 1 by omega, Rat.pow_succ]
    rw [cubePower] at powerSucc
    rw [Rat.mul_comm]
    exact powerSucc.symm
  have baseNonzero : (base : Rat) ≠ 0 := by
    simpa using (show base ≠ 0 by omega)
  have productEq :
      (base : Rat) * threeProjectionCandidate base first =
        (base : Rat) *
          ((base : Rat) ^ (3 * first + 2) / (1 - q ^ 3)) := by
    rw [candidateAuxiliary]
    simp only [Rat.div_def]
    rw [← Rat.mul_assoc, leadingPower]
  calc
    threeProjectionCandidate base first =
        ((base : Rat)⁻¹ * (base : Rat)) *
          threeProjectionCandidate base first := by
      rw [Rat.inv_mul_cancel (base : Rat) baseNonzero, Rat.one_mul]
    _ = (base : Rat)⁻¹ *
          ((base : Rat) * threeProjectionCandidate base first) := by
      rw [Rat.mul_assoc]
    _ = (base : Rat)⁻¹ *
          ((base : Rat) *
            ((base : Rat) ^ (3 * first + 2) / (1 - q ^ 3))) := by
      rw [productEq]
    _ = ((base : Rat)⁻¹ * (base : Rat)) *
          ((base : Rat) ^ (3 * first + 2) / (1 - q ^ 3)) := by
      rw [Rat.mul_assoc]
    _ = (base : Rat) ^ (3 * first + 2) / (1 - q ^ 3) := by
      rw [Rat.inv_mul_cancel (base : Rat) baseNonzero, Rat.one_mul]

theorem threeProjectionValidatedOutput_eq
    (base first : Nat) (baseAtLeastTwo : 2 ≤ base) :
    threeProjectionValidatedOutput base first =
      unaryCode base (3 * first + 2) := by
  unfold threeProjectionValidatedOutput
  rw [threeProjectionCandidate_eq base first baseAtLeastTwo,
    scanDigits_unaryCode base (3 * first + 2) baseAtLeastTwo,
    scanDigits_unaryCode base (3 * first + 2) baseAtLeastTwo,
    scanDigits_unaryCode base (3 * first + 2) baseAtLeastTwo]

/-! ## Arbitrary guesses in the three-to-one projection -/

def threeProjectionFirstPrefixState
    (base first firstGuess : Nat) : Rat :=
  scanDigits (base : Rat) (zeroDigits firstGuess)
    (threeProjectionFirstState base first)

def threeProjectionGeneralFirstGuessState
    (base first firstGuess : Nat) : Rat :=
  Tinv base (threeProjectionFirstPrefixState base first firstGuess)

def threeProjectionSecondPrefixState
    (base first firstGuess secondGuess : Nat) : Rat :=
  scanDigits (base : Rat) (zeroDigits secondGuess)
    (threeProjectionGeneralFirstGuessState base first firstGuess)

def threeProjectionGeneralSecondGuessState
    (base first firstGuess secondGuess : Nat) : Rat :=
  Tinv base
    (threeProjectionSecondPrefixState base first firstGuess secondGuess)

def threeProjectionGeneralNegativeState
    (base first firstGuess secondGuess : Nat) : Rat :=
  let Q := first + 1
  let r := 3 * Q - firstGuess
  let s := r - secondGuess
  scanDigits (base : Rat) (markerScanDigits (s - 1) (-1))
    (threeProjectionGeneralSecondGuessState
      base first firstGuess secondGuess)

def threeProjectionGeneralCandidate
    (base first firstGuess secondGuess : Nat) : Rat :=
  Finv base
    (threeProjectionGeneralNegativeState base first firstGuess secondGuess)

private theorem three_projection_power_data
    (base first firstGuess secondGuess : Nat)
    (baseAtLeastTwo : 2 ≤ base)
    (firstGuessPositive : 0 < firstGuess)
    (firstGuessBelow : firstGuess < 3 * (first + 1))
    (secondGuessPositive : 0 < secondGuess)
    (secondGuessBelow : secondGuess <
      3 * (first + 1) - firstGuess) :
    let Q := first + 1
    let r := 3 * Q - firstGuess
    let s := r - secondGuess
    let q : Rat := (base : Rat) ^ Q
    let R : Rat := (base : Rat) ^ r
    let S : Rat := (base : Rat) ^ s
    q ^ 3 = (base : Rat) ^ firstGuess * R ∧
      R = (base : Rat) ^ secondGuess * S ∧
      S < R ∧ R + S < q ^ 3 ∧ 0 < s := by
  dsimp
  let Q := first + 1
  let r := 3 * Q - firstGuess
  let s := r - secondGuess
  have rPositive : 0 < r := by unfold r Q; omega
  have rBelow : r < 3 * Q := by unfold r; omega
  have sPositive : 0 < s := by unfold s r Q; omega
  have sBelowR : s < r := by unfold s; omega
  have firstExponent : firstGuess + r = 3 * Q := by unfold r; omega
  have secondExponent : secondGuess + s = r := by unfold s; omega
  have cubePower : ((base : Rat) ^ Q) ^ 3 =
      (base : Rat) ^ (3 * Q) := by
    rw [show 3 * Q = Q + Q + Q by omega]
    repeat' rw [Lean.Grind.Semiring.pow_add]
    grind
  have firstSplit : (base : Rat) ^ (3 * Q) =
      (base : Rat) ^ firstGuess * (base : Rat) ^ r := by
    rw [← firstExponent]
    exact Lean.Grind.Semiring.pow_add _ _ _
  have secondSplit : (base : Rat) ^ r =
      (base : Rat) ^ secondGuess * (base : Rat) ^ s := by
    rw [← secondExponent]
    exact Lean.Grind.Semiring.pow_add _ _ _
  have naturalSBelowR : base ^ s < base ^ r :=
    Nat.pow_lt_pow_right (by omega) sBelowR
  have naturalRPlusSBelowCube :
      base ^ r + base ^ s < base ^ (3 * Q) := by
    have sumBelowDouble : base ^ r + base ^ s < 2 * base ^ r := by
      omega
    have doubleBelowNext : 2 * base ^ r ≤ base ^ (r + 1) := by
      calc
        2 * base ^ r ≤ base * base ^ r :=
          Nat.mul_le_mul_right (base ^ r) baseAtLeastTwo
        _ = base ^ r * base := Nat.mul_comm _ _
        _ = base ^ (r + 1) := (Nat.pow_succ _ _).symm
    have nextBelowCube : base ^ (r + 1) ≤ base ^ (3 * Q) :=
      Nat.pow_le_pow_right (by omega) (by omega)
    omega
  have rationalSBelowR :
      (base : Rat) ^ s < (base : Rat) ^ r := by
    rw [← Rat.natCast_pow, ← Rat.natCast_pow]
    exact_mod_cast naturalSBelowR
  have rationalSumBelowCube :
      (base : Rat) ^ r + (base : Rat) ^ s <
        ((base : Rat) ^ Q) ^ 3 := by
    rw [cubePower, ← Rat.natCast_pow, ← Rat.natCast_pow,
      ← Rat.natCast_pow, ← Rat.natCast_add]
    exact_mod_cast naturalRPlusSBelowCube
  exact ⟨cubePower.trans firstSplit, secondSplit, rationalSBelowR,
    rationalSumBelowCube, sPositive⟩

theorem threeProjectionFirstPrefixState_auxiliary
    (base first firstGuess secondGuess : Nat)
    (baseAtLeastTwo : 2 ≤ base)
    (firstGuessPositive : 0 < firstGuess)
    (firstGuessBelow : firstGuess < 3 * (first + 1))
    (secondGuessPositive : 0 < secondGuess)
    (secondGuessBelow : secondGuess <
      3 * (first + 1) - firstGuess) :
    let Q := first + 1
    let r := 3 * Q - firstGuess
    let q : Rat := (base : Rat) ^ Q
    let R : Rat := (base : Rat) ^ r
    let denominator : Rat := 1 + q + q ^ 2 + q ^ 3
    (base : Rat) *
        threeProjectionFirstPrefixState base first firstGuess =
      -(R / denominator) := by
  dsimp
  let Q := first + 1
  let r := 3 * Q - firstGuess
  let q : Rat := (base : Rat) ^ Q
  let R : Rat := (base : Rat) ^ r
  let denominator : Rat := 1 + q + q ^ 2 + q ^ 3
  obtain ⟨cubeSplit, _, _, _, _⟩ := three_projection_power_data
    base first firstGuess secondGuess baseAtLeastTwo firstGuessPositive
      firstGuessBelow secondGuessPositive secondGuessBelow
  have baseNonzero : (base : Rat) ≠ 0 := by
    simpa using (show base ≠ 0 by omega)
  have guessPowerNonzero := pow_ne_zero baseNonzero firstGuess
  have denominatorNonzero : denominator ≠ 0 := by
    let qNat : Nat := base ^ Q
    simpa [denominator, q, qNat, Rat.natCast_pow] using
      geometric_four_nonzero qNat
  unfold threeProjectionFirstPrefixState
  rw [auxiliary_scan_zeroDigits base firstGuess
    (threeProjectionFirstState base first) (by omega)]
  rw [threeProjectionFirstState_auxiliary base first baseAtLeastTwo]
  change (-(q ^ 3 / denominator)) / (base : Rat) ^ firstGuess =
    -(R / denominator)
  simp only [Rat.div_def]
  have guessCancel := Rat.mul_inv_cancel ((base : Rat) ^ firstGuess)
    guessPowerNonzero
  have denominatorCancel := Rat.mul_inv_cancel denominator
    denominatorNonzero
  grind

theorem threeProjectionGeneralFirstGuessState_auxiliary
    (base first firstGuess secondGuess : Nat)
    (baseAtLeastTwo : 2 ≤ base)
    (firstGuessPositive : 0 < firstGuess)
    (firstGuessBelow : firstGuess < 3 * (first + 1))
    (secondGuessPositive : 0 < secondGuess)
    (secondGuessBelow : secondGuess <
      3 * (first + 1) - firstGuess) :
    let Q := first + 1
    let r := 3 * Q - firstGuess
    let q : Rat := (base : Rat) ^ Q
    let R : Rat := (base : Rat) ^ r
    let denominator : Rat := 1 + q + q ^ 2 + q ^ 3
    (base : Rat) *
        threeProjectionGeneralFirstGuessState base first firstGuess =
      -(R / (denominator - R)) := by
  dsimp
  let Q := first + 1
  let r := 3 * Q - firstGuess
  let q : Rat := (base : Rat) ^ Q
  let R : Rat := (base : Rat) ^ r
  let denominator : Rat := 1 + q + q ^ 2 + q ^ 3
  obtain ⟨_, _, _, sumBelowCube, _⟩ := three_projection_power_data
    base first firstGuess secondGuess baseAtLeastTwo firstGuessPositive
      firstGuessBelow secondGuessPositive secondGuessBelow
  have RBelowCube : R < q ^ 3 := by
    have SNonnegative : 0 ≤ (base : Rat) ^
        (r - secondGuess) := by
      rw [← Rat.natCast_pow]
      exact_mod_cast (Nat.zero_le (base ^ (r - secondGuess)))
    change R + (base : Rat) ^ (r - secondGuess) < q ^ 3 at sumBelowCube
    grind
  have qNonnegative : 0 ≤ q := by
    unfold q
    rw [← Rat.natCast_pow]
    exact_mod_cast (Nat.zero_le (base ^ Q))
  have qSquareNonnegative : 0 ≤ q ^ 2 := Rat.pow_nonneg qNonnegative
  have qCubeNonnegative : 0 ≤ q ^ 3 := Rat.pow_nonneg qNonnegative
  have denominatorPositive : 0 < denominator := by
    unfold denominator
    grind
  have differencePositive : 0 < denominator - R := by
    unfold denominator
    grind
  have denominatorNonzero : denominator ≠ 0 := by grind
  have differenceNonzero : denominator - R ≠ 0 := by grind
  unfold threeProjectionGeneralFirstGuessState
  rw [auxiliary_Tinv]
  rw [threeProjectionFirstPrefixState_auxiliary base first firstGuess
    secondGuess baseAtLeastTwo firstGuessPositive firstGuessBelow
    secondGuessPositive secondGuessBelow]
  have onePlus : 1 + -(R / denominator) =
      (denominator - R) / denominator := by
    simp only [Rat.div_def]
    have denominatorCancel := Rat.mul_inv_cancel denominator
      denominatorNonzero
    grind
  rw [onePlus]
  have core := div_div_same_den R denominator (denominator - R)
    denominatorNonzero
  calc
    -(R / denominator) / ((denominator - R) / denominator) =
        -((R / denominator) /
          ((denominator - R) / denominator)) := by
      simp only [Rat.div_def]
      grind
    _ = -(R / (denominator - R)) := by rw [core]

theorem threeProjectionSecondPrefixState_auxiliary
    (base first firstGuess secondGuess : Nat)
    (baseAtLeastTwo : 2 ≤ base)
    (firstGuessPositive : 0 < firstGuess)
    (firstGuessBelow : firstGuess < 3 * (first + 1))
    (secondGuessPositive : 0 < secondGuess)
    (secondGuessBelow : secondGuess <
      3 * (first + 1) - firstGuess) :
    let Q := first + 1
    let r := 3 * Q - firstGuess
    let s := r - secondGuess
    let q : Rat := (base : Rat) ^ Q
    let R : Rat := (base : Rat) ^ r
    let S : Rat := (base : Rat) ^ s
    let denominator : Rat := 1 + q + q ^ 2 + q ^ 3
    (base : Rat) * threeProjectionSecondPrefixState
        base first firstGuess secondGuess =
      -(S / (denominator - R)) := by
  dsimp
  let Q := first + 1
  let r := 3 * Q - firstGuess
  let s := r - secondGuess
  let q : Rat := (base : Rat) ^ Q
  let R : Rat := (base : Rat) ^ r
  let S : Rat := (base : Rat) ^ s
  let denominator : Rat := 1 + q + q ^ 2 + q ^ 3
  obtain ⟨_, secondSplit, _, _, _⟩ := three_projection_power_data
    base first firstGuess secondGuess baseAtLeastTwo firstGuessPositive
      firstGuessBelow secondGuessPositive secondGuessBelow
  have baseNonzero : (base : Rat) ≠ 0 := by
    simpa using (show base ≠ 0 by omega)
  have guessPowerNonzero := pow_ne_zero baseNonzero secondGuess
  unfold threeProjectionSecondPrefixState
  rw [auxiliary_scan_zeroDigits base secondGuess
    (threeProjectionGeneralFirstGuessState base first firstGuess) (by omega)]
  rw [threeProjectionGeneralFirstGuessState_auxiliary base first firstGuess
    secondGuess baseAtLeastTwo firstGuessPositive firstGuessBelow
    secondGuessPositive secondGuessBelow]
  change (-(R / (denominator - R))) /
      (base : Rat) ^ secondGuess = -(S / (denominator - R))
  simp only [Rat.div_def]
  have guessCancel := Rat.mul_inv_cancel ((base : Rat) ^ secondGuess)
    guessPowerNonzero
  grind

theorem threeProjectionGeneralSecondGuessState_auxiliary
    (base first firstGuess secondGuess : Nat)
    (baseAtLeastTwo : 2 ≤ base)
    (firstGuessPositive : 0 < firstGuess)
    (firstGuessBelow : firstGuess < 3 * (first + 1))
    (secondGuessPositive : 0 < secondGuess)
    (secondGuessBelow : secondGuess <
      3 * (first + 1) - firstGuess) :
    let Q := first + 1
    let r := 3 * Q - firstGuess
    let s := r - secondGuess
    let q : Rat := (base : Rat) ^ Q
    let R : Rat := (base : Rat) ^ r
    let S : Rat := (base : Rat) ^ s
    let denominator : Rat := 1 + q + q ^ 2 + q ^ 3
    (base : Rat) * threeProjectionGeneralSecondGuessState
        base first firstGuess secondGuess =
      -(S / (denominator - R - S)) := by
  dsimp
  let Q := first + 1
  let r := 3 * Q - firstGuess
  let s := r - secondGuess
  let q : Rat := (base : Rat) ^ Q
  let R : Rat := (base : Rat) ^ r
  let S : Rat := (base : Rat) ^ s
  let denominator : Rat := 1 + q + q ^ 2 + q ^ 3
  obtain ⟨_, _, _, sumBelowCube, _⟩ := three_projection_power_data
    base first firstGuess secondGuess baseAtLeastTwo firstGuessPositive
      firstGuessBelow secondGuessPositive secondGuessBelow
  have qNonnegative : 0 ≤ q := by
    unfold q
    rw [← Rat.natCast_pow]
    exact_mod_cast (Nat.zero_le (base ^ Q))
  have qSquareNonnegative : 0 ≤ q ^ 2 := Rat.pow_nonneg qNonnegative
  have qCubeNonnegative : 0 ≤ q ^ 3 := Rat.pow_nonneg qNonnegative
  have denominatorPositive : 0 < denominator := by
    unfold denominator
    grind
  have firstDifferencePositive : 0 < denominator - R := by
    have SNonnegative : 0 ≤ S := by
      unfold S
      rw [← Rat.natCast_pow]
      exact_mod_cast (Nat.zero_le (base ^ s))
    unfold denominator at *
    grind
  have secondDifferencePositive : 0 < denominator - R - S := by
    unfold denominator at *
    grind
  have firstDifferenceNonzero : denominator - R ≠ 0 := by grind
  unfold threeProjectionGeneralSecondGuessState
  rw [auxiliary_Tinv]
  rw [threeProjectionSecondPrefixState_auxiliary base first firstGuess
    secondGuess baseAtLeastTwo firstGuessPositive firstGuessBelow
    secondGuessPositive secondGuessBelow]
  have onePlus : 1 + -(S / (denominator - R)) =
      (denominator - R - S) / (denominator - R) := by
    simp only [Rat.div_def]
    have differenceCancel := Rat.mul_inv_cancel (denominator - R)
      firstDifferenceNonzero
    grind
  rw [onePlus]
  have core := div_div_same_den S (denominator - R)
    (denominator - R - S) firstDifferenceNonzero
  calc
    -(S / (denominator - R)) /
        ((denominator - R - S) / (denominator - R)) =
      -((S / (denominator - R)) /
        ((denominator - R - S) / (denominator - R))) := by
        simp only [Rat.div_def]
        grind
    _ = -(S / (denominator - R - S)) := by rw [core]

theorem threeProjectionGeneralNegativeState_auxiliary
    (base first firstGuess secondGuess : Nat)
    (baseAtLeastTwo : 2 ≤ base)
    (firstGuessPositive : 0 < firstGuess)
    (firstGuessBelow : firstGuess < 3 * (first + 1))
    (secondGuessPositive : 0 < secondGuess)
    (secondGuessBelow : secondGuess <
      3 * (first + 1) - firstGuess) :
    let Q := first + 1
    let r := 3 * Q - firstGuess
    let s := r - secondGuess
    let q : Rat := (base : Rat) ^ Q
    let R : Rat := (base : Rat) ^ r
    let S : Rat := (base : Rat) ^ s
    let polynomial : Rat := q + q ^ 2 + q ^ 3 - R - S
    (base : Rat) * threeProjectionGeneralNegativeState
        base first firstGuess secondGuess =
      polynomial / (1 + polynomial) := by
  dsimp
  let Q := first + 1
  let r := 3 * Q - firstGuess
  let s := r - secondGuess
  let q : Rat := (base : Rat) ^ Q
  let R : Rat := (base : Rat) ^ r
  let S : Rat := (base : Rat) ^ s
  let denominator : Rat := 1 + q + q ^ 2 + q ^ 3
  let polynomial : Rat := q + q ^ 2 + q ^ 3 - R - S
  obtain ⟨_, _, _, sumBelowCube, sPositive⟩ :=
    three_projection_power_data base first firstGuess secondGuess
      baseAtLeastTwo firstGuessPositive firstGuessBelow
      secondGuessPositive secondGuessBelow
  have SNonzero : S ≠ 0 := by
    unfold S
    exact pow_ne_zero (by simpa using (show base ≠ 0 by omega)) s
  have qNonnegative : 0 ≤ q := by
    unfold q
    rw [← Rat.natCast_pow]
    exact_mod_cast (Nat.zero_le (base ^ Q))
  have qSquareNonnegative : 0 ≤ q ^ 2 := Rat.pow_nonneg qNonnegative
  have differencePositive : 0 < denominator - R - S := by
    unfold denominator at *
    grind
  have differenceNonzero : denominator - R - S ≠ 0 := by grind
  unfold threeProjectionGeneralNegativeState
  dsimp only
  rw [show 3 * (first + 1) - firstGuess = r by rfl,
    show r - secondGuess = s by rfl]
  rw [auxiliary_negative_scan base (s - 1)
    (threeProjectionGeneralSecondGuessState
      base first firstGuess secondGuess) (by omega)]
  rw [show s - 1 + 1 = s by omega]
  rw [threeProjectionGeneralSecondGuessState_auxiliary
    base first firstGuess secondGuess baseAtLeastTwo firstGuessPositive
    firstGuessBelow secondGuessPositive secondGuessBelow]
  change (-(S / (denominator - R - S))) / S + 1 =
    polynomial / (1 + polynomial)
  have denominatorEq : denominator - R - S = 1 + polynomial := by
    unfold denominator polynomial
    grind
  simp only [Rat.div_def]
  have SCancel := Rat.mul_inv_cancel S SNonzero
  have differenceCancel := Rat.mul_inv_cancel (denominator - R - S)
    differenceNonzero
  rw [denominatorEq] at differenceCancel ⊢
  unfold polynomial denominator at *
  grind

/-- The first guessed prefix does not logically depend on the existence of
the second guess.  This form also covers the terminal choice leaving
`r=1`, which the next nonempty-guess phase must reject. -/
theorem threeProjectionFirstPrefixState_auxiliary_independent
    (base first firstGuess : Nat) (baseAtLeastTwo : 2 ≤ base)
    (firstGuessBelow : firstGuess < 3 * (first + 1)) :
    let Q := first + 1
    let r := 3 * Q - firstGuess
    let q : Rat := (base : Rat) ^ Q
    let R : Rat := (base : Rat) ^ r
    let denominator : Rat := 1 + q + q ^ 2 + q ^ 3
    (base : Rat) *
        threeProjectionFirstPrefixState base first firstGuess =
      -(R / denominator) := by
  dsimp
  let Q := first + 1
  let r := 3 * Q - firstGuess
  let q : Rat := (base : Rat) ^ Q
  let R : Rat := (base : Rat) ^ r
  let denominator : Rat := 1 + q + q ^ 2 + q ^ 3
  have exponentEq : firstGuess + r = 3 * Q := by unfold r; omega
  have cubePower : q ^ 3 = (base : Rat) ^ (3 * Q) := by
    rw [show 3 * Q = Q + Q + Q by omega]
    unfold q
    repeat' rw [Lean.Grind.Semiring.pow_add]
    grind
  have cubeSplit : q ^ 3 = (base : Rat) ^ firstGuess * R := by
    rw [cubePower, ← exponentEq]
    exact Lean.Grind.Semiring.pow_add _ _ _
  have baseNonzero : (base : Rat) ≠ 0 := by
    simpa using (show base ≠ 0 by omega)
  have guessPowerNonzero := pow_ne_zero baseNonzero firstGuess
  have denominatorNonzero : denominator ≠ 0 := by
    let qNat : Nat := base ^ Q
    simpa [denominator, q, qNat, Rat.natCast_pow] using
      geometric_four_nonzero qNat
  unfold threeProjectionFirstPrefixState
  rw [auxiliary_scan_zeroDigits base firstGuess
    (threeProjectionFirstState base first) (by omega)]
  rw [threeProjectionFirstState_auxiliary base first baseAtLeastTwo]
  change (-(q ^ 3 / denominator)) / (base : Rat) ^ firstGuess =
    -(R / denominator)
  simp only [Rat.div_def]
  have guessCancel := Rat.mul_inv_cancel ((base : Rat) ^ firstGuess)
    guessPowerNonzero
  have denominatorCancel := Rat.mul_inv_cancel denominator
    denominatorNonzero
  grind

theorem threeProjectionGeneralFirstGuessState_auxiliary_independent
    (base first firstGuess : Nat) (baseAtLeastTwo : 2 ≤ base)
    (firstGuessPositive : 0 < firstGuess)
    (firstGuessBelow : firstGuess < 3 * (first + 1)) :
    let Q := first + 1
    let r := 3 * Q - firstGuess
    let q : Rat := (base : Rat) ^ Q
    let R : Rat := (base : Rat) ^ r
    let denominator : Rat := 1 + q + q ^ 2 + q ^ 3
    (base : Rat) *
        threeProjectionGeneralFirstGuessState base first firstGuess =
      -(R / (denominator - R)) := by
  dsimp
  let Q := first + 1
  let r := 3 * Q - firstGuess
  let q : Rat := (base : Rat) ^ Q
  let R : Rat := (base : Rat) ^ r
  let denominator : Rat := 1 + q + q ^ 2 + q ^ 3
  have rPositive : 0 < r := by unfold r Q; omega
  have rBelow : r < 3 * Q := by unfold r; omega
  have naturalRBelowCube : base ^ r < base ^ (3 * Q) :=
    Nat.pow_lt_pow_right (by omega) rBelow
  have cubePower : q ^ 3 = (base : Rat) ^ (3 * Q) := by
    rw [show 3 * Q = Q + Q + Q by omega]
    unfold q
    repeat' rw [Lean.Grind.Semiring.pow_add]
    grind
  have RBelowCube : R < q ^ 3 := by
    unfold R
    rw [cubePower, ← Rat.natCast_pow]
    exact_mod_cast naturalRBelowCube
  have qNonnegative : 0 ≤ q := by
    unfold q
    rw [← Rat.natCast_pow]
    exact_mod_cast (Nat.zero_le (base ^ Q))
  have denominatorPositive : 0 < denominator := by
    unfold denominator
    have q2Nonnegative : 0 ≤ q ^ 2 := Rat.pow_nonneg qNonnegative
    have q3Nonnegative : 0 ≤ q ^ 3 := Rat.pow_nonneg qNonnegative
    grind
  have differencePositive : 0 < denominator - R := by
    unfold denominator
    have q2Nonnegative : 0 ≤ q ^ 2 := Rat.pow_nonneg qNonnegative
    grind
  have denominatorNonzero : denominator ≠ 0 := by grind
  have differenceNonzero : denominator - R ≠ 0 := by grind
  unfold threeProjectionGeneralFirstGuessState
  rw [auxiliary_Tinv]
  rw [threeProjectionFirstPrefixState_auxiliary_independent base first
    firstGuess baseAtLeastTwo firstGuessBelow]
  have onePlus : 1 + -(R / denominator) =
      (denominator - R) / denominator := by
    simp only [Rat.div_def]
    have denominatorCancel := Rat.mul_inv_cancel denominator
      denominatorNonzero
    grind
  rw [onePlus]
  have core := div_div_same_den R denominator (denominator - R)
    denominatorNonzero
  calc
    -(R / denominator) / ((denominator - R) / denominator) =
        -((R / denominator) / ((denominator - R) / denominator)) := by
      simp only [Rat.div_def]
      grind
    _ = -(R / (denominator - R)) := by rw [core]

theorem threeProjectionGeneralCandidate_auxiliary
    (base first firstGuess secondGuess : Nat)
    (baseAtLeastTwo : 2 ≤ base)
    (firstGuessPositive : 0 < firstGuess)
    (firstGuessBelow : firstGuess < 3 * (first + 1))
    (secondGuessPositive : 0 < secondGuess)
    (secondGuessBelow : secondGuess <
      3 * (first + 1) - firstGuess) :
    let Q := first + 1
    let r := 3 * Q - firstGuess
    let s := r - secondGuess
    let q : Rat := (base : Rat) ^ Q
    let R : Rat := (base : Rat) ^ r
    let S : Rat := (base : Rat) ^ s
    let polynomial : Rat := q + q ^ 2 + q ^ 3 - R - S
    (base : Rat) * threeProjectionGeneralCandidate
        base first firstGuess secondGuess =
      polynomial / (1 - polynomial) := by
  dsimp
  let Q := first + 1
  let r := 3 * Q - firstGuess
  let s := r - secondGuess
  let q : Rat := (base : Rat) ^ Q
  let R : Rat := (base : Rat) ^ r
  let S : Rat := (base : Rat) ^ s
  let polynomial : Rat := q + q ^ 2 + q ^ 3 - R - S
  obtain ⟨_, _, _, sumBelowCube, _⟩ := three_projection_power_data
    base first firstGuess secondGuess baseAtLeastTwo firstGuessPositive
      firstGuessBelow secondGuessPositive secondGuessBelow
  have qGreaterOne : 1 < q := by
    have naturalGreater : 1 < base ^ Q :=
      Nat.one_lt_pow (by unfold Q; omega) (by omega)
    unfold q
    rw [← Rat.natCast_pow]
    exact_mod_cast naturalGreater
  have qNonnegative : 0 ≤ q := by grind
  have qSquareNonnegative : 0 ≤ q ^ 2 := Rat.pow_nonneg qNonnegative
  have polynomialGreaterOne : 1 < polynomial := by
    unfold polynomial
    grind
  have targetNonzero : 1 - polynomial ≠ 0 := by grind
  unfold threeProjectionGeneralCandidate
  rw [auxiliary_Finv]
  rw [threeProjectionGeneralNegativeState_auxiliary
    base first firstGuess secondGuess baseAtLeastTwo firstGuessPositive
    firstGuessBelow secondGuessPositive secondGuessBelow]
  change (polynomial / (1 + polynomial)) /
      (1 - 2 * (polynomial / (1 + polynomial))) =
    polynomial / (1 - polynomial)
  have plusNonzero : 1 + polynomial ≠ 0 := by grind
  simp only [Rat.div_def]
  have plusCancel := Rat.mul_inv_cancel (1 + polynomial) plusNonzero
  have targetCancel := Rat.mul_inv_cancel (1 - polynomial) targetNonzero
  grind

end Mortality.Compiler.ContractionProjectionArithmetic
