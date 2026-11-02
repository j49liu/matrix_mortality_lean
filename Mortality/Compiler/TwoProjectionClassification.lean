import Mortality.Compiler.ContractionProjectionArithmetic
import Mortality.Compiler.CodeRegion

/-!
# Exhaustive residue classification for the two-to-one projection

Write `Q=a+1` and let `h=2Q-b` be the exponent left after the guessed
prefix.  The admissible range is `1 ≤ h < 2Q`.  This file proves directly
over integer homogeneous representatives that the first validator rejects
when `h<Q`, both validators accept when `h=Q`, and the second validator
rejects when `Q<h`.
-/

namespace Mortality.Compiler.TwoProjectionClassification

open Mortality.Compiler
open Mortality.PeriodicCode

def candidateDenominator (base Q h : Nat) : Int :=
  1 - (base : Int) ^ Q - (base : Int) ^ (2 * Q) + (base : Int) ^ h

def candidateNumerator
    (base Q h deleted : Nat) : Int :=
  (base : Int) ^ (Q - 1 - deleted) +
    (base : Int) ^ (2 * Q - 1 - deleted) -
    (base : Int) ^ (h - 1 - deleted)

def secondNumerator
    (base Q h deleted : Nat) : Int :=
  2 * (base : Int) ^ (Q - 1 - deleted) +
    (base : Int) ^ (2 * Q - 1 - deleted) -
    (base : Int) ^ (h - Q - 1 - deleted) -
    (base : Int) ^ (h - 1 - deleted)

def candidateState (base Q h deleted : Nat) : Rat :=
  (candidateNumerator base Q h deleted : Rat) /
    (candidateDenominator base Q h : Rat)

def secondState (base Q h deleted : Nat) : Rat :=
  (secondNumerator base Q h deleted : Rat) /
    (candidateDenominator base Q h : Rat)

theorem candidateDenominator_one_residue
    (base Q h : Nat) (QPositive : 0 < Q) (hPositive : 0 < h) :
    (base : Int) ∣ 1 - candidateDenominator base Q h := by
  rcases base_dvd_positive_power base Q QPositive with ⟨qFactor, qEq⟩
  rcases base_dvd_positive_power base (2 * Q) (by omega) with
    ⟨squareFactor, squareEq⟩
  rcases base_dvd_positive_power base h hPositive with
    ⟨hFactor, hEq⟩
  refine ⟨qFactor + squareFactor - hFactor, ?_⟩
  unfold candidateDenominator
  rw [qEq, squareEq, hEq]
  grind

theorem candidateDenominator_not_dvd
    (base Q h : Nat) (baseAtLeastTwo : 2 ≤ base)
    (QPositive : 0 < Q) (hPositive : 0 < h) :
    ¬(base : Int) ∣ candidateDenominator base Q h := by
  intro denominatorDivisible
  have oneDifference := candidateDenominator_one_residue base Q h
    QPositive hPositive
  have sumDivisible := Int.dvd_add oneDifference denominatorDivisible
  have sumEq :
      1 - candidateDenominator base Q h + candidateDenominator base Q h =
        1 := by grind
  rw [sumEq] at sumDivisible
  have naturalDivisible : base ∣ 1 := by
    simpa using (Int.ofNat_dvd.mp sumDivisible)
  have baseAtMostOne := Nat.le_of_dvd Nat.zero_lt_one naturalDivisible
  omega

theorem candidateState_local
    (base Q h deleted : Nat) (baseAtLeastTwo : 2 ≤ base)
    (QPositive : 0 < Q) (hPositive : 0 < h) :
    LocalAt base (Vec2.affine (candidateState base Q h deleted)) := by
  have localFraction := local_affine_integer_div
    (prime := base) (numerator := candidateNumerator base Q h deleted)
    (denominator := candidateDenominator base Q h)
    (candidateDenominator_not_dvd base Q h baseAtLeastTwo QPositive
      hPositive)
  simpa [candidateState] using localFraction

theorem secondState_local
    (base Q h deleted : Nat) (baseAtLeastTwo : 2 ≤ base)
    (QPositive : 0 < Q) (hPositive : 0 < h) :
    LocalAt base (Vec2.affine (secondState base Q h deleted)) := by
  have localFraction := local_affine_integer_div
    (prime := base) (numerator := secondNumerator base Q h deleted)
    (denominator := candidateDenominator base Q h)
    (candidateDenominator_not_dvd base Q h baseAtLeastTwo QPositive
      hPositive)
  simpa [secondState] using localFraction

theorem candidateState_sameLine_integer
    (base Q h deleted : Nat) (baseAtLeastTwo : 2 ≤ base)
    (QPositive : 0 < Q) (hPositive : 0 < h) :
    SameLine (Vec2.affine (candidateState base Q h deleted))
      (integerVector (candidateNumerator base Q h deleted)
        (candidateDenominator base Q h)) := by
  have denominatorNotDivisible := candidateDenominator_not_dvd base Q h
    baseAtLeastTwo QPositive hPositive
  have denominatorNonzero : candidateDenominator base Q h ≠ 0 :=
    fun denominatorZero => denominatorNotDivisible (by
      rw [denominatorZero]
      exact Int.dvd_zero _)
  have same := affine_div_sameLine_integerVector
    (numerator := candidateNumerator base Q h deleted)
    (denominator := candidateDenominator base Q h) denominatorNonzero
  simpa [candidateState] using same

theorem secondState_sameLine_integer
    (base Q h deleted : Nat) (baseAtLeastTwo : 2 ≤ base)
    (QPositive : 0 < Q) (hPositive : 0 < h) :
    SameLine (Vec2.affine (secondState base Q h deleted))
      (integerVector (secondNumerator base Q h deleted)
        (candidateDenominator base Q h)) := by
  have denominatorNotDivisible := candidateDenominator_not_dvd base Q h
    baseAtLeastTwo QPositive hPositive
  have denominatorNonzero : candidateDenominator base Q h ≠ 0 :=
    fun denominatorZero => denominatorNotDivisible (by
      rw [denominatorZero]
      exact Int.dvd_zero _)
  have same := affine_div_sameLine_integerVector
    (numerator := secondNumerator base Q h deleted)
    (denominator := candidateDenominator base Q h) denominatorNonzero
  simpa [secondState] using same

private theorem delete_integer_fraction
    (base : Nat) (digit numerator denominator quotient : Int)
    (basePositive : 0 < base) (denominatorNonzero : denominator ≠ 0)
    (differenceEq : numerator - digit * denominator =
      (base : Int) * quotient) :
    deleteDigit (base : Rat) digit
        ((numerator : Rat) / (denominator : Rat)) =
      (quotient : Rat) / (denominator : Rat) := by
  have baseNonzero : (base : Rat) ≠ 0 := by
    simpa using (show base ≠ 0 by omega)
  have denominatorNonzeroRat : (denominator : Rat) ≠ 0 := by
    exact_mod_cast denominatorNonzero
  have differenceRat :
      (numerator : Rat) - (digit : Rat) * (denominator : Rat) =
        (base : Rat) * (quotient : Rat) := by
    exact_mod_cast differenceEq
  unfold deleteDigit
  rw [Rat.div_def, Rat.div_def, Rat.div_def]
  have baseCancel := Rat.mul_inv_cancel (base : Rat) baseNonzero
  have denominatorCancel := Rat.mul_inv_cancel (denominator : Rat)
    denominatorNonzeroRat
  grind

theorem candidateNumerator_zero_step
    (base Q h deleted : Nat)
    (deletedBelowQ : deleted < Q - 1)
    (deletedBelowH : deleted < h - 1) :
    candidateNumerator base Q h deleted =
      (base : Int) * candidateNumerator base Q h (deleted + 1) := by
  have qExponent : Q - 1 - deleted =
      Q - 1 - (deleted + 1) + 1 := by omega
  have squareExponent : 2 * Q - 1 - deleted =
      2 * Q - 1 - (deleted + 1) + 1 := by omega
  have hExponent : h - 1 - deleted =
      h - 1 - (deleted + 1) + 1 := by omega
  unfold candidateNumerator
  rw [qExponent, squareExponent, hExponent, Int.pow_succ,
    Int.pow_succ, Int.pow_succ]
  grind

theorem candidateState_delete_zero
    (base Q h deleted : Nat) (baseAtLeastTwo : 2 ≤ base)
    (QPositive : 0 < Q) (hPositive : 0 < h)
    (deletedBelowQ : deleted < Q - 1)
    (deletedBelowH : deleted < h - 1) :
    deleteDigit (base : Rat) 0 (candidateState base Q h deleted) =
      candidateState base Q h (deleted + 1) := by
  have denominatorNotDivisible := candidateDenominator_not_dvd base Q h
    baseAtLeastTwo QPositive hPositive
  have denominatorNonzero : candidateDenominator base Q h ≠ 0 :=
    fun denominatorZero => denominatorNotDivisible (by
      rw [denominatorZero]
      exact Int.dvd_zero _)
  have numeratorEq := candidateNumerator_zero_step base Q h deleted
    deletedBelowQ deletedBelowH
  have deletedEq := delete_integer_fraction base 0
    (candidateNumerator base Q h deleted) (candidateDenominator base Q h)
    (candidateNumerator base Q h (deleted + 1)) (by omega)
    denominatorNonzero (by simpa using numeratorEq)
  simpa [candidateState] using deletedEq

theorem candidate_zero_residue_below_h
    (base Q h deleted : Nat) (hBelowQ : h < Q)
    (deletedBelow : deleted < h - 1) :
    (base : Int) ∣ candidateNumerator base Q h deleted := by
  rcases base_dvd_positive_power base (Q - 1 - deleted) (by omega) with
    ⟨qFactor, qEq⟩
  rcases base_dvd_positive_power base (2 * Q - 1 - deleted) (by omega) with
    ⟨squareFactor, squareEq⟩
  rcases base_dvd_positive_power base (h - 1 - deleted) (by omega) with
    ⟨hFactor, hEq⟩
  refine ⟨qFactor + squareFactor - hFactor, ?_⟩
  unfold candidateNumerator
  rw [qEq, squareEq, hEq]
  grind

/-- If `h<Q`, the first validator reaches residue `-1`. -/
theorem candidate_marker_residue_below
    (base Q h : Nat) (QPositive : 0 < Q) (hPositive : 0 < h)
    (hBelowQ : h < Q) :
    (base : Int) ∣
      candidateNumerator base Q h (h - 1) -
        (-1) * candidateDenominator base Q h := by
  rcases base_dvd_positive_power base (Q - h) (by omega) with
    ⟨firstFactor, firstEq⟩
  rcases base_dvd_positive_power base (2 * Q - h) (by omega) with
    ⟨secondFactor, secondEq⟩
  rcases base_dvd_positive_power base Q QPositive with
    ⟨qFactor, qEq⟩
  rcases base_dvd_positive_power base (2 * Q) (by omega) with
    ⟨squareFactor, squareEq⟩
  rcases base_dvd_positive_power base h hPositive with
    ⟨hFactor, hEq⟩
  refine ⟨firstFactor + secondFactor - qFactor - squareFactor + hFactor,
    ?_⟩
  unfold candidateNumerator candidateDenominator
  rw [show Q - 1 - (h - 1) = Q - h by omega,
    show 2 * Q - 1 - (h - 1) = 2 * Q - h by omega,
    show h - 1 - (h - 1) = 0 by omega, Int.pow_zero,
    firstEq, secondEq, qEq, squareEq, hEq]
  grind

theorem candidate_zero_residue_above_Q
    (base Q h deleted : Nat) (QPositive : 0 < Q) (QBelowH : Q < h)
    (deletedBelow : deleted < Q - 1) :
    (base : Int) ∣ candidateNumerator base Q h deleted := by
  rcases base_dvd_positive_power base (Q - 1 - deleted) (by omega) with
    ⟨qFactor, qEq⟩
  rcases base_dvd_positive_power base (2 * Q - 1 - deleted) (by omega) with
    ⟨squareFactor, squareEq⟩
  rcases base_dvd_positive_power base (h - 1 - deleted) (by omega) with
    ⟨hFactor, hEq⟩
  refine ⟨qFactor + squareFactor - hFactor, ?_⟩
  unfold candidateNumerator
  rw [qEq, squareEq, hEq]
  grind

/-- If `Q<h<2Q`, the first validator reaches the expected residue one. -/
theorem candidate_marker_residue_above
    (base Q h : Nat) (QPositive : 0 < Q) (QBelowH : Q < h)
    (hBelowDouble : h < 2 * Q) :
    (base : Int) ∣
      candidateNumerator base Q h (Q - 1) -
        candidateDenominator base Q h := by
  rcases base_dvd_positive_power base Q QPositive with
    ⟨qFactor, qEq⟩
  rcases base_dvd_positive_power base (h - Q) (by omega) with
    ⟨gapFactor, gapEq⟩
  rcases base_dvd_positive_power base (2 * Q) (by omega) with
    ⟨squareFactor, squareEq⟩
  rcases base_dvd_positive_power base h (by omega) with
    ⟨hFactor, hEq⟩
  refine ⟨2 * qFactor - gapFactor + squareFactor - hFactor, ?_⟩
  unfold candidateNumerator candidateDenominator
  rw [show Q - 1 - (Q - 1) = 0 by omega,
    show 2 * Q - 1 - (Q - 1) = Q by omega,
    show h - 1 - (Q - 1) = h - Q by omega,
    Int.pow_zero, qEq, gapEq, squareEq, hEq]
  grind

/-- The first marker deletion in the case `Q<h<2Q` leaves the displayed
integer numerator for the second validator. -/
theorem first_marker_quotient_above
    (base Q h : Nat) (QPositive : 0 < Q) (QBelowH : Q < h)
    (hBelowDouble : h < 2 * Q) :
    candidateNumerator base Q h (Q - 1) -
        candidateDenominator base Q h =
      (base : Int) * secondNumerator base Q h 0 := by
  have qSucc : (base : Int) ^ Q =
      (base : Int) ^ (Q - 1) * (base : Int) := by
    calc
      (base : Int) ^ Q = (base : Int) ^ (Q - 1 + 1) := by
        congr 1 <;> omega
      _ = (base : Int) ^ (Q - 1) * (base : Int) := by
        rw [Int.pow_succ]
  have squareSucc : (base : Int) ^ (2 * Q) =
      (base : Int) ^ (2 * Q - 1) * (base : Int) := by
    calc
      (base : Int) ^ (2 * Q) =
          (base : Int) ^ (2 * Q - 1 + 1) := by congr 1 <;> omega
      _ = (base : Int) ^ (2 * Q - 1) * (base : Int) := by
        rw [Int.pow_succ]
  have gapSucc : (base : Int) ^ (h - Q) =
      (base : Int) ^ (h - Q - 1) * (base : Int) := by
    calc
      (base : Int) ^ (h - Q) =
          (base : Int) ^ (h - Q - 1 + 1) := by congr 1 <;> omega
      _ = (base : Int) ^ (h - Q - 1) * (base : Int) := by
        rw [Int.pow_succ]
  have hSucc : (base : Int) ^ h =
      (base : Int) ^ (h - 1) * (base : Int) := by
    calc
      (base : Int) ^ h = (base : Int) ^ (h - 1 + 1) := by
        congr 1 <;> omega
      _ = (base : Int) ^ (h - 1) * (base : Int) := by
        rw [Int.pow_succ]
  unfold candidateNumerator candidateDenominator secondNumerator
  rw [show Q - 1 - (Q - 1) = 0 by omega,
    show 2 * Q - 1 - (Q - 1) = Q by omega,
    show h - 1 - (Q - 1) = h - Q by omega,
    Int.pow_zero, qSucc, squareSucc, gapSucc, hSucc]
  simp only [Nat.sub_zero]
  grind

theorem candidateState_delete_marker_above
    (base Q h : Nat) (baseAtLeastTwo : 2 ≤ base)
    (QPositive : 0 < Q) (QBelowH : Q < h)
    (hBelowDouble : h < 2 * Q) :
    deleteDigit (base : Rat) 1
        (candidateState base Q h (Q - 1)) =
      secondState base Q h 0 := by
  have denominatorNotDivisible := candidateDenominator_not_dvd base Q h
    baseAtLeastTwo QPositive (by omega)
  have denominatorNonzero : candidateDenominator base Q h ≠ 0 :=
    fun denominatorZero => denominatorNotDivisible (by
      rw [denominatorZero]
      exact Int.dvd_zero _)
  have differenceEq := first_marker_quotient_above base Q h QPositive
    QBelowH hBelowDouble
  have deletedEq := delete_integer_fraction base 1
    (candidateNumerator base Q h (Q - 1))
    (candidateDenominator base Q h) (secondNumerator base Q h 0)
    (by omega) denominatorNonzero (by simpa using differenceEq)
  simpa [candidateState, secondState] using deletedEq

theorem secondNumerator_zero_step
    (base Q h deleted : Nat) (QBelowH : Q < h)
    (hBelowDouble : h < 2 * Q)
    (deletedBelow : deleted < h - Q - 1) :
    secondNumerator base Q h deleted =
      (base : Int) * secondNumerator base Q h (deleted + 1) := by
  have qExponent : Q - 1 - deleted =
      Q - 1 - (deleted + 1) + 1 := by omega
  have squareExponent : 2 * Q - 1 - deleted =
      2 * Q - 1 - (deleted + 1) + 1 := by omega
  have gapExponent : h - Q - 1 - deleted =
      h - Q - 1 - (deleted + 1) + 1 := by omega
  have hExponent : h - 1 - deleted =
      h - 1 - (deleted + 1) + 1 := by omega
  unfold secondNumerator
  rw [qExponent, squareExponent, gapExponent, hExponent,
    Int.pow_succ, Int.pow_succ, Int.pow_succ, Int.pow_succ]
  grind

theorem secondState_delete_zero
    (base Q h deleted : Nat) (baseAtLeastTwo : 2 ≤ base)
    (QPositive : 0 < Q) (QBelowH : Q < h)
    (hBelowDouble : h < 2 * Q)
    (deletedBelow : deleted < h - Q - 1) :
    deleteDigit (base : Rat) 0 (secondState base Q h deleted) =
      secondState base Q h (deleted + 1) := by
  have denominatorNotDivisible := candidateDenominator_not_dvd base Q h
    baseAtLeastTwo QPositive (by omega)
  have denominatorNonzero : candidateDenominator base Q h ≠ 0 :=
    fun denominatorZero => denominatorNotDivisible (by
      rw [denominatorZero]
      exact Int.dvd_zero _)
  have numeratorEq := secondNumerator_zero_step base Q h deleted QBelowH
    hBelowDouble deletedBelow
  have deletedEq := delete_integer_fraction base 0
    (secondNumerator base Q h deleted) (candidateDenominator base Q h)
    (secondNumerator base Q h (deleted + 1)) (by omega)
    denominatorNonzero (by simpa using numeratorEq)
  simpa [secondState] using deletedEq

theorem second_zero_residue
    (base Q h deleted : Nat) (QBelowH : Q < h)
    (hBelowDouble : h < 2 * Q)
    (deletedBelow : deleted < h - Q - 1) :
    (base : Int) ∣ secondNumerator base Q h deleted := by
  rcases base_dvd_positive_power base (Q - 1 - deleted) (by omega) with
    ⟨qFactor, qEq⟩
  rcases base_dvd_positive_power base (2 * Q - 1 - deleted) (by omega) with
    ⟨squareFactor, squareEq⟩
  rcases base_dvd_positive_power base (h - Q - 1 - deleted) (by omega) with
    ⟨gapFactor, gapEq⟩
  rcases base_dvd_positive_power base (h - 1 - deleted) (by omega) with
    ⟨hFactor, hEq⟩
  refine ⟨2 * qFactor + squareFactor - gapFactor - hFactor, ?_⟩
  unfold secondNumerator
  rw [qEq, squareEq, gapEq, hEq]
  grind

/-- Every wrong case `Q<h<2Q` reaches residue `-1` in the second
validator and is rejected there. -/
theorem second_marker_residue
    (base Q h : Nat) (QPositive : 0 < Q) (QBelowH : Q < h)
    (hBelowDouble : h < 2 * Q) :
    (base : Int) ∣
      secondNumerator base Q h (h - Q - 1) -
        (-1) * candidateDenominator base Q h := by
  rcases base_dvd_positive_power base (2 * Q - h) (by omega) with
    ⟨firstFactor, firstEq⟩
  rcases base_dvd_positive_power base (3 * Q - h) (by omega) with
    ⟨secondFactor, secondEq⟩
  rcases base_dvd_positive_power base Q QPositive with
    ⟨qFactor, qEq⟩
  rcases base_dvd_positive_power base (2 * Q) (by omega) with
    ⟨squareFactor, squareEq⟩
  rcases base_dvd_positive_power base h (by omega) with
    ⟨hFactor, hEq⟩
  refine ⟨2 * firstFactor + secondFactor - 2 * qFactor -
      squareFactor + hFactor, ?_⟩
  unfold secondNumerator candidateDenominator
  rw [show Q - 1 - (h - Q - 1) = 2 * Q - h by omega,
    show 2 * Q - 1 - (h - Q - 1) = 3 * Q - h by omega,
    show h - Q - 1 - (h - Q - 1) = 0 by omega,
    show h - 1 - (h - Q - 1) = Q by omega,
    Int.pow_zero, firstEq, secondEq, qEq, squareEq, hEq]
  grind

/-- At the unique accepted exponent `h=Q`, the candidate is exactly the
unary integer representative of `z_(2Q-1)`. -/
theorem accepted_candidate_integer
    (base Q : Nat) :
    candidateNumerator base Q Q 0 = (base : Int) ^ (2 * Q - 1) ∧
      candidateDenominator base Q Q = 1 - (base : Int) ^ (2 * Q) := by
  constructor
  · unfold candidateNumerator
    simp only [Nat.sub_zero]
    grind
  · unfold candidateDenominator
    grind

theorem accepted_candidate_state
    (base Q : Nat) (QPositive : 0 < Q) :
    candidateState base Q Q 0 = unaryCode base (2 * Q - 1) := by
  obtain ⟨numeratorEq, denominatorEq⟩ := accepted_candidate_integer base Q
  unfold candidateState
  rw [numeratorEq, denominatorEq, unaryCode_eq]
  simp only [Rat.intCast_pow, Rat.intCast_natCast, Rat.intCast_sub,
    Rat.intCast_one]
  rw [show 2 * Q - 1 + 1 = 2 * Q by omega]

/-- The integer candidate representative is the rational candidate
`P/(p(1-P))` used in the manuscript, expressed in auxiliary coordinates. -/
theorem candidateState_auxiliary
    (base Q h : Nat) (QPositive : 0 < Q) (hPositive : 0 < h) :
    let q : Rat := (base : Rat) ^ Q;
    let R : Rat := (base : Rat) ^ h;
    let polynomial : Rat := q + q ^ 2 - R;
    (base : Rat) * candidateState base Q h 0 =
      polynomial / (1 - polynomial) := by
  dsimp
  let q : Rat := (base : Rat) ^ Q
  let R : Rat := (base : Rat) ^ h
  let polynomial : Rat := q + q ^ 2 - R
  have qSucc : (base : Rat) ^ Q =
      (base : Rat) ^ (Q - 1) * (base : Rat) := by
    calc
      (base : Rat) ^ Q = (base : Rat) ^ (Q - 1 + 1) := by
        congr 1 <;> omega
      _ = (base : Rat) ^ (Q - 1) * (base : Rat) := by
        rw [Rat.pow_succ]
  have squareSucc : (base : Rat) ^ (2 * Q) =
      (base : Rat) ^ (2 * Q - 1) * (base : Rat) := by
    calc
      (base : Rat) ^ (2 * Q) =
          (base : Rat) ^ (2 * Q - 1 + 1) := by congr 1 <;> omega
      _ = (base : Rat) ^ (2 * Q - 1) * (base : Rat) := by
        rw [Rat.pow_succ]
  have hSucc : (base : Rat) ^ h =
      (base : Rat) ^ (h - 1) * (base : Rat) := by
    calc
      (base : Rat) ^ h = (base : Rat) ^ (h - 1 + 1) := by
        congr 1 <;> omega
      _ = (base : Rat) ^ (h - 1) * (base : Rat) := by
        rw [Rat.pow_succ]
  have squarePower : q ^ 2 = (base : Rat) ^ (2 * Q) := by
    calc
      q ^ 2 = q * q := by
        rw [show (2 : Nat) = 1 + 1 by omega,
          Lean.Grind.Semiring.pow_add]
        simp only [Rat.pow_one]
      _ = (base : Rat) ^ Q * (base : Rat) ^ Q := by rfl
      _ = (base : Rat) ^ (Q + Q) :=
        (Lean.Grind.Semiring.pow_add (base : Rat) Q Q).symm
      _ = (base : Rat) ^ (2 * Q) := by congr 1 <;> omega
  unfold candidateState candidateNumerator candidateDenominator
  simp only [Nat.sub_zero, Rat.intCast_sub, Rat.intCast_add,
    Rat.intCast_pow, Rat.intCast_natCast, Rat.intCast_ofNat, Rat.div_def]
  rw [squarePower]
  grind

/-- The operational guessed prefix and Möbius maps produce exactly the
integer candidate classified above. -/
theorem operational_candidate_eq
    (base Q h : Nat) (baseAtLeastTwo : 2 ≤ base)
    (QPositive : 0 < Q) (hPositive : 0 < h)
    (hBelowDouble : h < 2 * Q) :
    ContractionProjectionArithmetic.twoProjectionGeneralCandidate
        base (Q - 1) (2 * Q - h) =
      candidateState base Q h 0 := by
  have guessPositive : 0 < 2 * Q - h := by omega
  have guessBelow : 2 * Q - h < 2 * ((Q - 1) + 1) := by omega
  have operationalAuxiliary :=
    ContractionProjectionArithmetic.twoProjectionGeneralCandidate_auxiliary
      base (Q - 1) (2 * Q - h) baseAtLeastTwo guessPositive guessBelow
  have candidateAuxiliary := candidateState_auxiliary base Q h QPositive
    hPositive
  have firstExponentEq : Q - 1 + 1 = Q := by omega
  have remainingEq : 2 * Q - (2 * Q - h) = h := by omega
  simp only [firstExponentEq, remainingEq] at operationalAuxiliary
  have productEq :
      (base : Rat) *
          ContractionProjectionArithmetic.twoProjectionGeneralCandidate
            base (Q - 1) (2 * Q - h) =
        (base : Rat) * candidateState base Q h 0 := by
    exact operationalAuxiliary.trans candidateAuxiliary.symm
  have baseNonzero : (base : Rat) ≠ 0 := by
    simpa using (show base ≠ 0 by omega)
  calc
    ContractionProjectionArithmetic.twoProjectionGeneralCandidate
        base (Q - 1) (2 * Q - h) =
      ((base : Rat)⁻¹ * (base : Rat)) *
        ContractionProjectionArithmetic.twoProjectionGeneralCandidate
          base (Q - 1) (2 * Q - h) := by
      rw [Rat.inv_mul_cancel (base : Rat) baseNonzero, Rat.one_mul]
    _ = (base : Rat)⁻¹ *
        ((base : Rat) *
          ContractionProjectionArithmetic.twoProjectionGeneralCandidate
            base (Q - 1) (2 * Q - h)) := by rw [Rat.mul_assoc]
    _ = (base : Rat)⁻¹ *
        ((base : Rat) * candidateState base Q h 0) := by rw [productEq]
    _ = ((base : Rat)⁻¹ * (base : Rat)) *
        candidateState base Q h 0 := by rw [Rat.mul_assoc]
    _ = candidateState base Q h 0 := by
      rw [Rat.inv_mul_cancel (base : Rat) baseNonzero, Rat.one_mul]

end Mortality.Compiler.TwoProjectionClassification
