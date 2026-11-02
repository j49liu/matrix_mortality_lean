import Mortality.Compiler.ContractionProjectionArithmetic
import Mortality.Compiler.CodeRegion

/-!
# Exhaustive residue classification for the three-to-one projection

For `Q=a+1`, the two guessed prefixes leave exponents
`1 ≤ s < r < 3Q`.  The candidate polynomial is
`P=p^Q+p^(2Q)+p^(3Q)-p^r-p^s`.  This file proves the manuscript's
case split with integer homogeneous representatives.
-/

namespace Mortality.Compiler.ThreeProjectionClassification

open Mortality.Compiler
open Mortality.PeriodicCode

def candidateDenominator (base Q r s : Nat) : Int :=
  1 - (base : Int) ^ Q - (base : Int) ^ (2 * Q) -
    (base : Int) ^ (3 * Q) + (base : Int) ^ r + (base : Int) ^ s

def candidateNumerator
    (base Q r s deleted : Nat) : Int :=
  (base : Int) ^ (Q - 1 - deleted) +
    (base : Int) ^ (2 * Q - 1 - deleted) +
    (base : Int) ^ (3 * Q - 1 - deleted) -
    (base : Int) ^ (r - 1 - deleted) -
    (base : Int) ^ (s - 1 - deleted)

def candidateState (base Q r s deleted : Nat) : Rat :=
  (candidateNumerator base Q r s deleted : Rat) /
    (candidateDenominator base Q r s : Rat)

def generalFirstOutputNumerator
    (base Q r s deleted : Nat) : Int :=
  2 * (base : Int) ^ (Q - 1 - deleted) +
    2 * (base : Int) ^ (2 * Q - 1 - deleted) +
    (base : Int) ^ (3 * Q - 1 - deleted) -
    (base : Int) ^ (r - Q - 1 - deleted) -
    (base : Int) ^ (s - Q - 1 - deleted) -
    (base : Int) ^ (r - 1 - deleted) -
    (base : Int) ^ (s - 1 - deleted)

def sEqualsQFirstOutputNumerator
    (base Q r deleted : Nat) : Int :=
  (base : Int) ^ (Q - 1 - deleted) +
    (base : Int) ^ (2 * Q - 1 - deleted) +
    (base : Int) ^ (3 * Q - 1 - deleted) -
    (base : Int) ^ (r - 2 * Q - 1 - deleted) -
    (base : Int) ^ (r - 1 - deleted)

def sEqualsTwoQSecondOutputNumerator
    (base Q r deleted : Nat) : Int :=
  2 * (base : Int) ^ (Q - 1 - deleted) +
    (base : Int) ^ (2 * Q - 1 - deleted) +
    (base : Int) ^ (3 * Q - 1 - deleted) -
    (base : Int) ^ (r - 2 * Q - 1 - deleted) -
    (base : Int) ^ (r - Q - 1 - deleted) -
    (base : Int) ^ (r - 1 - deleted)

def generalFirstOutputState
    (base Q r s deleted : Nat) : Rat :=
  (generalFirstOutputNumerator base Q r s deleted : Rat) /
    (candidateDenominator base Q r s : Rat)

def sEqualsQCandidateNumerator
    (base Q r deleted : Nat) : Int :=
  (base : Int) ^ (2 * Q - 1 - deleted) +
    (base : Int) ^ (3 * Q - 1 - deleted) -
    (base : Int) ^ (r - 1 - deleted)

def sEqualsQCandidateState
    (base Q r deleted : Nat) : Rat :=
  (sEqualsQCandidateNumerator base Q r deleted : Rat) /
    (candidateDenominator base Q r Q : Rat)

def sEqualsQFirstOutputState
    (base Q r deleted : Nat) : Rat :=
  (sEqualsQFirstOutputNumerator base Q r deleted : Rat) /
    (candidateDenominator base Q r Q : Rat)

def sEqualsTwoQSecondOutputState
    (base Q r deleted : Nat) : Rat :=
  (sEqualsTwoQSecondOutputNumerator base Q r deleted : Rat) /
    (candidateDenominator base Q r (2 * Q) : Rat)

theorem candidateDenominator_one_residue
    (base Q r s : Nat) (QPositive : 0 < Q)
    (rPositive : 0 < r) (sPositive : 0 < s) :
    (base : Int) ∣ 1 - candidateDenominator base Q r s := by
  rcases base_dvd_positive_power base Q QPositive with ⟨q, hq⟩
  rcases base_dvd_positive_power base (2 * Q) (by omega) with ⟨q2, hq2⟩
  rcases base_dvd_positive_power base (3 * Q) (by omega) with ⟨q3, hq3⟩
  rcases base_dvd_positive_power base r rPositive with ⟨rf, hr⟩
  rcases base_dvd_positive_power base s sPositive with ⟨sf, hs⟩
  refine ⟨q + q2 + q3 - rf - sf, ?_⟩
  unfold candidateDenominator
  rw [hq, hq2, hq3, hr, hs]
  grind

theorem candidateDenominator_not_dvd
    (base Q r s : Nat) (baseAtLeastTwo : 2 ≤ base)
    (QPositive : 0 < Q) (rPositive : 0 < r) (sPositive : 0 < s) :
    ¬(base : Int) ∣ candidateDenominator base Q r s := by
  intro denominatorDivisible
  have differenceDivisible := candidateDenominator_one_residue base Q r s
    QPositive rPositive sPositive
  have sumDivisible := Int.dvd_add differenceDivisible denominatorDivisible
  have sumEq :
      1 - candidateDenominator base Q r s +
        candidateDenominator base Q r s = 1 := by grind
  rw [sumEq] at sumDivisible
  have naturalDivisible : base ∣ 1 := by
    simpa using (Int.ofNat_dvd.mp sumDivisible)
  have baseAtMostOne := Nat.le_of_dvd Nat.zero_lt_one naturalDivisible
  omega

theorem candidateState_local
    (base Q r s deleted : Nat) (baseAtLeastTwo : 2 ≤ base)
    (QPositive : 0 < Q) (rPositive : 0 < r) (sPositive : 0 < s) :
    LocalAt base (Vec2.affine (candidateState base Q r s deleted)) := by
  have localFraction := local_affine_integer_div
    (prime := base) (numerator := candidateNumerator base Q r s deleted)
    (denominator := candidateDenominator base Q r s)
    (candidateDenominator_not_dvd base Q r s baseAtLeastTwo QPositive
      rPositive sPositive)
  simpa [candidateState] using localFraction

private theorem fractionState_local
    (base : Nat) (numerator denominator : Int)
    (denominatorNotDivisible : ¬(base : Int) ∣ denominator) :
    LocalAt base (Vec2.affine ((numerator : Rat) / (denominator : Rat))) :=
  local_affine_integer_div denominatorNotDivisible

private theorem fractionState_sameLine_integer
    (numerator denominator : Int) (denominatorNonzero : denominator ≠ 0) :
    SameLine
      (Vec2.affine ((numerator : Rat) / (denominator : Rat)))
      (integerVector numerator denominator) :=
  affine_div_sameLine_integerVector denominatorNonzero

theorem candidateState_sameLine_integer
    (base Q r s deleted : Nat) (baseAtLeastTwo : 2 ≤ base)
    (QPositive : 0 < Q) (rPositive : 0 < r) (sPositive : 0 < s) :
    SameLine (Vec2.affine (candidateState base Q r s deleted))
      (integerVector (candidateNumerator base Q r s deleted)
        (candidateDenominator base Q r s)) := by
  have notDivisible := candidateDenominator_not_dvd base Q r s
    baseAtLeastTwo QPositive rPositive sPositive
  have nonzero : candidateDenominator base Q r s ≠ 0 :=
    fun zero => notDivisible (by rw [zero]; exact Int.dvd_zero _)
  simpa [candidateState] using
    fractionState_sameLine_integer
      (candidateNumerator base Q r s deleted)
      (candidateDenominator base Q r s) nonzero

theorem generalFirstOutputState_local
    (base Q r s deleted : Nat) (baseAtLeastTwo : 2 ≤ base)
    (QPositive : 0 < Q) (rPositive : 0 < r) (sPositive : 0 < s) :
    LocalAt base
      (Vec2.affine (generalFirstOutputState base Q r s deleted)) := by
  exact fractionState_local base _ _
    (candidateDenominator_not_dvd base Q r s baseAtLeastTwo QPositive
      rPositive sPositive)

theorem generalFirstOutputState_sameLine_integer
    (base Q r s deleted : Nat) (baseAtLeastTwo : 2 ≤ base)
    (QPositive : 0 < Q) (rPositive : 0 < r) (sPositive : 0 < s) :
    SameLine (Vec2.affine (generalFirstOutputState base Q r s deleted))
      (integerVector (generalFirstOutputNumerator base Q r s deleted)
        (candidateDenominator base Q r s)) := by
  have notDivisible := candidateDenominator_not_dvd base Q r s
    baseAtLeastTwo QPositive rPositive sPositive
  have nonzero : candidateDenominator base Q r s ≠ 0 :=
    fun zero => notDivisible (by rw [zero]; exact Int.dvd_zero _)
  exact fractionState_sameLine_integer _ _ nonzero

theorem sEqualsQCandidateState_eq
    (base Q r deleted : Nat) :
    sEqualsQCandidateState base Q r deleted =
      candidateState base Q r Q deleted := by
  unfold sEqualsQCandidateState sEqualsQCandidateNumerator candidateState
    candidateNumerator
  congr 1
  grind

theorem sEqualsQCandidateState_local
    (base Q r deleted : Nat) (baseAtLeastTwo : 2 ≤ base)
    (QPositive : 0 < Q) (rPositive : 0 < r) :
    LocalAt base
      (Vec2.affine (sEqualsQCandidateState base Q r deleted)) := by
  rw [sEqualsQCandidateState_eq]
  exact candidateState_local base Q r Q deleted baseAtLeastTwo QPositive
    rPositive QPositive

theorem sEqualsQCandidateState_sameLine_integer
    (base Q r deleted : Nat) (baseAtLeastTwo : 2 ≤ base)
    (QPositive : 0 < Q) (rPositive : 0 < r) :
    SameLine (Vec2.affine (sEqualsQCandidateState base Q r deleted))
      (integerVector (sEqualsQCandidateNumerator base Q r deleted)
        (candidateDenominator base Q r Q)) := by
  have notDivisible := candidateDenominator_not_dvd base Q r Q
    baseAtLeastTwo QPositive rPositive QPositive
  have nonzero : candidateDenominator base Q r Q ≠ 0 :=
    fun zero => notDivisible (by rw [zero]; exact Int.dvd_zero _)
  exact fractionState_sameLine_integer _ _ nonzero

theorem sEqualsQFirstOutputState_local
    (base Q r deleted : Nat) (baseAtLeastTwo : 2 ≤ base)
    (QPositive : 0 < Q) (rPositive : 0 < r) :
    LocalAt base
      (Vec2.affine (sEqualsQFirstOutputState base Q r deleted)) := by
  exact fractionState_local base _ _
    (candidateDenominator_not_dvd base Q r Q baseAtLeastTwo QPositive
      rPositive QPositive)

theorem sEqualsQFirstOutputState_sameLine_integer
    (base Q r deleted : Nat) (baseAtLeastTwo : 2 ≤ base)
    (QPositive : 0 < Q) (rPositive : 0 < r) :
    SameLine (Vec2.affine (sEqualsQFirstOutputState base Q r deleted))
      (integerVector (sEqualsQFirstOutputNumerator base Q r deleted)
        (candidateDenominator base Q r Q)) := by
  have notDivisible := candidateDenominator_not_dvd base Q r Q
    baseAtLeastTwo QPositive rPositive QPositive
  have nonzero : candidateDenominator base Q r Q ≠ 0 :=
    fun zero => notDivisible (by rw [zero]; exact Int.dvd_zero _)
  exact fractionState_sameLine_integer _ _ nonzero

theorem sEqualsTwoQSecondOutputState_local
    (base Q r deleted : Nat) (baseAtLeastTwo : 2 ≤ base)
    (QPositive : 0 < Q) (rPositive : 0 < r) :
    LocalAt base
      (Vec2.affine (sEqualsTwoQSecondOutputState base Q r deleted)) := by
  exact fractionState_local base _ _
    (candidateDenominator_not_dvd base Q r (2 * Q) baseAtLeastTwo
      QPositive rPositive (by omega))

theorem sEqualsTwoQSecondOutputState_sameLine_integer
    (base Q r deleted : Nat) (baseAtLeastTwo : 2 ≤ base)
    (QPositive : 0 < Q) (rPositive : 0 < r) :
    SameLine
      (Vec2.affine (sEqualsTwoQSecondOutputState base Q r deleted))
      (integerVector (sEqualsTwoQSecondOutputNumerator base Q r deleted)
        (candidateDenominator base Q r (2 * Q))) := by
  have notDivisible := candidateDenominator_not_dvd base Q r (2 * Q)
    baseAtLeastTwo QPositive rPositive (by omega)
  have nonzero : candidateDenominator base Q r (2 * Q) ≠ 0 :=
    fun zero => notDivisible (by rw [zero]; exact Int.dvd_zero _)
  exact fractionState_sameLine_integer _ _ nonzero

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
    (base Q r s deleted : Nat)
    (deletedBelowQ : deleted < Q - 1)
    (deletedBelowR : deleted < r - 1)
    (deletedBelowS : deleted < s - 1) :
    candidateNumerator base Q r s deleted =
      (base : Int) * candidateNumerator base Q r s (deleted + 1) := by
  have e1 : Q - 1 - deleted = Q - 1 - (deleted + 1) + 1 := by omega
  have e2 : 2 * Q - 1 - deleted =
      2 * Q - 1 - (deleted + 1) + 1 := by omega
  have e3 : 3 * Q - 1 - deleted =
      3 * Q - 1 - (deleted + 1) + 1 := by omega
  have er : r - 1 - deleted = r - 1 - (deleted + 1) + 1 := by omega
  have es : s - 1 - deleted = s - 1 - (deleted + 1) + 1 := by omega
  unfold candidateNumerator
  rw [e1, e2, e3, er, es, Int.pow_succ, Int.pow_succ, Int.pow_succ,
    Int.pow_succ, Int.pow_succ]
  grind

theorem candidateState_delete_zero
    (base Q r s deleted : Nat) (baseAtLeastTwo : 2 ≤ base)
    (QPositive : 0 < Q) (rPositive : 0 < r) (sPositive : 0 < s)
    (deletedBelowQ : deleted < Q - 1)
    (deletedBelowR : deleted < r - 1)
    (deletedBelowS : deleted < s - 1) :
    deleteDigit (base : Rat) 0 (candidateState base Q r s deleted) =
      candidateState base Q r s (deleted + 1) := by
  have notDivisible := candidateDenominator_not_dvd base Q r s
    baseAtLeastTwo QPositive rPositive sPositive
  have nonzero : candidateDenominator base Q r s ≠ 0 :=
    fun zero => notDivisible (by rw [zero]; exact Int.dvd_zero _)
  have step := candidateNumerator_zero_step base Q r s deleted
    deletedBelowQ deletedBelowR deletedBelowS
  simpa [candidateState] using delete_integer_fraction base 0
    (candidateNumerator base Q r s deleted)
    (candidateDenominator base Q r s)
    (candidateNumerator base Q r s (deleted + 1)) (by omega) nonzero
    (by simpa using step)

theorem sEqualsQCandidateNumerator_zero_step
    (base Q r deleted : Nat)
    (deletedBelowTwoQ : deleted < 2 * Q - 1)
    (deletedBelowR : deleted < r - 1) :
    sEqualsQCandidateNumerator base Q r deleted =
      (base : Int) * sEqualsQCandidateNumerator base Q r (deleted + 1) := by
  have e2 : 2 * Q - 1 - deleted =
      2 * Q - 1 - (deleted + 1) + 1 := by omega
  have e3 : 3 * Q - 1 - deleted =
      3 * Q - 1 - (deleted + 1) + 1 := by omega
  have er : r - 1 - deleted = r - 1 - (deleted + 1) + 1 := by omega
  unfold sEqualsQCandidateNumerator
  rw [e2, e3, er, Int.pow_succ, Int.pow_succ, Int.pow_succ]
  grind

theorem sEqualsQCandidateState_delete_zero
    (base Q r deleted : Nat) (baseAtLeastTwo : 2 ≤ base)
    (QPositive : 0 < Q) (rPositive : 0 < r)
    (deletedBelowTwoQ : deleted < 2 * Q - 1)
    (deletedBelowR : deleted < r - 1) :
    deleteDigit (base : Rat) 0
        (sEqualsQCandidateState base Q r deleted) =
      sEqualsQCandidateState base Q r (deleted + 1) := by
  have notDivisible := candidateDenominator_not_dvd base Q r Q
    baseAtLeastTwo QPositive rPositive QPositive
  have nonzero : candidateDenominator base Q r Q ≠ 0 :=
    fun zero => notDivisible (by rw [zero]; exact Int.dvd_zero _)
  have step := sEqualsQCandidateNumerator_zero_step base Q r deleted
    deletedBelowTwoQ deletedBelowR
  simpa [sEqualsQCandidateState] using delete_integer_fraction base 0
    (sEqualsQCandidateNumerator base Q r deleted)
    (candidateDenominator base Q r Q)
    (sEqualsQCandidateNumerator base Q r (deleted + 1)) (by omega)
    nonzero (by simpa using step)

theorem generalFirstOutputNumerator_zero_step
    (base Q r s deleted : Nat)
    (d1 : deleted < Q - 1) (d2 : deleted < 2 * Q - 1)
    (d3 : deleted < 3 * Q - 1) (drq : deleted < r - Q - 1)
    (dsq : deleted < s - Q - 1) (dr : deleted < r - 1)
    (ds : deleted < s - 1) :
    generalFirstOutputNumerator base Q r s deleted =
      (base : Int) *
        generalFirstOutputNumerator base Q r s (deleted + 1) := by
  have e1 : Q - 1 - deleted = Q - 1 - (deleted + 1) + 1 := by omega
  have e2 : 2 * Q - 1 - deleted =
      2 * Q - 1 - (deleted + 1) + 1 := by omega
  have e3 : 3 * Q - 1 - deleted =
      3 * Q - 1 - (deleted + 1) + 1 := by omega
  have erq : r - Q - 1 - deleted =
      r - Q - 1 - (deleted + 1) + 1 := by omega
  have esq : s - Q - 1 - deleted =
      s - Q - 1 - (deleted + 1) + 1 := by omega
  have er : r - 1 - deleted = r - 1 - (deleted + 1) + 1 := by omega
  have es : s - 1 - deleted = s - 1 - (deleted + 1) + 1 := by omega
  unfold generalFirstOutputNumerator
  rw [e1, e2, e3, erq, esq, er, es, Int.pow_succ, Int.pow_succ,
    Int.pow_succ, Int.pow_succ, Int.pow_succ, Int.pow_succ, Int.pow_succ]
  grind

theorem generalFirstOutputState_delete_zero
    (base Q r s deleted : Nat) (baseAtLeastTwo : 2 ≤ base)
    (QPositive : 0 < Q) (rPositive : 0 < r) (sPositive : 0 < s)
    (d1 : deleted < Q - 1) (d2 : deleted < 2 * Q - 1)
    (d3 : deleted < 3 * Q - 1) (drq : deleted < r - Q - 1)
    (dsq : deleted < s - Q - 1) (dr : deleted < r - 1)
    (ds : deleted < s - 1) :
    deleteDigit (base : Rat) 0
        (generalFirstOutputState base Q r s deleted) =
      generalFirstOutputState base Q r s (deleted + 1) := by
  have notDivisible := candidateDenominator_not_dvd base Q r s
    baseAtLeastTwo QPositive rPositive sPositive
  have nonzero : candidateDenominator base Q r s ≠ 0 :=
    fun zero => notDivisible (by rw [zero]; exact Int.dvd_zero _)
  have step := generalFirstOutputNumerator_zero_step base Q r s deleted
    d1 d2 d3 drq dsq dr ds
  simpa [generalFirstOutputState] using delete_integer_fraction base 0
    (generalFirstOutputNumerator base Q r s deleted)
    (candidateDenominator base Q r s)
    (generalFirstOutputNumerator base Q r s (deleted + 1)) (by omega)
    nonzero (by simpa using step)

theorem sEqualsQFirstOutputNumerator_zero_step
    (base Q r deleted : Nat)
    (d1 : deleted < Q - 1) (d2 : deleted < 2 * Q - 1)
    (d3 : deleted < 3 * Q - 1) (dr2 : deleted < r - 2 * Q - 1)
    (dr : deleted < r - 1) :
    sEqualsQFirstOutputNumerator base Q r deleted =
      (base : Int) *
        sEqualsQFirstOutputNumerator base Q r (deleted + 1) := by
  have e1 : Q - 1 - deleted = Q - 1 - (deleted + 1) + 1 := by omega
  have e2 : 2 * Q - 1 - deleted =
      2 * Q - 1 - (deleted + 1) + 1 := by omega
  have e3 : 3 * Q - 1 - deleted =
      3 * Q - 1 - (deleted + 1) + 1 := by omega
  have er2 : r - 2 * Q - 1 - deleted =
      r - 2 * Q - 1 - (deleted + 1) + 1 := by omega
  have er : r - 1 - deleted = r - 1 - (deleted + 1) + 1 := by omega
  unfold sEqualsQFirstOutputNumerator
  rw [e1, e2, e3, er2, er, Int.pow_succ, Int.pow_succ, Int.pow_succ,
    Int.pow_succ, Int.pow_succ]
  grind

theorem sEqualsQFirstOutputState_delete_zero
    (base Q r deleted : Nat) (baseAtLeastTwo : 2 ≤ base)
    (QPositive : 0 < Q) (rPositive : 0 < r)
    (d1 : deleted < Q - 1) (d2 : deleted < 2 * Q - 1)
    (d3 : deleted < 3 * Q - 1) (dr2 : deleted < r - 2 * Q - 1)
    (dr : deleted < r - 1) :
    deleteDigit (base : Rat) 0
        (sEqualsQFirstOutputState base Q r deleted) =
      sEqualsQFirstOutputState base Q r (deleted + 1) := by
  have notDivisible := candidateDenominator_not_dvd base Q r Q
    baseAtLeastTwo QPositive rPositive QPositive
  have nonzero : candidateDenominator base Q r Q ≠ 0 :=
    fun zero => notDivisible (by rw [zero]; exact Int.dvd_zero _)
  have step := sEqualsQFirstOutputNumerator_zero_step base Q r deleted
    d1 d2 d3 dr2 dr
  simpa [sEqualsQFirstOutputState] using delete_integer_fraction base 0
    (sEqualsQFirstOutputNumerator base Q r deleted)
    (candidateDenominator base Q r Q)
    (sEqualsQFirstOutputNumerator base Q r (deleted + 1)) (by omega)
    nonzero (by simpa using step)

theorem sEqualsTwoQSecondOutputNumerator_zero_step
    (base Q r deleted : Nat)
    (d1 : deleted < Q - 1) (d2 : deleted < 2 * Q - 1)
    (d3 : deleted < 3 * Q - 1) (dr2 : deleted < r - 2 * Q - 1)
    (drq : deleted < r - Q - 1) (dr : deleted < r - 1) :
    sEqualsTwoQSecondOutputNumerator base Q r deleted =
      (base : Int) *
        sEqualsTwoQSecondOutputNumerator base Q r (deleted + 1) := by
  have e1 : Q - 1 - deleted = Q - 1 - (deleted + 1) + 1 := by omega
  have e2 : 2 * Q - 1 - deleted =
      2 * Q - 1 - (deleted + 1) + 1 := by omega
  have e3 : 3 * Q - 1 - deleted =
      3 * Q - 1 - (deleted + 1) + 1 := by omega
  have er2 : r - 2 * Q - 1 - deleted =
      r - 2 * Q - 1 - (deleted + 1) + 1 := by omega
  have erq : r - Q - 1 - deleted =
      r - Q - 1 - (deleted + 1) + 1 := by omega
  have er : r - 1 - deleted = r - 1 - (deleted + 1) + 1 := by omega
  unfold sEqualsTwoQSecondOutputNumerator
  rw [e1, e2, e3, er2, erq, er, Int.pow_succ, Int.pow_succ,
    Int.pow_succ, Int.pow_succ, Int.pow_succ, Int.pow_succ]
  grind

theorem sEqualsTwoQSecondOutputState_delete_zero
    (base Q r deleted : Nat) (baseAtLeastTwo : 2 ≤ base)
    (QPositive : 0 < Q) (rPositive : 0 < r)
    (d1 : deleted < Q - 1) (d2 : deleted < 2 * Q - 1)
    (d3 : deleted < 3 * Q - 1) (dr2 : deleted < r - 2 * Q - 1)
    (drq : deleted < r - Q - 1) (dr : deleted < r - 1) :
    deleteDigit (base : Rat) 0
        (sEqualsTwoQSecondOutputState base Q r deleted) =
      sEqualsTwoQSecondOutputState base Q r (deleted + 1) := by
  have notDivisible := candidateDenominator_not_dvd base Q r (2 * Q)
    baseAtLeastTwo QPositive rPositive (by omega)
  have nonzero : candidateDenominator base Q r (2 * Q) ≠ 0 :=
    fun zero => notDivisible (by rw [zero]; exact Int.dvd_zero _)
  have step := sEqualsTwoQSecondOutputNumerator_zero_step base Q r deleted
    d1 d2 d3 dr2 drq dr
  simpa [sEqualsTwoQSecondOutputState] using delete_integer_fraction base 0
    (sEqualsTwoQSecondOutputNumerator base Q r deleted)
    (candidateDenominator base Q r (2 * Q))
    (sEqualsTwoQSecondOutputNumerator base Q r (deleted + 1)) (by omega)
    nonzero (by simpa using step)

theorem candidate_zero_residue
    (base Q r s deleted : Nat)
    (dQ : deleted < Q - 1) (dr : deleted < r - 1)
    (ds : deleted < s - 1) :
    (base : Int) ∣ candidateNumerator base Q r s deleted := by
  rcases base_dvd_positive_power base (Q - 1 - deleted) (by omega) with
    ⟨f1, e1⟩
  rcases base_dvd_positive_power base (2 * Q - 1 - deleted) (by omega) with
    ⟨f2, e2⟩
  rcases base_dvd_positive_power base (3 * Q - 1 - deleted) (by omega) with
    ⟨f3, e3⟩
  rcases base_dvd_positive_power base (r - 1 - deleted) (by omega) with
    ⟨fr, er⟩
  rcases base_dvd_positive_power base (s - 1 - deleted) (by omega) with
    ⟨fs, es⟩
  refine ⟨f1 + f2 + f3 - fr - fs, ?_⟩
  unfold candidateNumerator
  rw [e1, e2, e3, er, es]
  grind

theorem sEqualsQCandidate_zero_residue
    (base Q r deleted : Nat)
    (dTwoQ : deleted < 2 * Q - 1) (dr : deleted < r - 1) :
    (base : Int) ∣ sEqualsQCandidateNumerator base Q r deleted := by
  rcases base_dvd_positive_power base (2 * Q - 1 - deleted) (by omega) with
    ⟨f2, e2⟩
  rcases base_dvd_positive_power base (3 * Q - 1 - deleted) (by omega) with
    ⟨f3, e3⟩
  rcases base_dvd_positive_power base (r - 1 - deleted) (by omega) with
    ⟨fr, er⟩
  refine ⟨f2 + f3 - fr, ?_⟩
  unfold sEqualsQCandidateNumerator
  rw [e2, e3, er]
  grind

theorem generalFirstOutput_zero_residue
    (base Q r s deleted : Nat)
    (dQ : deleted < Q - 1) (drq : deleted < r - Q - 1)
    (dsq : deleted < s - Q - 1) :
    (base : Int) ∣ generalFirstOutputNumerator base Q r s deleted := by
  rcases base_dvd_positive_power base (Q - 1 - deleted) (by omega) with
    ⟨f1, e1⟩
  rcases base_dvd_positive_power base (2 * Q - 1 - deleted) (by omega) with
    ⟨f2, e2⟩
  rcases base_dvd_positive_power base (3 * Q - 1 - deleted) (by omega) with
    ⟨f3, e3⟩
  rcases base_dvd_positive_power base (r - Q - 1 - deleted) (by omega) with
    ⟨frq, erq⟩
  rcases base_dvd_positive_power base (s - Q - 1 - deleted) (by omega) with
    ⟨fsq, esq⟩
  rcases base_dvd_positive_power base (r - 1 - deleted) (by omega) with
    ⟨fr, er⟩
  rcases base_dvd_positive_power base (s - 1 - deleted) (by omega) with
    ⟨fs, es⟩
  refine ⟨2 * f1 + 2 * f2 + f3 - frq - fsq - fr - fs, ?_⟩
  unfold generalFirstOutputNumerator
  rw [e1, e2, e3, erq, esq, er, es]
  grind

theorem sEqualsQFirstOutput_zero_residue
    (base Q r deleted : Nat)
    (dQ : deleted < Q - 1) (dr2 : deleted < r - 2 * Q - 1) :
    (base : Int) ∣ sEqualsQFirstOutputNumerator base Q r deleted := by
  rcases base_dvd_positive_power base (Q - 1 - deleted) (by omega) with
    ⟨f1, e1⟩
  rcases base_dvd_positive_power base (2 * Q - 1 - deleted) (by omega) with
    ⟨f2, e2⟩
  rcases base_dvd_positive_power base (3 * Q - 1 - deleted) (by omega) with
    ⟨f3, e3⟩
  rcases base_dvd_positive_power base (r - 2 * Q - 1 - deleted) (by omega)
      with ⟨fr2, er2⟩
  rcases base_dvd_positive_power base (r - 1 - deleted) (by omega) with
    ⟨fr, er⟩
  refine ⟨f1 + f2 + f3 - fr2 - fr, ?_⟩
  unfold sEqualsQFirstOutputNumerator
  rw [e1, e2, e3, er2, er]
  grind

theorem sEqualsTwoQSecondOutput_zero_residue
    (base Q r deleted : Nat)
    (dQ : deleted < Q - 1) (dr2 : deleted < r - 2 * Q - 1) :
    (base : Int) ∣
      sEqualsTwoQSecondOutputNumerator base Q r deleted := by
  rcases base_dvd_positive_power base (Q - 1 - deleted) (by omega) with
    ⟨f1, e1⟩
  rcases base_dvd_positive_power base (2 * Q - 1 - deleted) (by omega) with
    ⟨f2, e2⟩
  rcases base_dvd_positive_power base (3 * Q - 1 - deleted) (by omega) with
    ⟨f3, e3⟩
  rcases base_dvd_positive_power base (r - 2 * Q - 1 - deleted) (by omega)
      with ⟨fr2, er2⟩
  rcases base_dvd_positive_power base (r - Q - 1 - deleted) (by omega) with
    ⟨frq, erq⟩
  rcases base_dvd_positive_power base (r - 1 - deleted) (by omega) with
    ⟨fr, er⟩
  refine ⟨2 * f1 + f2 + f3 - fr2 - frq - fr, ?_⟩
  unfold sEqualsTwoQSecondOutputNumerator
  rw [e1, e2, e3, er2, erq, er]
  grind

/-- If `s<Q`, the first validator sees `-1`. -/
theorem first_marker_s_below_Q
    (base Q r s : Nat) (QPositive : 0 < Q) (sPositive : 0 < s)
    (sBelowQ : s < Q) (sBelowR : s < r) :
    (base : Int) ∣
      candidateNumerator base Q r s (s - 1) -
        (-1) * candidateDenominator base Q r s := by
  rcases base_dvd_positive_power base (Q - s) (by omega) with ⟨f1, e1⟩
  rcases base_dvd_positive_power base (2 * Q - s) (by omega) with ⟨f2, e2⟩
  rcases base_dvd_positive_power base (3 * Q - s) (by omega) with ⟨f3, e3⟩
  rcases base_dvd_positive_power base (r - s) (by omega) with ⟨frs, ers⟩
  rcases base_dvd_positive_power base Q QPositive with ⟨fq, eq⟩
  rcases base_dvd_positive_power base (2 * Q) (by omega) with ⟨fq2, eq2⟩
  rcases base_dvd_positive_power base (3 * Q) (by omega) with ⟨fq3, eq3⟩
  rcases base_dvd_positive_power base r (by omega) with ⟨fr, er⟩
  rcases base_dvd_positive_power base s sPositive with ⟨fs, es⟩
  refine ⟨f1 + f2 + f3 - frs - fq - fq2 - fq3 + fr + fs, ?_⟩
  unfold candidateNumerator candidateDenominator
  rw [show Q - 1 - (s - 1) = Q - s by omega,
    show 2 * Q - 1 - (s - 1) = 2 * Q - s by omega,
    show 3 * Q - 1 - (s - 1) = 3 * Q - s by omega,
    show r - 1 - (s - 1) = r - s by omega,
    show s - 1 - (s - 1) = 0 by omega, Int.pow_zero,
    e1, e2, e3, ers, eq, eq2, eq3, er, es]
  grind

/-- On `s=Q` and `r<2Q`, cancellation of the `q` terms leaves residue
`-1` at exponent `r`. -/
theorem first_marker_s_eq_Q_r_below_twoQ
    (base Q r : Nat) (QPositive : 0 < Q)
    (QBelowR : Q < r) (rBelowTwoQ : r < 2 * Q) :
    (base : Int) ∣
      candidateNumerator base Q r Q (r - 1) -
        (-1) * candidateDenominator base Q r Q := by
  rcases base_dvd_positive_power base (2 * Q - r) (by omega) with
    ⟨f2, e2⟩
  rcases base_dvd_positive_power base (3 * Q - r) (by omega) with
    ⟨f3, e3⟩
  rcases base_dvd_positive_power base (2 * Q) (by omega) with
    ⟨fq2, eq2⟩
  rcases base_dvd_positive_power base (3 * Q) (by omega) with
    ⟨fq3, eq3⟩
  rcases base_dvd_positive_power base r (by omega) with ⟨fr, er⟩
  refine ⟨f2 + f3 - fq2 - fq3 + fr, ?_⟩
  unfold candidateNumerator candidateDenominator
  rw [show Q - 1 - (r - 1) = 0 by omega,
    show 2 * Q - 1 - (r - 1) = 2 * Q - r by omega,
    show 3 * Q - 1 - (r - 1) = 3 * Q - r by omega,
    show r - 1 - (r - 1) = 0 by omega,
    Int.pow_zero, e2, e3, eq2, eq3, er]
  grind

/-- The unique accepted pair is `(r,s)=(2Q,Q)`, where the candidate is
the unary representative of `z_(3Q-1)`. -/
theorem accepted_candidate_integer (base Q : Nat) :
    candidateNumerator base Q (2 * Q) Q 0 =
        (base : Int) ^ (3 * Q - 1) ∧
      candidateDenominator base Q (2 * Q) Q =
        1 - (base : Int) ^ (3 * Q) := by
  constructor
  · unfold candidateNumerator
    simp only [Nat.sub_zero]
    grind
  · unfold candidateDenominator
    grind

theorem accepted_candidate_state
    (base Q : Nat) (QPositive : 0 < Q) :
    candidateState base Q (2 * Q) Q 0 = unaryCode base (3 * Q - 1) := by
  obtain ⟨numeratorEq, denominatorEq⟩ := accepted_candidate_integer base Q
  unfold candidateState
  rw [numeratorEq, denominatorEq, unaryCode_eq]
  simp only [Rat.intCast_pow, Rat.intCast_natCast, Rat.intCast_sub,
    Rat.intCast_one]
  rw [show 3 * Q - 1 + 1 = 3 * Q by omega]

/-- For `Q<s`, the first validator reaches the expected residue one
after `Q-1` zeroes. -/
theorem first_marker_s_above_Q
    (base Q r s : Nat) (QPositive : 0 < Q)
    (QBelowS : Q < s) (sBelowR : s < r) :
    (base : Int) ∣
      candidateNumerator base Q r s (Q - 1) -
        candidateDenominator base Q r s := by
  rcases base_dvd_positive_power base Q QPositive with ⟨fq, eq⟩
  rcases base_dvd_positive_power base (2 * Q) (by omega) with ⟨fq2, eq2⟩
  rcases base_dvd_positive_power base (3 * Q) (by omega) with ⟨fq3, eq3⟩
  rcases base_dvd_positive_power base (r - Q) (by omega) with ⟨frq, erq⟩
  rcases base_dvd_positive_power base (s - Q) (by omega) with ⟨fsq, esq⟩
  rcases base_dvd_positive_power base r (by omega) with ⟨fr, er⟩
  rcases base_dvd_positive_power base s (by omega) with ⟨fs, es⟩
  refine ⟨2 * fq + 2 * fq2 + fq3 - frq - fsq - fr - fs, ?_⟩
  unfold candidateNumerator candidateDenominator
  rw [show Q - 1 - (Q - 1) = 0 by omega,
    show 2 * Q - 1 - (Q - 1) = Q by omega,
    show 3 * Q - 1 - (Q - 1) = 2 * Q by omega,
    show r - 1 - (Q - 1) = r - Q by omega,
    show s - 1 - (Q - 1) = s - Q by omega,
    Int.pow_zero, eq, eq2, eq3, erq, esq, er, es]
  grind

theorem first_marker_quotient_s_above_Q
    (base Q r s : Nat) (QPositive : 0 < Q)
    (QBelowS : Q < s) (sBelowR : s < r) :
    candidateNumerator base Q r s (Q - 1) -
        candidateDenominator base Q r s =
      (base : Int) * generalFirstOutputNumerator base Q r s 0 := by
  have qSucc : (base : Int) ^ Q =
      (base : Int) ^ (Q - 1) * (base : Int) := by
    calc
      (base : Int) ^ Q = (base : Int) ^ (Q - 1 + 1) := by
        congr 1 <;> omega
      _ = _ := by rw [Int.pow_succ]
  have q2Succ : (base : Int) ^ (2 * Q) =
      (base : Int) ^ (2 * Q - 1) * (base : Int) := by
    calc
      (base : Int) ^ (2 * Q) = (base : Int) ^ (2 * Q - 1 + 1) := by
        congr 1 <;> omega
      _ = _ := by rw [Int.pow_succ]
  have q3Succ : (base : Int) ^ (3 * Q) =
      (base : Int) ^ (3 * Q - 1) * (base : Int) := by
    calc
      (base : Int) ^ (3 * Q) = (base : Int) ^ (3 * Q - 1 + 1) := by
        congr 1 <;> omega
      _ = _ := by rw [Int.pow_succ]
  have rqSucc : (base : Int) ^ (r - Q) =
      (base : Int) ^ (r - Q - 1) * (base : Int) := by
    calc
      (base : Int) ^ (r - Q) =
          (base : Int) ^ (r - Q - 1 + 1) := by congr 1 <;> omega
      _ = _ := by rw [Int.pow_succ]
  have sqSucc : (base : Int) ^ (s - Q) =
      (base : Int) ^ (s - Q - 1) * (base : Int) := by
    calc
      (base : Int) ^ (s - Q) =
          (base : Int) ^ (s - Q - 1 + 1) := by congr 1 <;> omega
      _ = _ := by rw [Int.pow_succ]
  have rSucc : (base : Int) ^ r =
      (base : Int) ^ (r - 1) * (base : Int) := by
    calc
      (base : Int) ^ r = (base : Int) ^ (r - 1 + 1) := by
        congr 1 <;> omega
      _ = _ := by rw [Int.pow_succ]
  have sSucc : (base : Int) ^ s =
      (base : Int) ^ (s - 1) * (base : Int) := by
    calc
      (base : Int) ^ s = (base : Int) ^ (s - 1 + 1) := by
        congr 1 <;> omega
      _ = _ := by rw [Int.pow_succ]
  unfold candidateNumerator candidateDenominator
    generalFirstOutputNumerator
  rw [show Q - 1 - (Q - 1) = 0 by omega,
    show 2 * Q - 1 - (Q - 1) = Q by omega,
    show 3 * Q - 1 - (Q - 1) = 2 * Q by omega,
    show r - 1 - (Q - 1) = r - Q by omega,
    show s - 1 - (Q - 1) = s - Q by omega,
    Int.pow_zero, qSucc, q2Succ, q3Succ, rqSucc, sqSucc, rSucc, sSucc]
  simp only [Nat.sub_zero]
  grind

/-- If `s=Q` and `2Q<r<3Q`, the first validator has length `2Q`
and reaches residue one. -/
theorem first_marker_s_eq_Q_r_above_twoQ
    (base Q r : Nat) (QPositive : 0 < Q)
    (twoQBelowR : 2 * Q < r) (rBelowThreeQ : r < 3 * Q) :
    (base : Int) ∣
      candidateNumerator base Q r Q (2 * Q - 1) -
        candidateDenominator base Q r Q := by
  rcases base_dvd_positive_power base Q QPositive with ⟨fq, eq⟩
  rcases base_dvd_positive_power base (r - 2 * Q) (by omega) with
    ⟨fr2, er2⟩
  rcases base_dvd_positive_power base (2 * Q) (by omega) with
    ⟨fq2, eq2⟩
  rcases base_dvd_positive_power base (3 * Q) (by omega) with
    ⟨fq3, eq3⟩
  rcases base_dvd_positive_power base r (by omega) with ⟨fr, er⟩
  refine ⟨fq - fr2 + fq2 + fq3 - fr, ?_⟩
  unfold candidateNumerator candidateDenominator
  rw [show Q - 1 - (2 * Q - 1) = 0 by omega,
    show 2 * Q - 1 - (2 * Q - 1) = 0 by omega,
    show 3 * Q - 1 - (2 * Q - 1) = Q by omega,
    show r - 1 - (2 * Q - 1) = r - 2 * Q by omega,
    Int.pow_zero, eq, er2, eq2, eq3, er]
  grind

theorem first_marker_quotient_s_eq_Q_r_above_twoQ
    (base Q r : Nat) (QPositive : 0 < Q)
    (twoQBelowR : 2 * Q < r) (rBelowThreeQ : r < 3 * Q) :
    candidateNumerator base Q r Q (2 * Q - 1) -
        candidateDenominator base Q r Q =
      (base : Int) * sEqualsQFirstOutputNumerator base Q r 0 := by
  have qSucc : (base : Int) ^ Q =
      (base : Int) ^ (Q - 1) * (base : Int) := by
    calc
      (base : Int) ^ Q = (base : Int) ^ (Q - 1 + 1) := by
        congr 1 <;> omega
      _ = _ := by rw [Int.pow_succ]
  have q2Succ : (base : Int) ^ (2 * Q) =
      (base : Int) ^ (2 * Q - 1) * (base : Int) := by
    calc
      (base : Int) ^ (2 * Q) = (base : Int) ^ (2 * Q - 1 + 1) := by
        congr 1 <;> omega
      _ = _ := by rw [Int.pow_succ]
  have q3Succ : (base : Int) ^ (3 * Q) =
      (base : Int) ^ (3 * Q - 1) * (base : Int) := by
    calc
      (base : Int) ^ (3 * Q) = (base : Int) ^ (3 * Q - 1 + 1) := by
        congr 1 <;> omega
      _ = _ := by rw [Int.pow_succ]
  have gapSucc : (base : Int) ^ (r - 2 * Q) =
      (base : Int) ^ (r - 2 * Q - 1) * (base : Int) := by
    calc
      (base : Int) ^ (r - 2 * Q) =
          (base : Int) ^ (r - 2 * Q - 1 + 1) := by congr 1 <;> omega
      _ = _ := by rw [Int.pow_succ]
  have rSucc : (base : Int) ^ r =
      (base : Int) ^ (r - 1) * (base : Int) := by
    calc
      (base : Int) ^ r = (base : Int) ^ (r - 1 + 1) := by
        congr 1 <;> omega
      _ = _ := by rw [Int.pow_succ]
  unfold candidateNumerator candidateDenominator
    sEqualsQFirstOutputNumerator
  rw [show Q - 1 - (2 * Q - 1) = 0 by omega,
    show 2 * Q - 1 - (2 * Q - 1) = 0 by omega,
    show 3 * Q - 1 - (2 * Q - 1) = Q by omega,
    show r - 1 - (2 * Q - 1) = r - 2 * Q by omega,
    Int.pow_zero, qSucc, q2Succ, q3Succ, gapSucc, rSucc]
  simp only [Nat.sub_zero]
  grind

/-- In the remaining part of the `s=Q` case, the second validator
rejects residue `-1`. -/
theorem second_marker_s_eq_Q_r_above_twoQ
    (base Q r : Nat) (QPositive : 0 < Q)
    (twoQBelowR : 2 * Q < r) (rBelowThreeQ : r < 3 * Q) :
    (base : Int) ∣
      sEqualsQFirstOutputNumerator base Q r (r - 2 * Q - 1) -
        (-1) * candidateDenominator base Q r Q := by
  rcases base_dvd_positive_power base (3 * Q - r) (by omega) with
    ⟨f1, e1⟩
  rcases base_dvd_positive_power base (4 * Q - r) (by omega) with
    ⟨f2, e2⟩
  rcases base_dvd_positive_power base (5 * Q - r) (by omega) with
    ⟨f3, e3⟩
  rcases base_dvd_positive_power base (2 * Q) (by omega) with
    ⟨fq2, eq2⟩
  rcases base_dvd_positive_power base (3 * Q) (by omega) with
    ⟨fq3, eq3⟩
  rcases base_dvd_positive_power base r (by omega) with ⟨fr, er⟩
  refine ⟨f1 + f2 + f3 - 2 * fq2 - fq3 + fr, ?_⟩
  unfold sEqualsQFirstOutputNumerator candidateDenominator
  rw [show Q - 1 - (r - 2 * Q - 1) = 3 * Q - r by omega,
    show 2 * Q - 1 - (r - 2 * Q - 1) = 4 * Q - r by omega,
    show 3 * Q - 1 - (r - 2 * Q - 1) = 5 * Q - r by omega,
    show r - 2 * Q - 1 - (r - 2 * Q - 1) = 0 by omega,
    show r - 1 - (r - 2 * Q - 1) = 2 * Q by omega,
    Int.pow_zero, e1, e2, e3, eq2, eq3, er]
  grind

/-- If `Q<s<2Q`, the second validator rejects residue `-1`. -/
theorem second_marker_s_between_Q_twoQ
    (base Q r s : Nat) (QPositive : 0 < Q)
    (QBelowS : Q < s) (sBelowTwoQ : s < 2 * Q)
    (sBelowR : s < r) :
    (base : Int) ∣
      generalFirstOutputNumerator base Q r s (s - Q - 1) -
        (-1) * candidateDenominator base Q r s := by
  rcases base_dvd_positive_power base (2 * Q - s) (by omega) with
    ⟨f1, e1⟩
  rcases base_dvd_positive_power base (3 * Q - s) (by omega) with
    ⟨f2, e2⟩
  rcases base_dvd_positive_power base (4 * Q - s) (by omega) with
    ⟨f3, e3⟩
  rcases base_dvd_positive_power base (r - s) (by omega) with
    ⟨frs, ers⟩
  rcases base_dvd_positive_power base (r + Q - s) (by omega) with
    ⟨frqs, erqs⟩
  rcases base_dvd_positive_power base Q QPositive with ⟨fq, eq⟩
  rcases base_dvd_positive_power base (2 * Q) (by omega) with ⟨fq2, eq2⟩
  rcases base_dvd_positive_power base (3 * Q) (by omega) with ⟨fq3, eq3⟩
  rcases base_dvd_positive_power base r (by omega) with ⟨fr, er⟩
  rcases base_dvd_positive_power base s (by omega) with ⟨fs, es⟩
  refine ⟨2 * f1 + 2 * f2 + f3 - frs - frqs - fq - fq - fq2 -
      fq3 + fr + fs, ?_⟩
  unfold generalFirstOutputNumerator candidateDenominator
  rw [show Q - 1 - (s - Q - 1) = 2 * Q - s by omega,
    show 2 * Q - 1 - (s - Q - 1) = 3 * Q - s by omega,
    show 3 * Q - 1 - (s - Q - 1) = 4 * Q - s by omega,
    show r - Q - 1 - (s - Q - 1) = r - s by omega,
    show s - Q - 1 - (s - Q - 1) = 0 by omega,
    show r - 1 - (s - Q - 1) = r + Q - s by omega,
    show s - 1 - (s - Q - 1) = Q by omega,
    Int.pow_zero, e1, e2, e3, ers, erqs, eq, eq2, eq3, er, es]
  grind

/-- If `2Q<s`, the second validator sees residue two and rejects. -/
theorem second_marker_s_above_twoQ
    (base Q r s : Nat) (QPositive : 0 < Q)
    (twoQBelowS : 2 * Q < s) (sBelowR : s < r) :
    (base : Int) ∣
      generalFirstOutputNumerator base Q r s (Q - 1) -
        2 * candidateDenominator base Q r s := by
  rcases base_dvd_positive_power base Q QPositive with ⟨fq, eq⟩
  rcases base_dvd_positive_power base (2 * Q) (by omega) with ⟨fq2, eq2⟩
  rcases base_dvd_positive_power base (3 * Q) (by omega) with ⟨fq3, eq3⟩
  rcases base_dvd_positive_power base (r - 2 * Q) (by omega) with
    ⟨fr2, er2⟩
  rcases base_dvd_positive_power base (s - 2 * Q) (by omega) with
    ⟨fs2, es2⟩
  rcases base_dvd_positive_power base (r - Q) (by omega) with
    ⟨frq, erq⟩
  rcases base_dvd_positive_power base (s - Q) (by omega) with
    ⟨fsq, esq⟩
  rcases base_dvd_positive_power base r (by omega) with ⟨fr, er⟩
  rcases base_dvd_positive_power base s (by omega) with ⟨fs, es⟩
  refine ⟨4 * fq + 3 * fq2 + 2 * fq3 - fr2 - fs2 - frq - fsq -
      2 * fr - 2 * fs, ?_⟩
  unfold generalFirstOutputNumerator candidateDenominator
  rw [show Q - 1 - (Q - 1) = 0 by omega,
    show 2 * Q - 1 - (Q - 1) = Q by omega,
    show 3 * Q - 1 - (Q - 1) = 2 * Q by omega,
    show r - Q - 1 - (Q - 1) = r - 2 * Q by omega,
    show s - Q - 1 - (Q - 1) = s - 2 * Q by omega,
    show r - 1 - (Q - 1) = r - Q by omega,
    show s - 1 - (Q - 1) = s - Q by omega,
    Int.pow_zero, eq, eq2, eq3, er2, es2, erq, esq, er, es]
  grind

/-- At the boundary `s=2Q`, the second validator reaches residue one. -/
theorem second_marker_s_eq_twoQ
    (base Q r : Nat) (QPositive : 0 < Q)
    (twoQBelowR : 2 * Q < r) :
    (base : Int) ∣
      generalFirstOutputNumerator base Q r (2 * Q) (Q - 1) -
        candidateDenominator base Q r (2 * Q) := by
  rcases base_dvd_positive_power base Q QPositive with ⟨fq, eq⟩
  rcases base_dvd_positive_power base (2 * Q) (by omega) with ⟨fq2, eq2⟩
  rcases base_dvd_positive_power base (3 * Q) (by omega) with ⟨fq3, eq3⟩
  rcases base_dvd_positive_power base (r - 2 * Q) (by omega) with
    ⟨fr2, er2⟩
  rcases base_dvd_positive_power base (r - Q) (by omega) with
    ⟨frq, erq⟩
  rcases base_dvd_positive_power base r (by omega) with ⟨fr, er⟩
  refine ⟨2 * fq + fq2 + fq3 - fr2 - frq - fr, ?_⟩
  unfold generalFirstOutputNumerator candidateDenominator
  rw [show Q - 1 - (Q - 1) = 0 by omega,
    show 2 * Q - 1 - (Q - 1) = Q by omega,
    show 3 * Q - 1 - (Q - 1) = 2 * Q by omega,
    show r - Q - 1 - (Q - 1) = r - 2 * Q by omega,
    show 2 * Q - Q - 1 - (Q - 1) = 0 by omega,
    show r - 1 - (Q - 1) = r - Q by omega,
    Int.pow_zero, eq, eq2, eq3, er2, erq, er]
  grind

theorem second_marker_quotient_s_eq_twoQ
    (base Q r : Nat) (QPositive : 0 < Q)
    (twoQBelowR : 2 * Q < r) :
    generalFirstOutputNumerator base Q r (2 * Q) (Q - 1) -
        candidateDenominator base Q r (2 * Q) =
      (base : Int) * sEqualsTwoQSecondOutputNumerator base Q r 0 := by
  have qSucc : (base : Int) ^ Q =
      (base : Int) ^ (Q - 1) * (base : Int) := by
    calc
      (base : Int) ^ Q = (base : Int) ^ (Q - 1 + 1) := by
        congr 1 <;> omega
      _ = _ := by rw [Int.pow_succ]
  have q2Succ : (base : Int) ^ (2 * Q) =
      (base : Int) ^ (2 * Q - 1) * (base : Int) := by
    calc
      (base : Int) ^ (2 * Q) = (base : Int) ^ (2 * Q - 1 + 1) := by
        congr 1 <;> omega
      _ = _ := by rw [Int.pow_succ]
  have q3Succ : (base : Int) ^ (3 * Q) =
      (base : Int) ^ (3 * Q - 1) * (base : Int) := by
    calc
      (base : Int) ^ (3 * Q) = (base : Int) ^ (3 * Q - 1 + 1) := by
        congr 1 <;> omega
      _ = _ := by rw [Int.pow_succ]
  have r2Succ : (base : Int) ^ (r - 2 * Q) =
      (base : Int) ^ (r - 2 * Q - 1) * (base : Int) := by
    calc
      (base : Int) ^ (r - 2 * Q) =
          (base : Int) ^ (r - 2 * Q - 1 + 1) := by congr 1 <;> omega
      _ = _ := by rw [Int.pow_succ]
  have rqSucc : (base : Int) ^ (r - Q) =
      (base : Int) ^ (r - Q - 1) * (base : Int) := by
    calc
      (base : Int) ^ (r - Q) =
          (base : Int) ^ (r - Q - 1 + 1) := by congr 1 <;> omega
      _ = _ := by rw [Int.pow_succ]
  have rSucc : (base : Int) ^ r =
      (base : Int) ^ (r - 1) * (base : Int) := by
    calc
      (base : Int) ^ r = (base : Int) ^ (r - 1 + 1) := by
        congr 1 <;> omega
      _ = _ := by rw [Int.pow_succ]
  unfold generalFirstOutputNumerator candidateDenominator
    sEqualsTwoQSecondOutputNumerator
  rw [show Q - 1 - (Q - 1) = 0 by omega,
    show 2 * Q - 1 - (Q - 1) = Q by omega,
    show 3 * Q - 1 - (Q - 1) = 2 * Q by omega,
    show r - Q - 1 - (Q - 1) = r - 2 * Q by omega,
    show 2 * Q - Q - 1 - (Q - 1) = 0 by omega,
    show r - 1 - (Q - 1) = r - Q by omega,
    Int.pow_zero, qSucc, q2Succ, q3Succ, r2Succ, rqSucc, rSucc]
  simp only [Nat.sub_zero]
  grind

/-- At `s=2Q`, the third validator rejects residue `-1`. -/
theorem third_marker_s_eq_twoQ
    (base Q r : Nat) (QPositive : 0 < Q)
    (twoQBelowR : 2 * Q < r) (rBelowThreeQ : r < 3 * Q) :
    (base : Int) ∣
      sEqualsTwoQSecondOutputNumerator base Q r (r - 2 * Q - 1) -
        (-1) * candidateDenominator base Q r (2 * Q) := by
  rcases base_dvd_positive_power base (3 * Q - r) (by omega) with
    ⟨f1, e1⟩
  rcases base_dvd_positive_power base (4 * Q - r) (by omega) with
    ⟨f2, e2⟩
  rcases base_dvd_positive_power base (5 * Q - r) (by omega) with
    ⟨f3, e3⟩
  rcases base_dvd_positive_power base Q QPositive with ⟨fq, eq⟩
  rcases base_dvd_positive_power base (2 * Q) (by omega) with ⟨fq2, eq2⟩
  rcases base_dvd_positive_power base (3 * Q) (by omega) with ⟨fq3, eq3⟩
  rcases base_dvd_positive_power base r (by omega) with ⟨fr, er⟩
  refine ⟨2 * f1 + f2 + f3 - 2 * fq - fq2 - fq3 + fr, ?_⟩
  unfold sEqualsTwoQSecondOutputNumerator candidateDenominator
  rw [show Q - 1 - (r - 2 * Q - 1) = 3 * Q - r by omega,
    show 2 * Q - 1 - (r - 2 * Q - 1) = 4 * Q - r by omega,
    show 3 * Q - 1 - (r - 2 * Q - 1) = 5 * Q - r by omega,
    show r - 2 * Q - 1 - (r - 2 * Q - 1) = 0 by omega,
    show r - Q - 1 - (r - 2 * Q - 1) = Q by omega,
    show r - 1 - (r - 2 * Q - 1) = 2 * Q by omega,
    Int.pow_zero, e1, e2, e3, eq, eq2, eq3, er]
  grind

theorem candidateState_delete_marker_above_Q
    (base Q r s : Nat) (baseAtLeastTwo : 2 ≤ base)
    (QPositive : 0 < Q) (QBelowS : Q < s) (sBelowR : s < r) :
    deleteDigit (base : Rat) 1
        (candidateState base Q r s (Q - 1)) =
      generalFirstOutputState base Q r s 0 := by
  have notDivisible := candidateDenominator_not_dvd base Q r s
    baseAtLeastTwo QPositive (by omega) (by omega)
  have nonzero : candidateDenominator base Q r s ≠ 0 :=
    fun zero => notDivisible (by rw [zero]; exact Int.dvd_zero _)
  have difference := first_marker_quotient_s_above_Q base Q r s QPositive
    QBelowS sBelowR
  simpa [candidateState, generalFirstOutputState] using
    delete_integer_fraction base 1
      (candidateNumerator base Q r s (Q - 1))
      (candidateDenominator base Q r s)
      (generalFirstOutputNumerator base Q r s 0) (by omega) nonzero
      (by simpa using difference)

theorem sEqualsQCandidateState_delete_marker
    (base Q r : Nat) (baseAtLeastTwo : 2 ≤ base)
    (QPositive : 0 < Q) (twoQBelowR : 2 * Q < r)
    (rBelowThreeQ : r < 3 * Q) :
    deleteDigit (base : Rat) 1
        (sEqualsQCandidateState base Q r (2 * Q - 1)) =
      sEqualsQFirstOutputState base Q r 0 := by
  have notDivisible := candidateDenominator_not_dvd base Q r Q
    baseAtLeastTwo QPositive (by omega) QPositive
  have nonzero : candidateDenominator base Q r Q ≠ 0 :=
    fun zero => notDivisible (by rw [zero]; exact Int.dvd_zero _)
  have difference := first_marker_quotient_s_eq_Q_r_above_twoQ base Q r
    QPositive twoQBelowR rBelowThreeQ
  have numeratorEq :
      sEqualsQCandidateNumerator base Q r (2 * Q - 1) =
        candidateNumerator base Q r Q (2 * Q - 1) := by
    unfold sEqualsQCandidateNumerator candidateNumerator
    grind
  simpa [sEqualsQCandidateState, sEqualsQFirstOutputState] using
    delete_integer_fraction base 1
      (sEqualsQCandidateNumerator base Q r (2 * Q - 1))
      (candidateDenominator base Q r Q)
      (sEqualsQFirstOutputNumerator base Q r 0) (by omega) nonzero
      (by
        rw [numeratorEq]
        simpa using difference)

theorem generalFirstOutputState_delete_marker_s_eq_twoQ
    (base Q r : Nat) (baseAtLeastTwo : 2 ≤ base)
    (QPositive : 0 < Q) (twoQBelowR : 2 * Q < r) :
    deleteDigit (base : Rat) 1
        (generalFirstOutputState base Q r (2 * Q) (Q - 1)) =
      sEqualsTwoQSecondOutputState base Q r 0 := by
  have notDivisible := candidateDenominator_not_dvd base Q r (2 * Q)
    baseAtLeastTwo QPositive (by omega) (by omega)
  have nonzero : candidateDenominator base Q r (2 * Q) ≠ 0 :=
    fun zero => notDivisible (by rw [zero]; exact Int.dvd_zero _)
  have difference := second_marker_quotient_s_eq_twoQ base Q r QPositive
    twoQBelowR
  simpa [generalFirstOutputState, sEqualsTwoQSecondOutputState] using
    delete_integer_fraction base 1
      (generalFirstOutputNumerator base Q r (2 * Q) (Q - 1))
      (candidateDenominator base Q r (2 * Q))
      (sEqualsTwoQSecondOutputNumerator base Q r 0) (by omega) nonzero
      (by simpa using difference)

/-! ## Connection with the operational guessed prefixes -/

/-- The integer candidate representative is the rational candidate
`P/(p(1-P))`, expressed in the auxiliary coordinate `t=pz`. -/
theorem candidateState_auxiliary
    (base Q r s : Nat) (QPositive : 0 < Q)
    (rPositive : 0 < r) (sPositive : 0 < s) :
    let q : Rat := (base : Rat) ^ Q
    let R : Rat := (base : Rat) ^ r
    let S : Rat := (base : Rat) ^ s
    let polynomial : Rat := q + q ^ 2 + q ^ 3 - R - S
    (base : Rat) * candidateState base Q r s 0 =
      polynomial / (1 - polynomial) := by
  dsimp
  let q : Rat := (base : Rat) ^ Q
  let R : Rat := (base : Rat) ^ r
  let S : Rat := (base : Rat) ^ s
  let polynomial : Rat := q + q ^ 2 + q ^ 3 - R - S
  have qSucc : (base : Rat) ^ Q =
      (base : Rat) ^ (Q - 1) * (base : Rat) := by
    calc
      (base : Rat) ^ Q = (base : Rat) ^ (Q - 1 + 1) := by
        congr 1 <;> omega
      _ = _ := by rw [Rat.pow_succ]
  have q2Succ : (base : Rat) ^ (2 * Q) =
      (base : Rat) ^ (2 * Q - 1) * (base : Rat) := by
    calc
      (base : Rat) ^ (2 * Q) =
          (base : Rat) ^ (2 * Q - 1 + 1) := by congr 1 <;> omega
      _ = _ := by rw [Rat.pow_succ]
  have q3Succ : (base : Rat) ^ (3 * Q) =
      (base : Rat) ^ (3 * Q - 1) * (base : Rat) := by
    calc
      (base : Rat) ^ (3 * Q) =
          (base : Rat) ^ (3 * Q - 1 + 1) := by congr 1 <;> omega
      _ = _ := by rw [Rat.pow_succ]
  have rSucc : (base : Rat) ^ r =
      (base : Rat) ^ (r - 1) * (base : Rat) := by
    calc
      (base : Rat) ^ r = (base : Rat) ^ (r - 1 + 1) := by
        congr 1 <;> omega
      _ = _ := by rw [Rat.pow_succ]
  have sSucc : (base : Rat) ^ s =
      (base : Rat) ^ (s - 1) * (base : Rat) := by
    calc
      (base : Rat) ^ s = (base : Rat) ^ (s - 1 + 1) := by
        congr 1 <;> omega
      _ = _ := by rw [Rat.pow_succ]
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
  have cubePower : q ^ 3 = (base : Rat) ^ (3 * Q) := by
    rw [show 3 * Q = Q + Q + Q by omega]
    unfold q
    repeat' rw [Lean.Grind.Semiring.pow_add]
    grind
  unfold candidateState candidateNumerator candidateDenominator
  simp only [Nat.sub_zero, Rat.intCast_sub, Rat.intCast_add,
    Rat.intCast_pow, Rat.intCast_natCast, Rat.intCast_ofNat, Rat.div_def]
  rw [squarePower, cubePower]
  grind

/-- Every pair of admissible operational guesses produces exactly the
integer candidate to which the exhaustive residue classification applies. -/
theorem operational_candidate_eq
    (base Q r s : Nat) (baseAtLeastTwo : 2 ≤ base)
    (QPositive : 0 < Q) (sPositive : 0 < s)
    (sBelowR : s < r) (rBelowThreeQ : r < 3 * Q) :
    ContractionProjectionArithmetic.threeProjectionGeneralCandidate
        base (Q - 1) (3 * Q - r) (r - s) =
      candidateState base Q r s 0 := by
  have rPositive : 0 < r := by omega
  have firstGuessPositive : 0 < 3 * Q - r := by omega
  have firstGuessBelow :
      3 * Q - r < 3 * ((Q - 1) + 1) := by omega
  have secondGuessPositive : 0 < r - s := by omega
  have secondGuessBelow :
      r - s < 3 * ((Q - 1) + 1) - (3 * Q - r) := by omega
  have operationalAuxiliary :=
    ContractionProjectionArithmetic.threeProjectionGeneralCandidate_auxiliary
      base (Q - 1) (3 * Q - r) (r - s) baseAtLeastTwo
      firstGuessPositive firstGuessBelow secondGuessPositive secondGuessBelow
  have candidateAuxiliary := candidateState_auxiliary base Q r s QPositive
    rPositive sPositive
  have firstExponentEq : Q - 1 + 1 = Q := by omega
  have firstRemainingEq : 3 * Q - (3 * Q - r) = r := by omega
  have secondRemainingEq : r - (r - s) = s := by omega
  simp only [firstExponentEq, firstRemainingEq, secondRemainingEq] at operationalAuxiliary
  have productEq :
      (base : Rat) *
          ContractionProjectionArithmetic.threeProjectionGeneralCandidate
            base (Q - 1) (3 * Q - r) (r - s) =
        (base : Rat) * candidateState base Q r s 0 := by
    exact operationalAuxiliary.trans candidateAuxiliary.symm
  have baseNonzero : (base : Rat) ≠ 0 := by
    simpa using (show base ≠ 0 by omega)
  calc
    ContractionProjectionArithmetic.threeProjectionGeneralCandidate
        base (Q - 1) (3 * Q - r) (r - s) =
      ((base : Rat)⁻¹ * (base : Rat)) *
        ContractionProjectionArithmetic.threeProjectionGeneralCandidate
          base (Q - 1) (3 * Q - r) (r - s) := by
      rw [Rat.inv_mul_cancel (base : Rat) baseNonzero, Rat.one_mul]
    _ = (base : Rat)⁻¹ *
        ((base : Rat) *
          ContractionProjectionArithmetic.threeProjectionGeneralCandidate
            base (Q - 1) (3 * Q - r) (r - s)) := by rw [Rat.mul_assoc]
    _ = (base : Rat)⁻¹ *
        ((base : Rat) * candidateState base Q r s 0) := by rw [productEq]
    _ = ((base : Rat)⁻¹ * (base : Rat)) *
        candidateState base Q r s 0 := by rw [Rat.mul_assoc]
    _ = candidateState base Q r s 0 := by
      rw [Rat.inv_mul_cancel (base : Rat) baseNonzero, Rat.one_mul]

/-- The exhaustive outcome of the three validators.  Each rejection
constructor records the first validator that exposes a forbidden digit. -/
inductive ProjectionOutcome (base Q r s : Nat) : Prop where
  | firstRejectBelow
      (sBelowQ : s < Q)
      (residue : (base : Int) ∣
        candidateNumerator base Q r s (s - 1) -
          (-1) * candidateDenominator base Q r s)
  | firstRejectAtQ
      (sEqQ : s = Q) (rBelowTwoQ : r < 2 * Q)
      (residue : (base : Int) ∣
        candidateNumerator base Q r s (r - 1) -
          (-1) * candidateDenominator base Q r s)
  | accepted
      (sEqQ : s = Q) (rEqTwoQ : r = 2 * Q)
      (numeratorEq : candidateNumerator base Q r s 0 =
        (base : Int) ^ (3 * Q - 1))
      (denominatorEq : candidateDenominator base Q r s =
        1 - (base : Int) ^ (3 * Q))
  | secondRejectAtQ
      (sEqQ : s = Q) (twoQBelowR : 2 * Q < r)
      (residue : (base : Int) ∣
        sEqualsQFirstOutputNumerator base Q r (r - 2 * Q - 1) -
          (-1) * candidateDenominator base Q r s)
  | secondRejectBetween
      (QBelowS : Q < s) (sBelowTwoQ : s < 2 * Q)
      (residue : (base : Int) ∣
        generalFirstOutputNumerator base Q r s (s - Q - 1) -
          (-1) * candidateDenominator base Q r s)
  | thirdRejectAtTwoQ
      (sEqTwoQ : s = 2 * Q)
      (residue : (base : Int) ∣
        sEqualsTwoQSecondOutputNumerator base Q r (r - 2 * Q - 1) -
          (-1) * candidateDenominator base Q r s)
  | secondRejectAbove
      (twoQBelowS : 2 * Q < s)
      (residue : (base : Int) ∣
        generalFirstOutputNumerator base Q r s (Q - 1) -
          2 * candidateDenominator base Q r s)

/-- The five exponent regions in the manuscript, including the three
subcases on `s=Q`, exhaust every admissible pair `1 ≤ s < r < 3Q`. -/
theorem exhaustive_projection_outcome
    (base Q r s : Nat) (QPositive : 0 < Q)
    (sPositive : 0 < s) (sBelowR : s < r)
    (rBelowThreeQ : r < 3 * Q) :
    ProjectionOutcome base Q r s := by
  by_cases sBelowQ : s < Q
  · exact .firstRejectBelow sBelowQ
      (first_marker_s_below_Q base Q r s QPositive sPositive sBelowQ
        sBelowR)
  by_cases sEqQ : s = Q
  · by_cases rBelowTwoQ : r < 2 * Q
    · subst s
      exact .firstRejectAtQ rfl rBelowTwoQ
        (first_marker_s_eq_Q_r_below_twoQ base Q r QPositive (by omega)
          rBelowTwoQ)
    by_cases rEqTwoQ : r = 2 * Q
    · subst s
      subst r
      obtain ⟨numeratorEq, denominatorEq⟩ :=
        accepted_candidate_integer base Q
      exact .accepted rfl rfl numeratorEq denominatorEq
    · have twoQBelowR : 2 * Q < r := by omega
      subst s
      exact .secondRejectAtQ rfl twoQBelowR
        (second_marker_s_eq_Q_r_above_twoQ base Q r QPositive
          twoQBelowR rBelowThreeQ)
  · have QBelowS : Q < s := by omega
    by_cases sBelowTwoQ : s < 2 * Q
    · exact .secondRejectBetween QBelowS sBelowTwoQ
        (second_marker_s_between_Q_twoQ base Q r s QPositive QBelowS
          sBelowTwoQ sBelowR)
    by_cases sEqTwoQ : s = 2 * Q
    · subst s
      exact .thirdRejectAtTwoQ rfl
        (third_marker_s_eq_twoQ base Q r QPositive (by omega)
          rBelowThreeQ)
    · have twoQBelowS : 2 * Q < s := by omega
      exact .secondRejectAbove twoQBelowS
        (second_marker_s_above_twoQ base Q r s QPositive twoQBelowS
          sBelowR)

end Mortality.Compiler.ThreeProjectionClassification
