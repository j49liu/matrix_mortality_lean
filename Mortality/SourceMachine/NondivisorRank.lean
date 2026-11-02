import Mortality.SourceMachine.U20Reader

/-!
# Nondivisor ranks for Korec's instruction reader

Korec numbers a positive integer by its rank among the positive integers that
do not divide the program number plus one.  `NondivisorScan` is the operational
certificate used by the verified U20 reader.  This file connects the elementary
rank count to that inductive certificate.

The interval convention is explicit.  `nondivisorsBefore program previous
length` counts the nondivisors among

```text
previous + 1, ..., previous + length.
```

Consequently, if `candidate` is a nondivisor, its zero-based global rank is
`nondivisorCount program (candidate - 1)`.
-/

namespace Mortality.SourceMachine.KorecNondivisorRank

open Mortality.SourceMachine.KorecU20Interpreter

/-- The number of nondivisors in the `length` consecutive positive candidates
strictly after `previous`. -/
def nondivisorsBefore (program : Nat) : Nat → Nat → Nat
  | _, 0 => 0
  | previous, length + 1 =>
      (if previous + 1 ∣ program + 1 then 0 else 1) +
        nondivisorsBefore program (previous + 1) length

/-- The number of positive nondivisors at most `bound`. -/
def nondivisorCount (program bound : Nat) : Nat :=
  nondivisorsBefore program 0 bound

/-- Count the candidates selected by an arbitrary decidable marking rule in
the same interval convention as `nondivisorsBefore`. -/
def markedBefore (marked : Nat → Bool) : Nat → Nat → Nat
  | _, 0 => 0
  | previous, length + 1 =>
      (if marked (previous + 1) then 1 else 0) +
        markedBefore marked (previous + 1) length

/-- The number of marked positive integers at most `bound`. -/
def markedCount (marked : Nat → Bool) (bound : Nat) : Nat :=
  markedBefore marked 0 bound

/-- Mark an integer when it is divisible by at least one member of a finite
selected-factor list. -/
def markedByDivisorList (factors : List Nat) (value : Nat) : Bool :=
  factors.any fun factor => decide (factor ∣ value)

theorem markedByDivisorList_eq_true_iff
    (factors : List Nat) (value : Nat) :
    markedByDivisorList factors value = true ↔
      ∃ factor ∈ factors, factor ∣ value := by
  simp [markedByDivisorList, List.any_eq_true]

theorem markedByDivisorList_eq_false_iff
    (factors : List Nat) (value : Nat) :
    markedByDivisorList factors value = false ↔
      ∀ factor, factor ∈ factors → ¬factor ∣ value := by
  constructor
  · intro markedFalse factor factorMem factorDivides
    have markedTrue : markedByDivisorList factors value = true :=
      (markedByDivisorList_eq_true_iff factors value).mpr
        ⟨factor, factorMem, factorDivides⟩
    simp [markedFalse] at markedTrue
  · intro noFactor
    cases markedEq : markedByDivisorList factors value with
    | false => rfl
    | true =>
        obtain ⟨factor, factorMem, factorDivides⟩ :=
          (markedByDivisorList_eq_true_iff factors value).mp markedEq
        exact (noFactor factor factorMem factorDivides).elim

/-- An integer whose divisors are only one and itself is coprime to every
integer it does not divide.  This is the exact elementary prime property used
by the selected-factor construction. -/
theorem coprime_of_not_dvd_of_divisor_classification
    {factor value : Nat}
    (classify : ∀ divisor, divisor ∣ factor →
      divisor = 1 ∨ divisor = factor)
    (notDivides : ¬factor ∣ value) :
    Nat.Coprime factor value := by
  rw [Nat.coprime_iff_gcd_eq_one]
  rcases classify (Nat.gcd factor value)
      (Nat.gcd_dvd_left factor value) with gcdOne | gcdFactor
  · exact gcdOne
  · exfalso
    apply notDivides
    rw [← gcdFactor]
    exact Nat.gcd_dvd_right factor value

/-- A duplicate-free list of nonunit prime-like factors is pairwise
coprime. -/
theorem pairwise_coprime_of_nodup_and_divisor_classification
    {factors : List Nat}
    (nodup : factors.Nodup)
    (nonunit : ∀ factor, factor ∈ factors → 1 < factor)
    (classify : ∀ factor, factor ∈ factors →
      ∀ divisor, divisor ∣ factor →
        divisor = 1 ∨ divisor = factor) :
    factors.Pairwise Nat.Coprime := by
  induction factors with
  | nil => exact .nil
  | cons factor factors inductionHypothesis =>
      rw [List.nodup_cons] at nodup
      rw [List.pairwise_cons]
      constructor
      · intro other otherMem
        have factorNotDivides : ¬factor ∣ other := by
          intro factorDivides
          rcases classify other (by simp [otherMem]) factor factorDivides with
            factorOne | factorEq
          · have factorNonunit := nonunit factor (by simp)
            omega
          · exact nodup.1 (factorEq ▸ otherMem)
        exact coprime_of_not_dvd_of_divisor_classification
          (classify factor (by simp)) factorNotDivides
      · apply inductionHypothesis nodup.2
        · intro other otherMem
          exact nonunit other (by simp [otherMem])
        · intro other otherMem
          exact classify other (by simp [otherMem])

/-- The least common multiple of the positive unmarked integers at most the
given bound.  Starting with one keeps the value positive even when the
interval contains no unmarked integer. -/
def unmarkedLCM (factors : List Nat) : Nat → Nat
  | 0 => 1
  | bound + 1 =>
      if markedByDivisorList factors (bound + 1) then
        unmarkedLCM factors bound
      else
        Nat.lcm (unmarkedLCM factors bound) (bound + 1)

/-- The bounded unmarked LCM is always positive. -/
theorem unmarkedLCM_positive (factors : List Nat) (bound : Nat) :
    0 < unmarkedLCM factors bound := by
  induction bound with
  | zero => simp [unmarkedLCM]
  | succ bound inductionHypothesis =>
      by_cases marked :
          markedByDivisorList factors (bound + 1) = true
      · simpa [unmarkedLCM, marked] using inductionHypothesis
      · have lastPositive : 0 < bound + 1 := by omega
        simpa [unmarkedLCM, marked] using
          Nat.lcm_pos inductionHypothesis lastPositive

/-- Every positive unmarked integer in the interval divides the bounded
unmarked LCM. -/
theorem dvd_unmarkedLCM
    {factors : List Nat} {value bound : Nat}
    (valuePositive : 0 < value) (valueBounded : value ≤ bound)
    (unmarked : markedByDivisorList factors value = false) :
    value ∣ unmarkedLCM factors bound := by
  induction bound with
  | zero => omega
  | succ bound inductionHypothesis =>
      by_cases lastMarked :
          markedByDivisorList factors (bound + 1) = true
      · have valueBelow : value ≤ bound := by
          rcases Nat.eq_or_lt_of_le valueBounded with valueEq | valueStrict
          · subst value
            simp [lastMarked] at unmarked
          · omega
        simpa [unmarkedLCM, lastMarked] using
          inductionHypothesis valueBelow
      · by_cases valueEq : value = bound + 1
        · subst value
          simpa [unmarkedLCM, lastMarked] using
            Nat.dvd_lcm_right (unmarkedLCM factors bound) (bound + 1)
        · have valueBelow : value ≤ bound := by omega
          have earlierDivides := inductionHypothesis valueBelow
          have earlierIntoLcm := Nat.dvd_trans earlierDivides
            (Nat.dvd_lcm_left (unmarkedLCM factors bound) (bound + 1))
          simpa [unmarkedLCM, lastMarked] using earlierIntoLcm

/-- If a number is coprime to every bounded unmarked integer, it is coprime
to their LCM. -/
theorem coprime_unmarkedLCM
    {factors : List Nat} {factor bound : Nat}
    (pointwise : ∀ value, 0 < value → value ≤ bound →
      markedByDivisorList factors value = false →
      Nat.Coprime factor value) :
    Nat.Coprime factor (unmarkedLCM factors bound) := by
  induction bound with
  | zero => exact Nat.coprime_one_right factor
  | succ bound inductionHypothesis =>
      have earlierPointwise : ∀ value, 0 < value → value ≤ bound →
          markedByDivisorList factors value = false →
          Nat.Coprime factor value := by
        intro value positive bounded unmarked
        exact pointwise value positive (by omega) unmarked
      have earlierCoprime := inductionHypothesis earlierPointwise
      by_cases lastMarked :
          markedByDivisorList factors (bound + 1) = true
      · simpa [unmarkedLCM, lastMarked] using earlierCoprime
      · have lastCoprime := pointwise (bound + 1) (by omega) (by omega)
          (by cases markedEq : markedByDivisorList factors (bound + 1) <;>
            simp_all)
        have productCoprime := earlierCoprime.mul_right lastCoprime
        have lcmDividesProduct :=
          Nat.lcm_dvd_mul (unmarkedLCM factors bound) (bound + 1)
        have lcmCoprime :=
          productCoprime.coprime_dvd_right lcmDividesProduct
        simpa [unmarkedLCM, lastMarked] using lcmCoprime

/-- Marked interval counts concatenate. -/
theorem markedBefore_add
    (marked : Nat → Bool) (previous first second : Nat) :
    markedBefore marked previous (first + second) =
      markedBefore marked previous first +
        markedBefore marked (previous + first) second := by
  induction first generalizing previous with
  | zero => simp [markedBefore]
  | succ first inductionHypothesis =>
      rw [Nat.succ_add, markedBefore, markedBefore,
        inductionHypothesis]
      have startEq : previous + (first + 1) = previous + 1 + first := by
        omega
      rw [startEq]
      omega

/-- Appending the last candidate gives the usual right-recursive count
formula. -/
theorem markedCount_succ (marked : Nat → Bool) (bound : Nat) :
    markedCount marked (bound + 1) =
      markedCount marked bound + (if marked (bound + 1) then 1 else 0) := by
  calc
    markedCount marked (bound + 1) =
        markedBefore marked 0 bound + markedBefore marked bound 1 := by
          simpa [markedCount] using markedBefore_add marked 0 bound 1
    _ = markedCount marked bound +
        (if marked (bound + 1) then 1 else 0) := by
          simp [markedCount, markedBefore]

theorem markedCount_false (bound : Nat) :
    markedCount (fun _ => false) bound = 0 := by
  induction bound with
  | zero => rfl
  | succ bound inductionHypothesis =>
      rw [markedCount_succ, inductionHypothesis]
      rfl

/-- If two markings never hold together in the bounded interval, the count
of their Boolean union is the sum of their counts. -/
theorem markedCount_or_of_disjoint
    {left right : Nat → Bool} {bound : Nat}
    (disjoint : ∀ value, 0 < value → value ≤ bound →
      ¬(left value = true ∧ right value = true)) :
    markedCount (fun value => left value || right value) bound =
      markedCount left bound + markedCount right bound := by
  induction bound with
  | zero => rfl
  | succ bound inductionHypothesis =>
      have earlierDisjoint : ∀ value, 0 < value → value ≤ bound →
          ¬(left value = true ∧ right value = true) := by
        intro value positive bounded
        exact disjoint value positive (by omega)
      rw [markedCount_succ, markedCount_succ, markedCount_succ,
        inductionHypothesis earlierDisjoint]
      have lastDisjoint := disjoint (bound + 1) (by omega) (by omega)
      cases leftEq : left (bound + 1) <;>
        cases rightEq : right (bound + 1) <;>
        simp [leftEq, rightEq] at lastDisjoint ⊢ <;> omega

/-- There are exactly `bound / factor` positive multiples of `factor` at
most `bound`. The statement also covers `factor = 0`, when both sides are
zero. -/
theorem markedCount_dvd (factor bound : Nat) :
    markedCount (fun value => decide (factor ∣ value)) bound =
      bound / factor := by
  induction bound with
  | zero => simp [markedCount, markedBefore]
  | succ bound inductionHypothesis =>
      rw [markedCount_succ, Nat.succ_div, inductionHypothesis]
      by_cases divides : factor ∣ bound + 1 <;> simp [divides]

/-- Recursive disjointness of the sets of bounded multiples represented by a
factor list. -/
def DivisorListDisjointBelow : List Nat → Nat → Prop
  | [], _ => True
  | factor :: factors, bound =>
      (∀ value, 0 < value → value ≤ bound → factor ∣ value →
        markedByDivisorList factors value = false) ∧
      DivisorListDisjointBelow factors bound

/-- Pairwise coprime factors whose pairwise products exceed the working bound
have disjoint sets of positive multiples below that bound. -/
theorem divisorListDisjointBelow_of_pairwise
    {factors : List Nat} {bound : Nat}
    (separated : factors.Pairwise fun left right =>
      left.Coprime right ∧ bound < left * right) :
    DivisorListDisjointBelow factors bound := by
  induction factors with
  | nil => trivial
  | cons factor factors inductionHypothesis =>
      rw [List.pairwise_cons] at separated
      constructor
      · intro value valuePositive valueBounded factorDivides
        cases markedEq : markedByDivisorList factors value with
        | false => rfl
        | true =>
            obtain ⟨other, otherMem, otherDivides⟩ :=
              (markedByDivisorList_eq_true_iff factors value).mp markedEq
            have pair := separated.1 other otherMem
            have productDivides :=
              pair.1.mul_dvd_of_dvd_of_dvd factorDivides otherDivides
            have productBound := Nat.le_of_dvd valuePositive productDivides
            omega
      · exact inductionHypothesis separated.2

/-- Under bounded disjointness, Korec's marking count is the sum of the
individual quotient counts. -/
theorem markedCount_divisorList_eq_sum
    {factors : List Nat} {bound : Nat}
    (disjoint : DivisorListDisjointBelow factors bound) :
    markedCount (markedByDivisorList factors) bound =
      (factors.map fun factor => bound / factor).sum := by
  induction factors with
  | nil =>
      change markedCount (fun _ => false) bound = 0
      exact markedCount_false bound
  | cons factor factors inductionHypothesis =>
      have headDisjoint := disjoint.1
      have tailDisjoint := disjoint.2
      have unionDisjoint : ∀ value, 0 < value → value ≤ bound →
          ¬(decide (factor ∣ value) = true ∧
            markedByDivisorList factors value = true) := by
        intro value valuePositive valueBounded simultaneous
        have factorDivides : factor ∣ value := by
          simpa using simultaneous.1
        have tailFalse := headDisjoint value valuePositive valueBounded
          factorDivides
        simp [tailFalse] at simultaneous
      have unionCount := markedCount_or_of_disjoint unionDisjoint
      change markedCount
          (fun value => decide (factor ∣ value) ||
            markedByDivisorList factors value) bound =
        bound / factor +
          (factors.map fun other => bound / other).sum
      rw [unionCount, markedCount_dvd,
        inductionHypothesis tailDisjoint]

/-- Convenient sufficient form using pairwise coprimality and the product
bound found in Korec's condition (6.1.2). -/
theorem markedCount_divisorList_eq_sum_of_pairwise
    {factors : List Nat} {bound : Nat}
    (separated : factors.Pairwise fun left right =>
      left.Coprime right ∧ bound < left * right) :
    markedCount (markedByDivisorList factors) bound =
      (factors.map fun factor => bound / factor).sum :=
  markedCount_divisorList_eq_sum
    (divisorListDisjointBelow_of_pairwise separated)

/-- A positive residue modulo a selected factor proves that the factor is
absent from the coded number. -/
theorem not_dvd_of_mod_eq_positive
    {codedNumber factor residue : Nat}
    (residuePositive : 0 < residue)
    (remainder : codedNumber % factor = residue) :
    ¬factor ∣ codedNumber := by
  intro divides
  have remainderZero := Nat.mod_eq_zero_of_dvd divides
  rw [remainder] at remainderZero
  omega

/-- Pointwise positive CRT residues discharge absence of every selected
factor. -/
theorem selectedNotDivides_of_positive_residues
    {codedNumber : Nat} {factors : List Nat} {residue : Nat → Nat}
    (residuePositive : ∀ factor, factor ∈ factors → 0 < residue factor)
    (remainders : ∀ factor, factor ∈ factors →
      codedNumber % factor = residue factor) :
    ∀ factor, factor ∈ factors → ¬factor ∣ codedNumber := by
  intro factor factorMem
  exact not_dvd_of_mod_eq_positive
    (residuePositive factor factorMem) (remainders factor factorMem)

/-- Divisibility of a finite collection of covering moduli implies
divisibility of every bounded unmarked integer that divides one of them. -/
theorem unmarkedDivides_of_cover
    {codedNumber bound : Nat} {factors moduli : List Nat}
    (moduliDivide : ∀ modulus, modulus ∈ moduli → modulus ∣ codedNumber)
    (cover : ∀ value, 0 < value → value ≤ bound →
      markedByDivisorList factors value = false →
      ∃ modulus ∈ moduli, value ∣ modulus) :
    ∀ value, 0 < value → value ≤ bound →
      markedByDivisorList factors value = false → value ∣ codedNumber := by
  intro value valuePositive valueBounded unmarked
  obtain ⟨modulus, modulusMem, valueDivides⟩ :=
    cover value valuePositive valueBounded unmarked
  exact Nat.dvd_trans valueDivides (moduliDivide modulus modulusMem)

@[simp] theorem nondivisorsBefore_zero (program previous : Nat) :
    nondivisorsBefore program previous 0 = 0 := rfl

@[simp] theorem nondivisorsBefore_succ (program previous length : Nat) :
    nondivisorsBefore program previous (length + 1) =
      (if previous + 1 ∣ program + 1 then 0 else 1) +
        nondivisorsBefore program (previous + 1) length := rfl

@[simp] theorem nondivisorCount_zero (program : Nat) :
    nondivisorCount program 0 = 0 := rfl

@[simp] theorem markedBefore_zero (marked : Nat → Bool) (previous : Nat) :
    markedBefore marked previous 0 = 0 := rfl

@[simp] theorem markedBefore_succ
    (marked : Nat → Bool) (previous length : Nat) :
    markedBefore marked previous (length + 1) =
      (if marked (previous + 1) then 1 else 0) +
        markedBefore marked (previous + 1) length := rfl

/-- On a finite interval, an exact characterization of nondivisibility by a
Boolean marking rule identifies the two counts. -/
theorem nondivisorsBefore_eq_markedBefore
    {program previous length : Nat} {marked : Nat → Bool}
    (agrees : ∀ candidate, previous < candidate →
      candidate ≤ previous + length →
      (marked candidate = true ↔ ¬candidate ∣ program + 1)) :
    nondivisorsBefore program previous length =
      markedBefore marked previous length := by
  induction length generalizing previous with
  | zero => rfl
  | succ length inductionHypothesis =>
      have firstAgreement := agrees (previous + 1) (by omega) (by omega)
      have tailAgreement : ∀ candidate, previous + 1 < candidate →
          candidate ≤ previous + 1 + length →
          (marked candidate = true ↔ ¬candidate ∣ program + 1) := by
        intro candidate lower upper
        exact agrees candidate (by omega) (by omega)
      have tail := inductionHypothesis tailAgreement
      rw [nondivisorsBefore_succ, markedBefore_succ, tail]
      by_cases divides : previous + 1 ∣ program + 1
      · have markedFalse : marked (previous + 1) = false := by
          cases markedEq : marked (previous + 1) with
          | false => rfl
          | true =>
              exact (firstAgreement.mp markedEq divides).elim
        simp [divides, markedFalse]
      · have markedTrue : marked (previous + 1) = true :=
          firstAgreement.mpr divides
        simp [divides, markedTrue]

/-- Global specialization of `nondivisorsBefore_eq_markedBefore`. -/
theorem nondivisorCount_eq_markedCount
    {program bound : Nat} {marked : Nat → Bool}
    (agrees : ∀ candidate, 0 < candidate → candidate ≤ bound →
      (marked candidate = true ↔ ¬candidate ∣ program + 1)) :
    nondivisorCount program bound = markedCount marked bound := by
  simpa [nondivisorCount, markedCount] using
    nondivisorsBefore_eq_markedBefore
      (fun candidate positive bounded =>
        agrees candidate positive (by omega))

/-- If every selected factor fails to divide the coded number, while every
unmarked integer in the bounded region does divide it, selected-factor
membership characterizes the nondivisors there. This is the elementary core
of Korec's implication surrounding (6.2.2)--(6.2.3). -/
theorem markedByDivisorList_iff_not_dvd
    {program bound value : Nat} {factors : List Nat}
    (selectedNotDivides : ∀ factor, factor ∈ factors →
      ¬factor ∣ program + 1)
    (unmarkedDivides : ∀ candidate, 0 < candidate → candidate ≤ bound →
      markedByDivisorList factors candidate = false →
      candidate ∣ program + 1)
    (valuePositive : 0 < value) (valueBounded : value ≤ bound) :
    markedByDivisorList factors value = true ↔
      ¬value ∣ program + 1 := by
  constructor
  · intro marked valueDivides
    obtain ⟨factor, factorMem, factorDivides⟩ :=
      (markedByDivisorList_eq_true_iff factors value).mp marked
    exact selectedNotDivides factor factorMem
      (Nat.dvd_trans factorDivides valueDivides)
  · intro valueNotDivides
    cases markedEq : markedByDivisorList factors value with
    | false =>
        exact (valueNotDivides
          (unmarkedDivides value valuePositive valueBounded markedEq)).elim
    | true => rfl

/-- Counting the earlier nondivisors constructs the reader's scan to the next
specified nondivisor. -/
theorem nondivisorScan_of_interval_count
    {program previous length : Nat}
    (targetNotDivides :
      ¬(previous + length + 1) ∣ program + 1) :
    NondivisorScan program previous
      (nondivisorsBefore program previous length)
      (previous + length + 1) := by
  induction length generalizing previous with
  | zero =>
      simpa using NondivisorScan.found (program := program) previous
        targetNotDivides
  | succ length inductionHypothesis =>
      have targetNotDivides' :
          ¬(previous + 1 + length + 1) ∣ program + 1 := by
        simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
          targetNotDivides
      have suffix := inductionHypothesis
        (previous := previous + 1) targetNotDivides'
      have targetEq :
          previous + 1 + length + 1 = previous + (length + 1) + 1 := by
        omega
      by_cases divides : previous + 1 ∣ program + 1
      · rw [nondivisorsBefore_succ, if_pos divides, Nat.zero_add]
        have result := NondivisorScan.divisor divides suffix
        rw [targetEq] at result
        exact result
      · rw [nondivisorsBefore_succ, if_neg divides]
        have result := NondivisorScan.skip divides suffix
        rw [targetEq] at result
        simpa [Nat.add_comm] using result

/-- A positive nondivisor is selected by its zero-based global rank. -/
theorem nondivisorScan_of_count
    {program state candidate : Nat}
    (candidatePositive : 0 < candidate)
    (candidateNotDivides : ¬candidate ∣ program + 1)
    (rank : nondivisorCount program (candidate - 1) = state - 1) :
    NondivisorScan program 0 (state - 1) candidate := by
  have targetEq : 0 + (candidate - 1) + 1 = candidate := by omega
  have scan := nondivisorScan_of_interval_count
    (program := program) (previous := 0) (length := candidate - 1)
    (by rwa [targetEq])
  rw [targetEq] at scan
  rw [← rank]
  exact scan

/-- Interval counts concatenate. -/
theorem nondivisorsBefore_add
    (program previous first second : Nat) :
    nondivisorsBefore program previous (first + second) =
      nondivisorsBefore program previous first +
        nondivisorsBefore program (previous + first) second := by
  induction first generalizing previous with
  | zero => simp
  | succ first inductionHypothesis =>
      rw [Nat.succ_add, nondivisorsBefore_succ,
        nondivisorsBefore_succ, inductionHypothesis]
      have startEq : previous + (first + 1) = previous + 1 + first := by
        omega
      rw [startEq]
      omega

/-- Local-rank form of the reader certificate.  The incoming carry may lie
past earlier nondivisors: it suffices that the candidate raises the global
nondivisor count by exactly the simulated state number.  This is the
arithmetic interface for initializing and preserving a nonzero reader-rank
offset. -/
theorem nondivisorScan_of_rank_difference
    {program previous state candidate : Nat}
    (statePositive : 0 < state)
    (previousBelow : previous < candidate)
    (candidateNotDivides : ¬candidate ∣ program + 1)
    (rankDifference :
      nondivisorCount program candidate =
        nondivisorCount program previous + state) :
    NondivisorScan program previous (state - 1) candidate := by
  let length := candidate - previous - 1
  have targetEq : previous + length + 1 = candidate := by
    dsimp [length]
    omega
  have intervalFull :
      nondivisorsBefore program previous (length + 1) = state := by
    have candidateSplit : previous + (length + 1) = candidate := by omega
    have countSplit := nondivisorsBefore_add program 0 previous (length + 1)
    have countSplit' :
        nondivisorCount program candidate =
          nondivisorCount program previous +
            nondivisorsBefore program previous (length + 1) := by
      simpa [nondivisorCount, candidateSplit] using countSplit
    omega
  have intervalBefore :
      nondivisorsBefore program previous length = state - 1 := by
    have appendLast := nondivisorsBefore_add program previous length 1
    have lastStart : previous + length + 1 = candidate := targetEq
    have lastCount :
        nondivisorsBefore program (previous + length) 1 = 1 := by
      simp [nondivisorsBefore, lastStart, candidateNotDivides]
    rw [lastCount] at appendLast
    omega
  have targetNotDivides :
      ¬(previous + length + 1) ∣ program + 1 := by
    simpa [targetEq] using candidateNotDivides
  have scan := nondivisorScan_of_interval_count
    (program := program) (previous := previous) (length := length)
    targetNotDivides
  rw [intervalBefore, targetEq] at scan
  exact scan

/-- One-based form: a positive nondivisor with count `state` is the
`state`-th positive nondivisor. -/
theorem nondivisorScan_of_oneBasedRank
    {program state candidate : Nat}
    (statePositive : 0 < state)
    (candidatePositive : 0 < candidate)
    (candidateNotDivides : ¬candidate ∣ program + 1)
    (rank : nondivisorCount program candidate = state) :
    NondivisorScan program 0 (state - 1) candidate := by
  have countStep : nondivisorCount program candidate =
      nondivisorCount program (candidate - 1) + 1 := by
    have candidateEq : candidate - 1 + 1 = candidate := by omega
    calc
      nondivisorCount program candidate =
          nondivisorsBefore program 0 ((candidate - 1) + 1) := by
            rw [candidateEq]
            rfl
      _ = nondivisorsBefore program 0 (candidate - 1) +
          nondivisorsBefore program (candidate - 1) 1 := by
            simpa using nondivisorsBefore_add program 0 (candidate - 1) 1
      _ = nondivisorCount program (candidate - 1) + 1 := by
            simp [nondivisorCount, nondivisorsBefore,
              candidateNotDivides, candidateEq]
  apply nondivisorScan_of_count candidatePositive candidateNotDivides
  omega

/-- Korec's usual proof pattern: characterize the nondivisors up to a
candidate by a finite marking predicate, then compute the candidate's rank by
counting the marked integers. -/
theorem nondivisorScan_of_markedRank
    {program state candidate : Nat} {marked : Nat → Bool}
    (statePositive : 0 < state)
    (candidatePositive : 0 < candidate)
    (agrees : ∀ value, 0 < value → value ≤ candidate →
      (marked value = true ↔ ¬value ∣ program + 1))
    (candidateMarked : marked candidate = true)
    (rank : markedCount marked candidate = state) :
    NondivisorScan program 0 (state - 1) candidate := by
  have candidateNotDivides : ¬candidate ∣ program + 1 :=
    (agrees candidate candidatePositive (by omega)).mp candidateMarked
  apply nondivisorScan_of_oneBasedRank statePositive candidatePositive
    candidateNotDivides
  rw [nondivisorCount_eq_markedCount agrees]
  exact rank

/-- Selected factors, bounded divisibility of every unmarked integer, and a
finite count equation together produce the reader scan. -/
theorem nondivisorScan_of_divisorListRank
    {program state candidate : Nat} {factors : List Nat}
    (statePositive : 0 < state)
    (candidatePositive : 0 < candidate)
    (selectedNotDivides : ∀ factor, factor ∈ factors →
      ¬factor ∣ program + 1)
    (unmarkedDivides : ∀ value, 0 < value → value ≤ candidate →
      markedByDivisorList factors value = false →
      value ∣ program + 1)
    (candidateMarked : markedByDivisorList factors candidate = true)
    (rank : markedCount (markedByDivisorList factors) candidate = state) :
    NondivisorScan program 0 (state - 1) candidate := by
  apply nondivisorScan_of_markedRank statePositive candidatePositive
    (candidateMarked := candidateMarked) (rank := rank)
  intro value valuePositive valueBounded
  exact markedByDivisorList_iff_not_dvd selectedNotDivides
    unmarkedDivides valuePositive valueBounded

end Mortality.SourceMachine.KorecNondivisorRank
