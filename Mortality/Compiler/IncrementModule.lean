import Mortality.Compiler.CodeRegion
import Mortality.Compiler.PhysicalWord
import Mortality.Compiler.UnaryArithmetic

/-!
# The unary increment module

This file instantiates the four-letter table in Proposition 5.2 and
proves its successful execution for every unary input.  The proof keeps
all intermediate scan values explicit and shows that they remain in the
local region.
-/

namespace Mortality.Compiler.IncrementModule

open Mortality.PeriodicCode
open Mortality.Compiler.UnaryArithmetic

def entryZero (prime source privatePhase : Nat) : PhysicalTemplate :=
  { sourcePhase := source
    targetPhase := privatePhase
    digit := 0
    preCoefficient := -(prime : Int) + 1
    postSign := .positive
    postCoefficient := 0 }

def entryMarker (prime source target : Nat) : PhysicalTemplate :=
  { sourcePhase := source
    targetPhase := target
    digit := 1
    preCoefficient := -(prime : Int) + 1
    postSign := .positive
    postCoefficient := 0 }

def loopZero (privatePhase : Nat) : PhysicalTemplate :=
  { sourcePhase := privatePhase
    targetPhase := privatePhase
    digit := 0
    preCoefficient := 0
    postSign := .positive
    postCoefficient := 0 }

def exitMarker (privatePhase target : Nat) : PhysicalTemplate :=
  { sourcePhase := privatePhase
    targetPhase := target
    digit := 1
    preCoefficient := 0
    postSign := .positive
    postCoefficient := 0 }

def incrementTail (privatePhase target remainingZeros : Nat) :
    List PhysicalTemplate :=
  List.replicate remainingZeros (loopZero privatePhase) ++
    [exitMarker privatePhase target]

def incrementWord (prime source target privatePhase counter : Nat) :
    List PhysicalTemplate :=
  if counter = 0 then [entryMarker prime source target]
  else entryZero prime source privatePhase ::
    incrementTail privatePhase target (counter - 1)

def incrementAlphabet (prime source target privatePhase : Nat) :
    List PhysicalTemplate :=
  [entryZero prime source privatePhase,
    entryMarker prime source target,
    loopZero privatePhase,
    exitMarker privatePhase target]

@[simp] theorem incrementAlphabet_length (prime source target privatePhase : Nat) :
    (incrementAlphabet prime source target privatePhase).length = 4 := by
  rfl

theorem unaryCode_local (base counter : Nat) (baseAtLeastTwo : 2 ≤ base) :
    LocalAt base (Vec2.affine (unaryCode base counter)) := by
  unfold unaryCode
  exact periodicCode_local_affine base (unaryDigits counter) baseAtLeastTwo
    (by simp [unaryDigits])

theorem phaseUnaryCode_local (base phase counter : Nat)
    (baseAtLeastTwo : 2 ≤ base) :
    LocalAt base (phaseAffine phase (unaryCode base counter)) := by
  rw [show phaseAffine phase (unaryCode base counter) =
      Matrix2.apply (IntMatrix2.cast (chart phase))
        (Vec2.affine (unaryCode base counter)) by
    simpa [phaseAffine] using
      (chart_apply phase (unaryCode base counter)).symm]
  exact (local_chart_iff base phase _).mpr
    (unaryCode_local base counter baseAtLeastTwo)

theorem incrementState_local (base counter deleted : Nat)
    (baseAtLeastTwo : 2 ≤ base) :
    LocalAt base (Vec2.affine (incrementState base counter deleted)) := by
  have denominatorNotDivisible := one_sub_power_not_dvd base (counter + 2)
    baseAtLeastTwo (by omega)
  have localFraction := local_affine_integer_div
    (prime := base)
    (numerator := (base : Int) ^ (counter - deleted))
    (denominator := 1 - (base : Int) ^ (counter + 2))
    denominatorNotDivisible
  simpa [incrementState, Rat.intCast_pow, Rat.intCast_natCast,
    Rat.intCast_sub] using localFraction

theorem phaseIncrementState_local (base phase counter deleted : Nat)
    (baseAtLeastTwo : 2 ≤ base) :
    LocalAt base
      (phaseAffine phase (incrementState base counter deleted)) := by
  rw [show phaseAffine phase (incrementState base counter deleted) =
      Matrix2.apply (IntMatrix2.cast (chart phase))
        (Vec2.affine (incrementState base counter deleted)) by
    simpa [phaseAffine] using
      (chart_apply phase (incrementState base counter deleted)).symm]
  exact (local_chart_iff base phase _).mpr
    (incrementState_local base counter deleted baseAtLeastTwo)

theorem incrementState_sameLine_integer (base counter deleted : Nat)
    (baseAtLeastTwo : 2 ≤ base) :
    SameLine (Vec2.affine (incrementState base counter deleted))
      (integerVector ((base : Int) ^ (counter - deleted))
        (1 - (base : Int) ^ (counter + 2))) := by
  have denominatorNotDivisible := one_sub_power_not_dvd base (counter + 2)
    baseAtLeastTwo (by omega)
  have denominatorNonzero : 1 - (base : Int) ^ (counter + 2) ≠ 0 :=
    fun denominatorZero => denominatorNotDivisible
      (denominatorZero ▸ Int.dvd_zero _)
  have same := affine_div_sameLine_integerVector
    (numerator := (base : Int) ^ (counter - deleted))
    (denominator := 1 - (base : Int) ^ (counter + 2))
    denominatorNonzero
  simpa [incrementState, Rat.intCast_pow, Rat.intCast_natCast,
    Rat.intCast_sub] using same

/-- Before the unary marker, an increment scan state occupies digit zero in
its private phase.  This guarded form is used when the module is embedded in
the full fixed alphabet. -/
theorem incrementState_inPhaseAt_before
    {base phase counter deleted : Nat} (baseAtLeastTwo : 2 ≤ base)
    (deletedBelow : deleted < counter) :
    InPhaseAt base phase 0
      (phaseAffine phase (incrementState base counter deleted)) := by
  apply inPhaseAt_phaseAffine_integer
    (numerator := (base : Int) ^ (counter - deleted))
    (denominator := 1 - (base : Int) ^ (counter + 2))
    (by simp [ReservedDigit])
    (one_sub_power_not_dvd base (counter + 2) baseAtLeastTwo (by omega))
  · simpa using base_dvd_positive_power base (counter - deleted) (by omega)
  · exact incrementState_sameLine_integer base counter deleted baseAtLeastTwo

/-- After all zeros have been deleted, the increment scan exposes its marker
as digit one in the same private phase. -/
theorem incrementState_inPhaseAt_marker
    {base phase counter : Nat} (baseAtLeastTwo : 2 ≤ base) :
    InPhaseAt base phase 1
      (phaseAffine phase (incrementState base counter counter)) := by
  apply inPhaseAt_phaseAffine_integer
    (numerator := 1)
    (denominator := 1 - (base : Int) ^ (counter + 2))
    (by simp [ReservedDigit])
    (one_sub_power_not_dvd base (counter + 2) baseAtLeastTwo (by omega))
  · have powerDivisible := base_dvd_positive_power base (counter + 2)
      (by omega)
    simp only [Int.one_mul]
    rw [show (1 : Int) - (1 - (base : Int) ^ (counter + 2)) =
      (base : Int) ^ (counter + 2) by grind]
    exact powerDivisible
  · simpa using
      incrementState_sameLine_integer base counter counter baseAtLeastTwo

theorem loopZero_step (base privatePhase counter deleted : Nat)
    (baseAtLeastTwo : 2 ≤ base) (deletedBelow : deleted < counter) :
    SameLine
      ((loopZero privatePhase).act base
        (phaseAffine privatePhase (incrementState base counter deleted)))
      (phaseAffine privatePhase
        (incrementState base counter (deleted + 1))) := by
  have deletedEq := incrementState_delete_zero base counter deleted
    baseAtLeastTwo deletedBelow
  have action := physicalLetter_affine_sameLine_of_local
    (sourcePhase := privatePhase) (targetPhase := privatePhase)
    (digit := 0) (preCoefficient := 0) (postCoefficient := 0)
    (postSign := .positive) (primePositive := by omega)
    (incrementState_local base counter deleted baseAtLeastTwo)
    (by
      have nextLocal := incrementState_local base counter (deleted + 1)
        baseAtLeastTwo
      rw [← deletedEq] at nextLocal
      simpa [deleteDigit] using nextLocal)
  simp [localLetterMap] at action
  have deletedRaw := deletedEq
  unfold deleteDigit at deletedRaw
  simp only [Rat.intCast_zero] at deletedRaw
  rw [deletedRaw] at action
  exact action

theorem exitMarker_step (base privatePhase target counter : Nat)
    (baseAtLeastTwo : 2 ≤ base) :
    SameLine
      ((exitMarker privatePhase target).act base
        (phaseAffine privatePhase
          (incrementState base counter counter)))
      (phaseAffine target (unaryCode base (counter + 1))) := by
  have deletedEq := incrementState_delete_marker base counter baseAtLeastTwo
  have action := physicalLetter_affine_sameLine_of_local
    (sourcePhase := privatePhase) (targetPhase := target)
    (digit := 1) (preCoefficient := 0) (postCoefficient := 0)
    (postSign := .positive) (primePositive := by omega)
    (incrementState_local base counter counter baseAtLeastTwo)
    (by
      have outputLocal := unaryCode_local base (counter + 1) baseAtLeastTwo
      rw [← deletedEq] at outputLocal
      simpa [deleteDigit] using outputLocal)
  simp [localLetterMap] at action
  have deletedRaw := deletedEq
  unfold deleteDigit at deletedRaw
  simp only [Rat.intCast_one] at deletedRaw
  rw [deletedRaw] at action
  exact action

theorem incrementTail_correct (base privatePhase target deleted remaining : Nat)
    (baseAtLeastTwo : 2 ≤ base) :
    SameLine
      (physicalWordAction base (incrementTail privatePhase target remaining)
        (phaseAffine privatePhase
          (incrementState base (deleted + remaining) deleted)))
      (phaseAffine target (unaryCode base (deleted + remaining + 1))) := by
  induction remaining generalizing deleted with
  | zero =>
      simpa [incrementTail, physicalWordAction] using
        (exitMarker_step base privatePhase target deleted baseAtLeastTwo)
  | succ remaining inductionHypothesis =>
      have firstStep := loopZero_step base privatePhase
        (deleted + (remaining + 1)) deleted baseAtLeastTwo (by omega)
      have remainingRun := inductionHypothesis (deleted := deleted + 1)
      have remainingRun' :
          SameLine
            (physicalWordAction base
              (incrementTail privatePhase target remaining)
              (phaseAffine privatePhase
                (incrementState base (deleted + (remaining + 1))
                  (deleted + 1))))
            (phaseAffine target
              (unaryCode base (deleted + (remaining + 1) + 1))) := by
        simpa only [show deleted + 1 + remaining =
          deleted + (remaining + 1) by omega] using remainingRun
      have combined := physicalWordAction_cons_sameLine base
        (loopZero privatePhase)
        (incrementTail privatePhase target remaining)
        firstStep remainingRun'
      simpa [incrementTail, List.replicate_succ, physicalWordAction]
        using combined

theorem entryZero_step (base source privatePhase counter : Nat)
    (baseAtLeastTwo : 2 ≤ base) (counterPositive : 0 < counter) :
    SameLine
      ((entryZero base source privatePhase).act base
        (phaseAffine source (unaryCode base counter)))
      (phaseAffine privatePhase (incrementState base counter 1)) := by
  have deletedEq := incrementState_delete_zero base counter 0
    baseAtLeastTwo counterPositive
  rw [incrementState_zero base counter baseAtLeastTwo] at deletedEq
  have action := physicalLetter_affine_sameLine_of_local
    (sourcePhase := source) (targetPhase := privatePhase)
    (digit := 0) (preCoefficient := -(base : Int) + 1)
    (postCoefficient := 0) (postSign := .positive)
    (primePositive := by omega)
    (unaryCode_local base counter baseAtLeastTwo)
    (by
      have outputLocal := incrementState_local base counter 1 baseAtLeastTwo
      rw [← deletedEq] at outputLocal
      simpa [deleteDigit, ← S_eq_mutationMap] using outputLocal)
  simp [localLetterMap, ← S_eq_mutationMap] at action
  have deletedRaw := deletedEq
  unfold deleteDigit at deletedRaw
  simp only [Rat.intCast_zero, Nat.zero_add] at deletedRaw
  rw [deletedRaw] at action
  exact action

theorem entryMarker_step (base source target : Nat)
    (baseAtLeastTwo : 2 ≤ base) :
    SameLine
      ((entryMarker base source target).act base
        (phaseAffine source (unaryCode base 0)))
      (phaseAffine target (unaryCode base 1)) := by
  have deletedEq := incrementState_delete_marker base 0 baseAtLeastTwo
  rw [incrementState_zero base 0 baseAtLeastTwo] at deletedEq
  have action := physicalLetter_affine_sameLine_of_local
    (sourcePhase := source) (targetPhase := target)
    (digit := 1) (preCoefficient := -(base : Int) + 1)
    (postCoefficient := 0) (postSign := .positive)
    (primePositive := by omega)
    (unaryCode_local base 0 baseAtLeastTwo)
    (by
      have outputLocal := unaryCode_local base 1 baseAtLeastTwo
      rw [← deletedEq] at outputLocal
      simpa [deleteDigit, ← S_eq_mutationMap] using outputLocal)
  simp [localLetterMap, ← S_eq_mutationMap] at action
  have deletedRaw := deletedEq
  unfold deleteDigit at deletedRaw
  simp only [Rat.intCast_one, Nat.zero_add] at deletedRaw
  rw [deletedRaw] at action
  exact action

/-- Every unary input has the intended completed increment execution. -/
theorem incrementWord_correct (base source target privatePhase counter : Nat)
    (baseAtLeastTwo : 2 ≤ base) :
    SameLine
      (physicalWordAction base
        (incrementWord base source target privatePhase counter)
        (phaseAffine source (unaryCode base counter)))
      (phaseAffine target (unaryCode base (counter + 1))) := by
  by_cases counterZero : counter = 0
  · subst counter
    simpa [incrementWord, physicalWordAction] using
      (entryMarker_step base source target baseAtLeastTwo)
  · have counterPositive : 0 < counter := by omega
    have firstStep := entryZero_step base source privatePhase counter
      baseAtLeastTwo counterPositive
    have remainingRun := incrementTail_correct base privatePhase target 1
      (counter - 1) baseAtLeastTwo
    have remainingRun' :
        SameLine
          (physicalWordAction base
            (incrementTail privatePhase target (counter - 1))
            (phaseAffine privatePhase (incrementState base counter 1)))
          (phaseAffine target (unaryCode base (counter + 1))) := by
      simpa only [show 1 + (counter - 1) = counter by omega,
        show 1 + (counter - 1) + 1 = counter + 1 by omega]
        using remainingRun
    have combined := physicalWordAction_cons_sameLine base
      (entryZero base source privatePhase)
      (incrementTail privatePhase target (counter - 1))
      firstStep remainingRun'
    simpa [incrementWord, counterZero] using combined

/-- On `z_0`, the only increment-table letter that can stay local is the
immediate marker exit. -/
theorem first_letter_at_zero
    {prime phaseCount source target privatePhase : Nat}
    (primeProperty : IsPrime prime)
    (primeBound : 6 * phaseCount < prime)
    (sourceBound : source < phaseCount)
    (privateBound : privatePhase < phaseCount)
    (sourcePrivateDistinct : source ≠ privatePhase)
    {letter : PhysicalTemplate}
    (letterMem : letter ∈
      incrementAlphabet prime source target privatePhase)
    (outputLocal : LocalAt prime
      (letter.act prime (phaseAffine source (unaryCode prime 0)))) :
    letter = entryMarker prime source target := by
  simp [incrementAlphabet] at letterMem
  rcases letterMem with rfl | rfl | rfl | rfl
  · have forced := physicalLetter_periodic_affine_source_digit_unique
      (prime := prime) (phaseCount := phaseCount)
      (actualPhase := source) (sourcePhase := source)
      (targetPhase := privatePhase) (actualDigit := 1) (letterDigit := 0)
      (preCoefficient := -(prime : Int) + 1) (postCoefficient := 0)
      (postSign := .positive) [] primeProperty primeBound sourceBound
      sourceBound (by simp [ReservedDigit]) (by simp [ReservedDigit])
      (by simpa [entryZero, PhysicalTemplate.act, PhysicalTemplate.matrix,
        phaseAffine, unaryCode, unaryDigits] using outputLocal)
    omega
  · rfl
  · have forced := physicalLetter_periodic_affine_source_digit_unique
      (prime := prime) (phaseCount := phaseCount)
      (actualPhase := source) (sourcePhase := privatePhase)
      (targetPhase := privatePhase) (actualDigit := 1) (letterDigit := 0)
      (preCoefficient := 0) (postCoefficient := 0)
      (postSign := .positive) [] primeProperty primeBound sourceBound
      privateBound (by simp [ReservedDigit]) (by simp [ReservedDigit])
      (by simpa [loopZero, PhysicalTemplate.act, PhysicalTemplate.matrix,
        phaseAffine, unaryCode, unaryDigits] using outputLocal)
    exact False.elim (sourcePrivateDistinct forced.1)
  · have forced := physicalLetter_periodic_affine_source_digit_unique
      (prime := prime) (phaseCount := phaseCount)
      (actualPhase := source) (sourcePhase := privatePhase)
      (targetPhase := target) (actualDigit := 1) (letterDigit := 1)
      (preCoefficient := 0) (postCoefficient := 0)
      (postSign := .positive) [] primeProperty primeBound sourceBound
      privateBound (by simp [ReservedDigit]) (by simp [ReservedDigit])
      (by simpa [exitMarker, PhysicalTemplate.act, PhysicalTemplate.matrix,
        phaseAffine, unaryCode, unaryDigits] using outputLocal)
    exact False.elim (sourcePrivateDistinct forced.1)

/-- On a positive unary input, the only increment-table letter that can
stay local is the zero entry into the private phase. -/
theorem first_letter_at_positive
    {prime phaseCount source target privatePhase counter : Nat}
    (primeProperty : IsPrime prime)
    (primeBound : 6 * phaseCount < prime)
    (sourceBound : source < phaseCount)
    (privateBound : privatePhase < phaseCount)
    (sourcePrivateDistinct : source ≠ privatePhase)
    {letter : PhysicalTemplate}
    (letterMem : letter ∈
      incrementAlphabet prime source target privatePhase)
    (outputLocal : LocalAt prime
      (letter.act prime
        (phaseAffine source (unaryCode prime (counter + 1))))) :
    letter = entryZero prime source privatePhase := by
  simp [incrementAlphabet] at letterMem
  rcases letterMem with rfl | rfl | rfl | rfl
  · rfl
  · have forced := physicalLetter_periodic_affine_source_digit_unique
      (prime := prime) (phaseCount := phaseCount)
      (actualPhase := source) (sourcePhase := source)
      (targetPhase := target) (actualDigit := 0) (letterDigit := 1)
      (preCoefficient := -(prime : Int) + 1) (postCoefficient := 0)
      (postSign := .positive) (unaryDigits counter) primeProperty primeBound
      sourceBound sourceBound (by simp [ReservedDigit])
      (by simp [ReservedDigit])
      (by simpa [entryMarker, PhysicalTemplate.act, PhysicalTemplate.matrix,
        phaseAffine, unaryCode, show unaryDigits (counter + 1) =
          0 :: unaryDigits counter by
            simp [unaryDigits, List.replicate_succ]] using outputLocal)
    omega
  · have forced := physicalLetter_periodic_affine_source_digit_unique
      (prime := prime) (phaseCount := phaseCount)
      (actualPhase := source) (sourcePhase := privatePhase)
      (targetPhase := privatePhase) (actualDigit := 0) (letterDigit := 0)
      (preCoefficient := 0) (postCoefficient := 0)
      (postSign := .positive) (unaryDigits counter) primeProperty primeBound
      sourceBound privateBound (by simp [ReservedDigit])
      (by simp [ReservedDigit])
      (by simpa [loopZero, PhysicalTemplate.act, PhysicalTemplate.matrix,
        phaseAffine, unaryCode, show unaryDigits (counter + 1) =
          0 :: unaryDigits counter by
            simp [unaryDigits, List.replicate_succ]] using outputLocal)
    exact False.elim (sourcePrivateDistinct forced.1)
  · have forced := physicalLetter_periodic_affine_source_digit_unique
      (prime := prime) (phaseCount := phaseCount)
      (actualPhase := source) (sourcePhase := privatePhase)
      (targetPhase := target) (actualDigit := 0) (letterDigit := 1)
      (preCoefficient := 0) (postCoefficient := 0)
      (postSign := .positive) (unaryDigits counter) primeProperty primeBound
      sourceBound privateBound (by simp [ReservedDigit])
      (by simp [ReservedDigit])
      (by simpa [exitMarker, PhysicalTemplate.act, PhysicalTemplate.matrix,
        phaseAffine, unaryCode, show unaryDigits (counter + 1) =
          0 :: unaryDigits counter by
            simp [unaryDigits, List.replicate_succ]] using outputLocal)
    exact False.elim (sourcePrivateDistinct forced.1)

private theorem incrementLetter_source_bound
    {prime phaseCount source target privatePhase : Nat}
    (sourceBound : source < phaseCount)
    (privateBound : privatePhase < phaseCount)
    {letter : PhysicalTemplate}
    (letterMem : letter ∈
      incrementAlphabet prime source target privatePhase) :
    letter.sourcePhase < phaseCount := by
  simp [incrementAlphabet] at letterMem
  rcases letterMem with rfl | rfl | rfl | rfl <;>
    simp [entryZero, entryMarker, loopZero, exitMarker, sourceBound,
      privateBound]

private theorem incrementLetter_reserved
    {prime source target privatePhase : Nat} {letter : PhysicalTemplate}
    (letterMem : letter ∈
      incrementAlphabet prime source target privatePhase) :
    ReservedDigit letter.digit := by
  simp [incrementAlphabet] at letterMem
  rcases letterMem with rfl | rfl | rfl | rfl <;>
    simp [entryZero, entryMarker, loopZero, exitMarker, ReservedDigit]

/-- Before the marker is exposed, the private increment phase forces its
zero-loop letter. -/
theorem private_letter_before_marker
    {prime phaseCount source target privatePhase counter deleted : Nat}
    (primeProperty : IsPrime prime)
    (primeBound : 6 * phaseCount < prime)
    (sourceBound : source < phaseCount)
    (privateBound : privatePhase < phaseCount)
    (sourcePrivateDistinct : source ≠ privatePhase)
    (deletedBelow : deleted < counter)
    {letter : PhysicalTemplate}
    (letterMem : letter ∈
      incrementAlphabet prime source target privatePhase)
    (outputLocal : LocalAt prime
      (letter.act prime
        (phaseAffine privatePhase
          (incrementState prime counter deleted)))) :
    letter = loopZero privatePhase := by
  have denominatorNotDivisible := one_sub_power_not_dvd prime (counter + 2)
    primeProperty.1 (by omega)
  have actualResidue : (prime : Int) ∣
      (prime : Int) ^ (counter - deleted) -
        0 * (1 - (prime : Int) ^ (counter + 2)) := by
    simpa using base_dvd_positive_power prime (counter - deleted) (by omega)
  have forced := physicalLetter_affine_integer_source_digit_unique
    (prime := prime) (phaseCount := phaseCount)
    (actualPhase := privatePhase) (sourcePhase := letter.sourcePhase)
    (targetPhase := letter.targetPhase) (actualDigit := 0)
    (letterDigit := letter.digit)
    (preCoefficient := letter.preCoefficient)
    (postCoefficient := letter.postCoefficient)
    (postSign := letter.postSign)
    primeProperty primeBound privateBound
    (incrementLetter_source_bound sourceBound privateBound letterMem)
    (by simp [ReservedDigit]) (incrementLetter_reserved letterMem)
    denominatorNotDivisible actualResidue
    (incrementState_sameLine_integer prime counter deleted primeProperty.1)
    (by simpa [PhysicalTemplate.act, PhysicalTemplate.matrix, phaseAffine]
      using outputLocal)
  simp [incrementAlphabet] at letterMem
  rcases letterMem with rfl | rfl | rfl | rfl
  · exact False.elim (sourcePrivateDistinct forced.1.symm)
  · exact False.elim (sourcePrivateDistinct forced.1.symm)
  · rfl
  · simp [exitMarker] at forced

/-- Once all zeros have been deleted, the private increment phase forces
the marker exit. -/
theorem private_letter_at_marker
    {prime phaseCount source target privatePhase counter : Nat}
    (primeProperty : IsPrime prime)
    (primeBound : 6 * phaseCount < prime)
    (sourceBound : source < phaseCount)
    (privateBound : privatePhase < phaseCount)
    (sourcePrivateDistinct : source ≠ privatePhase)
    {letter : PhysicalTemplate}
    (letterMem : letter ∈
      incrementAlphabet prime source target privatePhase)
    (outputLocal : LocalAt prime
      (letter.act prime
        (phaseAffine privatePhase
          (incrementState prime counter counter)))) :
    letter = exitMarker privatePhase target := by
  have denominatorNotDivisible := one_sub_power_not_dvd prime (counter + 2)
    primeProperty.1 (by omega)
  have actualResidue : (prime : Int) ∣
      (prime : Int) ^ (counter - counter) -
        1 * (1 - (prime : Int) ^ (counter + 2)) := by
    simp only [Nat.sub_self, Int.pow_zero, Int.one_mul]
    have powerDivisible := base_dvd_positive_power prime (counter + 2)
      (by omega)
    rw [show (1 : Int) - (1 - (prime : Int) ^ (counter + 2)) =
      (prime : Int) ^ (counter + 2) by grind]
    exact powerDivisible
  have forced := physicalLetter_affine_integer_source_digit_unique
    (prime := prime) (phaseCount := phaseCount)
    (actualPhase := privatePhase) (sourcePhase := letter.sourcePhase)
    (targetPhase := letter.targetPhase) (actualDigit := 1)
    (letterDigit := letter.digit)
    (preCoefficient := letter.preCoefficient)
    (postCoefficient := letter.postCoefficient)
    (postSign := letter.postSign)
    primeProperty primeBound privateBound
    (incrementLetter_source_bound sourceBound privateBound letterMem)
    (by simp [ReservedDigit]) (incrementLetter_reserved letterMem)
    denominatorNotDivisible actualResidue
    (incrementState_sameLine_integer prime counter counter primeProperty.1)
    (by simpa [PhysicalTemplate.act, PhysicalTemplate.matrix, phaseAffine]
      using outputLocal)
  simp [incrementAlphabet] at letterMem
  rcases letterMem with rfl | rfl | rfl | rfl
  · exact False.elim (sourcePrivateDistinct forced.1.symm)
  · exact False.elim (sourcePrivateDistinct forced.1.symm)
  · simp [loopZero] at forced
  · rfl

/-- A surviving private-phase word of the exact remaining scan length is
the prescribed string of zero loops followed by the marker exit. -/
theorem incrementTail_surviving_unique
    {prime phaseCount source target privatePhase deleted remaining : Nat}
    (primeProperty : IsPrime prime)
    (primeBound : 6 * phaseCount < prime)
    (sourceBound : source < phaseCount)
    (privateBound : privatePhase < phaseCount)
    (sourcePrivateDistinct : source ≠ privatePhase)
    {word : List PhysicalTemplate}
    (wordOver : WordOver
      (incrementAlphabet prime source target privatePhase) word)
    (allLocal : AllStatesLocal prime word
      (phaseAffine privatePhase
        (incrementState prime (deleted + remaining) deleted)))
    (lengthEq : word.length = remaining + 1) :
    word = incrementTail privatePhase target remaining := by
  induction remaining generalizing deleted word with
  | zero =>
      cases word with
      | nil => simp at lengthEq
      | cons letter tail =>
          have tailEmpty : tail = [] := by
            apply List.eq_nil_of_length_eq_zero
            simpa using lengthEq
          subst tail
          have letterMem := wordOver letter (by simp)
          have letterEq := private_letter_at_marker
            (counter := deleted) primeProperty primeBound sourceBound
            privateBound sourcePrivateDistinct letterMem
            (by exact allLocal.2)
          subst letter
          simp [incrementTail]
  | succ remaining inductionHypothesis =>
      cases word with
      | nil => simp at lengthEq
      | cons letter tail =>
          have letterMem := wordOver letter (by simp)
          have tailOver : WordOver
              (incrementAlphabet prime source target privatePhase) tail := by
            intro candidate candidateMem
            exact wordOver candidate (by simp [candidateMem])
          have tailLength : tail.length = remaining + 1 := by
            simpa using lengthEq
          have letterEq := private_letter_before_marker
            (counter := deleted + (remaining + 1)) (deleted := deleted)
            primeProperty primeBound sourceBound privateBound
            sourcePrivateDistinct (by omega) letterMem allLocal.2.start
          subst letter
          have firstStep := loopZero_step prime privatePhase
            (deleted + (remaining + 1)) deleted primeProperty.1 (by omega)
          have canonicalLocal := phaseIncrementState_local prime privatePhase
            ((deleted + 1) + remaining) (deleted + 1) primeProperty.1
          have canonicalAll : AllStatesLocal prime tail
              (phaseAffine privatePhase
                (incrementState prime ((deleted + 1) + remaining)
                  (deleted + 1))) := by
            apply AllStatesLocal.of_sameLine
              (primePositive := by have := primeProperty.1; omega)
              allLocal.2 canonicalLocal.1
            simpa only [show deleted + (remaining + 1) =
              (deleted + 1) + remaining by omega] using firstStep.symm
          have tailEq := inductionHypothesis tailOver canonicalAll tailLength
          rw [tailEq]
          simp [incrementTail, List.replicate_succ]

/-- Among words of the prescribed execution length, locality at every
prefix forces the unique intended increment word. -/
theorem incrementWord_surviving_unique
    {prime phaseCount source target privatePhase counter : Nat}
    (primeProperty : IsPrime prime)
    (primeBound : 6 * phaseCount < prime)
    (sourceBound : source < phaseCount)
    (privateBound : privatePhase < phaseCount)
    (sourcePrivateDistinct : source ≠ privatePhase)
    {word : List PhysicalTemplate}
    (wordOver : WordOver
      (incrementAlphabet prime source target privatePhase) word)
    (allLocal : AllStatesLocal prime word
      (phaseAffine source (unaryCode prime counter)))
    (lengthEq : word.length = counter + 1) :
    word = incrementWord prime source target privatePhase counter := by
  cases counter with
  | zero =>
      cases word with
      | nil => simp at lengthEq
      | cons letter tail =>
          have tailEmpty : tail = [] := by
            apply List.eq_nil_of_length_eq_zero
            simpa using lengthEq
          subst tail
          have letterMem := wordOver letter (by simp)
          have letterEq := first_letter_at_zero primeProperty primeBound
            sourceBound privateBound sourcePrivateDistinct letterMem
            (by exact allLocal.2)
          subst letter
          simp [incrementWord]
  | succ previous =>
      cases word with
      | nil => simp at lengthEq
      | cons letter tail =>
          have letterMem := wordOver letter (by simp)
          have tailOver : WordOver
              (incrementAlphabet prime source target privatePhase) tail := by
            intro candidate candidateMem
            exact wordOver candidate (by simp [candidateMem])
          have tailLength : tail.length = previous + 1 := by
            simpa using lengthEq
          have letterEq := first_letter_at_positive
            (counter := previous) primeProperty primeBound sourceBound
            privateBound sourcePrivateDistinct letterMem allLocal.2.start
          subst letter
          have firstStep := entryZero_step prime source privatePhase
            (previous + 1) primeProperty.1 (by omega)
          have canonicalLocal := phaseIncrementState_local prime privatePhase
            (1 + previous) 1 primeProperty.1
          have canonicalAll : AllStatesLocal prime tail
              (phaseAffine privatePhase
                (incrementState prime (1 + previous) 1)) := by
            apply AllStatesLocal.of_sameLine
              (primePositive := by have := primeProperty.1; omega)
              allLocal.2 canonicalLocal.1
            simpa only [show previous + 1 = 1 + previous by omega]
              using firstStep.symm
          have tailEq := incrementTail_surviving_unique
            (deleted := 1) (remaining := previous) primeProperty primeBound
            sourceBound privateBound sourcePrivateDistinct tailOver
            canonicalAll tailLength
          rw [tailEq]
          simp [incrementWord]

/-- Every sufficiently long surviving word begins with the complete
intended increment execution.  This is the prefix form needed when the
module is cut out of an unrestricted ambient word. -/
theorem incrementWord_forced_prefix
    {prime phaseCount source target privatePhase counter : Nat}
    (primeProperty : IsPrime prime)
    (primeBound : 6 * phaseCount < prime)
    (sourceBound : source < phaseCount)
    (privateBound : privatePhase < phaseCount)
    (sourcePrivateDistinct : source ≠ privatePhase)
    {word : List PhysicalTemplate}
    (wordOver : WordOver
      (incrementAlphabet prime source target privatePhase) word)
    (allLocal : AllStatesLocal prime word
      (phaseAffine source (unaryCode prime counter)))
    (longEnough : counter + 1 ≤ word.length) :
    word.take (counter + 1) =
      incrementWord prime source target privatePhase counter := by
  apply incrementWord_surviving_unique primeProperty primeBound
    sourceBound privateBound sourcePrivateDistinct
    (wordOver.take (counter + 1)) (allLocal.take (counter + 1))
  rw [List.length_take, Nat.min_eq_left longEnough]

/-- Endpoint-local formulation of the unrestricted-word converse.  An
arbitrary word over the four increment letters may be presented without
prefix side conditions: locality of its final state makes every prefix
local, and hence forces its first complete increment block. -/
theorem incrementWord_forced_prefix_of_final_local
    {prime phaseCount source target privatePhase counter : Nat}
    (primeProperty : IsPrime prime)
    (primeBound : 6 * phaseCount < prime)
    (sourceBound : source < phaseCount)
    (privateBound : privatePhase < phaseCount)
    (sourcePrivateDistinct : source ≠ privatePhase)
    {word : List PhysicalTemplate}
    (wordOver : WordOver
      (incrementAlphabet prime source target privatePhase) word)
    (finalLocal : LocalAt prime
      (physicalWordAction prime word
        (phaseAffine source (unaryCode prime counter))))
    (longEnough : counter + 1 ≤ word.length) :
    word.take (counter + 1) =
      incrementWord prime source target privatePhase counter := by
  have inputNonzero :
      (phaseAffine source (unaryCode prime counter)).Nonzero :=
    Vec2.affine_nonzero _
  have allLocal := allStatesLocal_of_final_local
    (by have := primeProperty.1; omega) word inputNonzero finalLocal
  exact incrementWord_forced_prefix primeProperty primeBound sourceBound
    privateBound sourcePrivateDistinct wordOver allLocal longEnough

end Mortality.Compiler.IncrementModule
