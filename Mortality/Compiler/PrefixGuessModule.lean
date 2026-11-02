import Mortality.Compiler.IncrementModule

/-!
# Nonempty zero-prefix guesses

Odd halving, ternary division, and the contraction modules begin by
guessing a nonempty prefix of zero digits.  This file isolates the common
four-letter gadget.  A chosen length `b`, with `1 ≤ b ≤ n`, deletes
exactly `b` zeros from `z_n`; the last deletion is fused with `T`.
-/

namespace Mortality.Compiler.PrefixGuessModule

open Mortality.PeriodicCode
open Mortality.Compiler.UnaryArithmetic
open Mortality.Compiler.IncrementModule

def startContinue (source privatePhase : Nat) : PhysicalTemplate :=
  { sourcePhase := source
    targetPhase := privatePhase
    digit := 0
    preCoefficient := 0
    postSign := .positive
    postCoefficient := 0 }

def startExit (source handoff : Nat) : PhysicalTemplate :=
  { sourcePhase := source
    targetPhase := handoff
    digit := 0
    preCoefficient := 0
    postSign := .positive
    postCoefficient := -1 }

def privateLoop (privatePhase : Nat) : PhysicalTemplate :=
  { sourcePhase := privatePhase
    targetPhase := privatePhase
    digit := 0
    preCoefficient := 0
    postSign := .positive
    postCoefficient := 0 }

def privateExit (privatePhase handoff : Nat) : PhysicalTemplate :=
  { sourcePhase := privatePhase
    targetPhase := handoff
    digit := 0
    preCoefficient := 0
    postSign := .positive
    postCoefficient := -1 }

def prefixAlphabet (source privatePhase handoff : Nat) :
    List PhysicalTemplate :=
  [startContinue source privatePhase, startExit source handoff,
    privateLoop privatePhase, privateExit privatePhase handoff]

def prefixTail (privatePhase handoff loops : Nat) :
    List PhysicalTemplate :=
  List.replicate loops (privateLoop privatePhase) ++
    [privateExit privatePhase handoff]

def prefixWord (source privatePhase handoff length : Nat) :
    List PhysicalTemplate :=
  if length = 1 then [startExit source handoff]
  else startContinue source privatePhase ::
    prefixTail privatePhase handoff (length - 2)

@[simp] theorem prefixAlphabet_length (source privatePhase handoff : Nat) :
    (prefixAlphabet source privatePhase handoff).length = 4 := by
  rfl

@[simp] theorem prefixTail_length (privatePhase handoff loops : Nat) :
    (prefixTail privatePhase handoff loops).length = loops + 1 := by
  simp [prefixTail]

theorem prefixWord_length {source privatePhase handoff length : Nat}
    (lengthPositive : 0 < length) :
    (prefixWord source privatePhase handoff length).length = length := by
  by_cases lengthOne : length = 1
  · subst length
    simp [prefixWord]
  · simp [prefixWord, lengthOne]
    omega

theorem prefixWord_wordOver (source privatePhase handoff length : Nat) :
    WordOver (prefixAlphabet source privatePhase handoff)
      (prefixWord source privatePhase handoff length) := by
  intro letter letterMem
  by_cases lengthOne : length = 1
  · simp [prefixWord, lengthOne] at letterMem
    subst letter
    simp [prefixAlphabet]
  · simp [prefixWord, lengthOne, prefixTail] at letterMem
    rcases letterMem with rfl | ⟨_, rfl⟩ | rfl <;>
      simp [prefixAlphabet]

/-- Unary value after `deleted` leading zeros have been removed. -/
def prefixState (base counter deleted : Nat) : Rat :=
  (base : Rat) ^ (counter - deleted) /
    (1 - (base : Rat) ^ (counter + 1))

theorem prefixState_zero (base counter : Nat) :
    prefixState base counter 0 = unaryCode base counter := by
  rw [unaryCode_eq]
  simp [prefixState]

theorem prefixState_local (base counter deleted : Nat)
    (baseAtLeastTwo : 2 ≤ base) :
    LocalAt base (Vec2.affine (prefixState base counter deleted)) := by
  have denominatorNotDivisible := one_sub_power_not_dvd base (counter + 1)
    baseAtLeastTwo (by omega)
  have localFraction := local_affine_integer_div
    (prime := base) (numerator := (base : Int) ^ (counter - deleted))
    (denominator := 1 - (base : Int) ^ (counter + 1))
    denominatorNotDivisible
  simpa [prefixState, Rat.intCast_pow, Rat.intCast_natCast,
    Rat.intCast_sub] using localFraction

theorem prefixState_sameLine_integer (base counter deleted : Nat)
    (baseAtLeastTwo : 2 ≤ base) :
    SameLine (Vec2.affine (prefixState base counter deleted))
      (integerVector ((base : Int) ^ (counter - deleted))
        (1 - (base : Int) ^ (counter + 1))) := by
  have denominatorNotDivisible := one_sub_power_not_dvd base (counter + 1)
    baseAtLeastTwo (by omega)
  have denominatorNonzero : 1 - (base : Int) ^ (counter + 1) ≠ 0 :=
    fun denominatorZero => denominatorNotDivisible
      (denominatorZero ▸ Int.dvd_zero _)
  have same := affine_div_sameLine_integerVector
    (numerator := (base : Int) ^ (counter - deleted))
    (denominator := 1 - (base : Int) ^ (counter + 1))
    denominatorNonzero
  simpa [prefixState, Rat.intCast_pow, Rat.intCast_natCast,
    Rat.intCast_sub] using same

/-- Before the unary marker, a prefix-guess state occupies digit zero. -/
theorem prefixState_inPhaseAt_before
    {base phase counter deleted : Nat} (baseAtLeastTwo : 2 ≤ base)
    (deletedBelow : deleted < counter) :
    InPhaseAt base phase 0
      (phaseAffine phase (prefixState base counter deleted)) := by
  apply inPhaseAt_phaseAffine_integer
    (numerator := (base : Int) ^ (counter - deleted))
    (denominator := 1 - (base : Int) ^ (counter + 1))
    (by simp [ReservedDigit])
    (one_sub_power_not_dvd base (counter + 1) baseAtLeastTwo (by omega))
  · simpa using base_dvd_positive_power base (counter - deleted) (by omega)
  · exact prefixState_sameLine_integer base counter deleted baseAtLeastTwo

/-- At the unary marker, a prefix-guess state occupies digit one. -/
theorem prefixState_inPhaseAt_marker
    {base phase counter : Nat} (baseAtLeastTwo : 2 ≤ base) :
    InPhaseAt base phase 1
      (phaseAffine phase (prefixState base counter counter)) := by
  apply inPhaseAt_phaseAffine_integer
    (numerator := 1)
    (denominator := 1 - (base : Int) ^ (counter + 1))
    (by simp [ReservedDigit])
    (one_sub_power_not_dvd base (counter + 1) baseAtLeastTwo (by omega))
  · have powerDivisible := base_dvd_positive_power base (counter + 1)
      (by omega)
    simp only [Int.one_mul]
    rw [show (1 : Int) - (1 - (base : Int) ^ (counter + 1)) =
      (base : Int) ^ (counter + 1) by grind]
    exact powerDivisible
  · simpa using
      prefixState_sameLine_integer base counter counter baseAtLeastTwo

theorem prefixState_delete_zero (base counter deleted : Nat)
    (baseAtLeastTwo : 2 ≤ base) (deletedBelow : deleted < counter) :
    deleteDigit (base : Rat) 0 (prefixState base counter deleted) =
      prefixState base counter (deleted + 1) := by
  unfold deleteDigit prefixState
  have baseNonzero : (base : Rat) ≠ 0 := by
    simpa using (show base ≠ 0 by omega)
  have denominatorNonzero := one_sub_pow_ne_zero base (counter + 1)
    baseAtLeastTwo (by omega)
  have exponentEq : counter - deleted =
      counter - (deleted + 1) + 1 := by omega
  have powerEq : (base : Rat) ^ (counter - deleted) =
      (base : Rat) ^ (counter - (deleted + 1)) * (base : Rat) := by
    rw [exponentEq, Rat.pow_succ]
  rw [Rat.intCast_zero, Rat.div_def, Rat.div_def, Rat.div_def]
  have baseCancel := Rat.mul_inv_cancel (base : Rat) baseNonzero
  have denominatorCancel := Rat.mul_inv_cancel
    ((1 : Rat) - (base : Rat) ^ (counter + 1)) denominatorNonzero
  grind

theorem phasePrefixState_local (base phase counter deleted : Nat)
    (baseAtLeastTwo : 2 ≤ base) :
    LocalAt base (phaseAffine phase (prefixState base counter deleted)) := by
  rw [show phaseAffine phase (prefixState base counter deleted) =
      Matrix2.apply (IntMatrix2.cast (chart phase))
        (Vec2.affine (prefixState base counter deleted)) by
    simpa [phaseAffine] using
      (chart_apply phase (prefixState base counter deleted)).symm]
  exact (local_chart_iff base phase _).mpr
    (prefixState_local base counter deleted baseAtLeastTwo)

theorem phaseTPrefixState_local (base phase counter deleted : Nat)
    (baseAtLeastTwo : 2 ≤ base) :
    LocalAt base
      (phaseAffine phase (T base (prefixState base counter deleted))) := by
  have localT := mutationMap_local_of_local .positive (-1)
    (prefixState_local base counter deleted baseAtLeastTwo)
  rw [← T_eq_mutationMap] at localT
  rw [show phaseAffine phase (T base (prefixState base counter deleted)) =
      Matrix2.apply (IntMatrix2.cast (chart phase))
        (Vec2.affine (T base (prefixState base counter deleted))) by
    simpa [phaseAffine] using
      (chart_apply phase (T base (prefixState base counter deleted))).symm]
  exact (local_chart_iff base phase _).mpr localT

theorem identityZero_step
    (base source target counter deleted : Nat)
    (baseAtLeastTwo : 2 ≤ base) (deletedBelow : deleted < counter) :
    SameLine
      (Matrix2.apply
        (IntMatrix2.cast
          (physicalLetter base source target 0 0 .positive 0))
        (phaseAffine source (prefixState base counter deleted)))
      (phaseAffine target (prefixState base counter (deleted + 1))) := by
  have deletedEq := prefixState_delete_zero base counter deleted
    baseAtLeastTwo deletedBelow
  have action := physicalLetter_affine_sameLine_of_local
    (sourcePhase := source) (targetPhase := target) (digit := 0)
    (preCoefficient := 0) (postCoefficient := 0)
    (postSign := .positive) (primePositive := by omega)
    (prefixState_local base counter deleted baseAtLeastTwo)
    (by
      have nextLocal := prefixState_local base counter (deleted + 1)
        baseAtLeastTwo
      rw [← deletedEq] at nextLocal
      simpa [deleteDigit] using nextLocal)
  simp [localLetterMap] at action
  have deletedRaw := deletedEq
  unfold deleteDigit at deletedRaw
  simp only [Rat.intCast_zero] at deletedRaw
  rw [deletedRaw] at action
  exact action

theorem TZero_step
    (base source target counter deleted : Nat)
    (baseAtLeastTwo : 2 ≤ base) (deletedBelow : deleted < counter) :
    SameLine
      (Matrix2.apply
        (IntMatrix2.cast
          (physicalLetter base source target 0 0 .positive (-1)))
        (phaseAffine source (prefixState base counter deleted)))
      (phaseAffine target
        (T base (prefixState base counter (deleted + 1)))) := by
  have deletedEq := prefixState_delete_zero base counter deleted
    baseAtLeastTwo deletedBelow
  have action := physicalLetter_affine_sameLine_of_local
    (sourcePhase := source) (targetPhase := target) (digit := 0)
    (preCoefficient := 0) (postCoefficient := -1)
    (postSign := .positive) (primePositive := by omega)
    (prefixState_local base counter deleted baseAtLeastTwo)
    (by
      have nextLocal := prefixState_local base counter (deleted + 1)
        baseAtLeastTwo
      rw [← deletedEq] at nextLocal
      simpa [deleteDigit] using nextLocal)
  simp [localLetterMap, ← T_eq_mutationMap] at action
  have deletedRaw := deletedEq
  unfold deleteDigit at deletedRaw
  simp only [Rat.intCast_zero] at deletedRaw
  rw [deletedRaw] at action
  exact action

theorem startContinue_step
    (base source privatePhase counter : Nat) (baseAtLeastTwo : 2 ≤ base)
    (counterPositive : 0 < counter) :
    SameLine
      ((startContinue source privatePhase).act base
        (phaseAffine source (unaryCode base counter)))
      (phaseAffine privatePhase (prefixState base counter 1)) := by
  rw [← prefixState_zero base counter]
  simpa [startContinue, PhysicalTemplate.act, PhysicalTemplate.matrix] using
    identityZero_step base source privatePhase counter 0 baseAtLeastTwo
      counterPositive

theorem startExit_step
    (base source handoff counter : Nat) (baseAtLeastTwo : 2 ≤ base)
    (counterPositive : 0 < counter) :
    SameLine
      ((startExit source handoff).act base
        (phaseAffine source (unaryCode base counter)))
      (phaseAffine handoff (T base (prefixState base counter 1))) := by
  rw [← prefixState_zero base counter]
  simpa [startExit, PhysicalTemplate.act, PhysicalTemplate.matrix] using
    TZero_step base source handoff counter 0 baseAtLeastTwo counterPositive

theorem privateLoop_step
    (base privatePhase counter deleted : Nat)
    (baseAtLeastTwo : 2 ≤ base) (deletedBelow : deleted < counter) :
    SameLine
      ((privateLoop privatePhase).act base
        (phaseAffine privatePhase (prefixState base counter deleted)))
      (phaseAffine privatePhase
        (prefixState base counter (deleted + 1))) := by
  simpa [privateLoop, PhysicalTemplate.act, PhysicalTemplate.matrix] using
    identityZero_step base privatePhase privatePhase counter deleted
      baseAtLeastTwo deletedBelow

theorem privateExit_step
    (base privatePhase handoff counter deleted : Nat)
    (baseAtLeastTwo : 2 ≤ base) (deletedBelow : deleted < counter) :
    SameLine
      ((privateExit privatePhase handoff).act base
        (phaseAffine privatePhase (prefixState base counter deleted)))
      (phaseAffine handoff
        (T base (prefixState base counter (deleted + 1)))) := by
  simpa [privateExit, PhysicalTemplate.act, PhysicalTemplate.matrix] using
    TZero_step base privatePhase handoff counter deleted baseAtLeastTwo
      deletedBelow

theorem prefixTail_correct
    (base privatePhase handoff counter deleted loops : Nat)
    (baseAtLeastTwo : 2 ≤ base)
    (finalDeletionBelow : deleted + loops < counter) :
    SameLine
      (physicalWordAction base (prefixTail privatePhase handoff loops)
        (phaseAffine privatePhase (prefixState base counter deleted)))
      (phaseAffine handoff
        (T base (prefixState base counter (deleted + loops + 1)))) := by
  induction loops generalizing deleted with
  | zero =>
      simpa [prefixTail, physicalWordAction] using
        privateExit_step base privatePhase handoff counter deleted
          baseAtLeastTwo (by simpa using finalDeletionBelow)
  | succ loops inductionHypothesis =>
      have firstStep := privateLoop_step base privatePhase counter deleted
        baseAtLeastTwo (by omega)
      have tailRun := inductionHypothesis (deleted := deleted + 1) (by omega)
      have tailRun' : SameLine
          (physicalWordAction base (prefixTail privatePhase handoff loops)
            (phaseAffine privatePhase
              (prefixState base counter (deleted + 1))))
          (phaseAffine handoff
            (T base
              (prefixState base counter (deleted + (loops + 1) + 1)))) := by
        simpa only [show deleted + 1 + loops + 1 =
          deleted + (loops + 1) + 1 by omega] using tailRun
      have combined := physicalWordAction_cons_sameLine base
        (privateLoop privatePhase) (prefixTail privatePhase handoff loops)
        firstStep tailRun'
      simpa [prefixTail, List.replicate_succ, physicalWordAction]
        using combined

/-- Every nonempty prefix no longer than the zero block has the intended
successful guessed-prefix execution. -/
theorem prefixWord_correct
    (base source privatePhase handoff counter length : Nat)
    (baseAtLeastTwo : 2 ≤ base) (lengthPositive : 0 < length)
    (lengthBound : length ≤ counter) :
    SameLine
      (physicalWordAction base
        (prefixWord source privatePhase handoff length)
        (phaseAffine source (unaryCode base counter)))
      (phaseAffine handoff
        (T base (prefixState base counter length))) := by
  by_cases lengthOne : length = 1
  · subst length
    simpa [prefixWord, physicalWordAction] using
      startExit_step base source handoff counter baseAtLeastTwo (by omega)
  · have lengthAtLeastTwo : 2 ≤ length := by omega
    have firstStep := startContinue_step base source privatePhase counter
      baseAtLeastTwo (by omega)
    have tailRun := prefixTail_correct base privatePhase handoff counter 1
      (length - 2) baseAtLeastTwo (by omega)
    have tailRun' : SameLine
        (physicalWordAction base
          (prefixTail privatePhase handoff (length - 2))
          (phaseAffine privatePhase (prefixState base counter 1)))
        (phaseAffine handoff
          (T base (prefixState base counter length))) := by
      simpa only [show 1 + (length - 2) + 1 = length by omega]
        using tailRun
    have combined := physicalWordAction_cons_sameLine base
      (startContinue source privatePhase)
      (prefixTail privatePhase handoff (length - 2)) firstStep tailRun'
    simpa [prefixWord, lengthOne] using combined

/-- Forward obligation for a fixed prefix choice, including all prefix
states and exact word length. -/
theorem prefix_execution
    (base source privatePhase handoff counter length : Nat)
    (baseAtLeastTwo : 2 ≤ base) (lengthPositive : 0 < length)
    (lengthBound : length ≤ counter) :
    let word := prefixWord source privatePhase handoff length
    WordOver (prefixAlphabet source privatePhase handoff) word ∧
      word.length = length ∧
      SameLine
        (physicalWordAction base word
          (phaseAffine source (unaryCode base counter)))
        (phaseAffine handoff
          (T base (prefixState base counter length))) ∧
      AllStatesLocal base word
        (phaseAffine source (unaryCode base counter)) := by
  dsimp
  have action := prefixWord_correct base source privatePhase handoff counter
    length baseAtLeastTwo lengthPositive lengthBound
  have inputLocal := phaseUnaryCode_local base source counter baseAtLeastTwo
  have outputNonzero := physicalWordAction_nonzero (prime := base) (by omega)
    (prefixWord source privatePhase handoff length) inputLocal.1
  have finalLocal := LocalAt.of_sameLine
    (phaseTPrefixState_local base handoff counter length baseAtLeastTwo)
    outputNonzero action
  exact ⟨prefixWord_wordOver source privatePhase handoff length,
    prefixWord_length lengthPositive, action,
    allStatesLocal_of_final_local (by omega) _ inputLocal.1 finalLocal⟩

private theorem prefixLetter_source_bound
    {phaseCount source privatePhase handoff : Nat}
    {letter : PhysicalTemplate}
    (sourceBound : source < phaseCount)
    (privateBound : privatePhase < phaseCount)
    (letterMem : letter ∈ prefixAlphabet source privatePhase handoff) :
    letter.sourcePhase < phaseCount := by
  simp [prefixAlphabet] at letterMem
  rcases letterMem with rfl | rfl | rfl | rfl <;>
    simp [startContinue, startExit, privateLoop, privateExit, sourceBound,
      privateBound]

private theorem prefixLetter_reserved
    {source privatePhase handoff : Nat} {letter : PhysicalTemplate}
    (letterMem : letter ∈ prefixAlphabet source privatePhase handoff) :
    ReservedDigit letter.digit := by
  simp [prefixAlphabet] at letterMem
  rcases letterMem with rfl | rfl | rfl | rfl <;>
    simp [startContinue, startExit, privateLoop, privateExit, ReservedDigit]

/-- At a positive unary input, precisely the two source-phase choices can
survive: continue the guess or end it after the first zero. -/
theorem source_letter_positive
    {prime phaseCount source privatePhase handoff counter : Nat}
    (primeProperty : IsPrime prime)
    (primeBound : 6 * phaseCount < prime)
    (sourceBound : source < phaseCount)
    (privateBound : privatePhase < phaseCount)
    (sourcePrivateDistinct : source ≠ privatePhase)
    {letter : PhysicalTemplate}
    (letterMem : letter ∈ prefixAlphabet source privatePhase handoff)
    (outputLocal : LocalAt prime
      (letter.act prime
        (phaseAffine source (unaryCode prime (counter + 1))))) :
    letter = startContinue source privatePhase ∨
      letter = startExit source handoff := by
  have digitsEq : unaryDigits (counter + 1) = 0 :: unaryDigits counter := by
    simp [unaryDigits, List.replicate_succ]
  have forced := physicalLetter_periodic_affine_source_digit_unique
    (prime := prime) (phaseCount := phaseCount)
    (actualPhase := source) (sourcePhase := letter.sourcePhase)
    (targetPhase := letter.targetPhase) (actualDigit := 0)
    (letterDigit := letter.digit)
    (preCoefficient := letter.preCoefficient)
    (postCoefficient := letter.postCoefficient)
    (postSign := letter.postSign) (unaryDigits counter) primeProperty
    primeBound sourceBound
    (prefixLetter_source_bound sourceBound privateBound letterMem)
    (by simp [ReservedDigit]) (prefixLetter_reserved letterMem)
    (by simpa [PhysicalTemplate.act, PhysicalTemplate.matrix, phaseAffine,
      unaryCode, digitsEq] using outputLocal)
  simp [prefixAlphabet] at letterMem
  rcases letterMem with rfl | rfl | rfl | rfl
  · exact Or.inl rfl
  · exact Or.inr rfl
  · exact False.elim (sourcePrivateDistinct forced.1)
  · exact False.elim (sourcePrivateDistinct forced.1)

/-- The gadget cannot start on `z_0`, because it has no marker-one
entry. -/
theorem source_rejects_zero
    {prime phaseCount source privatePhase handoff : Nat}
    (primeProperty : IsPrime prime)
    (primeBound : 6 * phaseCount < prime)
    (sourceBound : source < phaseCount)
    (privateBound : privatePhase < phaseCount)
    {letter : PhysicalTemplate}
    (letterMem : letter ∈ prefixAlphabet source privatePhase handoff) :
    ¬LocalAt prime
      (letter.act prime (phaseAffine source (unaryCode prime 0))) := by
  intro outputLocal
  have forced := physicalLetter_periodic_affine_source_digit_unique
    (prime := prime) (phaseCount := phaseCount)
    (actualPhase := source) (sourcePhase := letter.sourcePhase)
    (targetPhase := letter.targetPhase) (actualDigit := 1)
    (letterDigit := letter.digit)
    (preCoefficient := letter.preCoefficient)
    (postCoefficient := letter.postCoefficient)
    (postSign := letter.postSign) [] primeProperty primeBound sourceBound
    (prefixLetter_source_bound sourceBound privateBound letterMem)
    (by simp [ReservedDigit]) (prefixLetter_reserved letterMem)
    (by simpa [PhysicalTemplate.act, PhysicalTemplate.matrix, phaseAffine,
      unaryCode, unaryDigits] using outputLocal)
  simp [prefixAlphabet] at letterMem
  rcases letterMem with rfl | rfl | rfl | rfl <;>
    simp [startContinue, startExit, privateLoop, privateExit] at forced

/-- While zeros remain in the private phase, the word may either consume
another zero or choose the current one as the last prefix digit. -/
theorem private_letter_before_marker
    {prime phaseCount source privatePhase handoff counter deleted : Nat}
    (primeProperty : IsPrime prime)
    (primeBound : 6 * phaseCount < prime)
    (sourceBound : source < phaseCount)
    (privateBound : privatePhase < phaseCount)
    (sourcePrivateDistinct : source ≠ privatePhase)
    (deletedBelow : deleted < counter)
    {letter : PhysicalTemplate}
    (letterMem : letter ∈ prefixAlphabet source privatePhase handoff)
    (outputLocal : LocalAt prime
      (letter.act prime
        (phaseAffine privatePhase
          (prefixState prime counter deleted)))) :
    letter = privateLoop privatePhase ∨
      letter = privateExit privatePhase handoff := by
  have denominatorNotDivisible := one_sub_power_not_dvd prime (counter + 1)
    primeProperty.1 (by omega)
  have actualResidue : (prime : Int) ∣
      (prime : Int) ^ (counter - deleted) -
        0 * (1 - (prime : Int) ^ (counter + 1)) := by
    simpa using base_dvd_positive_power prime (counter - deleted) (by omega)
  have forced := physicalLetter_affine_integer_source_digit_unique
    (prime := prime) (phaseCount := phaseCount)
    (actualPhase := privatePhase) (sourcePhase := letter.sourcePhase)
    (targetPhase := letter.targetPhase) (actualDigit := 0)
    (letterDigit := letter.digit)
    (preCoefficient := letter.preCoefficient)
    (postCoefficient := letter.postCoefficient)
    (postSign := letter.postSign) primeProperty primeBound privateBound
    (prefixLetter_source_bound sourceBound privateBound letterMem)
    (by simp [ReservedDigit]) (prefixLetter_reserved letterMem)
    denominatorNotDivisible actualResidue
    (prefixState_sameLine_integer prime counter deleted primeProperty.1)
    (by simpa [PhysicalTemplate.act, PhysicalTemplate.matrix, phaseAffine]
      using outputLocal)
  simp [prefixAlphabet] at letterMem
  rcases letterMem with rfl | rfl | rfl | rfl
  · exact False.elim (sourcePrivateDistinct forced.1.symm)
  · exact False.elim (sourcePrivateDistinct forced.1.symm)
  · exact Or.inl rfl
  · exact Or.inr rfl

/-- A prefix guess cannot pass the unary marker: all four of its letters
delete zero. -/
theorem private_rejects_marker
    {prime phaseCount source privatePhase handoff counter : Nat}
    (primeProperty : IsPrime prime)
    (primeBound : 6 * phaseCount < prime)
    (sourceBound : source < phaseCount)
    (privateBound : privatePhase < phaseCount)
    {letter : PhysicalTemplate}
    (letterMem : letter ∈ prefixAlphabet source privatePhase handoff) :
    ¬LocalAt prime
      (letter.act prime
        (phaseAffine privatePhase
          (prefixState prime counter counter))) := by
  intro outputLocal
  have denominatorNotDivisible := one_sub_power_not_dvd prime (counter + 1)
    primeProperty.1 (by omega)
  have actualResidue : (prime : Int) ∣
      (prime : Int) ^ (counter - counter) -
        1 * (1 - (prime : Int) ^ (counter + 1)) := by
    simp only [Nat.sub_self, Int.pow_zero, Int.one_mul]
    have powerDivisible := base_dvd_positive_power prime (counter + 1)
      (by omega)
    rw [show (1 : Int) - (1 - (prime : Int) ^ (counter + 1)) =
      (prime : Int) ^ (counter + 1) by grind]
    exact powerDivisible
  have forced := physicalLetter_affine_integer_source_digit_unique
    (prime := prime) (phaseCount := phaseCount)
    (actualPhase := privatePhase) (sourcePhase := letter.sourcePhase)
    (targetPhase := letter.targetPhase) (actualDigit := 1)
    (letterDigit := letter.digit)
    (preCoefficient := letter.preCoefficient)
    (postCoefficient := letter.postCoefficient)
    (postSign := letter.postSign) primeProperty primeBound privateBound
    (prefixLetter_source_bound sourceBound privateBound letterMem)
    (by simp [ReservedDigit]) (prefixLetter_reserved letterMem)
    denominatorNotDivisible actualResidue
    (prefixState_sameLine_integer prime counter counter primeProperty.1)
    (by simpa [PhysicalTemplate.act, PhysicalTemplate.matrix, phaseAffine]
      using outputLocal)
  simp [prefixAlphabet] at letterMem
  rcases letterMem with rfl | rfl | rfl | rfl <;>
    simp [startContinue, startExit, privateLoop, privateExit] at forced

end Mortality.Compiler.PrefixGuessModule
