import Mortality.Compiler.IncrementModule

/-!
# The typed right-subtraction module

This is the two-letter scan from Lemma 5.4.  Its external type is
`T(X_{c,d})` with `c < d`; the scan deletes `c` zeros and one marker,
then applies `T⁻¹`.  The result is `X_{c,d-c-1}`.
-/

namespace Mortality.Compiler.RightSubtractionModule

open Mortality.PeriodicCode
open Mortality.Compiler.UnaryArithmetic
open Mortality.Compiler.IncrementModule

def zeroLoop (phase : Nat) : PhysicalTemplate :=
  { sourcePhase := phase
    targetPhase := phase
    digit := 0
    preCoefficient := 0
    postSign := .positive
    postCoefficient := 0 }

def markerExit (source target : Nat) : PhysicalTemplate :=
  { sourcePhase := source
    targetPhase := target
    digit := 1
    preCoefficient := 0
    postSign := .positive
    postCoefficient := 1 }

def subtractionAlphabet (source target : Nat) : List PhysicalTemplate :=
  [zeroLoop source, markerExit source target]

def subtractionWord (source target first : Nat) : List PhysicalTemplate :=
  List.replicate first (zeroLoop source) ++ [markerExit source target]

@[simp] theorem subtractionAlphabet_length (source target : Nat) :
    (subtractionAlphabet source target).length = 2 := by
  rfl

@[simp] theorem subtractionWord_length (source target first : Nat) :
    (subtractionWord source target first).length = first + 1 := by
  simp [subtractionWord]

theorem subtractionWord_wordOver (source target first : Nat) :
    WordOver (subtractionAlphabet source target)
      (subtractionWord source target first) := by
  intro letter letterMem
  simp [subtractionWord] at letterMem
  rcases letterMem with ⟨_, rfl⟩ | rfl <;>
    simp [subtractionAlphabet]

/-- Local value after `deleted` zero deletions, before the final marker. -/
def subtractionState (base first second deleted : Nat) : Rat :=
  (base : Rat) ^ (first - deleted) *
      (1 - (base : Rat) ^ (second + 1)) /
    (1 - (base : Rat) ^ (first + 1))

theorem subtractionState_zero (base first second : Nat)
    (baseAtLeastTwo : 2 ≤ base) :
    subtractionState base first second 0 =
      T base (twoFieldCode base first second) := by
  rw [T_twoFieldCode base first second baseAtLeastTwo]
  simp [subtractionState]

theorem subtractionState_local (base first second deleted : Nat)
    (baseAtLeastTwo : 2 ≤ base) :
    LocalAt base (Vec2.affine (subtractionState base first second deleted)) := by
  have denominatorNotDivisible := one_sub_power_not_dvd base (first + 1)
    baseAtLeastTwo (by omega)
  have localFraction := local_affine_integer_div
    (prime := base)
    (numerator := (base : Int) ^ (first - deleted) *
      (1 - (base : Int) ^ (second + 1)))
    (denominator := 1 - (base : Int) ^ (first + 1))
    denominatorNotDivisible
  simpa [subtractionState, Rat.intCast_pow, Rat.intCast_natCast,
    Rat.intCast_mul, Rat.intCast_sub] using localFraction

theorem phaseSubtractionState_local
    (base phase first second deleted : Nat) (baseAtLeastTwo : 2 ≤ base) :
    LocalAt base
      (phaseAffine phase (subtractionState base first second deleted)) := by
  rw [show phaseAffine phase (subtractionState base first second deleted) =
      Matrix2.apply (IntMatrix2.cast (chart phase))
        (Vec2.affine (subtractionState base first second deleted)) by
    simpa [phaseAffine] using
      (chart_apply phase (subtractionState base first second deleted)).symm]
  exact (local_chart_iff base phase _).mpr
    (subtractionState_local base first second deleted baseAtLeastTwo)

theorem phaseTwoFieldCode_local (base phase first second : Nat)
    (baseAtLeastTwo : 2 ≤ base) :
    LocalAt base
      (phaseAffine phase (twoFieldCode base first second)) := by
  rw [show phaseAffine phase (twoFieldCode base first second) =
      Matrix2.apply (IntMatrix2.cast (chart phase))
        (Vec2.affine (twoFieldCode base first second)) by
    simpa [phaseAffine] using
      (chart_apply phase (twoFieldCode base first second)).symm]
  apply (local_chart_iff base phase _).mpr
  exact periodicCode_local_affine base (twoFieldDigits first second)
    baseAtLeastTwo (by simp [twoFieldDigits])

theorem subtractionState_sameLine_integer
    (base first second deleted : Nat) (baseAtLeastTwo : 2 ≤ base) :
    SameLine (Vec2.affine (subtractionState base first second deleted))
      (integerVector
        ((base : Int) ^ (first - deleted) *
          (1 - (base : Int) ^ (second + 1)))
        (1 - (base : Int) ^ (first + 1))) := by
  have denominatorNotDivisible := one_sub_power_not_dvd base (first + 1)
    baseAtLeastTwo (by omega)
  have denominatorNonzero : 1 - (base : Int) ^ (first + 1) ≠ 0 :=
    fun denominatorZero => denominatorNotDivisible
      (denominatorZero ▸ Int.dvd_zero _)
  have same := affine_div_sameLine_integerVector
    (numerator := (base : Int) ^ (first - deleted) *
      (1 - (base : Int) ^ (second + 1)))
    (denominator := 1 - (base : Int) ^ (first + 1))
    denominatorNonzero
  simpa [subtractionState, Rat.intCast_pow, Rat.intCast_natCast,
    Rat.intCast_mul, Rat.intCast_sub] using same

theorem subtractionState_delete_zero
    (base first second deleted : Nat) (baseAtLeastTwo : 2 ≤ base)
    (deletedBelow : deleted < first) :
    deleteDigit (base : Rat) 0 (subtractionState base first second deleted) =
      subtractionState base first second (deleted + 1) := by
  unfold deleteDigit subtractionState
  have baseNonzero : (base : Rat) ≠ 0 := by
    simpa using (show base ≠ 0 by omega)
  have denominatorNonzero := one_sub_pow_ne_zero base (first + 1)
    baseAtLeastTwo (by omega)
  have exponentEq : first - deleted = first - (deleted + 1) + 1 := by
    omega
  have powerEq : (base : Rat) ^ (first - deleted) =
      (base : Rat) ^ (first - (deleted + 1)) * (base : Rat) := by
    rw [exponentEq, Rat.pow_succ]
  rw [Rat.intCast_zero, Rat.div_def, Rat.div_def, Rat.div_def]
  have baseCancel := Rat.mul_inv_cancel (base : Rat) baseNonzero
  have denominatorCancel := Rat.mul_inv_cancel
    ((1 : Rat) - (base : Rat) ^ (first + 1)) denominatorNonzero
  grind

theorem subtractionState_delete_marker
    (base first second : Nat) (baseAtLeastTwo : 2 ≤ base) :
    deleteDigit (base : Rat) 1 (subtractionState base first second first) =
      ((base : Rat) ^ first - (base : Rat) ^ second) /
        (1 - (base : Rat) ^ (first + 1)) := by
  unfold deleteDigit subtractionState
  have baseNonzero : (base : Rat) ≠ 0 := by
    simpa using (show base ≠ 0 by omega)
  have denominatorNonzero := one_sub_pow_ne_zero base (first + 1)
    baseAtLeastTwo (by omega)
  have firstSucc : (base : Rat) ^ (first + 1) =
      (base : Rat) ^ first * (base : Rat) := by
    rw [Rat.pow_succ]
  have secondSucc : (base : Rat) ^ (second + 1) =
      (base : Rat) ^ second * (base : Rat) := by
    rw [Rat.pow_succ]
  simp only [Nat.sub_self, Rat.pow_zero]
  rw [Rat.div_def, Rat.div_def, Rat.div_def]
  have baseCancel := Rat.mul_inv_cancel (base : Rat) baseNonzero
  have denominatorCancel := Rat.mul_inv_cancel
    ((1 : Rat) - (base : Rat) ^ (first + 1)) denominatorNonzero
  grind

theorem zeroLoop_step
    (base phase first second deleted : Nat) (baseAtLeastTwo : 2 ≤ base)
    (deletedBelow : deleted < first) :
    SameLine
      ((zeroLoop phase).act base
        (phaseAffine phase
          (subtractionState base first second deleted)))
      (phaseAffine phase
        (subtractionState base first second (deleted + 1))) := by
  have deletedEq := subtractionState_delete_zero base first second deleted
    baseAtLeastTwo deletedBelow
  have action := physicalLetter_affine_sameLine_of_local
    (sourcePhase := phase) (targetPhase := phase) (digit := 0)
    (preCoefficient := 0) (postCoefficient := 0)
    (postSign := .positive) (primePositive := by omega)
    (subtractionState_local base first second deleted baseAtLeastTwo)
    (by
      have nextLocal := subtractionState_local base first second (deleted + 1)
        baseAtLeastTwo
      rw [← deletedEq] at nextLocal
      simpa [deleteDigit] using nextLocal)
  simp [localLetterMap] at action
  have deletedRaw := deletedEq
  unfold deleteDigit at deletedRaw
  simp only [Rat.intCast_zero] at deletedRaw
  rw [deletedRaw] at action
  exact action

theorem markerExit_step
    (base source target first second : Nat) (baseAtLeastTwo : 2 ≤ base)
    (less : first < second) :
    SameLine
      ((markerExit source target).act base
        (phaseAffine source
          (subtractionState base first second first)))
      (phaseAffine target
        (twoFieldCode base first (second - first - 1))) := by
  have deletedEq := subtractionState_delete_marker base first second
    baseAtLeastTwo
  have result := right_subtraction base first second baseAtLeastTwo less
  rw [right_subtraction_middle base first second baseAtLeastTwo] at result
  have deletedLocal : LocalAt base
      (Vec2.affine
        (deleteDigit (base : Rat) 1
          (subtractionState base first second first))) := by
    have denominatorNotDivisible := one_sub_power_not_dvd base (first + 1)
      baseAtLeastTwo (by omega)
    have middleLocal := local_affine_integer_div
      (prime := base)
      (numerator := (base : Int) ^ first - (base : Int) ^ second)
      (denominator := 1 - (base : Int) ^ (first + 1))
      denominatorNotDivisible
    rw [deletedEq]
    simpa [Rat.intCast_sub, Rat.intCast_pow, Rat.intCast_natCast] using
      middleLocal
  have action := physicalLetter_affine_sameLine_of_local
    (sourcePhase := source) (targetPhase := target) (digit := 1)
    (preCoefficient := 0) (postCoefficient := 1)
    (postSign := .positive) (primePositive := by omega)
    (subtractionState_local base first second first baseAtLeastTwo)
    (by simpa [deleteDigit] using deletedLocal)
  simp [localLetterMap, ← Tinv_eq_mutationMap] at action
  have deletedRaw := deletedEq
  unfold deleteDigit at deletedRaw
  simp only [Rat.intCast_one] at deletedRaw
  rw [deletedRaw, result] at action
  exact action

theorem subtractionTail_correct
    (base source target deleted remaining second : Nat)
    (baseAtLeastTwo : 2 ≤ base) (less : deleted + remaining < second) :
    SameLine
      (physicalWordAction base
        (List.replicate remaining (zeroLoop source) ++
          [markerExit source target])
        (phaseAffine source
          (subtractionState base (deleted + remaining) second deleted)))
      (phaseAffine target
        (twoFieldCode base (deleted + remaining)
          (second - (deleted + remaining) - 1))) := by
  induction remaining generalizing deleted with
  | zero =>
      simpa [physicalWordAction] using
        markerExit_step base source target deleted second baseAtLeastTwo
          (by simpa using less)
  | succ remaining inductionHypothesis =>
      have firstStep := zeroLoop_step base source
        (deleted + (remaining + 1)) second deleted baseAtLeastTwo (by omega)
      have tailRun := inductionHypothesis (deleted := deleted + 1) (by omega)
      have tailRun' :
          SameLine
            (physicalWordAction base
              (List.replicate remaining (zeroLoop source) ++
                [markerExit source target])
              (phaseAffine source
                (subtractionState base (deleted + (remaining + 1)) second
                  (deleted + 1))))
            (phaseAffine target
              (twoFieldCode base (deleted + (remaining + 1))
                (second - (deleted + (remaining + 1)) - 1))) := by
        simpa only [show deleted + 1 + remaining =
          deleted + (remaining + 1) by omega] using tailRun
      have combined := physicalWordAction_cons_sameLine base
        (zeroLoop source)
        (List.replicate remaining (zeroLoop source) ++
          [markerExit source target]) firstStep tailRun'
      simpa [List.replicate_succ, physicalWordAction] using combined

theorem subtractionWord_correct
    (base source target first second : Nat) (baseAtLeastTwo : 2 ≤ base)
    (less : first < second) :
    SameLine
      (physicalWordAction base (subtractionWord source target first)
        (phaseAffine source (T base (twoFieldCode base first second))))
      (phaseAffine target
        (twoFieldCode base first (second - first - 1))) := by
  rw [← subtractionState_zero base first second baseAtLeastTwo]
  simpa [subtractionWord] using
    subtractionTail_correct base source target 0 first second baseAtLeastTwo
      (by simpa using less)

/-- Forward typed-module obligation, including all surviving prefixes. -/
theorem subtraction_execution
    (base source target first second : Nat) (baseAtLeastTwo : 2 ≤ base)
    (less : first < second) :
    let word := subtractionWord source target first
    WordOver (subtractionAlphabet source target) word ∧
      word.length = first + 1 ∧
      SameLine
        (physicalWordAction base word
          (phaseAffine source (T base (twoFieldCode base first second))))
        (phaseAffine target
          (twoFieldCode base first (second - first - 1))) ∧
      AllStatesLocal base word
        (phaseAffine source (T base (twoFieldCode base first second))) := by
  dsimp
  have action := subtractionWord_correct base source target first second
    baseAtLeastTwo less
  have inputLocal : LocalAt base
      (phaseAffine source (T base (twoFieldCode base first second))) := by
    rw [← subtractionState_zero base first second baseAtLeastTwo]
    exact phaseSubtractionState_local base source first second 0
      baseAtLeastTwo
  have outputNonzero := physicalWordAction_nonzero (prime := base) (by omega)
    (subtractionWord source target first) inputLocal.1
  have finalLocal := LocalAt.of_sameLine
    (phaseTwoFieldCode_local base target first (second - first - 1)
      baseAtLeastTwo) outputNonzero action
  exact ⟨subtractionWord_wordOver source target first,
    subtractionWord_length source target first, action,
    allStatesLocal_of_final_local (by omega) _ inputLocal.1 finalLocal⟩

private theorem subtractionLetter_source_bound
    {phaseCount source target : Nat} {letter : PhysicalTemplate}
    (sourceBound : source < phaseCount)
    (letterMem : letter ∈ subtractionAlphabet source target) :
    letter.sourcePhase < phaseCount := by
  simp [subtractionAlphabet] at letterMem
  rcases letterMem with rfl | rfl <;>
    simpa [zeroLoop, markerExit] using sourceBound

private theorem subtractionLetter_reserved
    {source target : Nat} {letter : PhysicalTemplate}
    (letterMem : letter ∈ subtractionAlphabet source target) :
    ReservedDigit letter.digit := by
  simp [subtractionAlphabet] at letterMem
  rcases letterMem with rfl | rfl <;>
    simp [zeroLoop, markerExit, ReservedDigit]

/-- Before the marker, the only module letter that can preserve locality
is the zero loop. -/
theorem letter_before_marker
    {prime phaseCount source target first second deleted : Nat}
    (primeProperty : IsPrime prime)
    (primeBound : 6 * phaseCount < prime)
    (sourceBound : source < phaseCount)
    (deletedBelow : deleted < first)
    {letter : PhysicalTemplate}
    (letterMem : letter ∈ subtractionAlphabet source target)
    (outputLocal : LocalAt prime
      (letter.act prime
        (phaseAffine source
          (subtractionState prime first second deleted)))) :
    letter = zeroLoop source := by
  have denominatorNotDivisible := one_sub_power_not_dvd prime (first + 1)
    primeProperty.1 (by omega)
  have actualResidue : (prime : Int) ∣
      (prime : Int) ^ (first - deleted) *
          (1 - (prime : Int) ^ (second + 1)) -
        0 * (1 - (prime : Int) ^ (first + 1)) := by
    have dividesPower := base_dvd_positive_power prime (first - deleted)
      (by omega)
    rcases dividesPower with ⟨factor, factorEq⟩
    refine ⟨factor * (1 - (prime : Int) ^ (second + 1)), ?_⟩
    simp only [Int.zero_mul, Int.sub_zero]
    rw [factorEq]
    grind
  have forced := physicalLetter_affine_integer_source_digit_unique
    (prime := prime) (phaseCount := phaseCount)
    (actualPhase := source) (sourcePhase := letter.sourcePhase)
    (targetPhase := letter.targetPhase) (actualDigit := 0)
    (letterDigit := letter.digit)
    (preCoefficient := letter.preCoefficient)
    (postCoefficient := letter.postCoefficient)
    (postSign := letter.postSign) primeProperty primeBound sourceBound
    (subtractionLetter_source_bound sourceBound letterMem)
    (by simp [ReservedDigit]) (subtractionLetter_reserved letterMem)
    denominatorNotDivisible actualResidue
    (subtractionState_sameLine_integer prime first second deleted
      primeProperty.1)
    (by simpa [PhysicalTemplate.act, PhysicalTemplate.matrix, phaseAffine]
      using outputLocal)
  simp [subtractionAlphabet] at letterMem
  rcases letterMem with rfl | rfl
  · rfl
  · simp [markerExit] at forced

/-- At the marker, the only surviving module letter is the exit. -/
theorem letter_at_marker
    {prime phaseCount source target first second : Nat}
    (primeProperty : IsPrime prime)
    (primeBound : 6 * phaseCount < prime)
    (sourceBound : source < phaseCount)
    {letter : PhysicalTemplate}
    (letterMem : letter ∈ subtractionAlphabet source target)
    (outputLocal : LocalAt prime
      (letter.act prime
        (phaseAffine source
          (subtractionState prime first second first)))) :
    letter = markerExit source target := by
  have denominatorNotDivisible := one_sub_power_not_dvd prime (first + 1)
    primeProperty.1 (by omega)
  have firstPowerDivisible := base_dvd_positive_power prime (first + 1)
    (by omega)
  have secondPowerDivisible := base_dvd_positive_power prime (second + 1)
    (by omega)
  have actualResidue : (prime : Int) ∣
      (prime : Int) ^ (first - first) *
          (1 - (prime : Int) ^ (second + 1)) -
        1 * (1 - (prime : Int) ^ (first + 1)) := by
    simp only [Nat.sub_self, Int.pow_zero, Int.one_mul]
    rcases firstPowerDivisible with ⟨firstFactor, firstEq⟩
    rcases secondPowerDivisible with ⟨secondFactor, secondEq⟩
    refine ⟨firstFactor - secondFactor, ?_⟩
    rw [firstEq, secondEq]
    grind
  have forced := physicalLetter_affine_integer_source_digit_unique
    (prime := prime) (phaseCount := phaseCount)
    (actualPhase := source) (sourcePhase := letter.sourcePhase)
    (targetPhase := letter.targetPhase) (actualDigit := 1)
    (letterDigit := letter.digit)
    (preCoefficient := letter.preCoefficient)
    (postCoefficient := letter.postCoefficient)
    (postSign := letter.postSign) primeProperty primeBound sourceBound
    (subtractionLetter_source_bound sourceBound letterMem)
    (by simp [ReservedDigit]) (subtractionLetter_reserved letterMem)
    denominatorNotDivisible actualResidue
    (subtractionState_sameLine_integer prime first second first
      primeProperty.1)
    (by simpa [PhysicalTemplate.act, PhysicalTemplate.matrix, phaseAffine]
      using outputLocal)
  simp [subtractionAlphabet] at letterMem
  rcases letterMem with rfl | rfl
  · simp [zeroLoop] at forced
  · rfl

/-- Exact uniqueness of a surviving typed subtraction scan. -/
theorem subtractionTail_surviving_unique
    {prime phaseCount source target deleted remaining second : Nat}
    (primeProperty : IsPrime prime)
    (primeBound : 6 * phaseCount < prime)
    (sourceBound : source < phaseCount)
    {word : List PhysicalTemplate}
    (wordOver : WordOver (subtractionAlphabet source target) word)
    (allLocal : AllStatesLocal prime word
      (phaseAffine source
        (subtractionState prime (deleted + remaining) second deleted)))
    (lengthEq : word.length = remaining + 1) :
    word = List.replicate remaining (zeroLoop source) ++
      [markerExit source target] := by
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
          have letterEq := letter_at_marker primeProperty primeBound
            sourceBound letterMem (by exact allLocal.2)
          subst letter
          simp
  | succ remaining inductionHypothesis =>
      cases word with
      | nil => simp at lengthEq
      | cons letter tail =>
          have letterMem := wordOver letter (by simp)
          have tailOver : WordOver (subtractionAlphabet source target) tail := by
            intro candidate candidateMem
            exact wordOver candidate (by simp [candidateMem])
          have tailLength : tail.length = remaining + 1 := by
            simpa using lengthEq
          have letterEq := letter_before_marker
            (first := deleted + (remaining + 1)) (deleted := deleted)
            primeProperty primeBound sourceBound (by omega) letterMem
            allLocal.2.start
          subst letter
          have firstStep := zeroLoop_step prime source
            (deleted + (remaining + 1)) second deleted primeProperty.1
            (by omega)
          have canonicalLocal := phaseSubtractionState_local prime source
            ((deleted + 1) + remaining) second (deleted + 1)
            primeProperty.1
          have canonicalAll : AllStatesLocal prime tail
              (phaseAffine source
                (subtractionState prime ((deleted + 1) + remaining) second
                  (deleted + 1))) := by
            apply AllStatesLocal.of_sameLine
              (primePositive := by have := primeProperty.1; omega)
              allLocal.2 canonicalLocal.1
            simpa only [show deleted + (remaining + 1) =
              (deleted + 1) + remaining by omega] using firstStep.symm
          have tailEq := inductionHypothesis tailOver canonicalAll tailLength
          rw [tailEq]
          simp [List.replicate_succ]

theorem subtractionWord_surviving_unique
    {prime phaseCount source target first second : Nat}
    (primeProperty : IsPrime prime)
    (primeBound : 6 * phaseCount < prime)
    (sourceBound : source < phaseCount)
    {word : List PhysicalTemplate}
    (wordOver : WordOver (subtractionAlphabet source target) word)
    (allLocal : AllStatesLocal prime word
      (phaseAffine source (T prime (twoFieldCode prime first second))))
    (lengthEq : word.length = first + 1) :
    word = subtractionWord source target first := by
  rw [← subtractionState_zero prime first second primeProperty.1] at allLocal
  have allLocal' : AllStatesLocal prime word
      (phaseAffine source
        (subtractionState prime (0 + first) second 0)) := by
    simpa using allLocal
  simpa [subtractionWord] using
    subtractionTail_surviving_unique (deleted := 0) (remaining := first)
      (second := second) primeProperty primeBound sourceBound wordOver allLocal'
      lengthEq

theorem subtractionWord_forced_prefix_of_final_local
    {prime phaseCount source target first second : Nat}
    (primeProperty : IsPrime prime)
    (primeBound : 6 * phaseCount < prime)
    (sourceBound : source < phaseCount)
    {word : List PhysicalTemplate}
    (wordOver : WordOver (subtractionAlphabet source target) word)
    (finalLocal : LocalAt prime
      (physicalWordAction prime word
        (phaseAffine source (T prime (twoFieldCode prime first second)))))
    (longEnough : first + 1 ≤ word.length) :
    word.take (first + 1) = subtractionWord source target first := by
  have inputLocal : LocalAt prime
      (phaseAffine source (T prime (twoFieldCode prime first second))) := by
    rw [← subtractionState_zero prime first second primeProperty.1]
    exact phaseSubtractionState_local prime source first second 0
      primeProperty.1
  have allLocal := allStatesLocal_of_final_local
    (by have := primeProperty.1; omega) word inputLocal.1 finalLocal
  apply subtractionWord_surviving_unique primeProperty primeBound sourceBound
    (wordOver.take (first + 1)) (allLocal.take (first + 1))
  rw [List.length_take, Nat.min_eq_left longEnough]

end Mortality.Compiler.RightSubtractionModule
