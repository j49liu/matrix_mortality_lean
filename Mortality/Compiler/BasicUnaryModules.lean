import Mortality.Compiler.IncrementModule

/-!
# One-letter unary decrement and zero-test modules

These are the remaining two basic modules in Proposition 5.2.  In
addition to their successful actions, this file proves their exact domain
conditions from affine phase enforcement: decrement rejects `z_0`, and
the zero test rejects every positive unary code.
-/

namespace Mortality.Compiler.BasicUnaryModules

open Mortality.PeriodicCode
open Mortality.Compiler.UnaryArithmetic
open Mortality.Compiler.IncrementModule

def decrementLetter (prime source target : Nat) : PhysicalTemplate :=
  { sourcePhase := source
    targetPhase := target
    digit := 0
    preCoefficient := 0
    postSign := .positive
    postCoefficient := (prime : Int) - 1 }

def zeroTestLetter (source target : Nat) : PhysicalTemplate :=
  { sourcePhase := source
    targetPhase := target
    digit := 1
    preCoefficient := 0
    postSign := .positive
    postCoefficient := 0 }

theorem unaryDigits_succ (counter : Nat) :
    unaryDigits (counter + 1) = 0 :: unaryDigits counter := by
  simp [unaryDigits, List.replicate_succ]

theorem phaseAffine_local (base phase counter : Nat)
    (baseAtLeastTwo : 2 ≤ base) :
    LocalAt base (phaseAffine phase (unaryCode base counter)) := by
  rw [show phaseAffine phase (unaryCode base counter) =
      Matrix2.apply (IntMatrix2.cast (chart phase))
        (Vec2.affine (unaryCode base counter)) by
    simpa [phaseAffine] using
      (chart_apply phase (unaryCode base counter)).symm]
  exact (local_chart_iff base phase _).mpr
    (unaryCode_local base counter baseAtLeastTwo)

theorem deletion_from_positive_unary_local (base counter : Nat)
    (baseAtLeastTwo : 2 ≤ base) :
    LocalAt base
      (Vec2.affine
        (deleteDigit (base : Rat) 0 (unaryCode base (counter + 1)))) := by
  have rotated := deleteDigit_periodicCode_local base 0
    (unaryDigits counter) baseAtLeastTwo
  simpa [unaryCode, unaryDigits_succ] using rotated

/-- Successful positive decrement. -/
theorem decrementLetter_correct (base source target counter : Nat)
    (baseAtLeastTwo : 2 ≤ base) :
    SameLine
      ((decrementLetter base source target).act base
        (phaseAffine source (unaryCode base (counter + 1))))
      (phaseAffine target (unaryCode base counter)) := by
  have action := physicalLetter_affine_sameLine_of_local
    (sourcePhase := source) (targetPhase := target)
    (digit := 0) (preCoefficient := 0)
    (postCoefficient := (base : Int) - 1) (postSign := .positive)
    (primePositive := by omega)
    (unaryCode_local base (counter + 1) baseAtLeastTwo)
    (by
      simpa [deleteDigit] using
        (deletion_from_positive_unary_local base counter baseAtLeastTwo))
  simp [localLetterMap, ← Sinv_eq_mutationMap] at action
  have decrementEq := decrement_step base counter baseAtLeastTwo
  unfold deleteDigit at decrementEq
  simp only [Rat.intCast_zero] at decrementEq
  rw [decrementEq] at action
  exact action

/-- Successful zero test. -/
theorem zeroTestLetter_correct (base source target : Nat)
    (baseAtLeastTwo : 2 ≤ base) :
    SameLine
      ((zeroTestLetter source target).act base
        (phaseAffine source (unaryCode base 0)))
      (phaseAffine target (unaryCode base 0)) := by
  have rotation := physicalLetter_rotates_periodicCode base source target
    1 [] baseAtLeastTwo
  simpa [zeroTestLetter, PhysicalTemplate.act, PhysicalTemplate.matrix,
    phaseAffine, unaryCode, unaryDigits] using rotation

theorem decrement_rejects_zero
    {prime phaseCount source target : Nat}
    (primeProperty : IsPrime prime)
    (primeBound : 6 * phaseCount < prime)
    (sourceBound : source < phaseCount) :
    ¬LocalAt prime
      ((decrementLetter prime source target).act prime
        (phaseAffine source (unaryCode prime 0))) := by
  intro outputLocal
  have forced := physicalLetter_periodic_affine_source_digit_unique
    (prime := prime) (phaseCount := phaseCount)
    (actualPhase := source) (sourcePhase := source)
    (targetPhase := target) (actualDigit := 1) (letterDigit := 0)
    (preCoefficient := 0) (postCoefficient := (prime : Int) - 1)
    (postSign := .positive) [] primeProperty primeBound sourceBound
    sourceBound (by simp [ReservedDigit]) (by simp [ReservedDigit])
    (by
      simpa [decrementLetter, PhysicalTemplate.act, PhysicalTemplate.matrix,
        phaseAffine, unaryCode, unaryDigits] using outputLocal)
  omega

theorem zeroTest_rejects_positive
    {prime phaseCount source target counter : Nat}
    (primeProperty : IsPrime prime)
    (primeBound : 6 * phaseCount < prime)
    (sourceBound : source < phaseCount) :
    ¬LocalAt prime
      ((zeroTestLetter source target).act prime
        (phaseAffine source (unaryCode prime (counter + 1)))) := by
  intro outputLocal
  have forced := physicalLetter_periodic_affine_source_digit_unique
    (prime := prime) (phaseCount := phaseCount)
    (actualPhase := source) (sourcePhase := source)
    (targetPhase := target) (actualDigit := 0) (letterDigit := 1)
    (preCoefficient := 0) (postCoefficient := 0)
    (postSign := .positive) (unaryDigits counter) primeProperty primeBound
    sourceBound sourceBound (by simp [ReservedDigit])
    (by simp [ReservedDigit])
    (by
      simpa [zeroTestLetter, PhysicalTemplate.act, PhysicalTemplate.matrix,
        phaseAffine, unaryCode, unaryDigits_succ] using outputLocal)
  omega

/-- Exact local domain of the decrement module. -/
theorem decrement_output_local_iff
    {prime phaseCount source target counter : Nat}
    (primeProperty : IsPrime prime)
    (primeBound : 6 * phaseCount < prime)
    (sourceBound : source < phaseCount) :
    LocalAt prime
        ((decrementLetter prime source target).act prime
          (phaseAffine source (unaryCode prime counter))) ↔
      0 < counter := by
  constructor
  · intro outputLocal
    cases counter with
    | zero =>
        exact False.elim
          (decrement_rejects_zero primeProperty primeBound sourceBound
            outputLocal)
    | succ previous => exact Nat.zero_lt_succ previous
  · intro counterPositive
    cases counter with
    | zero => omega
    | succ previous =>
        have same := decrementLetter_correct prime source target previous
          primeProperty.1
        have primePositive : 0 < prime := by
          have := primeProperty.1
          omega
        have outputNonzero :=
          (decrementLetter prime source target).act_nonzero
            primePositive (phaseAffine_local prime source (previous + 1)
              primeProperty.1).1
        exact LocalAt.of_sameLine
          (phaseAffine_local prime target previous primeProperty.1)
          outputNonzero same

/-- Exact local domain of the zero-test module. -/
theorem zeroTest_output_local_iff
    {prime phaseCount source target counter : Nat}
    (primeProperty : IsPrime prime)
    (primeBound : 6 * phaseCount < prime)
    (sourceBound : source < phaseCount) :
    LocalAt prime
        ((zeroTestLetter source target).act prime
          (phaseAffine source (unaryCode prime counter))) ↔
      counter = 0 := by
  constructor
  · intro outputLocal
    by_cases counterZero : counter = 0
    · exact counterZero
    · obtain ⟨previous, rfl⟩ := Nat.exists_eq_succ_of_ne_zero counterZero
      exact False.elim
        (zeroTest_rejects_positive primeProperty primeBound sourceBound
          outputLocal)
  · intro counterZero
    subst counter
    have same := zeroTestLetter_correct prime source target primeProperty.1
    have primePositive : 0 < prime := by
      have := primeProperty.1
      omega
    have outputNonzero := (zeroTestLetter source target).act_nonzero
      primePositive (phaseAffine_local prime source 0 primeProperty.1).1
    exact LocalAt.of_sameLine
      (phaseAffine_local prime target 0 primeProperty.1)
      outputNonzero same

end Mortality.Compiler.BasicUnaryModules
