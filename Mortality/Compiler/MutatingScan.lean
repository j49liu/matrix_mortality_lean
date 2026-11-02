import Mortality.Compiler.CodeRegion
import Mortality.Compiler.PhysicalWord

/-!
# Physical realization of a finite periodic-code scan

A scan deletes a nonempty prefix of a periodic digit word.  All but the
last deletion remain in one private phase; the last deletion moves to the
next phase and applies one safe postmutation.  This lemma is the common
forward engine for the contraction projections.
-/

namespace Mortality.Compiler.MutatingScan

open Mortality.PeriodicCode
open Mortality.Compiler

def loopLetter (phase : Nat) (digit : Int) : PhysicalTemplate :=
  { sourcePhase := phase
    targetPhase := phase
    digit := digit
    preCoefficient := 0
    postSign := .positive
    postCoefficient := 0 }

def exitLetter (source target : Nat) (digit : Int)
    (postSign : Sign) (postCoefficient : Int) : PhysicalTemplate :=
  { sourcePhase := source
    targetPhase := target
    digit := digit
    preCoefficient := 0
    postSign := postSign
    postCoefficient := postCoefficient }

def word (source target : Nat) (leading : List Int) (last : Int)
    (postSign : Sign) (postCoefficient : Int) : List PhysicalTemplate :=
  leading.map (loopLetter source) ++
    [exitLetter source target last postSign postCoefficient]

@[simp] theorem word_length (source target : Nat) (leading : List Int)
    (last : Int) (postSign : Sign) (postCoefficient : Int) :
    (word source target leading last postSign postCoefficient).length =
      leading.length + 1 := by
  simp [word]

/-- Pure arithmetic counterpart of the physical scan: deleting a prefix
of a periodic word rotates that prefix to the rear. -/
theorem scanDigits_periodic_prefix
    (base : Nat) (leading suffix : List Int) (last : Int)
    (baseAtLeastTwo : 2 ≤ base) :
    scanDigits (base : Rat) (leading ++ [last])
        (periodicCode (base : Rat) (leading ++ [last] ++ suffix)) =
      periodicCode (base : Rat) (suffix ++ leading ++ [last]) := by
  induction leading generalizing suffix with
  | nil =>
      simpa [scanDigits] using
        deleteDigit_periodicCode_cons base last suffix baseAtLeastTwo
  | cons digit leading inductionHypothesis =>
      rw [List.cons_append, scanDigits]
      change scanDigits (base : Rat) (leading ++ [last])
          (deleteDigit (base : Rat) digit
            (periodicCode (base : Rat)
              (digit :: (leading ++ [last] ++ suffix)))) =
        periodicCode (base : Rat) (suffix ++ digit :: leading ++ [last])
      rw [deleteDigit_periodicCode_cons base digit
        (leading ++ [last] ++ suffix) baseAtLeastTwo]
      have tail := inductionHypothesis (suffix := suffix ++ [digit])
      simpa [List.append_assoc] using tail

private theorem exit_step
    (base source target : Nat) (last : Int) (suffix : List Int)
    (postSign : Sign) (postCoefficient : Int)
    (baseAtLeastTwo : 2 ≤ base) :
    SameLine
      ((exitLetter source target last postSign postCoefficient).act base
        (phaseAffine source
          (periodicCode (base : Rat) (last :: suffix))))
      (phaseAffine target
        (mutationMap base postSign postCoefficient
          (periodicCode (base : Rat) (suffix ++ [last])))) := by
  have inputLocal := periodicCode_local_affine base (last :: suffix)
    baseAtLeastTwo (by simp)
  have deletedLocal := deleteDigit_periodicCode_local base last suffix
    baseAtLeastTwo
  have outputLocal := mutationMap_local_of_local postSign postCoefficient
    deletedLocal
  have action := physicalLetter_affine_sameLine_of_local
    (sourcePhase := source) (targetPhase := target) (digit := last)
    (preCoefficient := 0) (postCoefficient := postCoefficient)
    (postSign := postSign) (by omega) inputLocal (by
      have zeroMutation : mutationMap base .positive 0
          (periodicCode (base : Rat) (last :: suffix)) =
          periodicCode (base : Rat) (last :: suffix) := by
        simp [mutationMap, mutationDenominator, Sign.value, Rat.div_def]
        grind
      rw [zeroMutation]
      simpa only [deleteDigit] using deletedLocal)
  have rotation := deleteDigit_periodicCode_cons base last suffix
    baseAtLeastTwo
  simp [localLetterMap] at action
  have rotationRaw := rotation
  unfold deleteDigit at rotationRaw
  rw [rotationRaw] at action
  simpa [exitLetter, PhysicalTemplate.act, PhysicalTemplate.matrix,
    phaseAffine]
    using action

/-- Deleting `leading ++ [last]` rotates that leading to the rear and then
applies the exit mutation. -/
theorem word_correct
    (base source target : Nat) (leading suffix : List Int) (last : Int)
    (postSign : Sign) (postCoefficient : Int)
    (baseAtLeastTwo : 2 ≤ base) :
    SameLine
      (physicalWordAction base
        (word source target leading last postSign postCoefficient)
        (phaseAffine source
          (periodicCode (base : Rat) (leading ++ [last] ++ suffix))))
      (phaseAffine target
        (mutationMap base postSign postCoefficient
          (periodicCode (base : Rat) (suffix ++ leading ++ [last])))) := by
  induction leading generalizing suffix with
  | nil =>
      simpa [word, physicalWordAction] using
        exit_step base source target last suffix postSign postCoefficient
          baseAtLeastTwo
  | cons digit leading inductionHypothesis =>
      have firstStep := physicalLetter_rotates_periodicCode base source
        source digit (leading ++ [last] ++ suffix) baseAtLeastTwo
      have tailRun := inductionHypothesis (suffix := suffix ++ [digit])
      have firstStep' :
          SameLine
            ((loopLetter source digit).act base
              (phaseAffine source
                (periodicCode (base : Rat)
                  ((digit :: leading) ++ [last] ++ suffix))))
            (phaseAffine source
              (periodicCode (base : Rat)
                (leading ++ [last] ++ (suffix ++ [digit])))) := by
        simpa [loopLetter, PhysicalTemplate.act, PhysicalTemplate.matrix,
          phaseAffine, List.append_assoc] using firstStep
      have combined := physicalWordAction_cons_sameLine base
        (loopLetter source digit)
        (word source target leading last postSign postCoefficient)
        firstStep' tailRun
      simpa [word, List.append_assoc] using combined

/-- The scan word stays local whenever its endpoint does.  This formulation
uses the global error irreversibility theorem and avoids duplicating a
leading-by-leading locality induction. -/
theorem word_allStatesLocal
    (base source target : Nat) (leading suffix : List Int) (last : Int)
    (postSign : Sign) (postCoefficient : Int)
    (baseAtLeastTwo : 2 ≤ base) :
    AllStatesLocal base
      (word source target leading last postSign postCoefficient)
      (phaseAffine source
        (periodicCode (base : Rat) (leading ++ [last] ++ suffix))) := by
  have inputLocal : LocalAt base
      (phaseAffine source
        (periodicCode (base : Rat) (leading ++ [last] ++ suffix))) := by
    rw [show phaseAffine source
        (periodicCode (base : Rat) (leading ++ [last] ++ suffix)) =
      Matrix2.apply (IntMatrix2.cast (chart source))
        (Vec2.affine
          (periodicCode (base : Rat) (leading ++ [last] ++ suffix))) by
      simpa [phaseAffine] using
        (chart_apply source
          (periodicCode (base : Rat)
            (leading ++ [last] ++ suffix))).symm]
    apply (local_chart_iff base source _).mpr
    exact periodicCode_local_affine base (leading ++ [last] ++ suffix)
      baseAtLeastTwo (by simp)
  have rotatedLocal := periodicCode_local_affine base
    (suffix ++ leading ++ [last]) baseAtLeastTwo (by simp)
  have mutatedLocal := mutationMap_local_of_local postSign postCoefficient
    rotatedLocal
  have finalLocal : LocalAt base
      (phaseAffine target
        (mutationMap base postSign postCoefficient
          (periodicCode (base : Rat) (suffix ++ leading ++ [last])))) := by
    rw [show phaseAffine target
        (mutationMap base postSign postCoefficient
          (periodicCode (base : Rat) (suffix ++ leading ++ [last]))) =
      Matrix2.apply (IntMatrix2.cast (chart target))
        (Vec2.affine
          (mutationMap base postSign postCoefficient
            (periodicCode (base : Rat)
              (suffix ++ leading ++ [last])))) by
      simpa [phaseAffine] using
        (chart_apply target
          (mutationMap base postSign postCoefficient
            (periodicCode (base : Rat)
              (suffix ++ leading ++ [last])))).symm]
    exact (local_chart_iff base target _).mpr mutatedLocal
  have action := word_correct base source target leading suffix last postSign
    postCoefficient baseAtLeastTwo
  have outputNonzero := physicalWordAction_nonzero (prime := base) (by omega)
    (word source target leading last postSign postCoefficient) inputLocal.1
  have actualFinalLocal := LocalAt.of_sameLine finalLocal outputNonzero action
  exact allStatesLocal_of_final_local (by omega) _ inputLocal.1
    actualFinalLocal

/-! ## Canonical states for a zero-prefix scan -/

def zeroStateDigits (zeros : Nat) (last : Int) (suffix : List Int)
    (deleted : Nat) : List Int :=
  List.replicate (zeros - deleted) 0 ++ [last] ++ suffix ++
    List.replicate deleted 0

def zeroState (base zeros : Nat) (last : Int) (suffix : List Int)
    (deleted : Nat) : Rat :=
  periodicCode (base : Rat) (zeroStateDigits zeros last suffix deleted)

theorem zeroStateDigits_zero (zeros : Nat) (last : Int)
    (suffix : List Int) :
    zeroStateDigits zeros last suffix 0 =
      List.replicate zeros 0 ++ [last] ++ suffix := by
  simp [zeroStateDigits]

theorem zeroStateDigits_before
    {zeros deleted : Nat} {last : Int} {suffix : List Int}
    (deletedBelow : deleted < zeros) :
    zeroStateDigits zeros last suffix deleted =
      0 :: (List.replicate (zeros - (deleted + 1)) 0 ++ [last] ++ suffix ++
        List.replicate deleted 0) := by
  unfold zeroStateDigits
  have exponentEq : zeros - deleted = zeros - (deleted + 1) + 1 := by omega
  rw [exponentEq, List.replicate_succ]
  rfl

theorem zeroStateDigits_at_marker (zeros : Nat) (last : Int)
    (suffix : List Int) :
    zeroStateDigits zeros last suffix zeros =
      last :: (suffix ++ List.replicate zeros 0) := by
  simp [zeroStateDigits]

theorem zeroStateDigits_rotate_zero
    {zeros deleted : Nat} {last : Int} {suffix : List Int} :
    let remaining :=
      List.replicate (zeros - (deleted + 1)) 0 ++ [last] ++ suffix ++
        List.replicate deleted 0
    remaining ++ [0] = zeroStateDigits zeros last suffix (deleted + 1) := by
  dsimp
  unfold zeroStateDigits
  rw [List.replicate_succ']
  simp [List.append_assoc]

theorem zeroStateDigits_rotate_marker (zeros : Nat) (last : Int)
    (suffix : List Int) :
    suffix ++ List.replicate zeros 0 ++ [last] =
      suffix ++ List.replicate zeros 0 ++ [last] := rfl

theorem zeroState_local
    (base zeros : Nat) (last : Int) (suffix : List Int) (deleted : Nat)
    (baseAtLeastTwo : 2 ≤ base) :
    LocalAt base (Vec2.affine (zeroState base zeros last suffix deleted)) := by
  apply periodicCode_local_affine base _ baseAtLeastTwo
  simp [zeroStateDigits]

theorem zeroState_delete_zero
    (base zeros : Nat) (last : Int) (suffix : List Int) (deleted : Nat)
    (baseAtLeastTwo : 2 ≤ base) (deletedBelow : deleted < zeros) :
    deleteDigit (base : Rat) 0 (zeroState base zeros last suffix deleted) =
      zeroState base zeros last suffix (deleted + 1) := by
  rw [zeroState, zeroStateDigits_before deletedBelow]
  rw [deleteDigit_periodicCode_cons base 0
    (List.replicate (zeros - (deleted + 1)) 0 ++ [last] ++ suffix ++
      List.replicate deleted 0) baseAtLeastTwo]
  have rotated := zeroStateDigits_rotate_zero
    (zeros := zeros) (deleted := deleted) (last := last) (suffix := suffix)
  unfold zeroState
  rw [← rotated]

theorem scan_zeroState
    (base zeros : Nat) (last : Int) (suffix : List Int)
    (deleted count : Nat) (baseAtLeastTwo : 2 ≤ base)
    (within : deleted + count ≤ zeros) :
    scanDigits (base : Rat) (List.replicate count 0)
        (zeroState base zeros last suffix deleted) =
      zeroState base zeros last suffix (deleted + count) := by
  induction count generalizing deleted with
  | zero => simp [scanDigits]
  | succ count inductionHypothesis =>
      rw [List.replicate_succ, scanDigits]
      rw [zeroState_delete_zero base zeros last suffix deleted baseAtLeastTwo
        (by omega)]
      have tail := inductionHypothesis (deleted := deleted + 1) (by omega)
      simpa only [show deleted + 1 + count = deleted + (count + 1) by omega]
        using tail

theorem phaseZeroState_local
    (base phase zeros : Nat) (last : Int) (suffix : List Int) (deleted : Nat)
    (baseAtLeastTwo : 2 ≤ base) :
    LocalAt base
      (phaseAffine phase (zeroState base zeros last suffix deleted)) := by
  rw [show phaseAffine phase (zeroState base zeros last suffix deleted) =
      Matrix2.apply (IntMatrix2.cast (chart phase))
        (Vec2.affine (zeroState base zeros last suffix deleted)) by
    simpa [phaseAffine] using
      (chart_apply phase (zeroState base zeros last suffix deleted)).symm]
  exact (local_chart_iff base phase _).mpr
    (zeroState_local base zeros last suffix deleted baseAtLeastTwo)

theorem zeroState_inPhaseAt_before
    (base phase zeros : Nat) (last : Int) (suffix : List Int)
    (deleted : Nat) (baseAtLeastTwo : 2 ≤ base)
    (deletedBelow : deleted < zeros) :
    InPhaseAt base phase 0
      (phaseAffine phase (zeroState base zeros last suffix deleted)) := by
  rw [zeroState, zeroStateDigits_before deletedBelow]
  exact periodicCode_inPhaseAt base phase 0 _ baseAtLeastTwo
    (by simp [ReservedDigit])

theorem zeroState_inPhaseAt_marker
    (base phase zeros : Nat) (last : Int) (suffix : List Int)
    (baseAtLeastTwo : 2 ≤ base) (reserved : ReservedDigit last) :
    InPhaseAt base phase last
      (phaseAffine phase (zeroState base zeros last suffix zeros)) := by
  rw [zeroState, zeroStateDigits_at_marker]
  exact periodicCode_inPhaseAt base phase last _ baseAtLeastTwo reserved

theorem zeroLoop_step
    (base phase zeros : Nat) (last : Int) (suffix : List Int)
    (deleted : Nat) (baseAtLeastTwo : 2 ≤ base)
    (deletedBelow : deleted < zeros) :
    SameLine
      ((loopLetter phase 0).act base
        (phaseAffine phase (zeroState base zeros last suffix deleted)))
      (phaseAffine phase
        (zeroState base zeros last suffix (deleted + 1))) := by
  rw [zeroState, zeroStateDigits_before deletedBelow]
  have rotation := physicalLetter_rotates_periodicCode base phase phase 0
    (List.replicate (zeros - (deleted + 1)) 0 ++ [last] ++ suffix ++
      List.replicate deleted 0) baseAtLeastTwo
  have rotated := zeroStateDigits_rotate_zero
    (zeros := zeros) (deleted := deleted) (last := last) (suffix := suffix)
  unfold zeroState
  rw [← rotated]
  simpa [loopLetter, PhysicalTemplate.act, PhysicalTemplate.matrix,
    phaseAffine] using rotation

theorem zeroMutationExit_step
    (base source target zeros deleted : Nat) (last : Int)
    (suffix : List Int) (postSign : Sign) (postCoefficient : Int)
    (baseAtLeastTwo : 2 ≤ base) (deletedBelow : deleted < zeros) :
    SameLine
      ((exitLetter source target 0 postSign postCoefficient).act base
        (phaseAffine source (zeroState base zeros last suffix deleted)))
      (phaseAffine target
        (mutationMap base postSign postCoefficient
          (zeroState base zeros last suffix (deleted + 1)))) := by
  have inputLocal := zeroState_local base zeros last suffix deleted
    baseAtLeastTwo
  have deletedEq := zeroState_delete_zero base zeros last suffix deleted
    baseAtLeastTwo deletedBelow
  have deletedLocal := zeroState_local base zeros last suffix (deleted + 1)
    baseAtLeastTwo
  have action := physicalLetter_affine_sameLine_of_local
    (sourcePhase := source) (targetPhase := target) (digit := 0)
    (preCoefficient := 0) (postCoefficient := postCoefficient)
    (postSign := postSign) (by omega) inputLocal (by
      have zeroMutation : mutationMap base .positive 0
          (zeroState base zeros last suffix deleted) =
          zeroState base zeros last suffix deleted := by
        simp [mutationMap, mutationDenominator, Sign.value, Rat.div_def]
        grind
      rw [zeroMutation]
      change LocalAt base
        (Vec2.affine
          (deleteDigit (base : Rat) 0
            (zeroState base zeros last suffix deleted)))
      rw [deletedEq]
      exact deletedLocal)
  simp [localLetterMap] at action
  change SameLine
    (Matrix2.apply
      (IntMatrix2.cast
        (physicalLetter base source target 0 0 postSign postCoefficient))
      (phaseAffine source (zeroState base zeros last suffix deleted)))
    (phaseAffine target
      (mutationMap base postSign postCoefficient
        (deleteDigit (base : Rat) 0
          (zeroState base zeros last suffix deleted)))) at action
  rw [deletedEq] at action
  simpa [exitLetter, PhysicalTemplate.act, PhysicalTemplate.matrix]
    using action

theorem zeroExit_step
    (base source target zeros : Nat) (last : Int) (suffix : List Int)
    (postSign : Sign) (postCoefficient : Int)
    (baseAtLeastTwo : 2 ≤ base) :
    SameLine
      ((exitLetter source target last postSign postCoefficient).act base
        (phaseAffine source (zeroState base zeros last suffix zeros)))
      (phaseAffine target
        (mutationMap base postSign postCoefficient
          (periodicCode (base : Rat)
            (suffix ++ List.replicate zeros 0 ++ [last])))) := by
  have action := word_correct base source target []
    (suffix ++ List.replicate zeros 0) last postSign postCoefficient
    baseAtLeastTwo
  rw [zeroState, zeroStateDigits_at_marker]
  simpa [word, physicalWordAction, List.append_assoc] using action

end Mortality.Compiler.MutatingScan
