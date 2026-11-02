import Mortality.SourceMachine.TwoCounterToKorecR2

/-!
# Shifting an ordinary two-counter program above an initialization prefix

Positive states are translated upward by a fixed offset while state zero
remains halt.  States inside the reserved prefix receive harmless self loops.
This permits a later finite input decoder to occupy states starting at one.
-/

namespace Mortality.SourceMachine.TwoCounterShift

open Mortality.SourceMachine
open Mortality.SourceMachine.TotalTwoCounter
open Mortality.SourceMachine.U20Compilation

def shiftState (offset : Nat) : Nat → Nat
  | 0 => 0
  | state + 1 => offset + state + 1

@[simp] theorem shiftState_zero (offset : Nat) : shiftState offset 0 = 0 := rfl

@[simp] theorem shiftState_succ (offset state : Nat) :
    shiftState offset (state + 1) = offset + state + 1 := rfl

def shiftInstruction (offset : Nat) :
    TotalTwoCounter.Instruction → TotalTwoCounter.Instruction
  | .increment counter target => .increment counter (shiftState offset target)
  | .decrement counter positiveTarget zeroTarget =>
      .decrement counter (shiftState offset positiveTarget)
        (shiftState offset zeroTarget)

/-- Relocate every positive source state above `offset`.  The reserved
positive prefix is total but cannot be entered from a shifted source state. -/
def shiftProgram (offset : Nat) (program : TotalTwoCounter.Program) :
    TotalTwoCounter.Program :=
  fun state =>
    if state ≤ offset then .increment .zero state
    else shiftInstruction offset (program (state - offset))

def shiftConfiguration (offset : Nat)
    (configuration : TotalTwoCounter.Configuration) :
    TotalTwoCounter.Configuration :=
  { configuration with state := shiftState offset configuration.state }

@[simp] theorem shiftConfiguration_halt (offset counterZero counterOne : Nat) :
    shiftConfiguration offset
        (TotalTwoCounter.haltConfiguration counterZero counterOne) =
      TotalTwoCounter.haltConfiguration counterZero counterOne := by
  rfl

@[simp] theorem shiftProgram_at_shifted_positive
    (offset : Nat) (program : TotalTwoCounter.Program) (state : Nat) :
    shiftProgram offset program (shiftState offset (state + 1)) =
      shiftInstruction offset (program (state + 1)) := by
  unfold shiftProgram
  rw [shiftState_succ]
  have outsidePrefix : ¬offset + state + 1 ≤ offset := by omega
  rw [if_neg outsidePrefix]
  congr 2
  omega

theorem execute_shiftInstruction
    (offset : Nat) (instruction : TotalTwoCounter.Instruction)
    (configuration : TotalTwoCounter.Configuration) :
    TotalTwoCounter.execute (shiftInstruction offset instruction)
        (shiftConfiguration offset configuration) =
      shiftConfiguration offset
        (TotalTwoCounter.execute instruction configuration) := by
  rcases configuration with ⟨state, counterZero, counterOne⟩
  cases instruction with
  | increment counter target =>
      cases target <;> cases counter <;> rfl
  | decrement counter positiveTarget zeroTarget =>
      cases positiveTarget <;> cases zeroTarget <;> cases counter <;>
        cases counterZero <;> cases counterOne <;> rfl

/-- Relocation commutes with one partial step, including halt. -/
theorem step_shiftConfiguration
    (offset : Nat) (program : TotalTwoCounter.Program)
    (configuration : TotalTwoCounter.Configuration) :
    TotalTwoCounter.step (shiftProgram offset program)
        (shiftConfiguration offset configuration) =
      (TotalTwoCounter.step program configuration).map
        (shiftConfiguration offset) := by
  cases configuration with
  | mk state counterZero counterOne =>
      cases state with
      | zero => rfl
      | succ state =>
          have lookup : shiftProgram offset program (offset + state + 1) =
              shiftInstruction offset (program (state + 1)) := by
            rw [← shiftState_succ]
            exact shiftProgram_at_shifted_positive offset program state
          simp only [TotalTwoCounter.step, shiftConfiguration, shiftState_succ,
            Nat.succ_ne_zero, if_false]
          rw [lookup]
          exact congrArg some
            (execute_shiftInstruction offset (program (state + 1))
              ⟨state + 1, counterZero, counterOne⟩)

theorem shift_iterate
    (offset : Nat) (program : TotalTwoCounter.Program) (fuel : Nat)
    (configuration : TotalTwoCounter.Configuration) :
    iterate (TotalTwoCounter.step (shiftProgram offset program)) fuel
        (shiftConfiguration offset configuration) =
      (iterate (TotalTwoCounter.step program) fuel configuration).map
        (shiftConfiguration offset) := by
  induction fuel with
  | zero => rfl
  | succ fuel inductionHypothesis =>
      simp only [iterate, inductionHypothesis]
      cases execution : iterate (TotalTwoCounter.step program) fuel configuration with
      | none => rfl
      | some middle =>
          simp [step_shiftConfiguration]

theorem source_iterate_exists_of_not_haltsFrom
    (program : TotalTwoCounter.Program)
    (start : TotalTwoCounter.Configuration)
    (notHalts : ¬TotalTwoCounter.HaltsFrom program start) :
    ∀ fuel, ∃ finish,
      iterate (TotalTwoCounter.step program) fuel start = some finish := by
  intro fuel
  induction fuel with
  | zero => exact ⟨_, rfl⟩
  | succ fuel inductionHypothesis =>
      obtain ⟨middle, middleExecution⟩ := inductionHypothesis
      have statePositive : 0 < middle.state := by
        by_cases stateZero : middle.state = 0
        · have middleRun := reaches_iff_exists_iterate.mpr
            ⟨fuel, middleExecution⟩
          have middleEq : middle =
              TotalTwoCounter.haltConfiguration middle.counterZero
                middle.counterOne := by
            cases middle
            simp_all [TotalTwoCounter.haltConfiguration]
          apply (notHalts ⟨middle.counterZero, middle.counterOne, ?_⟩).elim
          rw [← middleEq]
          exact middleRun
        · omega
      obtain ⟨finish, finalStep⟩ :=
        TotalTwoCounter.step_exists_of_positive program middle statePositive
      refine ⟨finish, ?_⟩
      simp [iterate, middleExecution, finalStep]

/-- Relocation preserves and reflects halting from every source
configuration. -/
theorem shiftedHaltsFrom_iff (offset : Nat)
    (program : TotalTwoCounter.Program)
    (start : TotalTwoCounter.Configuration) :
    TotalTwoCounter.HaltsFrom (shiftProgram offset program)
        (shiftConfiguration offset start) ↔
      TotalTwoCounter.HaltsFrom program start := by
  constructor
  · intro shiftedHalts
    by_cases sourceHalts : TotalTwoCounter.HaltsFrom program start
    · exact sourceHalts
    · exfalso
      obtain ⟨counterZero, counterOne, shiftedRun⟩ := shiftedHalts
      obtain ⟨haltFuel, haltExecution⟩ :=
        reaches_iff_exists_iterate.mp shiftedRun
      obtain ⟨sourceFinish, sourceExecution⟩ :=
        source_iterate_exists_of_not_haltsFrom program start sourceHalts
          (haltFuel + 1)
      have shiftedExecution := shift_iterate offset program (haltFuel + 1) start
      rw [sourceExecution] at shiftedExecution
      have cannotPassHalt := successful_iterations_before_halt
        (step := TotalTwoCounter.step (shiftProgram offset program))
        (haltEq := TotalTwoCounter.step_halt (shiftProgram offset program)
          counterZero counterOne)
        haltExecution shiftedExecution
      omega
  · rintro ⟨counterZero, counterOne, sourceRun⟩
    obtain ⟨fuel, sourceExecution⟩ := reaches_iff_exists_iterate.mp sourceRun
    refine ⟨counterZero, counterOne, reaches_iff_exists_iterate.mpr ⟨fuel, ?_⟩⟩
    rw [shift_iterate, sourceExecution]
    rfl

end Mortality.SourceMachine.TwoCounterShift
