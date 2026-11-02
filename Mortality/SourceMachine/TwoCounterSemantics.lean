import Mortality.SourceMachine.U2Semantics

/-!
# A total two-counter source language

This file separates the ordinary two-counter language used by the universal
machine compiler from Ivanov's concrete `U2` table.  Every positive control
state carries either an increment or a conditional decrement.  State zero is
the unique halt state, so a computation that has not halted always has a next
step.
-/

namespace Mortality.SourceMachine.TotalTwoCounter

open Mortality.SourceMachine

inductive Instruction where
  | increment (counter : Counter) (target : Nat)
  | decrement (counter : Counter) (positiveTarget zeroTarget : Nat)
  deriving DecidableEq, Repr

/-- A program is total on its positive control states.  Its value at state
zero is ignored by the operational semantics. -/
abbrev Program := Nat → Instruction

abbrev Configuration := SourceMachine.Configuration

/-- Execute one nonhalting instruction.  The caller supplies the current
control state; the instruction writes its advertised target. -/
def execute (instruction : Instruction) (configuration : Configuration) :
    Configuration :=
  match instruction with
  | .increment .zero target =>
      ⟨target, configuration.counterZero + 1, configuration.counterOne⟩
  | .increment .one target =>
      ⟨target, configuration.counterZero, configuration.counterOne + 1⟩
  | .decrement .zero positiveTarget zeroTarget =>
      match configuration.counterZero with
      | 0 => { configuration with state := zeroTarget }
      | value + 1 => ⟨positiveTarget, value, configuration.counterOne⟩
  | .decrement .one positiveTarget zeroTarget =>
      match configuration.counterOne with
      | 0 => { configuration with state := zeroTarget }
      | value + 1 => ⟨positiveTarget, configuration.counterZero, value⟩

/-- Execute one ordinary two-counter instruction, reserving state zero for
halt. -/
def step (program : Program) (configuration : Configuration) :
    Option Configuration :=
  if configuration.state = 0 then none
  else some (execute (program configuration.state) configuration)

/-- The input convention matches Korec's R2 convention: counter zero starts
at zero and counter one contains the input. -/
def initialConfiguration (input : Nat) : Configuration :=
  { state := 1, counterZero := 0, counterOne := input }

def haltConfiguration (counterZero counterOne : Nat) : Configuration :=
  { state := 0, counterZero, counterOne }

def HaltsFrom (program : Program) (start : Configuration) : Prop :=
  ∃ counterZero counterOne,
    Reaches (step program) start
      (haltConfiguration counterZero counterOne)

def Halts (program : Program) (input : Nat) : Prop :=
  HaltsFrom program (initialConfiguration input)

@[simp] theorem step_halt (program : Program) (counterZero counterOne : Nat) :
    step program (haltConfiguration counterZero counterOne) = none := by
  rfl

/-- Totality away from the distinguished halt state. -/
theorem step_exists_of_positive (program : Program) (configuration : Configuration)
    (positive : 0 < configuration.state) :
    ∃ target, step program configuration = some target := by
  rcases configuration with ⟨state, counterZero, counterOne⟩
  cases operation : program state with
  | increment counter target =>
      cases counter <;>
        simp [step, Nat.ne_of_gt positive, operation]
  | decrement counter positiveTarget zeroTarget =>
      cases counter <;> cases counterZero <;> cases counterOne <;>
        simp [step, Nat.ne_of_gt positive, operation]

theorem step_of_lookup {program : Program} {configuration : Configuration}
    {instruction : Instruction} (positive : 0 < configuration.state)
    (lookup : program configuration.state = instruction) :
    step program configuration = some (execute instruction configuration) := by
  simp [step, Nat.ne_of_gt positive, lookup]

end Mortality.SourceMachine.TotalTwoCounter
