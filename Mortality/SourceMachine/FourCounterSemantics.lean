import Mortality.SourceMachine.U2Semantics

/-!
# A finite four-register counter-machine interface

This is the source interface needed for the fixed universal TM0 compiler.
Programs may be undefined at a control state; undefined lookup is terminal.
The four register names and the branch order match the audited `lean-wang`
counter-machine layer.
-/

namespace Mortality.SourceMachine.FourCounter

open Mortality.SourceMachine

inductive Register where
  | left
  | right
  | temp
  | clock
  deriving DecidableEq, Repr

structure Registers where
  left : Nat
  right : Nat
  temp : Nat
  clock : Nat
  deriving DecidableEq, Repr

namespace Registers

def get (registers : Registers) : Register → Nat
  | .left => registers.left
  | .right => registers.right
  | .temp => registers.temp
  | .clock => registers.clock

def set (registers : Registers) : Register → Nat → Registers
  | .left, value => { registers with left := value }
  | .right, value => { registers with right := value }
  | .temp, value => { registers with temp := value }
  | .clock, value => { registers with clock := value }

def increment (registers : Registers) (register : Register) : Registers :=
  registers.set register (registers.get register + 1)

def decrement (registers : Registers) (register : Register) : Registers :=
  registers.set register (registers.get register - 1)

@[simp] theorem get_set_same (registers : Registers) (register : Register)
    (value : Nat) :
    (registers.set register value).get register = value := by
  cases register <;> rfl

@[simp] theorem get_set_other (registers : Registers)
    {changed candidate : Register} (distinct : candidate ≠ changed)
    (value : Nat) :
    (registers.set changed value).get candidate = registers.get candidate := by
  cases changed <;> cases candidate <;> simp_all [set, get]

@[simp] theorem get_increment_same (registers : Registers)
    (register : Register) :
    (registers.increment register).get register = registers.get register + 1 := by
  simp [increment]

@[simp] theorem get_decrement_same (registers : Registers)
    (register : Register) :
    (registers.decrement register).get register = registers.get register - 1 := by
  simp [decrement]

theorem decrement_of_positive (registers : Registers) (register : Register)
    {value : Nat} (valueEq : registers.get register = value + 1) :
    (registers.decrement register).get register = value := by
  simp [decrement, valueEq]

end Registers

inductive Instruction where
  | increment (register : Register) (target : Nat)
  | decrement (register : Register) (zeroTarget positiveTarget : Nat)
  deriving DecidableEq, Repr

/-- A program is represented extensionally; a missing instruction is a
terminal control state. -/
abbrev Program := Nat → Option Instruction

structure Configuration where
  state : Nat
  registers : Registers
  deriving DecidableEq, Repr

def step (program : Program) (configuration : Configuration) :
    Option Configuration :=
  match program configuration.state with
  | none => none
  | some (.increment register target) =>
      some ⟨target, configuration.registers.increment register⟩
  | some (.decrement register zeroTarget positiveTarget) =>
      if configuration.registers.get register = 0 then
        some ⟨zeroTarget, configuration.registers⟩
      else
        some ⟨positiveTarget, configuration.registers.decrement register⟩

def Terminal (program : Program) (configuration : Configuration) : Prop :=
  step program configuration = none

def HaltsFrom (program : Program) (start : Configuration) : Prop :=
  ∃ finish, Reaches (step program) start finish ∧ Terminal program finish

theorem step_increment
    {program : Program} {configuration : Configuration}
    {register : Register} {target : Nat}
    (lookup : program configuration.state = some (.increment register target)) :
    step program configuration =
      some ⟨target, configuration.registers.increment register⟩ := by
  simp [step, lookup]

theorem step_decrement_zero
    {program : Program} {configuration : Configuration}
    {register : Register} {zeroTarget positiveTarget : Nat}
    (lookup : program configuration.state =
      some (.decrement register zeroTarget positiveTarget))
    (zero : configuration.registers.get register = 0) :
    step program configuration = some ⟨zeroTarget, configuration.registers⟩ := by
  simp [step, lookup, zero]

theorem step_decrement_positive
    {program : Program} {configuration : Configuration}
    {register : Register} {zeroTarget positiveTarget : Nat}
    (lookup : program configuration.state =
      some (.decrement register zeroTarget positiveTarget))
    (positive : 0 < configuration.registers.get register) :
    step program configuration =
      some ⟨positiveTarget, configuration.registers.decrement register⟩ := by
  simp [step, lookup, Nat.ne_of_gt positive]

theorem terminal_iff_lookup_none (program : Program)
    (configuration : Configuration) :
    Terminal program configuration ↔ program configuration.state = none := by
  unfold Terminal
  cases lookup : program configuration.state with
  | none => simp [step, lookup]
  | some instruction =>
      cases instruction with
      | increment => simp [step, lookup]
      | decrement register zeroTarget positiveTarget =>
          by_cases zero : configuration.registers.get register = 0 <;>
            simp [step, lookup, zero]

end Mortality.SourceMachine.FourCounter
