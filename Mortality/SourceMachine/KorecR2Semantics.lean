import Mortality.SourceMachine.U20Semantics

/-!
# The two-register language interpreted by Korec U20

Korec obtains `U20` from the machine displayed in Figure 6 of
*Small universal register machines*.  Its instruction reader interprets a
three-symbol language on registers `R0` and `R2`.  A code `3j` conditionally
decrements `R0`, a code `3j+1` conditionally decrements `R2`, and a code
`3j+2` increments both registers.  For a conditional decrement the positive
destination is `j` and the zero destination is `j+1`.

This file isolates that source language and its deterministic operational
semantics.  It deliberately does not assert universality.
-/

namespace Mortality.SourceMachine.KorecR2

open Mortality.SourceMachine

/-- The three instruction forms decoded by Korec's simulation block. -/
inductive Instruction where
  | decrement (register : Counter) (positiveTarget : Nat)
  | incrementBoth (target : Nat)
  deriving DecidableEq, Repr

/-- The advertised positive-branch or unconditional destination. -/
def Instruction.target : Instruction → Nat
  | .decrement _ target => target
  | .incrementBoth target => target

/-- Korec's numerical operation code `3j+z`. -/
def Instruction.code : Instruction → Nat
  | .decrement .zero target => 3 * target
  | .decrement .one target => 3 * target + 1
  | .incrementBoth target => 3 * target + 2

/-- Decode the quotient and remainder modulo three exactly as `U20` does. -/
def decodeInstruction (code : Nat) : Instruction :=
  match code % 3 with
  | 0 => .decrement .zero (code / 3)
  | 1 => .decrement .one (code / 3)
  | _ => .incrementBoth (code / 3)

@[simp] theorem decodeInstruction_decrement_zero (target : Nat) :
    decodeInstruction (3 * target) = .decrement .zero target := by
  simp [decodeInstruction]

@[simp] theorem decodeInstruction_decrement_one (target : Nat) :
    decodeInstruction (3 * target + 1) = .decrement .one target := by
  simp [decodeInstruction]
  omega

@[simp] theorem decodeInstruction_incrementBoth (target : Nat) :
    decodeInstruction (3 * target + 2) = .incrementBoth target := by
  simp [decodeInstruction]
  omega

@[simp] theorem decodeInstruction_code (instruction : Instruction) :
    decodeInstruction instruction.code = instruction := by
  cases instruction with
  | decrement register target => cases register <;> simp [Instruction.code]
  | incrementBoth target => simp [Instruction.code]

/-- A finite program is represented extensionally by its instruction lookup.
State zero is reserved for halt, independently of this lookup. -/
abbrev Program := Nat → Option Instruction

structure Configuration where
  state : Nat
  registerZero : Nat
  registerTwo : Nat
  deriving DecidableEq, Repr

/-- One deterministic step of the interpreted two-register language. -/
def step (program : Program) (configuration : Configuration) :
    Option Configuration :=
  if configuration.state = 0 then none
  else
    match program configuration.state with
    | none => none
    | some (.decrement .zero positiveTarget) =>
        match configuration.registerZero with
        | 0 => some { configuration with state := positiveTarget + 1 }
        | value + 1 =>
            some
              { state := positiveTarget
                registerZero := value
                registerTwo := configuration.registerTwo }
    | some (.decrement .one positiveTarget) =>
        match configuration.registerTwo with
        | 0 => some { configuration with state := positiveTarget + 1 }
        | value + 1 =>
            some
              { state := positiveTarget
                registerZero := configuration.registerZero
                registerTwo := value }
    | some (.incrementBoth target) =>
        some
          { state := target
            registerZero := configuration.registerZero + 1
            registerTwo := configuration.registerTwo + 1 }

/-- The normal input convention for Korec's `R2` machines. -/
def initialConfiguration (input : Nat) : Configuration :=
  { state := 1, registerZero := 0, registerTwo := input }

def haltConfiguration (registerZero registerTwo : Nat) : Configuration :=
  { state := 0, registerZero, registerTwo }

def Halts (program : Program) (input : Nat) : Prop :=
  ∃ registerZero registerTwo,
    Reaches (step program) (initialConfiguration input)
      (haltConfiguration registerZero registerTwo)

/-- Halting from an arbitrary interpreted configuration.  This form is
needed when the surrounding universal machine initializes the simulated
control state and the reader carry directly. -/
def HaltsFrom (program : Program) (start : Configuration) : Prop :=
  ∃ registerZero registerTwo,
    Reaches (step program) start
      (haltConfiguration registerZero registerTwo)

theorem halts_iff_haltsFrom_initial (program : Program) (input : Nat) :
    Halts program input ↔ HaltsFrom program (initialConfiguration input) :=
  Iff.rfl

/-- The program obtained from a numerical instruction-code function. -/
def programOfCodes (codes : Nat → Nat) : Program :=
  fun state => if state = 0 then none else some (decodeInstruction (codes state))

@[simp] theorem programOfCodes_zero (codes : Nat → Nat) :
    programOfCodes codes 0 = none := by
  simp [programOfCodes]

@[simp] theorem programOfCodes_positive (codes : Nat → Nat) {state : Nat}
    (positive : 0 < state) :
    programOfCodes codes state = some (decodeInstruction (codes state)) := by
  simp [programOfCodes, Nat.ne_of_gt positive]

@[simp] theorem step_halt (program : Program) (registerZero registerTwo : Nat) :
    step program (haltConfiguration registerZero registerTwo) = none := by
  rfl

theorem step_decrement_zero_positive
    {program : Program} {state target value registerTwo : Nat}
    (statePositive : 0 < state)
    (lookup : program state = some (.decrement .zero target)) :
    step program
        { state, registerZero := value + 1, registerTwo } =
      some { state := target, registerZero := value, registerTwo } := by
  simp [step, Nat.ne_of_gt statePositive, lookup]

theorem step_decrement_zero_zero
    {program : Program} {state target registerTwo : Nat}
    (statePositive : 0 < state)
    (lookup : program state = some (.decrement .zero target)) :
    step program { state, registerZero := 0, registerTwo } =
      some { state := target + 1, registerZero := 0, registerTwo } := by
  simp [step, Nat.ne_of_gt statePositive, lookup]

theorem step_decrement_two_positive
    {program : Program} {state target registerZero value : Nat}
    (statePositive : 0 < state)
    (lookup : program state = some (.decrement .one target)) :
    step program
        { state, registerZero, registerTwo := value + 1 } =
      some { state := target, registerZero, registerTwo := value } := by
  simp [step, Nat.ne_of_gt statePositive, lookup]

theorem step_decrement_two_zero
    {program : Program} {state target registerZero : Nat}
    (statePositive : 0 < state)
    (lookup : program state = some (.decrement .one target)) :
    step program { state, registerZero, registerTwo := 0 } =
      some { state := target + 1, registerZero, registerTwo := 0 } := by
  simp [step, Nat.ne_of_gt statePositive, lookup]

theorem step_incrementBoth
    {program : Program} {state target registerZero registerTwo : Nat}
    (statePositive : 0 < state)
    (lookup : program state = some (.incrementBoth target)) :
    step program { state, registerZero, registerTwo } =
      some
        { state := target
          registerZero := registerZero + 1
          registerTwo := registerTwo + 1 } := by
  simp [step, Nat.ne_of_gt statePositive, lookup]

end Mortality.SourceMachine.KorecR2
