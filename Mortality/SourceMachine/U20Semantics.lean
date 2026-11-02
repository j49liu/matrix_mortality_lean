import Mortality.SourceMachine.U2Semantics

/-!
# Korec's twenty-instruction universal register machine

This file transcribes the machine obtained from Figure 6 on printed page 294
of Korec, *Small universal register machines*, Theoretical Computer Science
168 (1996), 267--301.  The displayed machine `U19` contains one pure zero
test at `q13`.  The paragraph immediately preceding the figure states the
exact conversion to `U20`: replace that test by a conditional decrement of
`R6` followed, on the positive branch, by one increment restoring `R6`.

The definitions below provide the intermediate source needed for a formal
Korec--Ivanov bridge.  They do not assert universality by citation.
-/

namespace Mortality.SourceMachine.KorecU20

/-- Korec's displayed machine uses registers `R0`, ..., `R7`. -/
abbrev Registers := Fin 8 → Nat

inductive Instruction where
  | increment (register : Fin 8) (target : Nat)
  | decrement (register : Fin 8) (positiveTarget zeroTarget : Nat)
  | halt
  deriving DecidableEq, Repr

structure Configuration where
  state : Nat
  registers : Registers

def Registers.update (registers : Registers) (register : Fin 8)
    (value : Nat) : Registers :=
  fun candidate => if candidate = register then value else registers candidate

@[simp] theorem Registers.update_same (registers : Registers)
    (register : Fin 8) (value : Nat) :
    registers.update register value register = value := by
  simp [Registers.update]

@[simp] theorem Registers.update_other (registers : Registers)
    {changed candidate : Fin 8} (distinct : candidate ≠ changed) (value : Nat) :
    registers.update changed value candidate = registers candidate := by
  simp [Registers.update, distinct]

/-- The twenty occupied addresses of `U20`.  State zero represents Stop. -/
def states : List Nat :=
  [1, 3, 4, 6, 7, 9, 10, 12, 13, 15,
    14, 16, 18, 20, 22, 23, 27, 30, 31, 32]

/-- The exact `U20` program reconstructed from Korec's Figure 6 and the
stated `U19`-to-`U20` replacement. -/
def instruction : Nat → Option Instruction
  | 0 => some .halt
  | 1 => some (.decrement 1 3 6)
  | 3 => some (.increment 7 1)
  | 4 => some (.decrement 5 6 7)
  | 6 => some (.increment 6 4)
  | 7 => some (.decrement 6 9 4)
  | 9 => some (.increment 5 10)
  | 10 => some (.decrement 7 12 13)
  | 12 => some (.increment 1 7)
  | 13 => some (.decrement 6 15 1)
  | 15 => some (.increment 6 14)
  | 14 => some (.decrement 4 1 16)
  | 16 => some (.decrement 5 18 23)
  | 18 => some (.decrement 5 20 27)
  | 20 => some (.decrement 5 22 30)
  | 22 => some (.increment 4 16)
  | 23 => some (.decrement 0 32 1)
  | 27 => some (.decrement 2 32 1)
  | 30 => some (.increment 0 31)
  | 31 => some (.increment 2 32)
  | 32 => some (.decrement 4 1 0)
  | _ => none

def Instruction.targets : Instruction → List Nat
  | .increment _ target => [target]
  | .decrement _ positiveTarget zeroTarget => [positiveTarget, zeroTarget]
  | .halt => []

def step : Configuration → Option Configuration
  | ⟨state, registers⟩ =>
      match instruction state with
      | none | some .halt => none
      | some (.increment register target) =>
          some
            { state := target
              registers := registers.update register (registers register + 1) }
      | some (.decrement register positiveTarget zeroTarget) =>
          if registers register = 0 then
            some { state := zeroTarget, registers := registers }
          else
            some
              { state := positiveTarget
                registers := registers.update register
                  (registers register - 1) }

def initialRegisters (input : Nat) : Registers :=
  fun register => if register = (2 : Fin 8) then input else 0

def initialConfiguration (input : Nat) : Configuration :=
  { state := 1, registers := initialRegisters input }

def haltConfiguration (registers : Registers) : Configuration :=
  { state := 0, registers }

def HaltsFrom (registers : Registers) : Prop :=
  ∃ finalRegisters,
    SourceMachine.Reaches step { state := 1, registers := registers }
      (haltConfiguration finalRegisters)

def Halts (input : Nat) : Prop :=
  HaltsFrom (initialRegisters input)

/-- The two-input convention used in Korec's definition of universality. -/
def initialRegistersTwo (programInput dataInput : Nat) : Registers :=
  fun register =>
    if register = (1 : Fin 8) then programInput
    else if register = (2 : Fin 8) then dataInput
    else 0

def HaltsTwo (programInput dataInput : Nat) : Prop :=
  HaltsFrom (initialRegistersTwo programInput dataInput)

@[simp] theorem initialRegisters_input (input : Nat) :
    initialRegisters input 2 = input := by
  simp [initialRegisters]

@[simp] theorem initialRegisters_other (input : Nat) {register : Fin 8}
    (registerNe : register ≠ 2) :
    initialRegisters input register = 0 := by
  simp [initialRegisters, registerNe]

theorem states_length : states.length = 20 := by
  decide

theorem states_nodup : states.Nodup := by
  decide

theorem instruction_defined_on_states (state : Nat) (stateMem : state ∈ states) :
    ∃ operation, instruction state = some operation := by
  simp [states] at stateMem
  rcases stateMem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl <;> simp [instruction]

theorem instruction_targets_valid (state : Nat) (stateMem : state ∈ states)
    {operation : Instruction} (operationEq : instruction state = some operation) :
    ∀ target ∈ operation.targets, target = 0 ∨ target ∈ states := by
  simp [states] at stateMem
  rcases stateMem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl <;>
    simp [instruction] at operationEq <;> subst operation <;>
    simp [Instruction.targets, states]

theorem instruction_count :
    (states.filter fun state =>
      match instruction state with
      | some (.increment _ _) => true
      | _ => false).length = 8 ∧
    (states.filter fun state =>
      match instruction state with
      | some (.decrement _ _ _) => true
      | _ => false).length = 12 := by
  decide

@[simp] theorem step_halt (registers : Registers) :
    step (haltConfiguration registers) = none := by
  rfl

end Mortality.SourceMachine.KorecU20
