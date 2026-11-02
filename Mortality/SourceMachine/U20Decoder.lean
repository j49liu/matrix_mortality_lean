import Mortality.SourceMachine.KorecR2Semantics

/-!
# Korec U20 decoder and simulation block

The instruction reader of `U20` leaves a numerical operation code in `R5`
and enters state `q16`.  States `q16`, `q18`, `q20`, and `q22` divide that
code by three.  The remainder chooses one of the three `KorecR2`
instructions, while the quotient becomes its destination state.  The final
states `q23`, `q27`, `q30`, `q31`, and `q32` execute that instruction.

This file proves those claims for arbitrary register contents.  The harder
instruction-reader proof is kept separate.
-/

namespace Mortality.SourceMachine.KorecU20Interpreter

open Mortality.SourceMachine
open Mortality.SourceMachine.KorecU20
open Mortality.SourceMachine.KorecR2

/-- An explicit eight-register vector, in the order `R0`, ..., `R7`. -/
def registers (r0 r1 r2 r3 r4 r5 r6 r7 : Nat) : KorecU20.Registers :=
  fun register =>
    match register.val with
    | 0 => r0
    | 1 => r1
    | 2 => r2
    | 3 => r3
    | 4 => r4
    | 5 => r5
    | 6 => r6
    | _ => r7

/-- Concrete notation for a `U20` configuration. -/
def configuration (state r0 r1 r2 r3 r4 r5 r6 r7 : Nat) :
    KorecU20.Configuration :=
  { state, registers := registers r0 r1 r2 r3 r4 r5 r6 r7 }

@[simp] theorem registers_zero (r0 r1 r2 r3 r4 r5 r6 r7 : Nat) :
    registers r0 r1 r2 r3 r4 r5 r6 r7 0 = r0 := rfl

@[simp] theorem registers_one (r0 r1 r2 r3 r4 r5 r6 r7 : Nat) :
    registers r0 r1 r2 r3 r4 r5 r6 r7 1 = r1 := rfl

@[simp] theorem registers_two (r0 r1 r2 r3 r4 r5 r6 r7 : Nat) :
    registers r0 r1 r2 r3 r4 r5 r6 r7 2 = r2 := rfl

@[simp] theorem registers_three (r0 r1 r2 r3 r4 r5 r6 r7 : Nat) :
    registers r0 r1 r2 r3 r4 r5 r6 r7 3 = r3 := rfl

@[simp] theorem registers_four (r0 r1 r2 r3 r4 r5 r6 r7 : Nat) :
    registers r0 r1 r2 r3 r4 r5 r6 r7 4 = r4 := rfl

@[simp] theorem registers_five (r0 r1 r2 r3 r4 r5 r6 r7 : Nat) :
    registers r0 r1 r2 r3 r4 r5 r6 r7 5 = r5 := rfl

@[simp] theorem registers_six (r0 r1 r2 r3 r4 r5 r6 r7 : Nat) :
    registers r0 r1 r2 r3 r4 r5 r6 r7 6 = r6 := rfl

@[simp] theorem registers_seven (r0 r1 r2 r3 r4 r5 r6 r7 : Nat) :
    registers r0 r1 r2 r3 r4 r5 r6 r7 7 = r7 := rfl

theorem registers_ext (f : KorecU20.Registers)
    (r0 r1 r2 r3 r4 r5 r6 r7 : Nat)
    (h0 : f 0 = r0) (h1 : f 1 = r1) (h2 : f 2 = r2)
    (h3 : f 3 = r3) (h4 : f 4 = r4) (h5 : f 5 = r5)
    (h6 : f 6 = r6) (h7 : f 7 = r7) :
    f = registers r0 r1 r2 r3 r4 r5 r6 r7 := by
  funext index
  exact Fin.cases h0 (fun index =>
    Fin.cases h1 (fun index =>
      Fin.cases h2 (fun index =>
        Fin.cases h3 (fun index =>
          Fin.cases h4 (fun index =>
            Fin.cases h5 (fun index =>
              Fin.cases h6 (fun index =>
                Fin.cases h7 (fun impossible => Fin.elim0 impossible) index) index) index)
              index) index) index) index) index

@[simp] theorem registers_update_zero
    (r0 r1 r2 r3 r4 r5 r6 r7 value : Nat) :
    (registers r0 r1 r2 r3 r4 r5 r6 r7).update 0 value =
      registers value r1 r2 r3 r4 r5 r6 r7 := by
  apply registers_ext <;> simp [KorecU20.Registers.update]

@[simp] theorem registers_update_one
    (r0 r1 r2 r3 r4 r5 r6 r7 value : Nat) :
    (registers r0 r1 r2 r3 r4 r5 r6 r7).update 1 value =
      registers r0 value r2 r3 r4 r5 r6 r7 := by
  apply registers_ext <;> simp [KorecU20.Registers.update]

@[simp] theorem registers_update_two
    (r0 r1 r2 r3 r4 r5 r6 r7 value : Nat) :
    (registers r0 r1 r2 r3 r4 r5 r6 r7).update 2 value =
      registers r0 r1 value r3 r4 r5 r6 r7 := by
  apply registers_ext <;> simp [KorecU20.Registers.update]

@[simp] theorem registers_update_four
    (r0 r1 r2 r3 r4 r5 r6 r7 value : Nat) :
    (registers r0 r1 r2 r3 r4 r5 r6 r7).update 4 value =
      registers r0 r1 r2 r3 value r5 r6 r7 := by
  apply registers_ext <;> simp [KorecU20.Registers.update]

@[simp] theorem registers_update_five
    (r0 r1 r2 r3 r4 r5 r6 r7 value : Nat) :
    (registers r0 r1 r2 r3 r4 r5 r6 r7).update 5 value =
      registers r0 r1 r2 r3 r4 value r6 r7 := by
  apply registers_ext <;> simp [KorecU20.Registers.update]

@[simp] theorem registers_update_six
    (r0 r1 r2 r3 r4 r5 r6 r7 value : Nat) :
    (registers r0 r1 r2 r3 r4 r5 r6 r7).update 6 value =
      registers r0 r1 r2 r3 r4 r5 value r7 := by
  apply registers_ext <;> simp [KorecU20.Registers.update]

@[simp] theorem registers_update_seven
    (r0 r1 r2 r3 r4 r5 r6 r7 value : Nat) :
    (registers r0 r1 r2 r3 r4 r5 r6 r7).update 7 value =
      registers r0 r1 r2 r3 r4 r5 r6 value := by
  apply registers_ext <;> simp [KorecU20.Registers.update]

theorem initialRegistersTwo_eq_registers (programInput dataInput : Nat) :
    KorecU20.initialRegistersTwo programInput dataInput =
      registers 0 programInput dataInput 0 0 0 0 0 := by
  apply registers_ext <;> simp [KorecU20.initialRegistersTwo]

/-- One complete quotient-producing trip through the decoder consumes three
units of `R5` and increments `R4`. -/
theorem decoder_cycle
    (r0 r1 r2 r3 quotient remainder r6 r7 : Nat) :
    Reaches KorecU20.step
      (configuration 16 r0 r1 r2 r3 quotient (remainder + 3) r6 r7)
      (configuration 16 r0 r1 r2 r3 (quotient + 1) remainder r6 r7) := by
  have firstStep :
      KorecU20.step
          (configuration 16 r0 r1 r2 r3 quotient (remainder + 3) r6 r7) =
        some (configuration 18 r0 r1 r2 r3 quotient (remainder + 2) r6 r7) := by
    simp [KorecU20.step, KorecU20.instruction, configuration]
  have secondStep :
      KorecU20.step
          (configuration 18 r0 r1 r2 r3 quotient (remainder + 2) r6 r7) =
        some (configuration 20 r0 r1 r2 r3 quotient (remainder + 1) r6 r7) := by
    simp [KorecU20.step, KorecU20.instruction, configuration]
  have thirdStep :
      KorecU20.step
          (configuration 20 r0 r1 r2 r3 quotient (remainder + 1) r6 r7) =
        some (configuration 22 r0 r1 r2 r3 quotient remainder r6 r7) := by
    simp [KorecU20.step, KorecU20.instruction, configuration]
  have fourthStep :
      KorecU20.step
          (configuration 22 r0 r1 r2 r3 quotient remainder r6 r7) =
        some (configuration 16 r0 r1 r2 r3 (quotient + 1) remainder r6 r7) := by
    simp [KorecU20.step, KorecU20.instruction, configuration]
  exact (Reaches.single firstStep).trans <|
    (Reaches.single secondStep).trans <|
      (Reaches.single thirdStep).trans (Reaches.single fourthStep)

/-- Repeated decoder cycles compute the quotient by three. -/
theorem decoder_reduce
    (r0 r1 r2 r3 initialQuotient quotient remainder r6 r7 : Nat) :
    Reaches KorecU20.step
      (configuration 16 r0 r1 r2 r3 initialQuotient
        (3 * quotient + remainder) r6 r7)
      (configuration 16 r0 r1 r2 r3 (initialQuotient + quotient)
        remainder r6 r7) := by
  induction quotient generalizing initialQuotient with
  | zero => simp; exact Reaches.refl _
  | succ quotient inductionHypothesis =>
      have first := decoder_cycle r0 r1 r2 r3 initialQuotient
        (3 * quotient + remainder) r6 r7
      have suffix := inductionHypothesis (initialQuotient := initialQuotient + 1)
      simpa [Nat.mul_succ, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        first.trans suffix

theorem decoder_remainder_zero
    (r0 r1 r2 r3 quotient r6 r7 : Nat) :
    Reaches KorecU20.step
      (configuration 16 r0 r1 r2 r3 quotient 0 r6 r7)
      (configuration 23 r0 r1 r2 r3 quotient 0 r6 r7) := by
  exact Reaches.single (by
    simp [KorecU20.step, KorecU20.instruction, configuration])

theorem decoder_remainder_one
    (r0 r1 r2 r3 quotient r6 r7 : Nat) :
    Reaches KorecU20.step
      (configuration 16 r0 r1 r2 r3 quotient 1 r6 r7)
      (configuration 27 r0 r1 r2 r3 quotient 0 r6 r7) := by
  have firstStep :
      KorecU20.step (configuration 16 r0 r1 r2 r3 quotient 1 r6 r7) =
        some (configuration 18 r0 r1 r2 r3 quotient 0 r6 r7) := by
    simp [KorecU20.step, KorecU20.instruction, configuration]
  have secondStep :
      KorecU20.step (configuration 18 r0 r1 r2 r3 quotient 0 r6 r7) =
        some (configuration 27 r0 r1 r2 r3 quotient 0 r6 r7) := by
    simp [KorecU20.step, KorecU20.instruction, configuration]
  exact (Reaches.single firstStep).trans (Reaches.single secondStep)

theorem decoder_remainder_two
    (r0 r1 r2 r3 quotient r6 r7 : Nat) :
    Reaches KorecU20.step
      (configuration 16 r0 r1 r2 r3 quotient 2 r6 r7)
      (configuration 30 r0 r1 r2 r3 quotient 0 r6 r7) := by
  have firstStep :
      KorecU20.step (configuration 16 r0 r1 r2 r3 quotient 2 r6 r7) =
        some (configuration 18 r0 r1 r2 r3 quotient 1 r6 r7) := by
    simp [KorecU20.step, KorecU20.instruction, configuration]
  have secondStep :
      KorecU20.step (configuration 18 r0 r1 r2 r3 quotient 1 r6 r7) =
        some (configuration 20 r0 r1 r2 r3 quotient 0 r6 r7) := by
    simp [KorecU20.step, KorecU20.instruction, configuration]
  have thirdStep :
      KorecU20.step (configuration 20 r0 r1 r2 r3 quotient 0 r6 r7) =
        some (configuration 30 r0 r1 r2 r3 quotient 0 r6 r7) := by
    simp [KorecU20.step, KorecU20.instruction, configuration]
  exact (Reaches.single firstStep).trans <|
    (Reaches.single secondStep).trans (Reaches.single thirdStep)

/-- The decoder sends `3j`, `3j+1`, and `3j+2` to the three operation
entries, with `j` stored in `R4`. -/
theorem decoder_correct
    (r0 r1 r2 r3 quotient remainder r6 r7 : Nat)
    (remainderBound : remainder < 3) :
    Reaches KorecU20.step
      (configuration 16 r0 r1 r2 r3 0 (3 * quotient + remainder) r6 r7)
      (configuration
        (match remainder with | 0 => 23 | 1 => 27 | _ => 30)
        r0 r1 r2 r3 quotient 0 r6 r7) := by
  have reduced := decoder_reduce r0 r1 r2 r3 0 quotient remainder r6 r7
  have quotientZero : 0 + quotient = quotient := by omega
  rw [quotientZero] at reduced
  have alternatives : remainder = 0 ∨ remainder = 1 ∨ remainder = 2 := by omega
  rcases alternatives with rfl | rfl | rfl
  · exact reduced.trans (decoder_remainder_zero r0 r1 r2 r3 quotient r6 r7)
  · exact reduced.trans (decoder_remainder_one r0 r1 r2 r3 quotient r6 r7)
  · exact reduced.trans (decoder_remainder_two r0 r1 r2 r3 quotient r6 r7)

/-- The representation of an interpreted `R2` configuration at the boundary
of one `U20` simulation cycle.  A positive state `j+1` is represented at
`q1` with `R4=j`; state zero is represented by `U20`'s Stop state. -/
def simulationConfiguration (programCode carry : Nat)
    (source : KorecR2.Configuration) : KorecU20.Configuration :=
  match source.state with
  | 0 =>
      configuration 0 source.registerZero programCode source.registerTwo
        0 0 0 carry 0
  | state + 1 =>
      configuration 1 source.registerZero programCode source.registerTwo
        0 state 0 carry 0

/-- `q32` converts the quotient in `R4` into the next simulated control
state, including the distinguished target zero. -/
theorem dispatch_target
    (programCode registerZero registerTwo carry target : Nat) :
    Reaches KorecU20.step
      (configuration 32 registerZero programCode registerTwo 0 target 0 carry 0)
      (simulationConfiguration programCode carry
        { state := target, registerZero, registerTwo }) := by
  cases target with
  | zero =>
      exact Reaches.single (by
        simp [KorecU20.step, KorecU20.instruction, simulationConfiguration,
          configuration])
  | succ target =>
      exact Reaches.single (by
        simp [KorecU20.step, KorecU20.instruction, simulationConfiguration,
          configuration])

theorem execute_decrement_zero_positive
    (programCode carry target value registerTwo : Nat) :
    Reaches KorecU20.step
      (configuration 23 (value + 1) programCode registerTwo 0 target 0 carry 0)
      (simulationConfiguration programCode carry
        { state := target, registerZero := value, registerTwo }) := by
  exact (Reaches.single (by
    simp [KorecU20.step, KorecU20.instruction, configuration,
      registers])).trans
    (dispatch_target programCode value registerTwo carry target)

theorem execute_decrement_zero_zero
    (programCode carry target registerTwo : Nat) :
    Reaches KorecU20.step
      (configuration 23 0 programCode registerTwo 0 target 0 carry 0)
      (simulationConfiguration programCode carry
        { state := target + 1, registerZero := 0, registerTwo }) := by
  exact Reaches.single (by
    simp [KorecU20.step, KorecU20.instruction, simulationConfiguration,
      configuration, registers])

theorem execute_decrement_two_positive
    (programCode carry target registerZero value : Nat) :
    Reaches KorecU20.step
      (configuration 27 registerZero programCode (value + 1) 0 target 0 carry 0)
      (simulationConfiguration programCode carry
        { state := target, registerZero, registerTwo := value }) := by
  exact (Reaches.single (by
    simp [KorecU20.step, KorecU20.instruction, configuration,
      registers])).trans
    (dispatch_target programCode registerZero value carry target)

theorem execute_decrement_two_zero
    (programCode carry target registerZero : Nat) :
    Reaches KorecU20.step
      (configuration 27 registerZero programCode 0 0 target 0 carry 0)
      (simulationConfiguration programCode carry
        { state := target + 1, registerZero, registerTwo := 0 }) := by
  exact Reaches.single (by
    simp [KorecU20.step, KorecU20.instruction, simulationConfiguration,
      configuration, registers])

theorem execute_incrementBoth
    (programCode carry target registerZero registerTwo : Nat) :
    Reaches KorecU20.step
      (configuration 30 registerZero programCode registerTwo 0 target 0 carry 0)
      (simulationConfiguration programCode carry
        { state := target
          registerZero := registerZero + 1
          registerTwo := registerTwo + 1 }) := by
  have firstStep :
      KorecU20.step
          (configuration 30 registerZero programCode registerTwo 0 target 0 carry 0) =
        some (configuration 31 (registerZero + 1) programCode registerTwo
          0 target 0 carry 0) := by
    simp [KorecU20.step, KorecU20.instruction, configuration]
  have secondStep :
      KorecU20.step
          (configuration 31 (registerZero + 1) programCode registerTwo
            0 target 0 carry 0) =
        some (configuration 32 (registerZero + 1) programCode (registerTwo + 1)
          0 target 0 carry 0) := by
    simp [KorecU20.step, KorecU20.instruction, configuration]
  exact (Reaches.single firstStep).trans <|
    (Reaches.single secondStep).trans <|
      dispatch_target programCode (registerZero + 1) (registerTwo + 1)
        carry target

/-- The represented `R2` configuration after executing one decoded
instruction. -/
def decodedResult (programCode carry registerZero registerTwo : Nat) :
    KorecR2.Instruction → KorecU20.Configuration
  | .decrement .zero target =>
      match registerZero with
      | 0 => simulationConfiguration programCode carry
          { state := target + 1, registerZero := 0, registerTwo }
      | value + 1 => simulationConfiguration programCode carry
          { state := target, registerZero := value, registerTwo }
  | .decrement .one target =>
      match registerTwo with
      | 0 => simulationConfiguration programCode carry
          { state := target + 1, registerZero, registerTwo := 0 }
      | value + 1 => simulationConfiguration programCode carry
          { state := target, registerZero, registerTwo := value }
  | .incrementBoth target => simulationConfiguration programCode carry
      { state := target
        registerZero := registerZero + 1
        registerTwo := registerTwo + 1 }

theorem decodedResult_of_r2Step
    {program : KorecR2.Program} {source target : KorecR2.Configuration}
    {operation : KorecR2.Instruction}
    (statePositive : 0 < source.state)
    (lookup : program source.state = some operation)
    (stepEq : KorecR2.step program source = some target)
    (programCode carry : Nat) :
    decodedResult programCode carry source.registerZero source.registerTwo operation =
      simulationConfiguration programCode carry target := by
  rcases source with ⟨state, registerZero, registerTwo⟩
  cases operation with
  | decrement register destination =>
      cases register <;> cases registerZero <;> cases registerTwo <;>
        simp [KorecR2.step, Nat.ne_of_gt statePositive, lookup] at stepEq <;>
        subst target <;> rfl
  | incrementBoth destination =>
      simp [KorecR2.step, Nat.ne_of_gt statePositive, lookup] at stepEq
      subst target
      rfl

/-- Once the reader has delivered an instruction code to `q16`, `U20`
performs exactly the corresponding `R2` operation. -/
theorem decode_and_execute
    (programCode carry registerZero registerTwo : Nat)
    (instruction : KorecR2.Instruction) :
    Reaches KorecU20.step
      (configuration 16 registerZero programCode registerTwo 0 0
        instruction.code carry 0)
      (decodedResult programCode carry registerZero registerTwo instruction) := by
  cases instruction with
  | decrement register target =>
      cases register
      · have decoded := decoder_correct registerZero programCode registerTwo 0
          target 0 carry 0 (by decide : 0 < 3)
        cases registerZero
        · simpa [KorecR2.Instruction.code, decodedResult] using decoded.trans
            (execute_decrement_zero_zero programCode carry target registerTwo)
        · rename_i value
          simpa [KorecR2.Instruction.code, decodedResult] using decoded.trans
            (execute_decrement_zero_positive programCode carry target value registerTwo)
      · have decoded := decoder_correct registerZero programCode registerTwo 0
          target 1 carry 0 (by decide : 1 < 3)
        cases registerTwo
        · simpa [KorecR2.Instruction.code, decodedResult] using decoded.trans
            (execute_decrement_two_zero programCode carry target registerZero)
        · rename_i value
          simpa [KorecR2.Instruction.code, decodedResult] using decoded.trans
            (execute_decrement_two_positive programCode carry target registerZero value)
  | incrementBoth target =>
      have decoded := decoder_correct registerZero programCode registerTwo 0
        target 2 carry 0 (by decide : 2 < 3)
      simpa [KorecR2.Instruction.code, decodedResult] using decoded.trans
        (execute_incrementBoth programCode carry target registerZero registerTwo)

end Mortality.SourceMachine.KorecU20Interpreter
