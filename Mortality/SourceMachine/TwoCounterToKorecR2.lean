import Mortality.SourceMachine.TwoCounterSemantics
import Mortality.SourceMachine.KorecR2Semantics
import Mortality.SourceMachine.U20Simulation

/-!
# Compilation of ordinary two-counter programs to Korec's R2 language

Korec's reader language has only three operations.  Its conditional
decrement must branch to consecutive states, and its sole increment changes
both counters.  This file gives an eight-address macro for every ordinary
two-counter instruction and proves exact preservation and reflection of
halting.
-/

namespace Mortality.SourceMachine.TwoCounterToKorecR2

open Mortality.SourceMachine
open Mortality.SourceMachine.TotalTwoCounter
open Mortality.SourceMachine.U20Compilation

/-- Entry address of an eight-address macro.  Source halt remains target
halt, while source state one remains target state one. -/
def entry : Nat → Nat
  | 0 => 0
  | state + 1 => 8 * state + 1

@[simp] theorem entry_zero : entry 0 = 0 := rfl

theorem entry_succ (state : Nat) :
    entry (state + 1) = 8 * state + 1 := rfl

@[simp] theorem entry_succ_ne_zero (state : Nat) :
    entry (state + 1) ≠ 0 := by
  simp [entry]

def sourceState (state : Nat) : Nat := (state - 1) / 8 + 1

def macroOffset (state : Nat) : Nat := (state - 1) % 8

@[simp] theorem sourceState_entry_add (state offset : Nat)
    (bound : offset < 8) :
    sourceState (entry (state + 1) + offset) = state + 1 := by
  simp only [entry_succ, sourceState]
  omega

@[simp] theorem macroOffset_entry_add (state offset : Nat)
    (bound : offset < 8) :
    macroOffset (entry (state + 1) + offset) = offset := by
  simp only [entry_succ, macroOffset]
  omega

@[simp] theorem entry_positive {state : Nat} (positive : 0 < state) :
    0 < entry state := by
  obtain ⟨predecessor, rfl⟩ := Nat.exists_eq_succ_of_ne_zero
    (Nat.ne_of_gt positive)
  simp [entry]

/-- Swap the two counter names.  After an `incrementBoth`, decrementing the
other counter implements an increment of the requested counter. -/
def other : Counter → Counter
  | .zero => .one
  | .one => .zero

/-- Instruction installed at one offset of a source macro.  Offsets not used
by the selected operation enter a nonhalting self loop; no well-formed
simulation reaches them. -/
def instructionAt (sourceEntry : Nat)
    (instruction : TotalTwoCounter.Instruction) (offset : Nat) :
    KorecR2.Instruction :=
  match instruction, offset with
  | .increment _ _, 0 => .incrementBoth (sourceEntry + 1)
  | .increment counter target, 1 => .decrement (other counter) (entry target)
  | .decrement counter _ _, 0 => .decrement counter (sourceEntry + 1)
  | .decrement _ _ _, 1 => .incrementBoth (sourceEntry + 3)
  | .decrement _ _ _, 2 => .incrementBoth (sourceEntry + 5)
  | .decrement _ _ _, 3 => .decrement .zero (sourceEntry + 4)
  | .decrement _ positiveTarget _, 4 =>
      .decrement .one (entry positiveTarget)
  | .decrement _ _ _, 5 => .decrement .zero (sourceEntry + 6)
  | .decrement _ _ zeroTarget, 6 => .decrement .one (entry zeroTarget)
  | _, _ => .incrementBoth sourceEntry

/-- The compiled target program.  Division by eight recovers the source
state; the remainder selects its macro instruction. -/
def compile (program : TotalTwoCounter.Program) : KorecR2.Program :=
  fun state =>
    if state = 0 then none
    else
      let source := sourceState state
      some (instructionAt (entry source) (program source) (macroOffset state))

@[simp] theorem compile_zero (program : TotalTwoCounter.Program) :
    compile program 0 = none := by
  simp [compile]

@[simp] theorem compile_entry_add (program : TotalTwoCounter.Program)
    (state offset : Nat) (bound : offset < 8) :
    compile program (entry (state + 1) + offset) =
      some (instructionAt (entry (state + 1)) (program (state + 1)) offset) := by
  have positive : entry (state + 1) + offset ≠ 0 := by
    simp [entry]
  unfold compile
  rw [if_neg positive]
  dsimp only
  rw [sourceState_entry_add state offset bound,
    macroOffset_entry_add state offset bound]

@[simp] theorem compile_entry (program : TotalTwoCounter.Program) (state : Nat) :
    compile program (entry (state + 1)) =
      some (instructionAt (entry (state + 1)) (program (state + 1)) 0) := by
  simpa using compile_entry_add program state 0 (by omega)

@[simp] theorem compile_entry_one (program : TotalTwoCounter.Program) (state : Nat) :
    compile program (entry (state + 1) + 1) =
      some (instructionAt (entry (state + 1)) (program (state + 1)) 1) := by
  exact compile_entry_add program state 1 (by omega)

@[simp] theorem compile_entry_two (program : TotalTwoCounter.Program) (state : Nat) :
    compile program (entry (state + 1) + 2) =
      some (instructionAt (entry (state + 1)) (program (state + 1)) 2) := by
  exact compile_entry_add program state 2 (by omega)

@[simp] theorem compile_entry_three (program : TotalTwoCounter.Program) (state : Nat) :
    compile program (entry (state + 1) + 3) =
      some (instructionAt (entry (state + 1)) (program (state + 1)) 3) := by
  exact compile_entry_add program state 3 (by omega)

@[simp] theorem compile_entry_four (program : TotalTwoCounter.Program) (state : Nat) :
    compile program (entry (state + 1) + 4) =
      some (instructionAt (entry (state + 1)) (program (state + 1)) 4) := by
  exact compile_entry_add program state 4 (by omega)

@[simp] theorem compile_entry_five (program : TotalTwoCounter.Program) (state : Nat) :
    compile program (entry (state + 1) + 5) =
      some (instructionAt (entry (state + 1)) (program (state + 1)) 5) := by
  exact compile_entry_add program state 5 (by omega)

@[simp] theorem compile_entry_six (program : TotalTwoCounter.Program) (state : Nat) :
    compile program (entry (state + 1) + 6) =
      some (instructionAt (entry (state + 1)) (program (state + 1)) 6) := by
  exact compile_entry_add program state 6 (by omega)

/-- Preserve the counter values and replace the source label by its macro
entry. -/
def encodeConfiguration (configuration : TotalTwoCounter.Configuration) :
    KorecR2.Configuration :=
  { state := entry configuration.state
    registerZero := configuration.counterZero
    registerTwo := configuration.counterOne }

@[simp] theorem encode_initial (input : Nat) :
    encodeConfiguration (TotalTwoCounter.initialConfiguration input) =
      KorecR2.initialConfiguration input := by
  rfl

@[simp] theorem encode_halt (counterZero counterOne : Nat) :
    encodeConfiguration
        (TotalTwoCounter.haltConfiguration counterZero counterOne) =
      KorecR2.haltConfiguration counterZero counterOne := by
  rfl

/-- Each ordinary source step is implemented by a nonempty macro: two R2
steps for an increment and four for a conditional decrement. -/
theorem compile_step_iteration
    {program : TotalTwoCounter.Program}
    {before after : TotalTwoCounter.Configuration}
    (stepEq : TotalTwoCounter.step program before = some after) :
    ∃ fuel,
      0 < fuel ∧
      iterate (KorecR2.step (compile program)) fuel
          (encodeConfiguration before) =
        some (encodeConfiguration after) := by
  rcases before with ⟨state, counterZero, counterOne⟩
  have statePositive : 0 < state := by
    by_cases stateZero : state = 0
    · simp [TotalTwoCounter.step, stateZero] at stepEq
    · omega
  obtain ⟨sourceState, rfl⟩ := Nat.exists_eq_succ_of_ne_zero
    (Nat.ne_of_gt statePositive)
  cases operation : program (sourceState + 1) with
  | increment counter target =>
      cases counter with
      | zero =>
          simp [TotalTwoCounter.step, TotalTwoCounter.execute, operation] at stepEq
          subst after
          refine ⟨2, by omega, ?_⟩
          simp [iterate, encodeConfiguration, KorecR2.step,
            instructionAt, other, operation]
      | one =>
          simp [TotalTwoCounter.step, TotalTwoCounter.execute, operation] at stepEq
          subst after
          refine ⟨2, by omega, ?_⟩
          simp [iterate, encodeConfiguration, KorecR2.step,
            instructionAt, other, operation]
  | decrement counter positiveTarget zeroTarget =>
      cases counter with
      | zero =>
          cases counterZero with
          | zero =>
              simp [TotalTwoCounter.step, TotalTwoCounter.execute, operation] at stepEq
              subst after
              refine ⟨4, by omega, ?_⟩
              simp [iterate, encodeConfiguration, KorecR2.step,
                instructionAt, operation]
          | succ value =>
              simp [TotalTwoCounter.step, TotalTwoCounter.execute, operation] at stepEq
              subst after
              refine ⟨4, by omega, ?_⟩
              simp [iterate, encodeConfiguration, KorecR2.step,
                instructionAt, operation]
      | one =>
          cases counterOne with
          | zero =>
              simp [TotalTwoCounter.step, TotalTwoCounter.execute, operation] at stepEq
              subst after
              refine ⟨4, by omega, ?_⟩
              simp [iterate, encodeConfiguration, KorecR2.step,
                instructionAt, operation]
          | succ value =>
              simp [TotalTwoCounter.step, TotalTwoCounter.execute, operation] at stepEq
              subst after
              refine ⟨4, by omega, ?_⟩
              simp [iterate, encodeConfiguration, KorecR2.step,
                instructionAt, operation]

/-- Every positive target address contains an instruction. -/
theorem compile_operationAt (program : TotalTwoCounter.Program)
    (state : Nat) (positive : 0 < state) :
    ∃ operation, compile program state = some operation := by
  unfold compile
  rw [if_neg (Nat.ne_of_gt positive)]
  exact ⟨_, rfl⟩

/-- Compile an exact finite source execution, retaining a lower bound on the
number of target steps. -/
theorem compile_iterate
    {program : TotalTwoCounter.Program}
    {source finish : TotalTwoCounter.Configuration} {sourceFuel : Nat}
    (sourceExecution :
      iterate (TotalTwoCounter.step program) sourceFuel source = some finish) :
    ∃ targetFuel,
      sourceFuel ≤ targetFuel ∧
      iterate (KorecR2.step (compile program)) targetFuel
          (encodeConfiguration source) =
        some (encodeConfiguration finish) := by
  induction sourceFuel generalizing finish with
  | zero =>
      simp [iterate] at sourceExecution
      subst finish
      exact ⟨0, by omega, rfl⟩
  | succ sourceFuel inductionHypothesis =>
      simp only [iterate] at sourceExecution
      cases prefixEq : iterate (TotalTwoCounter.step program) sourceFuel source with
      | none => simp [prefixEq] at sourceExecution
      | some middle =>
          have lastStep : TotalTwoCounter.step program middle = some finish := by
            simpa [prefixEq] using sourceExecution
          obtain ⟨prefixFuel, prefixBound, compiledPrefix⟩ :=
            inductionHypothesis prefixEq
          obtain ⟨stepFuel, stepPositive, compiledStep⟩ :=
            compile_step_iteration lastStep
          refine ⟨prefixFuel + stepFuel, by omega, ?_⟩
          rw [iterate_add, compiledPrefix]
          simpa using compiledStep

/-- A nonhalting source computation has a successful prefix of every finite
length because the source program is total away from state zero. -/
theorem source_iterate_exists_of_not_halts
    (program : TotalTwoCounter.Program) (input : Nat)
    (notHalts : ¬TotalTwoCounter.Halts program input) :
    ∀ fuel, ∃ finish,
      iterate (TotalTwoCounter.step program) fuel
          (TotalTwoCounter.initialConfiguration input) = some finish := by
  intro fuel
  induction fuel with
  | zero => exact ⟨_, rfl⟩
  | succ fuel inductionHypothesis =>
      obtain ⟨middle, middleExecution⟩ := inductionHypothesis
      have statePositive : 0 < middle.state := by
        by_cases stateZero : middle.state = 0
        · have middleRun := reaches_iff_exists_iterate.mpr
            ⟨fuel, middleExecution⟩
          have middleEq :
              middle = TotalTwoCounter.haltConfiguration middle.counterZero
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

/-- The eight-address compiler preserves and reflects halting.  Reflection
uses determinism and the positive length of every compiled macro, so a target
run cannot halt inside a macro. -/
theorem compiledHalts_iff (program : TotalTwoCounter.Program) (input : Nat) :
    KorecR2.Halts (compile program) input ↔
      TotalTwoCounter.Halts program input := by
  constructor
  · intro targetHalts
    by_cases sourceHalts : TotalTwoCounter.Halts program input
    · exact sourceHalts
    · exfalso
      obtain ⟨registerZero, registerTwo, targetRun⟩ := targetHalts
      obtain ⟨haltFuel, haltExecution⟩ :=
        reaches_iff_exists_iterate.mp targetRun
      obtain ⟨sourceFinish, sourceExecution⟩ :=
        source_iterate_exists_of_not_halts program input sourceHalts
          (haltFuel + 1)
      obtain ⟨targetFuel, fuelBound, compiledExecution⟩ :=
        compile_iterate sourceExecution
      rw [encode_initial] at compiledExecution
      have cannotPassHalt := successful_iterations_before_halt
        (step := KorecR2.step (compile program))
        (haltEq := KorecR2.step_halt (compile program) registerZero registerTwo)
        haltExecution compiledExecution
      omega
  · rintro ⟨counterZero, counterOne, sourceRun⟩
    obtain ⟨sourceFuel, sourceExecution⟩ :=
      reaches_iff_exists_iterate.mp sourceRun
    obtain ⟨targetFuel, _, targetExecution⟩ :=
      compile_iterate sourceExecution
    refine ⟨counterZero, counterOne, reaches_iff_exists_iterate.mpr ⟨targetFuel, ?_⟩⟩
    simpa using targetExecution

end Mortality.SourceMachine.TwoCounterToKorecR2
