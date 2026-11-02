import Mortality.SourceMachine.KorecR2Semantics
import Mortality.SourceMachine.U20Simulation

/-!
# Relocating an R2 program above a simple fixed entry macro

This file treats the simplest useful relocation layout.  State zero remains
halt.  A three-instruction prefix at states one, two, and three increments
both registers and then decrements each one, thereby entering the relocated
state one without changing the data.

Korec's numerical program-code construction uses the same
register-preserving jump idea, but its reserved labels need not be
consecutive and it may require a longer chain.  `R2Embedding` formalizes that
general interface.  The construction below remains useful as a transparent
special case and as a check on the target-zero restart behavior.

This file proves exact halting preservation for the three-state layout.
-/

namespace Mortality.SourceMachine.R2Relocation

open Mortality.SourceMachine
open Mortality.SourceMachine.KorecR2
open Mortality.SourceMachine.U20Compilation

/-- State zero remains halt; every positive state is translated by `offset`. -/
def shiftState (offset : Nat) : Nat → Nat
  | 0 => 0
  | state + 1 => offset + state + 1

@[simp] theorem shiftState_zero (offset : Nat) : shiftState offset 0 = 0 := rfl

@[simp] theorem shiftState_succ (offset state : Nat) :
    shiftState offset (state + 1) = offset + state + 1 := rfl

def shiftInstruction (offset : Nat) :
    KorecR2.Instruction → KorecR2.Instruction
  | .decrement register target => .decrement register (shiftState offset target)
  | .incrementBoth target => .incrementBoth (shiftState offset target)

/-- Relocation adds `3 * offset` to the numerical operation code exactly when
the advertised target is positive. This is Korec's congruence (6.2.5), with
the operation remainder modulo three left unchanged. -/
theorem shiftInstruction_code (offset : Nat)
    (instruction : KorecR2.Instruction) :
    (shiftInstruction offset instruction).code =
      if instruction.target = 0 then instruction.code
      else instruction.code + 3 * offset := by
  cases instruction with
  | decrement register target =>
      cases register <;> cases target <;>
        simp [shiftInstruction, shiftState, KorecR2.Instruction.target,
          KorecR2.Instruction.code] <;> omega
  | incrementBoth target =>
      cases target <;>
        simp [shiftInstruction, shiftState, KorecR2.Instruction.target,
          KorecR2.Instruction.code] <;> omega

def shiftConfiguration (offset : Nat)
    (configuration : KorecR2.Configuration) : KorecR2.Configuration :=
  { configuration with state := shiftState offset configuration.state }

@[simp] theorem shiftConfiguration_halt
    (offset registerZero registerTwo : Nat) :
    shiftConfiguration offset
        (KorecR2.haltConfiguration registerZero registerTwo) =
      KorecR2.haltConfiguration registerZero registerTwo := by
  rfl

/-- Relocate the source program above `offset`.  States one through three
form a register-preserving entry macro.  The unused gap is left terminal;
the checked simulation never enters it. -/
def relocate (offset : Nat) (program : KorecR2.Program) : KorecR2.Program :=
  fun state =>
    if state = 0 then none
    else if state = 1 then some (.incrementBoth 2)
    else if state = 2 then some (.decrement .zero 3)
    else if state = 3 then some (.decrement .one (offset + 1))
    else if offset < state then
      (program (state - offset)).map (shiftInstruction offset)
    else none

@[simp] theorem relocate_zero (offset : Nat) (program : KorecR2.Program) :
    relocate offset program 0 = none := by
  simp [relocate]

@[simp] theorem relocate_one (offset : Nat) (program : KorecR2.Program) :
    relocate offset program 1 = some (.incrementBoth 2) := by
  simp [relocate]

@[simp] theorem relocate_two (offset : Nat) (program : KorecR2.Program) :
    relocate offset program 2 = some (.decrement .zero 3) := by
  simp [relocate]

@[simp] theorem relocate_three (offset : Nat) (program : KorecR2.Program) :
    relocate offset program 3 = some (.decrement .one (offset + 1)) := by
  simp [relocate]

@[simp] theorem relocate_shifted_positive
    (offset : Nat) (program : KorecR2.Program) (state : Nat)
    (offsetLarge : 3 ≤ offset) :
    relocate offset program (shiftState offset (state + 1)) =
      (program (state + 1)).map (shiftInstruction offset) := by
  simp only [shiftState_succ, relocate]
  have notZero : offset + state + 1 ≠ 0 := by omega
  have notOne : offset + state + 1 ≠ 1 := by omega
  have notTwo : offset + state + 1 ≠ 2 := by omega
  have notThree : offset + state + 1 ≠ 3 := by omega
  rw [if_neg notZero, if_neg notOne, if_neg notTwo, if_neg notThree,
    if_pos (by omega)]
  congr 2
  omega

/-- The three-state entry macro preserves arbitrary register values. -/
theorem entry_reaches_configuration
    (offset registerZero registerTwo : Nat) (program : KorecR2.Program) :
    Reaches (KorecR2.step (relocate offset program))
      { state := 1, registerZero, registerTwo }
      { state := offset + 1, registerZero, registerTwo } := by
  have first : KorecR2.step (relocate offset program)
      { state := 1
        registerZero := registerZero
        registerTwo := registerTwo } =
    some { state := 2
           registerZero := registerZero + 1
           registerTwo := registerTwo + 1 } := by
    simp [KorecR2.step]
  have second : KorecR2.step (relocate offset program)
      { state := 2
        registerZero := registerZero + 1
        registerTwo := registerTwo + 1 } =
    some { state := 3
           registerZero := registerZero
           registerTwo := registerTwo + 1 } := by
    simp [KorecR2.step]
  have third : KorecR2.step (relocate offset program)
      { state := 3
        registerZero := registerZero
        registerTwo := registerTwo + 1 } =
    some { state := offset + 1
           registerZero := registerZero
           registerTwo := registerTwo } := by
    simp [KorecR2.step]
  exact (Reaches.single first).trans <|
    (Reaches.single second).trans (Reaches.single third)

/-- One source step expands to either one relocated step, or four steps when
a zero-valued conditional with target zero restarts at source state one. -/
theorem relocate_step_iteration
    {offset : Nat} {program : KorecR2.Program} (offsetLarge : 3 ≤ offset)
    {before after : KorecR2.Configuration}
    (stepEq : KorecR2.step program before = some after) :
    ∃ fuel, 0 < fuel ∧
      iterate (KorecR2.step (relocate offset program)) fuel
          (shiftConfiguration offset before) =
        some (shiftConfiguration offset after) := by
  rcases before with ⟨state, registerZero, registerTwo⟩
  have statePositive : 0 < state := by
    by_cases stateZero : state = 0
    · simp [KorecR2.step, stateZero] at stepEq
    · omega
  obtain ⟨state, rfl⟩ := Nat.exists_eq_succ_of_ne_zero
    (Nat.ne_of_gt statePositive)
  have relocatedLookup :=
    relocate_shifted_positive offset program state offsetLarge
  cases lookup : program (state + 1) with
  | none => simp [KorecR2.step, lookup] at stepEq
  | some operation =>
      rw [lookup] at relocatedLookup
      have relocatedLookup' :
          relocate offset program (offset + state + 1) =
            some (shiftInstruction offset operation) := by
        simpa [shiftState] using relocatedLookup
      cases operation with
      | incrementBoth target =>
          simp [KorecR2.step, lookup] at stepEq
          subst after
          refine ⟨1, by omega, ?_⟩
          cases target <;>
            simp [iterate, KorecR2.step, relocatedLookup',
              shiftInstruction, shiftConfiguration]
      | decrement register target =>
          cases register with
          | zero =>
              cases registerZero with
              | zero =>
                  simp [KorecR2.step, lookup] at stepEq
                  subst after
                  cases target with
                  | zero =>
                      refine ⟨4, by omega, ?_⟩
                      simp [iterate, KorecR2.step, relocatedLookup',
                        shiftInstruction, shiftConfiguration]
                  | succ target =>
                      refine ⟨1, by omega, ?_⟩
                      simp [iterate, KorecR2.step, relocatedLookup',
                        shiftInstruction, shiftConfiguration]
                      omega
              | succ value =>
                  simp [KorecR2.step, lookup] at stepEq
                  subst after
                  refine ⟨1, by omega, ?_⟩
                  cases target <;>
                    simp [iterate, KorecR2.step, relocatedLookup',
                      shiftInstruction, shiftConfiguration]
          | one =>
              cases registerTwo with
              | zero =>
                  simp [KorecR2.step, lookup] at stepEq
                  subst after
                  cases target with
                  | zero =>
                      refine ⟨4, by omega, ?_⟩
                      simp [iterate, KorecR2.step, relocatedLookup',
                        shiftInstruction, shiftConfiguration]
                  | succ target =>
                      refine ⟨1, by omega, ?_⟩
                      simp [iterate, KorecR2.step, relocatedLookup',
                        shiftInstruction, shiftConfiguration]
                      omega
              | succ value =>
                  simp [KorecR2.step, lookup] at stepEq
                  subst after
                  refine ⟨1, by omega, ?_⟩
                  cases target <;>
                    simp [iterate, KorecR2.step, relocatedLookup',
                      shiftInstruction, shiftConfiguration]

/-- Compile a finite source execution while retaining a lower bound on the
number of relocated steps. -/
theorem relocate_iterate
    {offset : Nat} {program : KorecR2.Program} (offsetLarge : 3 ≤ offset)
    {source finish : KorecR2.Configuration} {sourceFuel : Nat}
    (sourceExecution :
      iterate (KorecR2.step program) sourceFuel source = some finish) :
    ∃ targetFuel, sourceFuel ≤ targetFuel ∧
      iterate (KorecR2.step (relocate offset program)) targetFuel
          (shiftConfiguration offset source) =
        some (shiftConfiguration offset finish) := by
  induction sourceFuel generalizing finish with
  | zero =>
      simp [iterate] at sourceExecution
      subst finish
      exact ⟨0, by omega, rfl⟩
  | succ sourceFuel inductionHypothesis =>
      simp only [iterate] at sourceExecution
      cases prefixEq : iterate (KorecR2.step program) sourceFuel source with
      | none => simp [prefixEq] at sourceExecution
      | some middle =>
          have lastStep : KorecR2.step program middle = some finish := by
            simpa [prefixEq] using sourceExecution
          obtain ⟨prefixFuel, prefixBound, compiledPrefix⟩ :=
            inductionHypothesis prefixEq
          obtain ⟨stepFuel, stepPositive, compiledStep⟩ :=
            relocate_step_iteration offsetLarge lastStep
          refine ⟨prefixFuel + stepFuel, by omega, ?_⟩
          rw [iterate_add, compiledPrefix]
          simpa using compiledStep

def HaltsFrom (program : KorecR2.Program)
    (start : KorecR2.Configuration) : Prop :=
  ∃ registerZero registerTwo,
    Reaches (KorecR2.step program) start
      (KorecR2.haltConfiguration registerZero registerTwo)

theorem source_iterate_exists_of_not_haltsFrom
    (program : KorecR2.Program)
    (operationAt : ∀ state, 0 < state →
      ∃ operation, program state = some operation)
    (start : KorecR2.Configuration)
    (notHalts : ¬HaltsFrom program start) :
    ∀ fuel, ∃ finish,
      iterate (KorecR2.step program) fuel start = some finish := by
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
              KorecR2.haltConfiguration middle.registerZero
                middle.registerTwo := by
            cases middle
            simp_all [KorecR2.haltConfiguration]
          apply (notHalts ⟨middle.registerZero, middle.registerTwo, ?_⟩).elim
          rw [← middleEq]
          exact middleRun
        · omega
      obtain ⟨operation, lookup⟩ := operationAt middle.state statePositive
      rcases middle with ⟨state, registerZero, registerTwo⟩
      cases operation with
      | decrement register target =>
          cases register <;> cases registerZero <;> cases registerTwo <;>
            simp [iterate, middleExecution, KorecR2.step,
              Nat.ne_of_gt statePositive, lookup]
      | incrementBoth target =>
          simp [iterate, middleExecution, KorecR2.step,
            Nat.ne_of_gt statePositive, lookup]

/-- Relocating every positive source label preserves and reflects halting
from an already shifted configuration. -/
theorem shiftedHaltsFrom_iff
    (offset : Nat) (program : KorecR2.Program) (offsetLarge : 3 ≤ offset)
    (operationAt : ∀ state, 0 < state →
      ∃ operation, program state = some operation)
    (start : KorecR2.Configuration) :
    HaltsFrom (relocate offset program) (shiftConfiguration offset start) ↔
      HaltsFrom program start := by
  constructor
  · intro shiftedHalts
    by_cases sourceHalts : HaltsFrom program start
    · exact sourceHalts
    · exfalso
      obtain ⟨registerZero, registerTwo, shiftedRun⟩ := shiftedHalts
      obtain ⟨haltFuel, haltExecution⟩ :=
        reaches_iff_exists_iterate.mp shiftedRun
      obtain ⟨sourceFinish, sourceExecution⟩ :=
        source_iterate_exists_of_not_haltsFrom program operationAt start
          sourceHalts (haltFuel + 1)
      obtain ⟨targetFuel, fuelBound, shiftedExecution⟩ :=
        relocate_iterate offsetLarge sourceExecution
      have cannotPassHalt := successful_iterations_before_halt
        (step := KorecR2.step (relocate offset program))
        (haltEq := KorecR2.step_halt (relocate offset program)
          registerZero registerTwo)
        haltExecution shiftedExecution
      omega
  · rintro ⟨registerZero, registerTwo, sourceRun⟩
    obtain ⟨fuel, sourceExecution⟩ := reaches_iff_exists_iterate.mp sourceRun
    obtain ⟨targetFuel, _, targetExecution⟩ :=
      relocate_iterate offsetLarge sourceExecution
    exact ⟨registerZero, registerTwo,
      reaches_iff_exists_iterate.mpr ⟨targetFuel, by simpa using targetExecution⟩⟩

/-- The three-state entry macro preserves both registers and reaches the
relocated source initial configuration. -/
theorem entry_reaches (offset input : Nat) (program : KorecR2.Program) :
    Reaches (KorecR2.step (relocate offset program))
      (KorecR2.initialConfiguration input)
      (shiftConfiguration offset (KorecR2.initialConfiguration input)) := by
  simpa [KorecR2.initialConfiguration, shiftConfiguration] using
    entry_reaches_configuration offset 0 input program

theorem haltsFrom_iff_after_prefix
    (program : KorecR2.Program) {start middle : KorecR2.Configuration}
    (prefixRun : Reaches (KorecR2.step program) start middle) :
    HaltsFrom program start ↔ HaltsFrom program middle := by
  constructor
  · rintro ⟨registerZero, registerTwo, wholeRun⟩
    obtain ⟨wholeFuel, wholeExecution⟩ :=
      reaches_iff_exists_iterate.mp wholeRun
    obtain ⟨prefixFuel, prefixExecution⟩ :=
      reaches_iff_exists_iterate.mp prefixRun
    have prefixBound : prefixFuel ≤ wholeFuel :=
      successful_iterations_before_halt
        (KorecR2.step_halt program registerZero registerTwo)
        wholeExecution prefixExecution
    have suffixExecution := strip_iteration_prefix prefixBound wholeExecution
      prefixExecution
    exact ⟨registerZero, registerTwo, reaches_iff_exists_iterate.mpr
      ⟨wholeFuel - prefixFuel, suffixExecution⟩⟩
  · rintro ⟨registerZero, registerTwo, suffix⟩
    exact ⟨registerZero, registerTwo, prefixRun.trans suffix⟩

/-- Exact halting equivalence from the standard state-one input convention
to the relocated program with its register-preserving entry macro. -/
theorem relocatedHalts_iff
    (offset : Nat) (program : KorecR2.Program) (offsetLarge : 3 ≤ offset)
    (operationAt : ∀ state, 0 < state →
      ∃ operation, program state = some operation)
    (input : Nat) :
    KorecR2.Halts (relocate offset program) input ↔
      KorecR2.Halts program input := by
  change HaltsFrom (relocate offset program)
      (KorecR2.initialConfiguration input) ↔
    HaltsFrom program (KorecR2.initialConfiguration input)
  rw [haltsFrom_iff_after_prefix _ (entry_reaches offset input program)]
  exact shiftedHaltsFrom_iff offset program offsetLarge operationAt
    (KorecR2.initialConfiguration input)

end Mortality.SourceMachine.R2Relocation
