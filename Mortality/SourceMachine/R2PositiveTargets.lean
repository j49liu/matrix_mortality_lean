import Mortality.SourceMachine.FiniteControlBounds
import Mortality.SourceMachine.U20Simulation

/-!
# Eliminating zero targets from Korec R2 decrements

Korec's conditional decrement with advertised target zero has a positive
branch to halt and a zero branch to state one.  After an additive relocation,
that zero branch enters the relocation prefix.  This file removes that case
before relocation.

Every old control state `s` is renamed `s + 1`.  New state one is an
unconditional halt gateway containing `INCREMENT BOTH; HALT`.  Consequently,
all advertised targets of conditional decrements are positive.  The gateway
changes the two register values once, but halting only observes the control
state, so this change is immaterial.
-/

namespace Mortality.SourceMachine.R2PositiveTargets

open Mortality.SourceMachine
open Mortality.SourceMachine.KorecR2
open Mortality.SourceMachine.U20Compilation

/-- Rename every old state, including halt, by adding one. -/
def shiftState (state : Nat) : Nat := state + 1

/-- Rename every advertised target by adding one. -/
def shiftInstruction : KorecR2.Instruction → KorecR2.Instruction
  | .decrement register target => .decrement register (shiftState target)
  | .incrementBoth target => .incrementBoth (shiftState target)

@[simp] theorem shiftInstruction_target (operation : KorecR2.Instruction) :
    (shiftInstruction operation).target = shiftState operation.target := by
  cases operation <;> rfl

@[simp] theorem shiftInstruction_code (operation : KorecR2.Instruction) :
    (shiftInstruction operation).code = operation.code + 3 := by
  cases operation with
  | decrement register target =>
      cases register <;>
        simp [shiftInstruction, shiftState, KorecR2.Instruction.code] <;> omega
  | incrementBoth target =>
      simp [shiftInstruction, shiftState, KorecR2.Instruction.code]
      omega

/-- State zero remains terminal.  State one is the halt gateway, and state
`s + 1` contains the renamed instruction of old state `s` for `s > 0`. -/
def normalize (program : KorecR2.Program) : KorecR2.Program := fun state =>
  if state = 0 then none
  else if state = 1 then some (.incrementBoth 0)
  else (program (state - 1)).map shiftInstruction

@[simp] theorem normalize_zero (program : KorecR2.Program) :
    normalize program 0 = none := by
  simp [normalize]

@[simp] theorem normalize_one (program : KorecR2.Program) :
    normalize program 1 = some (.incrementBoth 0) := by
  simp [normalize]

@[simp] theorem normalize_shifted_positive
    (program : KorecR2.Program) {state : Nat} (statePositive : 0 < state) :
    normalize program (shiftState state) =
      (program state).map shiftInstruction := by
  simp [normalize, shiftState, Nat.ne_of_gt statePositive]

/-- Rename a source configuration.  In particular, an old halt state is
mapped to the new halt gateway rather than to target state zero. -/
def shiftConfiguration
    (configuration : KorecR2.Configuration) : KorecR2.Configuration :=
  { configuration with state := shiftState configuration.state }

@[simp] theorem shiftConfiguration_initial (input : Nat) :
    shiftConfiguration (KorecR2.initialConfiguration input) =
      { state := 2, registerZero := 0, registerTwo := input } := by
  rfl

@[simp] theorem shiftConfiguration_halt (registerZero registerTwo : Nat) :
    shiftConfiguration (KorecR2.haltConfiguration registerZero registerTwo) =
      { state := 1, registerZero, registerTwo } := by
  rfl

/-- One source step is exactly one normalized step. -/
theorem normalize_step
    {program : KorecR2.Program}
    {source target : KorecR2.Configuration}
    (stepEq : KorecR2.step program source = some target) :
    KorecR2.step (normalize program) (shiftConfiguration source) =
      some (shiftConfiguration target) := by
  rcases source with ⟨state, registerZero, registerTwo⟩
  have statePositive : 0 < state := by
    by_cases stateZero : state = 0
    · simp [KorecR2.step, stateZero] at stepEq
    · omega
  cases lookup : program state with
  | none =>
      simp [KorecR2.step, lookup, Nat.ne_of_gt statePositive] at stepEq
  | some operation =>
      have normalizedLookup :
          normalize program (shiftState state) =
            some (shiftInstruction operation) := by
        simp [normalize_shifted_positive program statePositive, lookup]
      cases operation with
      | incrementBoth next =>
          simp [KorecR2.step, lookup, Nat.ne_of_gt statePositive] at stepEq
          subst target
          change normalize program (state + 1) =
            some (shiftInstruction (.incrementBoth next)) at normalizedLookup
          rw [show shiftConfiguration
              { state := state, registerZero, registerTwo } =
                { state := state + 1, registerZero, registerTwo } by rfl]
          simp [KorecR2.step, normalizedLookup, shiftInstruction,
            shiftConfiguration, shiftState]
      | decrement register next =>
          cases register <;> cases registerZero <;> cases registerTwo <;>
            simp [KorecR2.step, lookup, Nat.ne_of_gt statePositive] at stepEq
          all_goals
            subst target
            change normalize program (state + 1) =
              some (shiftInstruction (.decrement _ next)) at normalizedLookup
            simp [KorecR2.step, shiftConfiguration, normalizedLookup,
              shiftInstruction, shiftState]

/-- Normalize an exact finite source execution without changing its length. -/
theorem normalize_iterate
    {program : KorecR2.Program}
    {source finish : KorecR2.Configuration} {fuel : Nat}
    (sourceExecution :
      iterate (KorecR2.step program) fuel source = some finish) :
    iterate (KorecR2.step (normalize program)) fuel
        (shiftConfiguration source) =
      some (shiftConfiguration finish) := by
  induction fuel generalizing finish with
  | zero =>
      simp [iterate] at sourceExecution
      subst finish
      rfl
  | succ fuel inductionHypothesis =>
      simp only [iterate] at sourceExecution ⊢
      cases prefixEq : iterate (KorecR2.step program) fuel source with
      | none => simp [prefixEq] at sourceExecution
      | some middle =>
          have lastStep : KorecR2.step program middle = some finish := by
            simpa [prefixEq] using sourceExecution
          rw [inductionHypothesis prefixEq]
          exact normalize_step lastStep

/-- The halt gateway performs one final normalized step to target state zero. -/
theorem gateway_step (program : KorecR2.Program)
    (registerZero registerTwo : Nat) :
    KorecR2.step (normalize program)
        { state := 1, registerZero, registerTwo } =
      some
        { state := 0
          registerZero := registerZero + 1
          registerTwo := registerTwo + 1 } := by
  simp [KorecR2.step]

/-- A program total at positive states has a successful prefix of every
length whenever it does not halt from the given start. -/
theorem iterate_exists_of_not_haltsFrom
    (program : KorecR2.Program)
    (operationAt : ∀ state, 0 < state → ∃ operation,
      program state = some operation)
    (start : KorecR2.Configuration)
    (notHalts : ¬KorecR2.HaltsFrom program start) :
    ∀ fuel, ∃ finish,
      iterate (KorecR2.step program) fuel start = some finish := by
  intro fuel
  induction fuel with
  | zero => exact ⟨start, rfl⟩
  | succ fuel inductionHypothesis =>
      obtain ⟨middle, middleExecution⟩ := inductionHypothesis
      have statePositive : 0 < middle.state := by
        by_cases stateZero : middle.state = 0
        · have middleRun : Reaches (KorecR2.step program) start middle :=
            reaches_iff_exists_iterate.mpr ⟨fuel, middleExecution⟩
          have middleEq : middle =
              KorecR2.haltConfiguration middle.registerZero
                middle.registerTwo := by
            cases middle
            simp_all [KorecR2.haltConfiguration]
          exact (notHalts ⟨middle.registerZero, middle.registerTwo,
            middleEq ▸ middleRun⟩).elim
        · omega
      obtain ⟨operation, lookup⟩ := operationAt middle.state statePositive
      rcases middle with ⟨state, registerZero, registerTwo⟩
      change 0 < state at statePositive
      cases operation with
      | incrementBoth target =>
          refine ⟨
            { state := target
              registerZero := registerZero + 1
              registerTwo := registerTwo + 1 }, ?_⟩
          simp [iterate, middleExecution, KorecR2.step,
            Nat.ne_of_gt statePositive, lookup]
      | decrement register target =>
          cases register with
          | zero =>
              cases registerZero with
              | zero =>
                  refine ⟨
                    { state := target + 1
                      registerZero := 0
                      registerTwo }, ?_⟩
                  simp [iterate, middleExecution, KorecR2.step,
                    Nat.ne_of_gt statePositive, lookup]
              | succ value =>
                  refine ⟨
                    { state := target
                      registerZero := value
                      registerTwo }, ?_⟩
                  simp [iterate, middleExecution, KorecR2.step,
                    Nat.ne_of_gt statePositive, lookup]
          | one =>
              cases registerTwo with
              | zero =>
                  refine ⟨
                    { state := target + 1
                      registerZero
                      registerTwo := 0 }, ?_⟩
                  simp [iterate, middleExecution, KorecR2.step,
                    Nat.ne_of_gt statePositive, lookup]
              | succ value =>
                  refine ⟨
                    { state := target
                      registerZero
                      registerTwo := value }, ?_⟩
                  simp [iterate, middleExecution, KorecR2.step,
                    Nat.ne_of_gt statePositive, lookup]

/-- Adding the halt gateway preserves and reflects halting from every source
configuration, provided the source program is total away from halt. -/
theorem normalizedHaltsFrom_iff
    (program : KorecR2.Program)
    (operationAt : ∀ state, 0 < state → ∃ operation,
      program state = some operation)
    (start : KorecR2.Configuration) :
    KorecR2.HaltsFrom (normalize program) (shiftConfiguration start) ↔
      KorecR2.HaltsFrom program start := by
  constructor
  · intro normalizedHalts
    by_cases sourceHalts : KorecR2.HaltsFrom program start
    · exact sourceHalts
    · exfalso
      obtain ⟨registerZero, registerTwo, normalizedRun⟩ := normalizedHalts
      obtain ⟨haltFuel, haltExecution⟩ :=
        reaches_iff_exists_iterate.mp normalizedRun
      obtain ⟨sourceFinish, sourceExecution⟩ :=
        iterate_exists_of_not_haltsFrom program operationAt start
          sourceHalts (haltFuel + 1)
      have normalizedExecution := normalize_iterate sourceExecution
      have cannotPassHalt := successful_iterations_before_halt
        (step := KorecR2.step (normalize program))
        (haltEq := KorecR2.step_halt (normalize program)
          registerZero registerTwo)
        haltExecution normalizedExecution
      omega
  · rintro ⟨registerZero, registerTwo, sourceRun⟩
    obtain ⟨sourceFuel, sourceExecution⟩ :=
      reaches_iff_exists_iterate.mp sourceRun
    have shiftedExecution := normalize_iterate sourceExecution
    refine ⟨registerZero + 1, registerTwo + 1,
      reaches_iff_exists_iterate.mpr ⟨sourceFuel + 1, ?_⟩⟩
    rw [iterate_add, shiftedExecution]
    simpa [iterate, KorecR2.haltConfiguration, shiftConfiguration,
      shiftState] using
      gateway_step program registerZero registerTwo

/-- The normalized initial control state is two. -/
theorem normalizedHalts_iff
    (program : KorecR2.Program)
    (operationAt : ∀ state, 0 < state → ∃ operation,
      program state = some operation)
    (input : Nat) :
    KorecR2.HaltsFrom (normalize program)
        { state := 2, registerZero := 0, registerTwo := input } ↔
      KorecR2.Halts program input := by
  rw [KorecR2.halts_iff_haltsFrom_initial]
  simpa only [shiftConfiguration_initial] using
    normalizedHaltsFrom_iff program operationAt
      (KorecR2.initialConfiguration input)

/-- No normalized conditional decrement advertises target zero. -/
theorem normalize_decrement_target_positive
    {program : KorecR2.Program} {state : Nat}
    {register : Counter} {target : Nat}
    (lookup : normalize program state = some (.decrement register target)) :
    0 < target := by
  by_cases stateZero : state = 0
  · subst state
    simp at lookup
  by_cases stateOne : state = 1
  · subst state
    simp at lookup
  simp [normalize, stateZero, stateOne] at lookup
  cases sourceLookup : program (state - 1) with
  | none => simp [sourceLookup] at lookup
  | some operation =>
      simp [sourceLookup] at lookup
      cases operation <;> simp [shiftInstruction, shiftState] at lookup
      omega

/-- Every normalized instruction has a positive numerical operation code. -/
theorem normalize_code_positive
    {program : KorecR2.Program} {state : Nat}
    {operation : KorecR2.Instruction}
    (lookup : normalize program state = some operation) :
    0 < operation.code := by
  cases operation with
  | incrementBoth target =>
      simp [KorecR2.Instruction.code]
  | decrement register target =>
      have targetPositive := normalize_decrement_target_positive lookup
      cases register <;> simp [KorecR2.Instruction.code] <;> omega

/-- Normalization preserves totality away from state zero. -/
theorem normalize_operationAt
    {program : KorecR2.Program}
    (operationAt : ∀ state, 0 < state → ∃ operation,
      program state = some operation) :
    ∀ state, 0 < state → ∃ operation,
      normalize program state = some operation := by
  intro state statePositive
  by_cases stateOne : state = 1
  · subst state
    exact ⟨.incrementBoth 0, by simp⟩
  · have oldStatePositive : 0 < state - 1 := by omega
    obtain ⟨operation, lookup⟩ := operationAt (state - 1) oldStatePositive
    exact ⟨shiftInstruction operation, by
      simp [normalize, Nat.ne_of_gt statePositive, stateOne, lookup]⟩

/-- A finite forward control bound grows by exactly one under normalization. -/
theorem normalize_closedBelow
    {program : KorecR2.Program} {bound : Nat}
    (programClosed : KorecR2.ClosedBelow program bound) :
    KorecR2.ClosedBelow (normalize program) (bound + 1) := by
  intro source target sourceBounded stepEq
  rcases source with ⟨state, registerZero, registerTwo⟩
  change state < bound + 1 at sourceBounded
  by_cases stateZero : state = 0
  · subst state
    simp [KorecR2.step] at stepEq
  by_cases stateOne : state = 1
  · subst state
    simp [KorecR2.step] at stepEq
    subst target
    simp
  have oldStatePositive : 0 < state - 1 := by omega
  have oldStateBounded : state - 1 < bound := by omega
  cases oldLookup : program (state - 1) with
  | none =>
      simp [KorecR2.step, normalize, stateZero, stateOne, oldLookup] at stepEq
  | some operation =>
      have normalizedLookup : normalize program state =
          some (shiftInstruction operation) := by
        simp [normalize, stateZero, stateOne, oldLookup]
      let oldSource : KorecR2.Configuration :=
        { state := state - 1, registerZero, registerTwo }
      cases operation with
      | incrementBoth next =>
          simp [KorecR2.step, stateZero, normalizedLookup,
            shiftInstruction, shiftState] at stepEq
          subst target
          have oldStep : KorecR2.step program oldSource =
              some
                { state := next
                  registerZero := registerZero + 1
                  registerTwo := registerTwo + 1 } := by
            simp [oldSource, KorecR2.step, Nat.ne_of_gt oldStatePositive,
              oldLookup]
          have targetBound := programClosed oldStateBounded oldStep
          simp at targetBound ⊢
          omega
      | decrement register next =>
          have zeroBranchBound : next + 1 < bound := by
            have oldStep : KorecR2.step program
                { state := state - 1
                  registerZero := 0
                  registerTwo := 0 } =
              some
                { state := next + 1
                  registerZero := 0
                  registerTwo := 0 } := by
              cases register <;>
                simp [KorecR2.step, Nat.ne_of_gt oldStatePositive,
                  oldLookup]
            exact programClosed oldStateBounded oldStep
          have positiveBranchBound : next < bound := by omega
          cases register <;> cases registerZero <;> cases registerTwo <;>
            simp [KorecR2.step, stateZero, normalizedLookup,
              shiftInstruction, shiftState] at stepEq
          all_goals
            subst target
            simp
            omega

/-- A semantic finite-control bound forces the looked-up instruction's two
syntactic destinations below the same bound. -/
theorem targetsBelow_of_closedBelow_lookup
    {program : KorecR2.Program} {bound state : Nat}
    {operation : KorecR2.Instruction}
    (programClosed : KorecR2.ClosedBelow program bound)
    (statePositive : 0 < state) (stateBounded : state < bound)
    (lookup : program state = some operation) :
    operation.TargetsBelow bound := by
  cases operation with
  | incrementBoth target =>
      have stepEq : KorecR2.step program
          { state, registerZero := 0, registerTwo := 0 } =
        some { state := target, registerZero := 1, registerTwo := 1 } := by
        simp [KorecR2.step, Nat.ne_of_gt statePositive, lookup]
      exact programClosed stateBounded stepEq
  | decrement register target =>
      have stepEq : KorecR2.step program
          { state, registerZero := 0, registerTwo := 0 } =
        some { state := target + 1, registerZero := 0, registerTwo := 0 } := by
        cases register <;>
          simp [KorecR2.step, Nat.ne_of_gt statePositive, lookup]
      simpa [KorecR2.Instruction.TargetsBelow] using
        programClosed stateBounded stepEq

end Mortality.SourceMachine.R2PositiveTargets
