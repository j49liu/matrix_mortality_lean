import Mortality.SourceMachine.FourCounterToTwoCounter

/-!
# A finite-control initializer for four-counter programs

The fixed universal counter program begins in one of finitely many logical
control states, selected by the first input symbol.  This module removes that
input-dependent control state.  It stores the finite tag in the temporary
register, counts it down from state zero, and then enters a relocated copy of
the source program.  Thus the compiled two-counter program always starts in
state one, under the standard input convention.
-/

namespace Mortality.SourceMachine.FourCounterInitializer

open Mortality.SourceMachine
open Mortality.SourceMachine.FourCounter
open Mortality.SourceMachine.FourCounterEncoding
open Mortality.SourceMachine.FourCounterToTwoCounter
open Mortality.SourceMachine.TotalTwoCounter
open Mortality.SourceMachine.U20Compilation

def sourceOffset (tagBound : Nat) : Nat := tagBound + 1

def shiftInstruction (offset : Nat) :
    FourCounter.Instruction → FourCounter.Instruction
  | .increment register target => .increment register (offset + target)
  | .decrement register zeroTarget positiveTarget =>
      .decrement register (offset + zeroTarget) (offset + positiveTarget)

def shiftConfiguration (offset : Nat)
    (configuration : FourCounter.Configuration) :
    FourCounter.Configuration :=
  { configuration with state := offset + configuration.state }

def withTemp (registers : FourCounter.Registers) (value : Nat) :
    FourCounter.Registers :=
  { registers with temp := value }

@[simp] theorem withTemp_temp (registers : FourCounter.Registers) (value : Nat) :
    (withTemp registers value).temp = value := rfl

@[simp] theorem withTemp_get_temp
    (registers : FourCounter.Registers) (value : Nat) :
    (withTemp registers value).get .temp = value := rfl

@[simp] theorem withTemp_decrement_succ
    (registers : FourCounter.Registers) (value : Nat) :
    (withTemp registers (value + 1)).decrement .temp =
      withTemp registers value := by
  cases registers
  simp [withTemp, FourCounter.Registers.decrement,
    FourCounter.Registers.set, FourCounter.Registers.get]

/-- States below `sourceOffset tagBound` form the initializer.  Every later
state belongs to the relocated source program. -/
def initializedProgram (tagBound : Nat) (target : Nat → Nat)
    (program : FourCounter.Program) : FourCounter.Program :=
  fun state =>
    if state < sourceOffset tagBound then
      some (.decrement .temp
        (sourceOffset tagBound + target state) (state + 1))
    else
      (program (state - sourceOffset tagBound)).map
        (shiftInstruction (sourceOffset tagBound))

@[simp] theorem initializedProgram_prefix
    (tagBound : Nat) (target : Nat → Nat) (program : FourCounter.Program)
    {state : Nat} (inPrefix : state < sourceOffset tagBound) :
    initializedProgram tagBound target program state =
      some (.decrement .temp
        (sourceOffset tagBound + target state) (state + 1)) := by
  simp [initializedProgram, inPrefix]

@[simp] theorem initializedProgram_source
    (tagBound : Nat) (target : Nat → Nat) (program : FourCounter.Program)
    (state : Nat) :
    initializedProgram tagBound target program
        (sourceOffset tagBound + state) =
      (program state).map (shiftInstruction (sourceOffset tagBound)) := by
  have outside : ¬sourceOffset tagBound + state < sourceOffset tagBound := by
    omega
  simp [initializedProgram, outside]

theorem execute_shiftInstruction
    (offset : Nat) (instruction : FourCounter.Instruction)
    (registers : FourCounter.Registers) :
    (match shiftInstruction offset instruction with
      | .increment register target =>
          some (FourCounter.Configuration.mk target
            (registers.increment register))
      | .decrement register zeroTarget positiveTarget =>
          if registers.get register = 0 then
            some (FourCounter.Configuration.mk zeroTarget registers)
          else
            some (FourCounter.Configuration.mk positiveTarget
              (registers.decrement register))) =
    (match instruction with
      | .increment register target =>
          some (shiftConfiguration offset
            (FourCounter.Configuration.mk target
              (registers.increment register)))
      | .decrement register zeroTarget positiveTarget =>
          if registers.get register = 0 then
            some (shiftConfiguration offset
              (FourCounter.Configuration.mk zeroTarget registers))
          else
            some (shiftConfiguration offset
              (FourCounter.Configuration.mk positiveTarget
                (registers.decrement register)))) := by
  cases instruction <;> rfl

/-- Once the initializer has entered the relocated source program, every
step commutes with relocation, including a missing terminal instruction. -/
theorem step_shiftConfiguration
    (tagBound : Nat) (target : Nat → Nat) (program : FourCounter.Program)
    (configuration : FourCounter.Configuration) :
    FourCounter.step (initializedProgram tagBound target program)
        (shiftConfiguration (sourceOffset tagBound) configuration) =
      (FourCounter.step program configuration).map
        (shiftConfiguration (sourceOffset tagBound)) := by
  rcases configuration with ⟨state, registers⟩
  simp only [FourCounter.step, shiftConfiguration,
    initializedProgram_source]
  cases lookup : program state with
  | none => simp
  | some instruction =>
      cases instruction with
      | increment register next =>
          simp [shiftInstruction, shiftConfiguration]
      | decrement register zeroTarget positiveTarget =>
          by_cases zero : registers.get register = 0 <;>
            simp [shiftInstruction, shiftConfiguration, zero]

theorem iterate_shiftConfiguration
    (tagBound : Nat) (target : Nat → Nat) (program : FourCounter.Program)
    (fuel : Nat) (configuration : FourCounter.Configuration) :
    iterate (FourCounter.step (initializedProgram tagBound target program)) fuel
        (shiftConfiguration (sourceOffset tagBound) configuration) =
      (iterate (FourCounter.step program) fuel configuration).map
        (shiftConfiguration (sourceOffset tagBound)) := by
  induction fuel with
  | zero => rfl
  | succ fuel inductionHypothesis =>
      simp only [iterate, inductionHypothesis]
      cases execution : iterate (FourCounter.step program) fuel configuration with
      | none => rfl
      | some middle => simp [step_shiftConfiguration]

theorem shiftedHaltsFrom_iff
    (tagBound : Nat) (target : Nat → Nat) (program : FourCounter.Program)
    (start : FourCounter.Configuration) :
    FourCounter.HaltsFrom (initializedProgram tagBound target program)
        (shiftConfiguration (sourceOffset tagBound) start) ↔
      FourCounter.HaltsFrom program start := by
  constructor
  · rintro ⟨finish, shiftedRun, shiftedTerminal⟩
    obtain ⟨fuel, shiftedExecution⟩ :=
      reaches_iff_exists_iterate.mp shiftedRun
    have commuting := iterate_shiftConfiguration tagBound target program fuel start
    cases sourceExecution : iterate (FourCounter.step program) fuel start with
    | none =>
        rw [shiftedExecution, sourceExecution] at commuting
        simp at commuting
    | some sourceFinish =>
        rw [sourceExecution] at commuting
        have finishEq : finish =
            shiftConfiguration (sourceOffset tagBound) sourceFinish := by
          exact Option.some.inj (shiftedExecution.symm.trans commuting)
        subst finish
        have stepCommuting :=
          step_shiftConfiguration tagBound target program sourceFinish
        rw [shiftedTerminal] at stepCommuting
        cases sourceStep : FourCounter.step program sourceFinish with
        | none =>
            exact ⟨sourceFinish,
              reaches_iff_exists_iterate.mpr ⟨fuel, sourceExecution⟩,
              sourceStep⟩
        | some next => simp [sourceStep] at stepCommuting
  · rintro ⟨finish, sourceRun, sourceTerminal⟩
    obtain ⟨fuel, sourceExecution⟩ :=
      reaches_iff_exists_iterate.mp sourceRun
    refine ⟨shiftConfiguration (sourceOffset tagBound) finish,
      reaches_iff_exists_iterate.mpr ⟨fuel, ?_⟩, ?_⟩
    · rw [iterate_shiftConfiguration, sourceExecution]
      rfl
    · change FourCounter.step
        (initializedProgram tagBound target program)
        (shiftConfiguration (sourceOffset tagBound) finish) = none
      change FourCounter.step program finish = none at sourceTerminal
      rw [step_shiftConfiguration, sourceTerminal]
      rfl

/-- Starting at initializer state `state` with `remaining` in the temporary
register reaches the relocated source state selected by the original tag
`state + remaining`. -/
theorem countdown_reaches
    (tagBound : Nat) (target : Nat → Nat) (program : FourCounter.Program)
    (registers : FourCounter.Registers) (state remaining : Nat)
    (tagInRange : state + remaining < tagBound) :
    Reaches (FourCounter.step (initializedProgram tagBound target program))
      ⟨state, withTemp registers remaining⟩
      (shiftConfiguration (sourceOffset tagBound)
        ⟨target (state + remaining), withTemp registers 0⟩) := by
  induction remaining generalizing state with
  | zero =>
      have inPrefix : state < sourceOffset tagBound := by
        simp [sourceOffset]
        omega
      apply Reaches.single
      rw [FourCounter.step_decrement_zero
        (initializedProgram_prefix tagBound target program inPrefix)]
      · rfl
      · rfl
  | succ remaining inductionHypothesis =>
      have inPrefix : state < sourceOffset tagBound := by
        simp [sourceOffset]
        omega
      have positive : 0 < (withTemp registers (remaining + 1)).get .temp := by
        simp
      have firstStep :
          FourCounter.step (initializedProgram tagBound target program)
              ⟨state, withTemp registers (remaining + 1)⟩ =
            some ⟨state + 1, withTemp registers remaining⟩ := by
        rw [FourCounter.step_decrement_positive
          (initializedProgram_prefix tagBound target program inPrefix) positive]
        simp
      have suffix := inductionHypothesis (state := state + 1) (by omega)
      exact (Reaches.single firstStep).trans (by
        simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using suffix)

theorem initializer_reaches
    (tagBound : Nat) (target : Nat → Nat) (program : FourCounter.Program)
    (registers : FourCounter.Registers) (tag : Nat)
    (tagInRange : tag < tagBound) :
    Reaches (FourCounter.step (initializedProgram tagBound target program))
      ⟨0, withTemp registers tag⟩
      (shiftConfiguration (sourceOffset tagBound)
        ⟨target tag, withTemp registers 0⟩) := by
  simpa using countdown_reaches tagBound target program registers 0 tag
    (by simpa using tagInRange)

/-- For a deterministic partial step function, a known successful prefix can
be removed from a later halting computation. -/
theorem haltsFrom_iff_after_prefix
    (program : FourCounter.Program)
    {start middle : FourCounter.Configuration}
    (prefixRun : Reaches (FourCounter.step program) start middle) :
    FourCounter.HaltsFrom program start ↔
      FourCounter.HaltsFrom program middle := by
  constructor
  · rintro ⟨finish, run, terminal⟩
    obtain ⟨wholeFuel, wholeExecution⟩ :=
      reaches_iff_exists_iterate.mp run
    obtain ⟨prefixFuel, prefixExecution⟩ :=
      reaches_iff_exists_iterate.mp prefixRun
    have prefixBound : prefixFuel ≤ wholeFuel :=
      successful_iterations_before_halt terminal wholeExecution prefixExecution
    have suffixExecution := strip_iteration_prefix prefixBound wholeExecution
      prefixExecution
    exact ⟨finish, reaches_iff_exists_iterate.mpr
      ⟨wholeFuel - prefixFuel, suffixExecution⟩, terminal⟩
  · rintro ⟨finish, suffix, terminal⟩
    exact ⟨finish, prefixRun.trans suffix, terminal⟩

/-- The finite initializer makes an input-dependent source control state
compatible with a fixed state-zero four-counter start. -/
theorem initializedHaltsFrom_iff
    (tagBound : Nat) (target : Nat → Nat) (program : FourCounter.Program)
    (registers : FourCounter.Registers) (tag : Nat)
    (tagInRange : tag < tagBound) :
    FourCounter.HaltsFrom (initializedProgram tagBound target program)
        ⟨0, withTemp registers tag⟩ ↔
      FourCounter.HaltsFrom program
        ⟨target tag, withTemp registers 0⟩ := by
  rw [haltsFrom_iff_after_prefix _
    (initializer_reaches tagBound target program registers tag tagInRange)]
  exact shiftedHaltsFrom_iff tagBound target program
    ⟨target tag, withTemp registers 0⟩

@[simp] theorem encodeConfiguration_initial
    (registers : FourCounter.Registers) (tag : Nat) :
    encodeConfiguration
        ({ state := 0, registers := withTemp registers tag } :
          FourCounter.Configuration) =
      TotalTwoCounter.initialConfiguration (encode (withTemp registers tag)) := by
  rfl

/-- End-to-end interface of the initializer and the prime-exponent compiler.
The resulting ordinary two-counter machine uses its standard fixed control
state one. -/
theorem compiledInitializedHalts_iff
    (tagBound : Nat) (target : Nat → Nat) (program : FourCounter.Program)
    (registers : FourCounter.Registers) (tag : Nat)
    (tagInRange : tag < tagBound) :
    TotalTwoCounter.Halts
        (compile (initializedProgram tagBound target program))
        (encode (withTemp registers tag)) ↔
      FourCounter.HaltsFrom program
        ⟨target tag, withTemp registers 0⟩ := by
  change TargetHaltsFrom (compile (initializedProgram tagBound target program))
      (encodeConfiguration
        ({ state := 0, registers := withTemp registers tag } :
          FourCounter.Configuration)) ↔ _
  rw [targetHalts_iff_sourceHalts, initializedHaltsFrom_iff _ _ _ _ _ tagInRange]

end Mortality.SourceMachine.FourCounterInitializer
