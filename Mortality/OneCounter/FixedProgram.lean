import Mortality.OneCounter.FixedSimulation

/-!
# Cleanup and reversal of the fixed one-counter simulation

The forward relation first simulates the quotient two-counter machine.
At the source halt state it may instead decrement the encoded counter to
zero.  Reversing the complete relation gives the exact reachability query
used by the matrix compiler.
-/

namespace Mortality.OneCounter

/-- The forward cleanup loop decrements a positive counter at the source
halt state. -/
def CleanupStep : Configuration Nat → Configuration Nat → Prop :=
  fun before after =>
    before.state = 278 ∧ after.state = 278 ∧
      before.counter = after.counter + 1

/-- The forward simulation relation, including its terminal cleanup loop. -/
def ForwardStep : Configuration Nat → Configuration Nat → Prop :=
  fun before after =>
    ForwardSimulationStep before after ∨ CleanupStep before after

/-- The abstract edge relation of the final one-counter program. -/
def FixedProgramStep : Configuration Nat → Configuration Nat → Prop :=
  Reaches.converse ForwardStep

/-- The exact initial configuration supplied by a source input. -/
def inputConfiguration (input : Nat) : Configuration Nat :=
  { state := 1, counter := 2 ^ input - 1 }

/-- The fixed endpoint at the source halt state. -/
def zeroHaltConfiguration : Configuration Nat :=
  { state := 278, counter := 0 }

@[simp] theorem encodeSource_initial (input : Nat) :
    encodeSource (SourceMachine.initialConfiguration input) 0 =
      inputConfiguration input := by
  simp [encodeSource, SourceMachine.initialConfiguration, inputConfiguration,
    primeCode_initial]

@[simp] theorem encodeSource_halt (counterZero counterOne time : Nat) :
    encodeSource (SourceMachine.haltConfiguration counterZero counterOne) time =
      { state := 278, counter := primeCode counterZero counterOne time } := by
  rfl

/-- A simulation edge cannot leave the source halt state. -/
theorem not_forwardSimulationStep_of_state_eq_halt
    {before after : Configuration Nat} (stateEq : before.state = 278) :
    ¬ ForwardSimulationStep before after := by
  cases before with
  | mk state counter =>
      change state = 278 at stateEq
      subst state
      simp [ForwardSimulationStep]

/-- Cleanup alone takes every counter at the halt state to zero. -/
theorem cleanup_reaches_zero (counter : Nat) :
    Reaches ForwardStep { state := 278, counter := counter }
      zeroHaltConfiguration := by
  induction counter with
  | zero => exact .refl _
  | succ counter inductionHypothesis =>
      have first : ForwardStep
          { state := 278, counter := counter + 1 }
          { state := 278, counter := counter } := by
        right
        simp [CleanupStep]
      exact (Reaches.single first).trans inductionHypothesis

/-- Every run from an encoded source configuration is either still in the
simulation phase or has already witnessed source halting and entered cleanup. -/
theorem forwardRun_classification {source : SourceConfiguration}
    {after : Configuration Nat} (time : Nat)
    (run : Reaches ForwardStep (encodeSource source time) after) :
    (∃ sourceAfter nextTime,
      SourceMachine.Reaches SourceMachine.quotientStep source sourceAfter ∧
      after = encodeSource sourceAfter nextTime) ∨
    (∃ counterZero counterOne,
      SourceMachine.Reaches SourceMachine.quotientStep source
        (SourceMachine.haltConfiguration counterZero counterOne) ∧
      after.state = 278) := by
  induction run with
  | refl => exact Or.inl ⟨source, time, .refl _, rfl⟩
  | tail hRun hStep inductionHypothesis =>
      rcases inductionHypothesis with simulationPhase | cleanupPhase
      · obtain ⟨sourceMiddle, middleTime, sourceRun, middleEq⟩ :=
          simulationPhase
        rcases hStep with simulationStep | cleanupStep
        · rw [middleEq] at simulationStep
          obtain ⟨sourceAfter, nextTime, sourceStep, afterEq⟩ :=
            forwardSimulation_to_quotientStep middleTime simulationStep
          exact Or.inl
            ⟨sourceAfter, nextTime, .tail sourceRun sourceStep, afterEq⟩
        · rw [middleEq] at cleanupStep
          have sourceStateEq : sourceMiddle.state = 278 := by
            simpa [CleanupStep, encodeSource] using cleanupStep.1
          have sourceMiddleEq : sourceMiddle =
              SourceMachine.haltConfiguration sourceMiddle.counterZero
                sourceMiddle.counterOne := by
            cases sourceMiddle
            simp [SourceMachine.haltConfiguration] at sourceStateEq ⊢
            exact sourceStateEq
          rw [sourceMiddleEq] at sourceRun
          exact Or.inr
            ⟨sourceMiddle.counterZero, sourceMiddle.counterOne, sourceRun,
              cleanupStep.2.1⟩
      · obtain ⟨counterZero, counterOne, sourceRun, middleStateEq⟩ :=
          cleanupPhase
        rcases hStep with simulationStep | cleanupStep
        · exact False.elim
            (not_forwardSimulationStep_of_state_eq_halt middleStateEq
              simulationStep)
        · exact Or.inr
            ⟨counterZero, counterOne, sourceRun, cleanupStep.2.1⟩

/-- Forward reachability to the zero halt configuration is equivalent to
halting of the quotient source machine. -/
theorem forward_reaches_zero_halt_iff (input : Nat) :
    Reaches ForwardStep (inputConfiguration input) zeroHaltConfiguration ↔
      SourceMachine.QuotientHalts input := by
  constructor
  · intro run
    have encodedRun : Reaches ForwardStep
        (encodeSource (SourceMachine.initialConfiguration input) 0)
        zeroHaltConfiguration := by
      simpa using run
    rcases forwardRun_classification 0 encodedRun with
      simulationPhase | cleanupPhase
    · obtain ⟨sourceAfter, nextTime, sourceRun, finishEq⟩ := simulationPhase
      have stateEq : sourceAfter.state = 278 := by
        simpa [zeroHaltConfiguration, encodeSource] using
          congrArg Configuration.state finishEq.symm
      have sourceAfterEq : sourceAfter =
          SourceMachine.haltConfiguration sourceAfter.counterZero
            sourceAfter.counterOne := by
        cases sourceAfter
        simp [SourceMachine.haltConfiguration] at stateEq ⊢
        exact stateEq
      refine ⟨sourceAfter.counterZero, sourceAfter.counterOne, ?_⟩
      rw [sourceAfterEq] at sourceRun
      exact sourceRun
    · obtain ⟨counterZero, counterOne, sourceRun, _⟩ := cleanupPhase
      exact ⟨counterZero, counterOne, sourceRun⟩
  · rintro ⟨counterZero, counterOne, sourceRun⟩
    obtain ⟨nextTime, simulationRun⟩ :=
      quotientRun_to_forwardSimulation sourceRun 0
    have enlargedRun : Reaches ForwardStep
        (encodeSource (SourceMachine.initialConfiguration input) 0)
        (encodeSource
          (SourceMachine.haltConfiguration counterZero counterOne) nextTime) :=
      simulationRun.mono (fun step => Or.inl step)
    have cleanupRun :=
      cleanup_reaches_zero (primeCode counterZero counterOne nextTime)
    have completeRun := enlargedRun.trans (by simpa using cleanupRun)
    simpa using completeRun

/-- Reversing every edge gives the exact query used in the paper. -/
theorem fixedProgram_reaches_input_iff (input : Nat) :
    Reaches FixedProgramStep zeroHaltConfiguration (inputConfiguration input) ↔
      SourceMachine.QuotientHalts input := by
  rw [FixedProgramStep, Reaches.reverse_iff]
  exact forward_reaches_zero_halt_iff input

/-- The fixed program has the same variable-input halting behavior as U2. -/
theorem fixedProgram_reaches_input_iff_u2Halts (input : Nat) :
    Reaches FixedProgramStep zeroHaltConfiguration (inputConfiguration input) ↔
      SourceMachine.U2Halts input := by
  rw [fixedProgram_reaches_input_iff,
    SourceMachine.quotientHalts_iff_u2Halts]

end Mortality.OneCounter
