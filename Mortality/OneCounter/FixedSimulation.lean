import Mortality.OneCounter.PrimeEncoding
import Mortality.SourceMachine.U2Semantics

/-!
# One-counter simulation of the fixed quotient machine

This file defines the forward program `Q` from the proof of Theorem 3.4.
Its increment edges use the reverse relations of `D2` and `D3`; its
positive decrement edges use the reverse relations of `C2` and `C3`;
and its zero branches use the two congruence tests.

The first theorem proves completeness of one simulated source step.
The converse, which classifies every enabled edge on an encoded input,
is kept separate because it is the invariant needed for exact
reachability rather than just for existence of a simulation.
-/

namespace Mortality.OneCounter

abbrev SourceConfiguration := SourceMachine.Configuration

/-- Encode a quotient-source configuration and its auxiliary clock. -/
def encodeSource (configuration : SourceConfiguration) (time : Nat) :
    Configuration Nat :=
  { state := configuration.state
    counter := primeCode configuration.counterZero configuration.counterOne time }

/-- One edge of the forward one-counter simulation `Q`, before cleanup. -/
def ForwardSimulationStep : Configuration Nat → Configuration Nat → Prop :=
  fun before after =>
    match SourceMachine.quotientAt before.state with
    | none => False
    | some (.inc .zero target) =>
        after.state = target ∧
          Instruction.evaluate .divideTwoOdd after.counter = some before.counter
    | some (.inc .one target) =>
        after.state = target ∧
          Instruction.evaluate .divideThreeTwo after.counter = some before.counter
    | some (.dec .zero positive zeroDest) =>
        (after.state = positive ∧
          Instruction.evaluate .contractTwo after.counter = some before.counter) ∨
        (after.state = zeroDest ∧
          Instruction.evaluate (.congruenceTest 2 [0]) before.counter =
            some after.counter)
    | some (.dec .one positive zeroDest) =>
        (after.state = positive ∧
          Instruction.evaluate .contractThree after.counter = some before.counter) ∨
        (after.state = zeroDest ∧
          Instruction.evaluate (.congruenceTest 3 [0, 1]) before.counter =
            some after.counter)
    | some .halt => False

/-- Every quotient-machine step has its prescribed one-counter simulation edge. -/
theorem quotientStep_to_forwardSimulation {before after : SourceConfiguration}
    (sourceStep : SourceMachine.quotientStep before = some after)
    (time : Nat) :
    ∃ nextTime,
      ForwardSimulationStep (encodeSource before time) (encodeSource after nextTime) := by
  unfold SourceMachine.quotientStep at sourceStep
  cases lookup : SourceMachine.quotientAt before.state with
  | none => simp [lookup] at sourceStep
  | some instruction =>
      simp [lookup] at sourceStep
      cases instruction with
      | inc counter target =>
          cases before with
          | mk state counterZero counterOne =>
              cases counter
              · simp [SourceMachine.execute, SourceMachine.Configuration.readCounter,
                  SourceMachine.Configuration.setCounter,
                  SourceMachine.Configuration.setState] at sourceStep
                subst after
                refine ⟨time, ?_⟩
                simp [ForwardSimulationStep, encodeSource, lookup,
                  divideTwo_primeCode]
              · simp [SourceMachine.execute, SourceMachine.Configuration.readCounter,
                  SourceMachine.Configuration.setCounter,
                  SourceMachine.Configuration.setState] at sourceStep
                subst after
                refine ⟨time, ?_⟩
                simp [ForwardSimulationStep, encodeSource, lookup,
                  divideThree_primeCode]
      | dec counter positive zeroDest =>
          cases before with
          | mk state counterZero counterOne =>
              cases counter
              · cases counterZero with
                | zero =>
                    simp [SourceMachine.execute,
                      SourceMachine.Configuration.readCounter,
                      SourceMachine.Configuration.setState] at sourceStep
                    subst after
                    refine ⟨time, ?_⟩
                    simp [ForwardSimulationStep, encodeSource, lookup,
                      Instruction.evaluate, primeCode_zero_mod_two]
                | succ counterZero =>
                    simp [SourceMachine.execute,
                      SourceMachine.Configuration.readCounter,
                      SourceMachine.Configuration.setCounter,
                      SourceMachine.Configuration.setState] at sourceStep
                    subst after
                    refine ⟨time + 1, ?_⟩
                    simp [ForwardSimulationStep, encodeSource, lookup,
                      contractTwo_primeCode]
              · cases counterOne with
                | zero =>
                    simp [SourceMachine.execute,
                      SourceMachine.Configuration.readCounter,
                      SourceMachine.Configuration.setState] at sourceStep
                    subst after
                    refine ⟨time, ?_⟩
                    rcases primeCode_zero_one_mod_three counterZero time with
                      residue | residue <;>
                      simp [ForwardSimulationStep, encodeSource, lookup,
                        Instruction.evaluate, residue]
                | succ counterOne =>
                    simp [SourceMachine.execute,
                      SourceMachine.Configuration.readCounter,
                      SourceMachine.Configuration.setCounter,
                      SourceMachine.Configuration.setState] at sourceStep
                    subst after
                    refine ⟨time + 1, ?_⟩
                    simp [ForwardSimulationStep, encodeSource, lookup,
                      contractThree_primeCode]
      | halt => simp [SourceMachine.execute] at sourceStep

/-- Every simulation edge on an encoded input is the prescribed source step. -/
theorem forwardSimulation_to_quotientStep {before : SourceConfiguration}
    {after : Configuration Nat} (time : Nat)
    (simulationStep : ForwardSimulationStep (encodeSource before time) after) :
    ∃ sourceAfter nextTime,
      SourceMachine.quotientStep before = some sourceAfter ∧
      after = encodeSource sourceAfter nextTime := by
  cases before with
  | mk state counterZero counterOne =>
      cases after with
      | mk afterState afterCounter =>
          unfold ForwardSimulationStep at simulationStep
          simp only [encodeSource] at simulationStep
          cases lookup : SourceMachine.quotientAt state with
          | none => simp [lookup] at simulationStep
          | some instruction =>
              simp only [lookup] at simulationStep
              cases instruction with
              | inc counter target =>
                  cases counter
                  · rcases simulationStep with ⟨stateEq, evaluation⟩
                    have counterEq :=
                      Instruction.evaluate_divideTwoOdd_iff.mp evaluation
                    refine ⟨{ state := target, counterZero := counterZero + 1, counterOne := counterOne }, time, ?_, ?_⟩
                    · simp [SourceMachine.quotientStep, lookup,
                        SourceMachine.execute, SourceMachine.Configuration.readCounter,
                        SourceMachine.Configuration.setCounter,
                        SourceMachine.Configuration.setState]
                    · cases stateEq
                      simp [encodeSource, counterEq, primeCode_succ_zero]
                  · rcases simulationStep with ⟨stateEq, evaluation⟩
                    have counterEq :=
                      Instruction.evaluate_divideThreeTwo_iff.mp evaluation
                    refine ⟨{ state := target, counterZero := counterZero, counterOne := counterOne + 1 }, time, ?_, ?_⟩
                    · simp [SourceMachine.quotientStep, lookup,
                        SourceMachine.execute, SourceMachine.Configuration.readCounter,
                        SourceMachine.Configuration.setCounter,
                        SourceMachine.Configuration.setState]
                    · cases stateEq
                      simp [encodeSource, counterEq, primeCode_succ_one]
              | dec counter positive zeroDest =>
                  cases counter
                  · rcases simulationStep with positiveStep | zeroStep
                    · rcases positiveStep with ⟨stateEq, evaluation⟩
                      rcases Instruction.evaluate_contractTwo_iff.mp evaluation with
                        ⟨a, inputEq, outputEq⟩
                      cases counterZero with
                      | zero =>
                          have residueEq := congrArg (fun n => n % 2) outputEq
                          simp [primeCode_zero_mod_two] at residueEq
                      | succ counterZero =>
                          have codeEq := primeCode_succ_zero counterZero counterOne time
                          have aEq : a = primeCode counterZero counterOne time := by
                            omega
                          subst a
                          refine ⟨{ state := positive, counterZero := counterZero, counterOne := counterOne }, time + 1, ?_, ?_⟩
                          · simp [SourceMachine.quotientStep, lookup,
                              SourceMachine.execute,
                              SourceMachine.Configuration.readCounter,
                              SourceMachine.Configuration.setCounter,
                              SourceMachine.Configuration.setState]
                          · cases stateEq
                            simp [encodeSource, inputEq, primeCode_succ_time]
                    · rcases zeroStep with ⟨stateEq, evaluation⟩
                      have counterEq :=
                        Instruction.evaluate_congruenceTest_eq evaluation
                      have enabled :
                          Instruction.evaluate (.congruenceTest 2 [0])
                            (primeCode counterZero counterOne time) =
                              some (primeCode counterZero counterOne time) := by
                        simpa [counterEq] using evaluation
                      have zeroCounter :=
                        (testTwo_primeCode_iff counterZero counterOne time).mp enabled
                      subst counterZero
                      refine ⟨{ state := zeroDest, counterZero := 0, counterOne := counterOne }, time, ?_, ?_⟩
                      · simp [SourceMachine.quotientStep, lookup,
                          SourceMachine.execute,
                          SourceMachine.Configuration.readCounter,
                          SourceMachine.Configuration.setState]
                      · cases stateEq
                        simp [encodeSource, counterEq]
                  · rcases simulationStep with positiveStep | zeroStep
                    · rcases positiveStep with ⟨stateEq, evaluation⟩
                      rcases Instruction.evaluate_contractThree_iff.mp evaluation with
                        ⟨a, inputEq, outputEq⟩
                      cases counterOne with
                      | zero =>
                          have residueEq := congrArg (fun n => n % 3) outputEq
                          rcases primeCode_zero_one_mod_three counterZero time with
                            residue | residue <;> simp [residue] at residueEq
                      | succ counterOne =>
                          have codeEq := primeCode_succ_one counterZero counterOne time
                          have aEq : a = primeCode counterZero counterOne time := by
                            omega
                          subst a
                          refine ⟨{ state := positive, counterZero := counterZero, counterOne := counterOne }, time + 1, ?_, ?_⟩
                          · simp [SourceMachine.quotientStep, lookup,
                              SourceMachine.execute,
                              SourceMachine.Configuration.readCounter,
                              SourceMachine.Configuration.setCounter,
                              SourceMachine.Configuration.setState]
                          · cases stateEq
                            simp [encodeSource, inputEq, primeCode_succ_time]
                    · rcases zeroStep with ⟨stateEq, evaluation⟩
                      have counterEq :=
                        Instruction.evaluate_congruenceTest_eq evaluation
                      have enabled :
                          Instruction.evaluate (.congruenceTest 3 [0, 1])
                            (primeCode counterZero counterOne time) =
                              some (primeCode counterZero counterOne time) := by
                        simpa [counterEq] using evaluation
                      have zeroCounter :=
                        (testThree_primeCode_iff counterZero counterOne time).mp enabled
                      subst counterOne
                      refine ⟨{ state := zeroDest, counterZero := counterZero, counterOne := 0 }, time, ?_, ?_⟩
                      · simp [SourceMachine.quotientStep, lookup,
                          SourceMachine.execute,
                          SourceMachine.Configuration.readCounter,
                          SourceMachine.Configuration.setState]
                      · cases stateEq
                        simp [encodeSource, counterEq]
              | halt => contradiction

/-- Every quotient-machine run has a forward one-counter simulation run. -/
theorem quotientRun_to_forwardSimulation {before after : SourceConfiguration}
    (sourceRun : SourceMachine.Reaches SourceMachine.quotientStep before after)
    (time : Nat) :
    ∃ nextTime,
      Reaches ForwardSimulationStep (encodeSource before time)
        (encodeSource after nextTime) := by
  induction sourceRun generalizing time with
  | refl => exact ⟨time, .refl _⟩
  | tail prefixRun sourceStep inductionHypothesis =>
      obtain ⟨middleTime, simulationRun⟩ := inductionHypothesis time
      obtain ⟨nextTime, simulationStep⟩ :=
        quotientStep_to_forwardSimulation sourceStep middleTime
      exact ⟨nextTime, .tail simulationRun simulationStep⟩

/-- A forward simulation run starting at an encoding never leaves the
encoded configurations.  It therefore determines a quotient-machine run. -/
theorem forwardSimulationRun_to_quotientRun {before : SourceConfiguration}
    {after : Configuration Nat} (time : Nat)
    (simulationRun :
      Reaches ForwardSimulationStep (encodeSource before time) after) :
    ∃ sourceAfter nextTime,
      SourceMachine.Reaches SourceMachine.quotientStep before sourceAfter ∧
      after = encodeSource sourceAfter nextTime := by
  induction simulationRun with
  | refl => exact ⟨before, time, .refl _, rfl⟩
  | tail prefixRun simulationStep inductionHypothesis =>
      obtain ⟨sourceMiddle, middleTime, sourceRun, middleEq⟩ :=
        inductionHypothesis
      rw [middleEq] at simulationStep
      obtain ⟨sourceAfter, nextTime, sourceStep, afterEq⟩ :=
        forwardSimulation_to_quotientStep middleTime simulationStep
      exact ⟨sourceAfter, nextTime, .tail sourceRun sourceStep, afterEq⟩

/-- Exact correspondence for reaching a control state.  The source
counters and the auxiliary clock are existential on both sides. -/
theorem forwardSimulationReachesState_iff {before : SourceConfiguration}
    (time targetState : Nat) :
    (∃ afterCounter,
      Reaches ForwardSimulationStep (encodeSource before time)
        { state := targetState, counter := afterCounter }) ↔
      ∃ sourceAfter,
        SourceMachine.Reaches SourceMachine.quotientStep before sourceAfter ∧
        sourceAfter.state = targetState := by
  constructor
  · rintro ⟨afterCounter, simulationRun⟩
    obtain ⟨sourceAfter, finalTime, sourceRun, encodingEq⟩ :=
      forwardSimulationRun_to_quotientRun time simulationRun
    refine ⟨sourceAfter, sourceRun, ?_⟩
    simpa [encodeSource] using congrArg Configuration.state encodingEq.symm
  · rintro ⟨sourceAfter, sourceRun, stateEq⟩
    obtain ⟨nextTime, simulationRun⟩ :=
      quotientRun_to_forwardSimulation sourceRun time
    refine ⟨primeCode sourceAfter.counterZero sourceAfter.counterOne nextTime, ?_⟩
    simpa [encodeSource, stateEq] using simulationRun

end Mortality.OneCounter
