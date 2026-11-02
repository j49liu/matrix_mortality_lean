import Mortality.OneCounter.FixedProgram

/-!
# The explicit finite edge list

This file materializes the fixed reversed relation as a finite one-counter
program.  One quotient increment gives one division edge.  One quotient
conditional decrement gives a contraction edge and a zero-test edge.  The
reversed cleanup contributes the sole increment edge.
-/

namespace Mortality.OneCounter

set_option maxRecDepth 100000

/-- Reverse the simulation edges contributed by one source instruction. -/
def reversedEdges (source : Nat) : Option SourceMachine.RawInstruction →
    List (Edge Nat)
  | none => []
  | some (.inc .zero target) =>
      [{ source := target, target := source, instruction := .divideTwoOdd }]
  | some (.inc .one target) =>
      [{ source := target, target := source, instruction := .divideThreeTwo }]
  | some (.dec .zero positive zeroDest) =>
      [{ source := positive, target := source, instruction := .contractTwo },
        { source := zeroDest, target := source, instruction := .congruenceTest 2 [0] }]
  | some (.dec .one positive zeroDest) =>
      [{ source := positive, target := source, instruction := .contractThree },
        { source := zeroDest, target := source, instruction := .congruenceTest 3 [0, 1] }]
  | some .halt => []

/-- The cleanup edge after reversal. -/
def reversedCleanupEdge : Edge Nat :=
  { source := 278, target := 278, instruction := .increment }

/-- The concrete finite one-counter program compiled in the manuscript. -/
def fixedProgram : Program Nat :=
  { edges := reversedCleanupEdge ::
      SourceMachine.quotientStates.flatMap fun source =>
        reversedEdges source (SourceMachine.quotientAt source) }

/-- Counts of the six instruction kinds in a concrete edge list. -/
structure FixedInstructionCounts where
  increment : Nat
  testTwo : Nat
  testThree : Nat
  divideTwo : Nat
  divideThree : Nat
  contractTwo : Nat
  contractThree : Nat
  deriving DecidableEq, Repr

namespace FixedInstructionCounts

def addEdge (counts : FixedInstructionCounts) (edge : Edge Nat) :
    FixedInstructionCounts :=
  match edge.instruction with
  | .increment => { counts with increment := counts.increment + 1 }
  | .congruenceTest 2 [0] => { counts with testTwo := counts.testTwo + 1 }
  | .congruenceTest 3 [0, 1] =>
      { counts with testThree := counts.testThree + 1 }
  | .divideTwoOdd => { counts with divideTwo := counts.divideTwo + 1 }
  | .divideThreeTwo => { counts with divideThree := counts.divideThree + 1 }
  | .contractTwo => { counts with contractTwo := counts.contractTwo + 1 }
  | .contractThree => { counts with contractThree := counts.contractThree + 1 }
  | .congruenceTest _ _ => counts

end FixedInstructionCounts

def fixedInstructionCounts : FixedInstructionCounts :=
  fixedProgram.edges.foldl FixedInstructionCounts.addEdge
    { increment := 0, testTwo := 0, testThree := 0,
      divideTwo := 0, divideThree := 0,
      contractTwo := 0, contractThree := 0 }

/-- The finite program has the 378 edges implied by the quotient counts. -/
theorem fixedProgram_edge_count : fixedProgram.edges.length = 378 := by
  decide

/-- The explicit edge list has exactly the occurrence counts used by the
generator calculation. -/
theorem fixedProgram_instruction_counts :
    fixedInstructionCounts =
      { increment := 1, testTwo := 80, testThree := 28,
        divideTwo := 88, divideThree := 73,
        contractTwo := 80, contractThree := 28 } := by
  decide

/-- The finite edge list realizes exactly the reversed forward relation. -/
theorem fixedProgram_step_iff (before after : Configuration Nat) :
    Step fixedProgram before after ↔ FixedProgramStep before after := by
  cases before with
  | mk beforeState beforeCounter =>
    cases after with
    | mk afterState afterCounter =>
      constructor
      · rintro ⟨edge, edgeMem, edgeSource, edgeTarget, evaluation⟩
        simp only [fixedProgram, List.mem_cons] at edgeMem
        rcases edgeMem with cleanupEdge | generatedEdge
        · subst edge
          simp only [reversedCleanupEdge] at edgeSource edgeTarget evaluation
          subst beforeState
          subst afterState
          simp only [Instruction.evaluate_increment, Option.some.injEq] at evaluation
          unfold FixedProgramStep Reaches.converse ForwardStep CleanupStep
          exact Or.inr ⟨rfl, rfl, evaluation.symm⟩
        · rw [List.mem_flatMap] at generatedEdge
          obtain ⟨source, sourceMem, edgeMem⟩ := generatedEdge
          cases lookup : SourceMachine.quotientAt source with
          | none =>
              rw [lookup] at edgeMem
              simp [reversedEdges] at edgeMem
          | some instruction =>
              rw [lookup] at edgeMem
              cases instruction with
              | inc counter target =>
                  cases counter <;>
                    simp only [reversedEdges, List.mem_singleton] at edgeMem <;>
                    subst edge <;>
                    simp only at edgeSource edgeTarget evaluation <;>
                    subst beforeState <;> subst afterState <;>
                    exact Or.inl (by
                      simp [ForwardSimulationStep, lookup, evaluation])
              | dec counter positive zeroDest =>
                  cases counter <;>
                    simp [reversedEdges] at edgeMem
                  · rcases edgeMem with positiveEdge | zeroEdge
                    · subst edge
                      simp only at edgeSource edgeTarget evaluation
                      subst beforeState
                      subst afterState
                      exact Or.inl (by
                        simp [ForwardSimulationStep, lookup, evaluation])
                    · subst edge
                      simp only at edgeSource edgeTarget evaluation
                      subst beforeState
                      subst afterState
                      have counterEq :=
                        Instruction.evaluate_congruenceTest_eq evaluation
                      exact Or.inl (by
                        simp only [ForwardSimulationStep, lookup]
                        exact Or.inr ⟨True.intro,
                          by simpa [counterEq] using evaluation⟩)
                  · rcases edgeMem with positiveEdge | zeroEdge
                    · subst edge
                      simp only at edgeSource edgeTarget evaluation
                      subst beforeState
                      subst afterState
                      exact Or.inl (by
                        simp [ForwardSimulationStep, lookup, evaluation])
                    · subst edge
                      simp only at edgeSource edgeTarget evaluation
                      subst beforeState
                      subst afterState
                      have counterEq :=
                        Instruction.evaluate_congruenceTest_eq evaluation
                      exact Or.inl (by
                        simp only [ForwardSimulationStep, lookup]
                        exact Or.inr ⟨True.intro,
                          by simpa [counterEq] using evaluation⟩)
              | halt => simp [reversedEdges] at edgeMem
      · intro reversedStep
        unfold FixedProgramStep Reaches.converse ForwardStep at reversedStep
        rcases reversedStep with simulationStep | cleanupStep
        · unfold ForwardSimulationStep at simulationStep
          cases lookup : SourceMachine.quotientAt afterState with
          | none => simp [lookup] at simulationStep
          | some instruction =>
              have sourceMem := SourceMachine.quotientAt_state_mem lookup
              simp only [lookup] at simulationStep
              cases instruction with
              | inc counter target =>
                  cases counter
                  · rcases simulationStep with ⟨stateEq, evaluation⟩
                    refine ⟨{ source := target, target := afterState, instruction := .divideTwoOdd }, ?_, ?_, rfl, evaluation⟩
                    · simp only [fixedProgram, List.mem_cons]
                      right
                      apply List.mem_flatMap.mpr
                      exact ⟨afterState, sourceMem, by simp [reversedEdges, lookup]⟩
                    · exact stateEq.symm
                  · rcases simulationStep with ⟨stateEq, evaluation⟩
                    refine ⟨{ source := target, target := afterState, instruction := .divideThreeTwo }, ?_, ?_, rfl, evaluation⟩
                    · simp only [fixedProgram, List.mem_cons]
                      right
                      apply List.mem_flatMap.mpr
                      exact ⟨afterState, sourceMem, by simp [reversedEdges, lookup]⟩
                    · exact stateEq.symm
              | dec counter positive zeroDest =>
                  cases counter
                  · rcases simulationStep with positiveStep | zeroStep
                    · rcases positiveStep with ⟨stateEq, evaluation⟩
                      refine ⟨{ source := positive, target := afterState, instruction := .contractTwo }, ?_, ?_, rfl, evaluation⟩
                      · simp only [fixedProgram, List.mem_cons]
                        right
                        apply List.mem_flatMap.mpr
                        exact ⟨afterState, sourceMem, by simp [reversedEdges, lookup]⟩
                      · exact stateEq.symm
                    · rcases zeroStep with ⟨stateEq, evaluation⟩
                      have counterEq :=
                        Instruction.evaluate_congruenceTest_eq evaluation
                      refine ⟨{ source := zeroDest, target := afterState, instruction := .congruenceTest 2 [0] }, ?_, ?_, rfl, ?_⟩
                      · simp only [fixedProgram, List.mem_cons]
                        right
                        apply List.mem_flatMap.mpr
                        exact ⟨afterState, sourceMem, by simp [reversedEdges, lookup]⟩
                      · exact stateEq.symm
                      · simpa [counterEq] using evaluation
                  · rcases simulationStep with positiveStep | zeroStep
                    · rcases positiveStep with ⟨stateEq, evaluation⟩
                      refine ⟨{ source := positive, target := afterState, instruction := .contractThree }, ?_, ?_, rfl, evaluation⟩
                      · simp only [fixedProgram, List.mem_cons]
                        right
                        apply List.mem_flatMap.mpr
                        exact ⟨afterState, sourceMem, by simp [reversedEdges, lookup]⟩
                      · exact stateEq.symm
                    · rcases zeroStep with ⟨stateEq, evaluation⟩
                      have counterEq :=
                        Instruction.evaluate_congruenceTest_eq evaluation
                      refine ⟨{ source := zeroDest, target := afterState, instruction := .congruenceTest 3 [0, 1] }, ?_, ?_, rfl, ?_⟩
                      · simp only [fixedProgram, List.mem_cons]
                        right
                        apply List.mem_flatMap.mpr
                        exact ⟨afterState, sourceMem, by simp [reversedEdges, lookup]⟩
                      · exact stateEq.symm
                      · simpa [counterEq] using evaluation
              | halt => contradiction
        · rcases cleanupStep with ⟨afterStateEq, beforeStateEq, counterEq⟩
          change afterState = 278 at afterStateEq
          change beforeState = 278 at beforeStateEq
          subst afterState
          subst beforeState
          refine ⟨reversedCleanupEdge, ?_, rfl, rfl, ?_⟩
          · simp [fixedProgram]
          · change some (beforeCounter + 1) = some afterCounter
            simp only [Option.some.injEq]
            exact counterEq.symm

/-- Reachability in the explicit program is reachability in the abstract
reversed relation. -/
theorem fixedProgram_reaches_iff (start finish : Configuration Nat) :
    Reaches (Step fixedProgram) start finish ↔
      Reaches FixedProgramStep start finish := by
  constructor
  · exact Reaches.mono (fun {_ _} step => (fixedProgram_step_iff _ _).mp step)
  · exact Reaches.mono (fun {_ _} step => (fixedProgram_step_iff _ _).mpr step)

/-- The concrete finite program has the desired exact variable endpoint. -/
theorem concreteFixedProgram_reaches_input_iff_u2Halts (input : Nat) :
    Reaches (Step fixedProgram) zeroHaltConfiguration
        (inputConfiguration input) ↔
      SourceMachine.U2Halts input := by
  rw [fixedProgram_reaches_iff,
    fixedProgram_reaches_input_iff_u2Halts]

end Mortality.OneCounter
