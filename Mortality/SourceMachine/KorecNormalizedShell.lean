import Mortality.SourceMachine.KorecLocalProgramCode
import Mortality.SourceMachine.R2PositiveTargets
import Mortality.SourceMachine.R2Relocation

/-!
# A bounded arithmetic shell for normalized Korec programs

After zero decrement targets have been eliminated, the control and carry
parts of Korec's program-code argument become elementary.  This file packages
only the remaining number theory: selected factors, their residues, and a
candidate whose quotient sum has the required relocated state rank.

The upper envelope

`candidate localState < 3 * offset + leastNondivisor`

is Korec's carry inequality.  Every nonterminal relocated instruction has
code at least `3 * offset`, so the residual carry is below the least selected
factor.  The theorem `RankShell.toControlLCMLayout` verifies that deduction,
as well as the whole finite control invariant.
-/

namespace Mortality.SourceMachine.KorecNormalizedShell

open Mortality.SourceMachine
open Mortality.SourceMachine.KorecR2
open Mortality.SourceMachine.KorecLocalProgramCode

/-- The purely arithmetic data needed for a normalized source program whose
positive states are strictly below `span`.  Candidates are indexed by the
unrelocated source state; their quotient sums already include `offset`. -/
structure RankShell (offset span leastNondivisor bound : Nat)
    (program : KorecR2.Program) where
  leastPositive : 0 < leastNondivisor
  leastBounded : leastNondivisor ≤ bound
  selectedFactors : List Nat
  selectedNodup : selectedFactors.Nodup
  selectedProductSeparated : selectedFactors.Pairwise fun left right =>
    bound < left * right
  selectedAtLeastLeast : ∀ factor, factor ∈ selectedFactors →
    leastNondivisor ≤ factor
  selectedAtMostBound : ∀ factor, factor ∈ selectedFactors → factor ≤ bound
  selectedResidue : Nat → Nat
  selectedResiduePositive : ∀ factor, factor ∈ selectedFactors →
    0 < selectedResidue factor
  selectedResidueBelow : ∀ factor, factor ∈ selectedFactors →
    selectedResidue factor < factor
  selectedDivisorClassification : ∀ factor, factor ∈ selectedFactors →
    ∀ divisor, divisor ∣ factor → divisor = 1 ∨ divisor = factor
  candidate : Nat → Nat
  candidateMem : ∀ {state}, 0 < state → state < span →
    candidate state ∈ selectedFactors
  candidateRankSum : ∀ {state}, 0 < state → state < span →
    (selectedFactors.map fun factor => candidate state / factor).sum =
      offset + state
  operationResidue : ∀ {state operation}, 0 < state → state < span →
    program state = some operation →
    selectedResidue (candidate state) =
      (R2Relocation.shiftInstruction offset operation).code
  candidateUpper : ∀ {state}, 0 < state → state < span →
    candidate state < 3 * offset + leastNondivisor

/-- The program-independent number-theoretic core.  Compared with
`RankShell`, a frame contains no residue assignment.  The lower envelope
puts every candidate above every bounded relocated operation code, so the
residues can be assigned canonically from the program. -/
structure RankFrame (offset span leastNondivisor bound : Nat) where
  leastAtLeastTwo : 2 ≤ leastNondivisor
  leastBounded : leastNondivisor ≤ bound
  selectedFactors : List Nat
  selectedNodup : selectedFactors.Nodup
  selectedProductSeparated : selectedFactors.Pairwise fun left right =>
    bound < left * right
  selectedAtLeastLeast : ∀ factor, factor ∈ selectedFactors →
    leastNondivisor ≤ factor
  selectedAtMostBound : ∀ factor, factor ∈ selectedFactors → factor ≤ bound
  selectedDivisorClassification : ∀ factor, factor ∈ selectedFactors →
    ∀ divisor, divisor ∣ factor → divisor = 1 ∨ divisor = factor
  candidate : Nat → Nat
  candidateMem : ∀ {state}, 0 < state → state < span →
    candidate state ∈ selectedFactors
  candidateRankSum : ∀ {state}, 0 < state → state < span →
    (selectedFactors.map fun factor => candidate state / factor).sum =
      offset + state
  candidateLower : ∀ {state}, 0 < state → state < span →
    3 * (offset + span) ≤ candidate state
  candidateUpper : ∀ {state}, 0 < state → state < span →
    candidate state < 3 * offset + leastNondivisor

theorem RankFrame.candidate_injective
    {offset span leastNondivisor bound : Nat}
    (frame : RankFrame offset span leastNondivisor bound)
    {left right : Nat}
    (leftPositive : 0 < left) (leftBounded : left < span)
    (rightPositive : 0 < right) (rightBounded : right < span)
    (candidateEq : frame.candidate left = frame.candidate right) :
    left = right := by
  have leftRank := frame.candidateRankSum leftPositive leftBounded
  have rightRank := frame.candidateRankSum rightPositive rightBounded
  rw [candidateEq] at leftRank
  rw [leftRank] at rightRank
  omega

private theorem code_lt_three_mul_span
    {span : Nat} {operation : KorecR2.Instruction}
    (targetsBelow : operation.TargetsBelow span) :
    operation.code < 3 * span := by
  cases operation with
  | incrementBoth target =>
      simp [KorecR2.Instruction.TargetsBelow,
        KorecR2.Instruction.code] at targetsBelow ⊢
      omega
  | decrement register target =>
      simp [KorecR2.Instruction.TargetsBelow] at targetsBelow
      cases register <;>
        simp [KorecR2.Instruction.code] <;> omega

private theorem shifted_code_lt_frame_lower
    {offset span : Nat} {operation : KorecR2.Instruction}
    (targetsBelow : operation.TargetsBelow span) :
    (R2Relocation.shiftInstruction offset operation).code <
      3 * (offset + span) := by
  have sourceCodeBound := code_lt_three_mul_span targetsBelow
  rw [R2Relocation.shiftInstruction_code]
  split <;> omega

private def IsCandidate
    {offset span leastNondivisor bound : Nat}
    (frame : RankFrame offset span leastNondivisor bound)
    (factor : Nat) : Prop :=
  ∃ state, 0 < state ∧ state < span ∧ frame.candidate state = factor

/-- Assign a program residue to candidate factors and residue one to every
other selected factor.  Candidate injectivity makes this well-defined. -/
noncomputable def RankFrame.assignedResidue
    {offset span leastNondivisor bound : Nat}
    (frame : RankFrame offset span leastNondivisor bound)
    (program : KorecR2.Program) (factor : Nat) : Nat :=
  letI : Decidable (IsCandidate frame factor) := Classical.propDecidable _
  if witness : IsCandidate frame factor then
    match program (Classical.choose witness) with
    | some operation =>
        (R2Relocation.shiftInstruction offset operation).code
    | none => 1
  else 1

theorem RankFrame.assignedResidue_candidate
    {offset span leastNondivisor bound : Nat}
    (frame : RankFrame offset span leastNondivisor bound)
    {program : KorecR2.Program}
    {state : Nat} (statePositive : 0 < state) (stateBounded : state < span)
    {operation : KorecR2.Instruction}
    (lookup : program state = some operation) :
    frame.assignedResidue program (frame.candidate state) =
      (R2Relocation.shiftInstruction offset operation).code := by
  have witness : IsCandidate frame (frame.candidate state) :=
    ⟨state, statePositive, stateBounded, rfl⟩
  let chosen := Classical.choose witness
  have chosenSpec := Classical.choose_spec witness
  have chosenEq : chosen = state :=
    frame.candidate_injective chosenSpec.1 chosenSpec.2.1
      statePositive stateBounded chosenSpec.2.2
  simp [RankFrame.assignedResidue, witness, chosen, chosenEq, lookup]

theorem RankFrame.assignedResidue_positive
    {offset span leastNondivisor bound : Nat}
    (frame : RankFrame offset span leastNondivisor bound)
    {program : KorecR2.Program}
    (operationAt : ∀ state, 0 < state → state < span →
      ∃ operation, program state = some operation)
    (codePositive : ∀ {state operation}, 0 < state → state < span →
      program state = some operation → 0 < operation.code)
    {factor : Nat} (_factorMem : factor ∈ frame.selectedFactors) :
    0 < frame.assignedResidue program factor := by
  by_cases witness : IsCandidate frame factor
  · let state := Classical.choose witness
    have stateSpec := Classical.choose_spec witness
    obtain ⟨operation, lookup⟩ :=
      operationAt state stateSpec.1 stateSpec.2.1
    have shiftedPositive :
        0 < (R2Relocation.shiftInstruction offset operation).code := by
      rw [R2Relocation.shiftInstruction_code]
      have := codePositive stateSpec.1 stateSpec.2.1 lookup
      split <;> omega
    simpa [RankFrame.assignedResidue, witness, state, lookup] using
      shiftedPositive
  · simp [RankFrame.assignedResidue, witness]

theorem RankFrame.assignedResidue_below
    {offset span leastNondivisor bound : Nat}
    (frame : RankFrame offset span leastNondivisor bound)
    {program : KorecR2.Program}
    (operationAt : ∀ state, 0 < state → state < span →
      ∃ operation, program state = some operation)
    (targetsBelow : ∀ {state operation}, 0 < state → state < span →
      program state = some operation → operation.TargetsBelow span)
    {factor : Nat} (factorMem : factor ∈ frame.selectedFactors) :
    frame.assignedResidue program factor < factor := by
  by_cases witness : IsCandidate frame factor
  · let state := Classical.choose witness
    have stateSpec := Classical.choose_spec witness
    obtain ⟨operation, lookup⟩ :=
      operationAt state stateSpec.1 stateSpec.2.1
    have codeBound := shifted_code_lt_frame_lower
      (offset := offset) (targetsBelow stateSpec.1 stateSpec.2.1 lookup)
    have candidateLower := frame.candidateLower stateSpec.1 stateSpec.2.1
    have factorEq := stateSpec.2.2
    simp [RankFrame.assignedResidue, witness, state, lookup]
    omega
  · have factorAtLeast := frame.selectedAtLeastLeast factor factorMem
    have leastTwo := frame.leastAtLeastTwo
    simp [RankFrame.assignedResidue, witness]
    omega

/-- Fill the residue fields of a frame from a bounded positive-code program. -/
noncomputable def RankFrame.toRankShell
    {offset span leastNondivisor bound : Nat}
    {program : KorecR2.Program}
    (frame : RankFrame offset span leastNondivisor bound)
    (operationAt : ∀ state, 0 < state → state < span →
      ∃ operation, program state = some operation)
    (targetsBelow : ∀ {state operation}, 0 < state → state < span →
      program state = some operation → operation.TargetsBelow span)
    (codePositive : ∀ {state operation}, 0 < state → state < span →
      program state = some operation → 0 < operation.code) :
    RankShell offset span leastNondivisor bound program where
  leastPositive := by
    have leastTwo := frame.leastAtLeastTwo
    omega
  leastBounded := frame.leastBounded
  selectedFactors := frame.selectedFactors
  selectedNodup := frame.selectedNodup
  selectedProductSeparated := frame.selectedProductSeparated
  selectedAtLeastLeast := frame.selectedAtLeastLeast
  selectedAtMostBound := frame.selectedAtMostBound
  selectedResidue := frame.assignedResidue program
  selectedResiduePositive := fun _ factorMem =>
    frame.assignedResidue_positive operationAt codePositive factorMem
  selectedResidueBelow := fun _ factorMem =>
    frame.assignedResidue_below operationAt targetsBelow factorMem
  selectedDivisorClassification := frame.selectedDivisorClassification
  candidate := frame.candidate
  candidateMem := frame.candidateMem
  candidateRankSum := frame.candidateRankSum
  operationResidue := fun statePositive stateBounded lookup =>
    frame.assignedResidue_candidate statePositive stateBounded lookup
  candidateUpper := frame.candidateUpper

/-- The relocated positive-state interval, together with target halt. -/
def Relevant (offset span state : Nat) : Prop :=
  state = 0 ∨ offset < state ∧ state < offset + span

theorem relevant_shiftState
    {offset span state : Nat} (statePositive : 0 < state)
    (stateBounded : state < span) :
    Relevant offset span (R2Relocation.shiftState offset state) := by
  cases state with
  | zero => omega
  | succ predecessor =>
      right
      simp [R2Relocation.shiftState]
      omega

theorem relevant_zero (offset span : Nat) : Relevant offset span 0 :=
  Or.inl rfl

theorem shiftState_sub_offset
    {offset state : Nat} (statePositive : 0 < state) :
    R2Relocation.shiftState offset state - offset = state := by
  obtain ⟨predecessor, rfl⟩ := Nat.exists_eq_succ_of_ne_zero
    (Nat.ne_of_gt statePositive)
  simp only [R2Relocation.shiftState]
  rw [show offset + predecessor + 1 = offset + (predecessor + 1) by omega,
    Nat.add_sub_cancel_left]

/-- A positive relevant relocated state has a unique positive local label. -/
theorem exists_localState
    {offset span state : Nat} (relevant : Relevant offset span state)
    (statePositive : 0 < state) :
    ∃ localState, 0 < localState ∧ localState < span ∧
      state = R2Relocation.shiftState offset localState := by
  rcases relevant with rfl | ⟨offsetBelow, upper⟩
  · omega
  · let localState := state - offset
    refine ⟨localState, by omega, by omega, ?_⟩
    have recompose : offset + localState = state := by
      exact Nat.add_sub_of_le (Nat.le_of_lt offsetBelow)
    rw [← recompose]
    obtain ⟨predecessor, localEq⟩ := Nat.exists_eq_succ_of_ne_zero
      (by omega : localState ≠ 0)
    rw [localEq]
    simp [R2Relocation.shiftState]
    omega

private theorem shifted_code_at_least_three_mul_offset_of_positive_target
    {offset : Nat} {operation : KorecR2.Instruction} {target : Nat}
    (noZeroDecrement : ∀ {register destination},
      operation = .decrement register destination → 0 < destination)
    (targetMem : target ∈
      possibleTargets (R2Relocation.shiftInstruction offset operation))
    (targetPositive : 0 < target) :
    3 * offset ≤ (R2Relocation.shiftInstruction offset operation).code := by
  cases operation with
  | decrement register destination =>
      have destinationPositive : 0 < destination :=
        noZeroDecrement rfl
      obtain ⟨predecessor, rfl⟩ := Nat.exists_eq_succ_of_ne_zero
        (Nat.ne_of_gt destinationPositive)
      cases register <;>
        simp [R2Relocation.shiftInstruction,
          R2Relocation.shiftState, KorecR2.Instruction.code] <;> omega
  | incrementBoth destination =>
      cases destination with
      | zero =>
          simp [R2Relocation.shiftInstruction, R2Relocation.shiftState,
            possibleTargets] at targetMem
          omega
      | succ predecessor =>
          simp [R2Relocation.shiftInstruction, R2Relocation.shiftState,
            KorecR2.Instruction.code]
          omega

private theorem shifted_target_relevant
    {offset span target : Nat} {operation : KorecR2.Instruction}
    (targetsBelow : operation.TargetsBelow span)
    (noZeroDecrement : ∀ {register destination},
      operation = .decrement register destination → 0 < destination)
    (targetMem : target ∈
      possibleTargets (R2Relocation.shiftInstruction offset operation)) :
    Relevant offset span target := by
  cases operation with
  | incrementBoth destination =>
      cases destination with
      | zero =>
          simp [R2Relocation.shiftInstruction, R2Relocation.shiftState,
            possibleTargets] at targetMem
          subst target
          exact relevant_zero offset span
      | succ predecessor =>
          simp [KorecR2.Instruction.TargetsBelow] at targetsBelow
          simp [R2Relocation.shiftInstruction, R2Relocation.shiftState,
            possibleTargets] at targetMem
          subst target
          right
          omega
  | decrement register destination =>
      have destinationPositive : 0 < destination :=
        noZeroDecrement rfl
      obtain ⟨predecessor, rfl⟩ := Nat.exists_eq_succ_of_ne_zero
        (Nat.ne_of_gt destinationPositive)
      simp [KorecR2.Instruction.TargetsBelow] at targetsBelow
      cases register <;>
        simp [R2Relocation.shiftInstruction, R2Relocation.shiftState,
          possibleTargets] at targetMem
      all_goals
        rcases targetMem with rfl | rfl <;> right <;> omega

/-- The arithmetic shell supplies a complete global-rank layout.  All
control-flow facts and all carry inequalities are derived here. -/
def RankShell.toControlLCMLayout
    {offset span leastNondivisor bound : Nat}
    {program : KorecR2.Program}
    (offsetLarge : 3 ≤ offset)
    (operationAt : ∀ state, 0 < state → state < span →
      ∃ operation, program state = some operation)
    (targetsBelow : ∀ {state operation}, 0 < state → state < span →
      program state = some operation → operation.TargetsBelow span)
    (noZeroDecrement : ∀ {state register target},
      program state = some (.decrement register target) → 0 < target)
    (shell : RankShell offset span leastNondivisor bound program) :
    ControlLCMLayout leastNondivisor bound
      (R2Relocation.relocate offset program) where
  Relevant := Relevant offset span
  leastPositive := shell.leastPositive
  leastBounded := shell.leastBounded
  operationAt := by
    intro state relevant statePositive
    obtain ⟨localState, localPositive, localBounded, stateEq⟩ :=
      exists_localState relevant statePositive
    obtain ⟨operation, lookup⟩ :=
      operationAt localState localPositive localBounded
    refine ⟨R2Relocation.shiftInstruction offset operation, ?_⟩
    subst state
    obtain ⟨predecessor, rfl⟩ := Nat.exists_eq_succ_of_ne_zero
      (Nat.ne_of_gt localPositive)
    simpa using
      R2Relocation.relocate_shifted_positive offset program predecessor
        offsetLarge |>.trans (by simp [lookup])
  selectedFactors := shell.selectedFactors
  selectedNodup := shell.selectedNodup
  selectedProductSeparated := shell.selectedProductSeparated
  selectedAtLeastLeast := shell.selectedAtLeastLeast
  selectedAtMostBound := shell.selectedAtMostBound
  selectedResidue := shell.selectedResidue
  selectedResiduePositive := shell.selectedResiduePositive
  selectedResidueBelow := shell.selectedResidueBelow
  selectedDivisorClassification := shell.selectedDivisorClassification
  candidate state := shell.candidate (state - offset)
  candidateMem := by
    intro state relevant statePositive
    obtain ⟨localState, localPositive, localBounded, stateEq⟩ :=
      exists_localState relevant statePositive
    subst state
    have subtraction := shiftState_sub_offset
      (offset := offset) localPositive
    simpa [subtraction] using shell.candidateMem localPositive localBounded
  candidateRankSum := by
    intro state relevant statePositive
    obtain ⟨localState, localPositive, localBounded, stateEq⟩ :=
      exists_localState relevant statePositive
    subst state
    have subtraction := shiftState_sub_offset
      (offset := offset) localPositive
    rw [show shell.candidate
      (R2Relocation.shiftState offset localState - offset) =
        shell.candidate localState by rw [subtraction]]
    calc
      (shell.selectedFactors.map fun factor =>
          shell.candidate localState / factor).sum =
          offset + localState :=
        shell.candidateRankSum localPositive localBounded
      _ = R2Relocation.shiftState offset localState := by
        obtain ⟨predecessor, rfl⟩ := Nat.exists_eq_succ_of_ne_zero
          (Nat.ne_of_gt localPositive)
        simp [R2Relocation.shiftState]
        omega
  operationResidue := by
    intro state operation relevant statePositive lookup
    obtain ⟨localState, localPositive, localBounded, stateEq⟩ :=
      exists_localState relevant statePositive
    subst state
    obtain ⟨predecessor, localEq⟩ := Nat.exists_eq_succ_of_ne_zero
      (Nat.ne_of_gt localPositive)
    have localEq' : localState = predecessor + 1 := by omega
    have relocatedLookup :=
      R2Relocation.relocate_shifted_positive offset program predecessor
        offsetLarge
    rw [← localEq'] at relocatedLookup
    cases sourceLookup : program localState with
    | none =>
        rw [sourceLookup] at relocatedLookup
        simp at relocatedLookup
        rw [relocatedLookup] at lookup
        contradiction
    | some sourceOperation =>
        have operationEq : operation =
            R2Relocation.shiftInstruction offset sourceOperation := by
          rw [sourceLookup] at relocatedLookup
          simp at relocatedLookup
          rw [relocatedLookup] at lookup
          exact Option.some.inj lookup.symm
        subst operation
        have subtraction := shiftState_sub_offset
          (offset := offset) localPositive
        simpa [subtraction] using
          shell.operationResidue localPositive localBounded sourceLookup
  nextRelevant := by
    intro state target operation relevant lookup targetMem
    by_cases statePositive : 0 < state
    · obtain ⟨localState, localPositive, localBounded, stateEq⟩ :=
        exists_localState relevant statePositive
      subst state
      obtain ⟨predecessor, localEq⟩ := Nat.exists_eq_succ_of_ne_zero
        (Nat.ne_of_gt localPositive)
      have localEq' : localState = predecessor + 1 := by omega
      have relocatedLookup :=
        R2Relocation.relocate_shifted_positive offset program predecessor
          offsetLarge
      rw [← localEq'] at relocatedLookup
      cases sourceLookup : program localState with
      | none =>
          rw [sourceLookup] at relocatedLookup
          simp at relocatedLookup
          rw [relocatedLookup] at lookup
          contradiction
      | some sourceOperation =>
          have operationEq : operation =
              R2Relocation.shiftInstruction offset sourceOperation := by
            rw [sourceLookup] at relocatedLookup
            simp at relocatedLookup
            rw [relocatedLookup] at lookup
            exact Option.some.inj lookup.symm
          subst operation
          exact shifted_target_relevant
            (targetsBelow localPositive localBounded sourceLookup)
            (fun {_ destination} instructionEq => by
              apply noZeroDecrement
              rw [sourceLookup]
              exact congrArg some instructionEq)
            targetMem
    · have stateZero : state = 0 := by omega
      subst state
      simp at lookup
  nextCarryBelow := by
    intro state target operation relevant lookup targetMem targetPositive
    have statePositive : 0 < state := by
      by_cases stateZero : state = 0
      · subst state
        simp at lookup
      · omega
    obtain ⟨localState, localPositive, localBounded, stateEq⟩ :=
      exists_localState relevant statePositive
    subst state
    obtain ⟨predecessor, localEq⟩ := Nat.exists_eq_succ_of_ne_zero
      (Nat.ne_of_gt localPositive)
    have localEq' : localState = predecessor + 1 := by omega
    have relocatedLookup :=
      R2Relocation.relocate_shifted_positive offset program predecessor
        offsetLarge
    rw [← localEq'] at relocatedLookup
    cases sourceLookup : program localState with
    | none =>
        rw [sourceLookup] at relocatedLookup
        simp at relocatedLookup
        rw [relocatedLookup] at lookup
        contradiction
    | some sourceOperation =>
        have operationEq : operation =
            R2Relocation.shiftInstruction offset sourceOperation := by
          rw [sourceLookup] at relocatedLookup
          simp at relocatedLookup
          rw [relocatedLookup] at lookup
          exact Option.some.inj lookup.symm
        subst operation
        have codeLower : 3 * offset ≤
            (R2Relocation.shiftInstruction offset sourceOperation).code :=
          shifted_code_at_least_three_mul_offset_of_positive_target
            (fun {_ destination} instructionEq => by
              apply noZeroDecrement
              rw [sourceLookup]
              exact congrArg some instructionEq)
            targetMem targetPositive
        have subtraction := shiftState_sub_offset
          (offset := offset) localPositive
        have candidateUpper := shell.candidateUpper localPositive localBounded
        change shell.candidate
            (R2Relocation.shiftState offset localState - offset) -
              (R2Relocation.shiftInstruction offset sourceOperation).code <
            leastNondivisor
        rw [subtraction]
        by_cases codeAtMostCandidate :
            (R2Relocation.shiftInstruction offset sourceOperation).code ≤
              shell.candidate localState
        · rw [Nat.sub_lt_iff_lt_add codeAtMostCandidate]
          omega
        · rw [Nat.sub_eq_zero_of_le
            (Nat.le_of_lt (Nat.lt_of_not_ge codeAtMostCandidate))]
          exact shell.leastPositive

end Mortality.SourceMachine.KorecNormalizedShell
