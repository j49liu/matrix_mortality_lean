import Mortality.SourceMachine.FourCounterInitializer
import Mortality.SourceMachine.TwoCounterToKorecR2

/-!
# Finite control bounds through the R2 compiler

Korec's numerical program code needs instructions only on a finite
forward-invariant set of control states.  This file records a generic bound
for the eight-address compiler from total two-counter programs to Korec R2.
-/

namespace Mortality.SourceMachine

namespace TotalTwoCounter

/-- Every advertised destination of an ordinary two-counter instruction lies
strictly below `bound`. -/
def Instruction.TargetsBelow (bound : Nat) : Instruction → Prop
  | .increment _ target => target < bound
  | .decrement _ positiveTarget zeroTarget =>
      positiveTarget < bound ∧ zeroTarget < bound

/-- The positive control states below `bound` form a forward-invariant region
for the program. -/
def ClosedBelow (program : Program) (bound : Nat) : Prop :=
  ∀ state, 0 < state → state < bound →
    (program state).TargetsBelow bound

end TotalTwoCounter

namespace FourCounter

/-- Every advertised destination of a four-counter instruction lies below
`bound`. -/
def Instruction.TargetsBelow (bound : Nat) : Instruction → Prop
  | .increment _ target => target < bound
  | .decrement _ zeroTarget positiveTarget =>
      zeroTarget < bound ∧ positiveTarget < bound

/-- Every instruction installed in the bounded source region stays in that
region. Missing instructions are terminal and need no target condition. -/
def ClosedBelow (program : Program) (bound : Nat) : Prop :=
  ∀ {state instruction}, state < bound → program state = some instruction →
    instruction.TargetsBelow bound

end FourCounter

namespace FourCounterToTwoCounter

open FourCounter
open FourCounterEncoding
open TotalTwoCounter

/-- Exclusive target bound for the twenty-address block compiler. -/
def compiledStateBound (sourceBound : Nat) : Nat := entry sourceBound

theorem compiledStateBound_initial (sourceBound : Nat) :
    1 < compiledStateBound (sourceBound + 1) := by
  simp [compiledStateBound, entry, blockStride]

theorem sourceState_lt_of_lt_compiledStateBound
    {sourceBound state : Nat} (statePositive : 0 < state)
    (stateBounded : state < compiledStateBound sourceBound) :
    sourceState state < sourceBound := by
  have numeratorBound : state - 1 < sourceBound * blockStride := by
    change state < 20 * sourceBound + 1 at stateBounded
    change state - 1 < sourceBound * 20
    omega
  have quotientBound : (state - 1) / blockStride < sourceBound :=
    (Nat.div_lt_iff_lt_mul (by decide : 0 < blockStride)).2 (by
      simpa [Nat.mul_comm] using numeratorBound)
  simpa [sourceState] using quotientBound

private theorem entry_add_lt_compiledStateBound
    {sourceBound source offset : Nat} (sourceBounded : source < sourceBound)
    (offsetBound : offset < blockStride) :
    entry source + offset < compiledStateBound sourceBound := by
  change offset < 20 at offsetBound
  change 20 * source + 1 + offset < 20 * sourceBound + 1
  omega

private theorem entry_target_lt_compiledStateBound
    {sourceBound target : Nat} (targetBounded : target < sourceBound) :
    entry target < compiledStateBound sourceBound := by
  change 20 * target + 1 < 20 * sourceBound + 1
  omega

/-- The twenty-address compiler preserves a finite four-counter control
bound. Padding addresses self-loop inside their own private interval. -/
theorem compile_closedBelow
    {program : FourCounter.Program} {sourceBound : Nat}
    (programClosed : FourCounter.ClosedBelow program sourceBound) :
    TotalTwoCounter.ClosedBelow (compile program)
      (compiledStateBound sourceBound) := by
  intro state statePositive stateBounded
  have decodedSourceBound := sourceState_lt_of_lt_compiledStateBound
    statePositive stateBounded
  generalize offsetEq : blockOffset state = offset
  have offsetBound : offset < blockStride := by
    rw [← offsetEq]
    exact Nat.mod_lt _ (by decide)
  have localBound : ∀ offset, offset < blockStride →
      entry (sourceState state) + offset < compiledStateBound sourceBound :=
    fun offset bound =>
      entry_add_lt_compiledStateBound decodedSourceBound bound
  have localZero := localBound 0 (by decide)
  have localOne := localBound 1 (by decide)
  have localTwo := localBound 2 (by decide)
  have localThree := localBound 3 (by decide)
  have localFour := localBound 4 (by decide)
  have localFive := localBound 5 (by decide)
  have localSix := localBound 6 (by decide)
  have localSeven := localBound 7 (by decide)
  have localEight := localBound 8 (by decide)
  have localNine := localBound 9 (by decide)
  have localTen := localBound 10 (by decide)
  have localEleven := localBound 11 (by decide)
  have localTwelve := localBound 12 (by decide)
  have localThirteen := localBound 13 (by decide)
  have localFourteen := localBound 14 (by decide)
  have localFifteen := localBound 15 (by decide)
  have localSixteen := localBound 16 (by decide)
  have localSeventeen := localBound 17 (by decide)
  have localEighteen := localBound 18 (by decide)
  have localNineteen := localBound 19 (by decide)
  have offsetCases : offset = 0 ∨ offset = 1 ∨ offset = 2 ∨ offset = 3 ∨
      offset = 4 ∨ offset = 5 ∨ offset = 6 ∨ offset = 7 ∨
      offset = 8 ∨ offset = 9 ∨ offset = 10 ∨ offset = 11 ∨
      offset = 12 ∨ offset = 13 ∨ offset = 14 ∨ offset = 15 ∨
      offset = 16 ∨ offset = 17 ∨ offset = 18 ∨ offset = 19 := by
    change offset < 20 at offsetBound
    omega
  unfold compile
  rw [if_neg (Nat.ne_of_gt statePositive)]
  rw [offsetEq]
  cases lookup : program (sourceState state) with
  | none =>
      rcases offsetCases with rfl | rfl | rfl | rfl | rfl | rfl | rfl |
          rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
          rfl | rfl | rfl <;>
        simp [compileBlock, lookup, terminalBlock, paddingInstruction,
          TotalTwoCounter.Instruction.TargetsBelow] <;> omega
  | some instruction =>
      have advertised := programClosed decodedSourceBound lookup
      cases instruction with
      | increment register target =>
          have targetBound := entry_target_lt_compiledStateBound
            (by simpa [FourCounter.Instruction.TargetsBelow] using advertised)
          cases register <;>
            rcases offsetCases with rfl | rfl | rfl | rfl | rfl | rfl | rfl |
              rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
              rfl | rfl | rfl <;>
            simp [compileBlock, lookup, incrementBlock, paddingInstruction,
              registerPrime, TotalTwoCounter.Instruction.TargetsBelow] <;>
            first | assumption | omega
      | decrement register zeroTarget positiveTarget =>
          have zeroBound := entry_target_lt_compiledStateBound
            (by simpa [FourCounter.Instruction.TargetsBelow] using advertised.1)
          have positiveBound := entry_target_lt_compiledStateBound
            (by simpa [FourCounter.Instruction.TargetsBelow] using advertised.2)
          cases register <;>
            rcases offsetCases with rfl | rfl | rfl | rfl | rfl | rfl | rfl |
              rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
              rfl | rfl | rfl <;>
            simp [compileBlock, lookup, decrementBlock, paddingInstruction,
              registerPrime, TotalTwoCounter.Instruction.TargetsBelow] <;>
            first
            | assumption
            | omega

end FourCounterToTwoCounter

namespace FourCounterInitializer

open FourCounter

/-- Exclusive control bound after adjoining the finite tag-countdown prefix
and relocating the source program. -/
def initializedStateBound (tagBound sourceBound : Nat) : Nat :=
  sourceOffset tagBound + sourceBound

/-- The initializer preserves finiteness of the source control graph. -/
theorem initializedProgram_closedBelow
    {tagBound sourceBound : Nat} {target : Nat → Nat}
    {program : FourCounter.Program}
    (sourceBoundPositive : 0 < sourceBound)
    (targetBounded : ∀ tag, tag < sourceOffset tagBound →
      target tag < sourceBound)
    (programClosed : FourCounter.ClosedBelow program sourceBound) :
    FourCounter.ClosedBelow (initializedProgram tagBound target program)
      (initializedStateBound tagBound sourceBound) := by
  intro state instruction stateBounded lookup
  by_cases inPrefix : state < sourceOffset tagBound
  · rw [initializedProgram_prefix tagBound target program inPrefix] at lookup
    have selectedBound := targetBounded state inPrefix
    simp only [Option.some.injEq] at lookup
    subst instruction
    simp [sourceOffset] at inPrefix
    simp [FourCounter.Instruction.TargetsBelow, initializedStateBound,
      sourceOffset]
    constructor <;> omega
  · have offsetLe : sourceOffset tagBound ≤ state := by omega
    obtain ⟨sourceState, stateEq⟩ := Nat.exists_eq_add_of_le offsetLe
    rw [stateEq] at stateBounded lookup
    have sourceStateBound : sourceState < sourceBound := by
      simp [initializedStateBound] at stateBounded
      omega
    rw [initializedProgram_source] at lookup
    cases sourceLookup : program sourceState with
    | none => simp [sourceLookup] at lookup
    | some sourceInstruction =>
        have advertised := programClosed sourceStateBound sourceLookup
        simp [sourceLookup] at lookup
        subst instruction
        cases sourceInstruction <;>
          simp [shiftInstruction, FourCounter.Instruction.TargetsBelow,
            initializedStateBound] at advertised ⊢ <;>
          omega

end FourCounterInitializer

namespace KorecR2

/-- Both possible destinations of a restricted decrement, or the unique
destination of an increment, lie below `bound`. -/
def Instruction.TargetsBelow (bound : Nat) : Instruction → Prop
  | .decrement _ positiveTarget => positiveTarget + 1 < bound
  | .incrementBoth target => target < bound

/-- A control-state bound, independent of the two register values. -/
def ClosedBelow (program : Program) (bound : Nat) : Prop :=
  ∀ {source target}, source.state < bound →
    step program source = some target → target.state < bound

/-- An instruction whose destinations lie below the bound preserves the
bound in one R2 step. -/
theorem step_state_lt_of_lookup
    {program : Program} {bound : Nat} {source target : Configuration}
    {operation : Instruction}
    (sourcePositive : 0 < source.state)
    (lookup : program source.state = some operation)
    (targetsBelow : operation.TargetsBelow bound)
    (stepEq : step program source = some target) :
    target.state < bound := by
  rcases source with ⟨state, registerZero, registerTwo⟩
  cases operation with
  | decrement register destination =>
      cases register <;> cases registerZero <;> cases registerTwo <;>
        simp [step, Nat.ne_of_gt sourcePositive, lookup] at stepEq
      all_goals
        have targetStateEq := congrArg Configuration.state stepEq
        simp at targetStateEq
        simp [Instruction.TargetsBelow] at targetsBelow
        omega
  | incrementBoth destination =>
      simp [step, Nat.ne_of_gt sourcePositive, lookup] at stepEq
      subst target
      exact targetsBelow

end KorecR2

namespace TwoCounterToKorecR2

open TotalTwoCounter

/-- Exclusive R2 control bound corresponding to an exclusive ordinary
two-counter bound. -/
def compiledStateBound (sourceBound : Nat) : Nat := entry sourceBound

theorem compiledStateBound_initial {sourceBound : Nat}
    (boundLarge : 1 < sourceBound) :
    1 < compiledStateBound sourceBound := by
  obtain ⟨predecessor, rfl⟩ := Nat.exists_eq_succ_of_ne_zero
    (by omega : sourceBound ≠ 0)
  simp [compiledStateBound, entry]
  omega

theorem sourceState_lt_of_lt_compiledStateBound
    {sourceBound state : Nat} (statePositive : 0 < state)
    (stateBounded : state < compiledStateBound sourceBound) :
    sourceState state < sourceBound := by
  cases sourceBound with
  | zero => simp [compiledStateBound, entry] at stateBounded
  | succ predecessor =>
      simp only [compiledStateBound, entry] at stateBounded
      have numeratorBound : state - 1 < predecessor * 8 := by omega
      have quotientBound : (state - 1) / 8 < predecessor :=
        (Nat.div_lt_iff_lt_mul (by decide : 0 < 8)).2 numeratorBound
      simp only [sourceState]
      omega

theorem sourceState_positive (state : Nat) :
    0 < sourceState state := by
  simp [sourceState]

private theorem entry_add_lt_compiledStateBound
    {sourceBound source offset : Nat}
    (sourcePositive : 0 < source) (sourceBounded : source < sourceBound)
    (offsetBound : offset < 8) :
    entry source + offset < compiledStateBound sourceBound := by
  obtain ⟨sourcePredecessor, rfl⟩ := Nat.exists_eq_succ_of_ne_zero
    (Nat.ne_of_gt sourcePositive)
  obtain ⟨boundPredecessor, rfl⟩ := Nat.exists_eq_succ_of_ne_zero
    (by omega : sourceBound ≠ 0)
  simp [entry, compiledStateBound] at sourceBounded ⊢
  omega

private theorem entry_target_succ_lt_compiledStateBound
    {sourceBound target : Nat} (boundLarge : 1 < sourceBound)
    (targetBounded : target < sourceBound) :
    entry target + 1 < compiledStateBound sourceBound := by
  cases target with
  | zero =>
      cases sourceBound with
      | zero => omega
      | succ boundPredecessor =>
          simp [entry, compiledStateBound]
          omega
  | succ targetPredecessor =>
      obtain ⟨boundPredecessor, rfl⟩ := Nat.exists_eq_succ_of_ne_zero
        (by omega : sourceBound ≠ 0)
      simp [entry, compiledStateBound] at targetBounded ⊢
      omega

/-- Every macro instruction installed for a bounded source state has bounded
R2 destinations, including the extra zero branch of a Korec decrement. -/
theorem instructionAt_targetsBelow
    {program : TotalTwoCounter.Program} {sourceBound source offset : Nat}
    (boundLarge : 1 < sourceBound)
    (sourcePositive : 0 < source) (sourceBounded : source < sourceBound)
    (programClosed : TotalTwoCounter.ClosedBelow program sourceBound)
    (offsetBound : offset < 8) :
    (instructionAt (entry source) (program source) offset).TargetsBelow
      (compiledStateBound sourceBound) := by
  have advertised := programClosed source sourcePositive sourceBounded
  have localBound : ∀ localOffset, localOffset < 8 →
      entry source + localOffset < compiledStateBound sourceBound :=
    fun localOffset bound =>
      entry_add_lt_compiledStateBound sourcePositive sourceBounded bound
  have localZero := localBound 0 (by omega)
  have localOne := localBound 1 (by omega)
  have localTwo := localBound 2 (by omega)
  have localThree := localBound 3 (by omega)
  have localFour := localBound 4 (by omega)
  have localFive := localBound 5 (by omega)
  have localSix := localBound 6 (by omega)
  have localSeven := localBound 7 (by omega)
  have offsetCases : offset = 0 ∨ offset = 1 ∨ offset = 2 ∨ offset = 3 ∨
      offset = 4 ∨ offset = 5 ∨ offset = 6 ∨ offset = 7 := by
    omega
  rcases offsetCases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    cases operation : program source with
    | increment counter target =>
        cases counter <;>
          simp [instructionAt, operation,
            KorecR2.Instruction.TargetsBelow] at advertised ⊢
        all_goals
          first
          | exact entry_target_succ_lt_compiledStateBound boundLarge advertised
          | omega
    | decrement counter positiveTarget zeroTarget =>
        cases counter <;>
          simp [instructionAt, operation,
            KorecR2.Instruction.TargetsBelow] at advertised ⊢
        all_goals
          first
          | exact entry_target_succ_lt_compiledStateBound boundLarge advertised.1
          | exact entry_target_succ_lt_compiledStateBound boundLarge advertised.2
          | omega

/-- The eight-address R2 compiler preserves every finite forward control
bound of the ordinary two-counter source. -/
theorem compile_closedBelow
    {program : TotalTwoCounter.Program} {sourceBound : Nat}
    (boundLarge : 1 < sourceBound)
    (programClosed : TotalTwoCounter.ClosedBelow program sourceBound) :
    KorecR2.ClosedBelow (compile program) (compiledStateBound sourceBound) := by
  intro source target sourceBounded stepEq
  have sourcePositive : 0 < source.state := by
    by_cases stateZero : source.state = 0
    · simp [KorecR2.step, stateZero] at stepEq
    · omega
  have decodedSourceBound := sourceState_lt_of_lt_compiledStateBound
    sourcePositive sourceBounded
  have decodedSourcePositive := sourceState_positive source.state
  have offsetBound : macroOffset source.state < 8 := by
    exact Nat.mod_lt _ (by decide)
  have lookup : compile program source.state =
      some (instructionAt (entry (sourceState source.state))
        (program (sourceState source.state)) (macroOffset source.state)) := by
    simp [compile, Nat.ne_of_gt sourcePositive]
  exact KorecR2.step_state_lt_of_lookup
    (operation := instructionAt (entry (sourceState source.state))
      (program (sourceState source.state)) (macroOffset source.state))
    sourcePositive lookup
    (instructionAt_targetsBelow boundLarge decodedSourcePositive
      decodedSourceBound programClosed offsetBound) stepEq

end TwoCounterToKorecR2

end Mortality.SourceMachine
