import Mortality.SourceMachine.FourCounterEncoding
import Mortality.SourceMachine.TwoCounterSemantics
import Mortality.SourceMachine.U20Simulation

/-!
# Prime-exponent compilation from four counters to two counters

This file begins the executable compiler from the four-register source
interface to ordinary two-counter programs.  Each source state owns a private
twenty-address interval.  The largest block uses prime seven and occupies
eighteen addresses, so the intervals are disjoint.

The logical register tuple is stored in counter one.  Counter zero is scratch
and is zero at every source boundary.  This orientation matches the input
convention of `TotalTwoCounter`.
-/

namespace Mortality.SourceMachine.FourCounterToTwoCounter

open Mortality.SourceMachine
open Mortality.SourceMachine.FourCounter
open Mortality.SourceMachine.FourCounterEncoding
open Mortality.SourceMachine.TotalTwoCounter
open Mortality.SourceMachine.U20Compilation

def blockStride : Nat := 20

def entry (state : Nat) : Nat := blockStride * state + 1

theorem entry_positive (state : Nat) : 0 < entry state := by
  simp [entry, blockStride]

def sourceState (state : Nat) : Nat := (state - 1) / blockStride

def blockOffset (state : Nat) : Nat := (state - 1) % blockStride

@[simp] theorem sourceState_entry_add (state offset : Nat)
    (bound : offset < blockStride) :
    sourceState (entry state + offset) = state := by
  change offset < 20 at bound
  simp only [sourceState, entry, blockStride]
  omega

@[simp] theorem blockOffset_entry_add (state offset : Nat)
    (bound : offset < blockStride) :
    blockOffset (entry state + offset) = offset := by
  change offset < 20 at bound
  simp only [blockOffset, entry, blockStride]
  omega

/-- Multiply counter one by `prime`, using counter zero as scratch. -/
def incrementBlock (start prime target : Nat) :
    List TotalTwoCounter.Instruction :=
  [.decrement .one (start + 1) (start + prime + 1)] ++
    ((List.range prime).map fun offset =>
      .increment .zero
        (if offset + 1 = prime then start else start + offset + 2)) ++
    [.decrement .zero (start + prime + 2) target,
      .increment .one (start + prime + 1)]

/-- Test divisibility of counter one by `prime`.  On success divide by
`prime`; on failure restore the original value.  Counter zero is zero at
both exits. -/
def decrementBlock (start prime positiveTarget zeroTarget : Nat) :
    List TotalTwoCounter.Instruction :=
  ((List.range prime).map fun offset =>
      .decrement .one (start + offset + 1)
        (if offset = 0 then start + 2 * prime + 2
        else start + 2 * prime + 1 - offset)) ++
    [.increment .zero start] ++
    ((List.range prime).map fun offset =>
      .increment .one (start + prime + offset + 2)) ++
    [.decrement .zero (start + prime + 1) zeroTarget,
      .decrement .zero (start + 2 * prime + 3) positiveTarget,
      .increment .one (start + 2 * prime + 2)]

@[simp] theorem incrementBlock_length (start prime target : Nat) :
    (incrementBlock start prime target).length = prime + 3 := by
  simp [incrementBlock]

@[simp] theorem decrementBlock_length
    (start prime positiveTarget zeroTarget : Nat) :
    (decrementBlock start prime positiveTarget zeroTarget).length =
      2 * prime + 4 := by
  simp [decrementBlock]
  omega

def terminalBlock : List TotalTwoCounter.Instruction :=
  [.increment .zero 0]

def compileBlock (program : FourCounter.Program) (state : Nat) :
    List TotalTwoCounter.Instruction :=
  match program state with
  | none => terminalBlock
  | some (.increment register target) =>
      incrementBlock (entry state) (registerPrime register) (entry target)
  | some (.decrement register zeroTarget positiveTarget) =>
      decrementBlock (entry state) (registerPrime register)
        (entry positiveTarget) (entry zeroTarget)

/-- A harmless nonhalting instruction used only at unreachable padding
offsets of a private block. -/
def paddingInstruction (state : Nat) : TotalTwoCounter.Instruction :=
  .increment .zero state

/-- The complete ordinary two-counter target.  State zero is ignored by the
target semantics and therefore remains the unique halt state. -/
def compile (program : FourCounter.Program) : TotalTwoCounter.Program :=
  fun state =>
    if state = 0 then paddingInstruction 0
    else
      (compileBlock program (sourceState state))[blockOffset state]?.getD
        (paddingInstruction state)

@[simp] theorem compile_entry_add
    (program : FourCounter.Program) (state offset : Nat)
    (offsetBound : offset < blockStride)
    (blockBound : offset < (compileBlock program state).length) :
    compile program (entry state + offset) =
      (compileBlock program state)[offset] := by
  have addressPositive : entry state + offset ≠ 0 := by
    have := entry_positive state
    omega
  unfold compile
  rw [if_neg addressPositive]
  rw [sourceState_entry_add state offset offsetBound,
    blockOffset_entry_add state offset offsetBound]
  simp [List.getElem?_eq_getElem blockBound]

@[simp] theorem compile_terminal_entry
    {program : FourCounter.Program} {state : Nat}
    (terminal : program state = none) :
    compile program (entry state) = .increment .zero 0 := by
  have blockLength : 0 < (compileBlock program state).length := by
    simp [compileBlock, terminal, terminalBlock]
  simpa [compileBlock, terminal, terminalBlock] using
    compile_entry_add program state 0 (by simp [blockStride]) blockLength

@[simp] theorem incrementBlock_get_zero (start prime target : Nat) :
    (incrementBlock start prime target)[0]? =
      some (.decrement .one (start + 1) (start + prime + 1)) := by
  simp [incrementBlock]

@[simp] theorem incrementBlock_get_increment
    (start prime target offset : Nat) (bound : offset < prime) :
    (incrementBlock start prime target)[offset + 1]? =
      some (.increment .zero
        (if offset + 1 = prime then start else start + offset + 2)) := by
  simp [incrementBlock, List.getElem?_append, bound]

@[simp] theorem incrementBlock_get_transfer (start prime target : Nat) :
    (incrementBlock start prime target)[prime + 1]? =
      some (.decrement .zero (start + prime + 2) target) := by
  simp [incrementBlock]

@[simp] theorem incrementBlock_get_restore (start prime target : Nat) :
    (incrementBlock start prime target)[prime + 2]? =
      some (.increment .one (start + prime + 1)) := by
  simp [incrementBlock]

def blockConfiguration (state scratch primary : Nat) :
    TotalTwoCounter.Configuration :=
  { state, counterZero := scratch, counterOne := primary }

def encodeConfiguration (configuration : FourCounter.Configuration) :
    TotalTwoCounter.Configuration :=
  blockConfiguration (entry configuration.state) 0
    (encode configuration.registers)

def RealizesBlock (program : FourCounter.Program) (start : Nat)
    (block : List TotalTwoCounter.Instruction) : Prop :=
  ∀ offset, (bound : offset < block.length) →
    some (compile program (start + offset)) = block[offset]?

theorem registerPrime_lt_stride (register : Register) :
    registerPrime register + 3 < blockStride := by
  cases register <;> decide

theorem decrementBlock_lt_stride (register : Register) :
    2 * registerPrime register + 4 ≤ blockStride := by
  cases register <;> decide

theorem realizes_incrementBlock
    {program : FourCounter.Program} {state target : Nat} {register : Register}
    (lookup : program state = some (.increment register target)) :
    RealizesBlock program (entry state)
      (incrementBlock (entry state) (registerPrime register) (entry target)) := by
  intro offset bound
  have offsetBound : offset < blockStride := by
    rw [incrementBlock_length] at bound
    have primeBound := registerPrime_lt_stride register
    omega
  have blockEq :
      compileBlock program state =
        incrementBlock (entry state) (registerPrime register) (entry target) := by
    simp [compileBlock, lookup]
  have addressPositive : entry state + offset ≠ 0 := by
    have := entry_positive state
    omega
  unfold compile
  rw [if_neg addressPositive]
  rw [sourceState_entry_add state offset offsetBound,
    blockOffset_entry_add state offset offsetBound, blockEq]
  simp [List.getElem?_eq_getElem bound]

theorem realizes_decrementBlock
    {program : FourCounter.Program} {state zeroTarget positiveTarget : Nat}
    {register : Register}
    (lookup : program state =
      some (.decrement register zeroTarget positiveTarget)) :
    RealizesBlock program (entry state)
      (decrementBlock (entry state) (registerPrime register)
        (entry positiveTarget) (entry zeroTarget)) := by
  intro offset bound
  have offsetBound : offset < blockStride := by
    rw [decrementBlock_length] at bound
    have blockBound := decrementBlock_lt_stride register
    omega
  have blockEq :
      compileBlock program state =
        decrementBlock (entry state) (registerPrime register)
          (entry positiveTarget) (entry zeroTarget) := by
    simp [compileBlock, lookup]
  have addressPositive : entry state + offset ≠ 0 := by
    have := entry_positive state
    omega
  unfold compile
  rw [if_neg addressPositive]
  rw [sourceState_entry_add state offset offsetBound,
    blockOffset_entry_add state offset offsetBound, blockEq]
  simp [List.getElem?_eq_getElem bound]

theorem targetStep_of_lookup
    {program : FourCounter.Program}
    {configuration : TotalTwoCounter.Configuration}
    {instruction : TotalTwoCounter.Instruction}
    (positive : 0 < configuration.state)
    (lookup : compile program configuration.state = instruction) :
    TotalTwoCounter.step (compile program) configuration =
      some (TotalTwoCounter.execute instruction configuration) :=
  TotalTwoCounter.step_of_lookup positive lookup

/-- The consecutive counter-zero increments in a multiplication block. -/
theorem incrementBlock_scratchScan
    {program : FourCounter.Program}
    {start prime target offset remaining scratch primary : Nat}
    (realizes : RealizesBlock program start
      (incrementBlock start prime target))
    (sum : offset + remaining = prime)
    (positiveRemaining : 0 < remaining) :
    Reaches (TotalTwoCounter.step (compile program))
      (blockConfiguration (start + offset + 1) scratch primary)
      (blockConfiguration start (scratch + remaining) primary) := by
  induction remaining generalizing offset scratch with
  | zero => omega
  | succ remaining inductionHypothesis =>
      have offsetBound : offset < prime := by omega
      have blockBound : offset + 1 <
          (incrementBlock start prime target).length := by
        simp
        omega
      have lookup := realizes (offset + 1) blockBound
      rw [incrementBlock_get_increment start prime target offset offsetBound]
        at lookup
      by_cases noRemainder : remaining = 0
      · subst remaining
        have last : offset + 1 = prime := by omega
        apply Reaches.single
        rw [targetStep_of_lookup (program := program)
          (configuration := blockConfiguration (start + offset + 1)
            scratch primary) (by simp [blockConfiguration])
          (by simpa [blockConfiguration, Nat.add_assoc] using lookup)]
        simp [TotalTwoCounter.execute, blockConfiguration, last]
      · have notLast : offset + 1 ≠ prime := by omega
        have firstStep :
            TotalTwoCounter.step (compile program)
                (blockConfiguration (start + offset + 1) scratch primary) =
              some (blockConfiguration (start + (offset + 1) + 1)
                (scratch + 1) primary) := by
          rw [targetStep_of_lookup (program := program)
            (configuration := blockConfiguration (start + offset + 1)
              scratch primary) (by simp [blockConfiguration])
            (by simpa [blockConfiguration, Nat.add_assoc] using lookup)]
          simp [TotalTwoCounter.execute, blockConfiguration, notLast]
          omega
        have suffix := inductionHypothesis (offset := offset + 1)
          (scratch := scratch + 1) (by omega) (by omega)
        exact (Reaches.single firstStep).trans (by
          simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using suffix)

/-- One multiplication cycle consumes one primary unit and adds `prime`
scratch units. -/
theorem incrementBlock_cycle
    {program : FourCounter.Program}
    {start prime target scratch primary : Nat}
    (positivePrime : 0 < prime)
    (realizes : RealizesBlock program start
      (incrementBlock start prime target))
    (startPositive : 0 < start) :
    Reaches (TotalTwoCounter.step (compile program))
      (blockConfiguration start scratch (primary + 1))
      (blockConfiguration start (scratch + prime) primary) := by
  have blockBound : 0 < (incrementBlock start prime target).length := by simp
  have lookup := realizes 0 blockBound
  rw [incrementBlock_get_zero] at lookup
  have firstStep :
      TotalTwoCounter.step (compile program)
          (blockConfiguration start scratch (primary + 1)) =
        some (blockConfiguration (start + 1) scratch primary) := by
    rw [targetStep_of_lookup (program := program)
      (configuration := blockConfiguration start scratch (primary + 1))
      startPositive (by simpa [blockConfiguration] using lookup)]
    simp [TotalTwoCounter.execute, blockConfiguration]
  exact (Reaches.single firstStep).trans
    (incrementBlock_scratchScan realizes (offset := 0)
      (remaining := prime) (scratch := scratch) (primary := primary)
      (by omega) positivePrime)

/-- The multiplication loop consumes the whole primary counter. -/
theorem incrementBlock_consume
    {program : FourCounter.Program}
    {start prime target scratch primary : Nat}
    (positivePrime : 0 < prime)
    (realizes : RealizesBlock program start
      (incrementBlock start prime target))
    (startPositive : 0 < start) :
    Reaches (TotalTwoCounter.step (compile program))
      (blockConfiguration start scratch primary)
      (blockConfiguration (start + prime + 1)
        (scratch + prime * primary) 0) := by
  induction primary generalizing scratch with
  | zero =>
      have blockBound : 0 < (incrementBlock start prime target).length := by simp
      have lookup := realizes 0 blockBound
      rw [incrementBlock_get_zero] at lookup
      apply Reaches.single
      rw [targetStep_of_lookup (program := program)
        (configuration := blockConfiguration start scratch 0)
        startPositive (by simpa [blockConfiguration] using lookup)]
      simp [TotalTwoCounter.execute, blockConfiguration]
  | succ primary inductionHypothesis =>
      exact (incrementBlock_cycle positivePrime realizes startPositive
        (scratch := scratch) (primary := primary)).trans (by
          simpa [Nat.mul_succ, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
            using inductionHypothesis (scratch := scratch + prime))

/-- The transfer loop returns all scratch units to the primary counter and
exits the multiplication block. -/
theorem incrementBlock_transfer
    {program : FourCounter.Program}
    {start prime target scratch primary : Nat}
    (realizes : RealizesBlock program start
      (incrementBlock start prime target)) :
    Reaches (TotalTwoCounter.step (compile program))
      (blockConfiguration (start + prime + 1) scratch primary)
      (blockConfiguration target 0 (scratch + primary)) := by
  induction scratch generalizing primary with
  | zero =>
      have blockBound : prime + 1 <
          (incrementBlock start prime target).length := by simp
      have lookup := realizes (prime + 1) blockBound
      rw [incrementBlock_get_transfer] at lookup
      apply Reaches.single
      rw [targetStep_of_lookup (program := program)
        (configuration := blockConfiguration (start + prime + 1) 0 primary)
        (by simp [blockConfiguration])
        (by simpa [blockConfiguration, Nat.add_assoc] using lookup)]
      simp [TotalTwoCounter.execute, blockConfiguration]
  | succ scratch inductionHypothesis =>
      have transferBound : prime + 1 <
          (incrementBlock start prime target).length := by simp
      have transferLookup := realizes (prime + 1) transferBound
      rw [incrementBlock_get_transfer] at transferLookup
      have firstStep :
          TotalTwoCounter.step (compile program)
              (blockConfiguration (start + prime + 1) (scratch + 1) primary) =
            some (blockConfiguration (start + prime + 2) scratch primary) := by
        rw [targetStep_of_lookup (program := program)
          (configuration := blockConfiguration (start + prime + 1)
            (scratch + 1) primary) (by simp [blockConfiguration])
          (by simpa [blockConfiguration, Nat.add_assoc] using transferLookup)]
        simp [TotalTwoCounter.execute, blockConfiguration]
        omega
      have restoreBound : prime + 2 <
          (incrementBlock start prime target).length := by simp
      have restoreLookup := realizes (prime + 2) restoreBound
      rw [incrementBlock_get_restore] at restoreLookup
      have secondStep :
          TotalTwoCounter.step (compile program)
              (blockConfiguration (start + prime + 2) scratch primary) =
            some (blockConfiguration (start + prime + 1) scratch
              (primary + 1)) := by
        rw [targetStep_of_lookup (program := program)
          (configuration := blockConfiguration (start + prime + 2)
            scratch primary) (by simp [blockConfiguration])
          (by simpa [blockConfiguration, Nat.add_assoc] using restoreLookup)]
        simp [TotalTwoCounter.execute, blockConfiguration]
        omega
      exact (Reaches.single firstStep).trans <|
        (Reaches.single secondStep).trans (by
          simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
            using inductionHypothesis (primary := primary + 1))

/-- Semantic correctness of a realized multiplication block. -/
theorem incrementBlock_correct
    {program : FourCounter.Program}
    {start prime target input : Nat}
    (positivePrime : 0 < prime)
    (realizes : RealizesBlock program start
      (incrementBlock start prime target))
    (startPositive : 0 < start) :
    Reaches (TotalTwoCounter.step (compile program))
      (blockConfiguration start 0 input)
      (blockConfiguration target 0 (prime * input)) := by
  exact (incrementBlock_consume positivePrime realizes startPositive
    (scratch := 0) (primary := input)).trans (by
      simpa [Nat.add_comm] using incrementBlock_transfer realizes
        (scratch := prime * input) (primary := 0))

/-- A source-register increment is simulated from one encoded boundary to
the next. -/
theorem compile_increment
    {program : FourCounter.Program} {configuration : FourCounter.Configuration}
    {register : Register} {target : Nat}
    (lookup : program configuration.state =
      some (.increment register target)) :
    Reaches (TotalTwoCounter.step (compile program))
      (encodeConfiguration configuration)
      (encodeConfiguration
        ⟨target, configuration.registers.increment register⟩) := by
  have run := incrementBlock_correct
    (program := program)
    (positivePrime := Nat.zero_lt_of_lt (registerPrime_large register))
    (realizes_incrementBlock lookup)
    (entry_positive configuration.state)
    (input := encode configuration.registers)
  simpa [encodeConfiguration, encode_increment] using run

/-- A missing source instruction reaches the distinguished two-counter halt
state in one step.  The scratch counter's terminal value is irrelevant. -/
theorem compile_terminal
    {program : FourCounter.Program} {configuration : FourCounter.Configuration}
    (terminal : program configuration.state = none) :
    TotalTwoCounter.step (compile program) (encodeConfiguration configuration) =
      some (blockConfiguration 0 1 (encode configuration.registers)) := by
  rw [targetStep_of_lookup (program := program)
    (configuration := encodeConfiguration configuration)
    (by simp [encodeConfiguration, blockConfiguration, entry_positive])
    (by simpa [encodeConfiguration, blockConfiguration] using
      compile_terminal_entry terminal)]
  simp [TotalTwoCounter.execute, encodeConfiguration, blockConfiguration]

@[simp] theorem decrementBlock_get_test
    (start prime positiveTarget zeroTarget offset : Nat)
    (bound : offset < prime) :
    (decrementBlock start prime positiveTarget zeroTarget)[offset]? =
      some (.decrement .one (start + offset + 1)
        (if offset = 0 then start + 2 * prime + 2
        else start + 2 * prime + 1 - offset)) := by
  simp [decrementBlock, List.getElem?_append, bound]

@[simp] theorem decrementBlock_get_scratch
    (start prime positiveTarget zeroTarget : Nat) :
    (decrementBlock start prime positiveTarget zeroTarget)[prime]? =
      some (.increment .zero start) := by
  simp [decrementBlock]

@[simp] theorem decrementBlock_get_restoreIncrement
    (start prime positiveTarget zeroTarget offset : Nat)
    (bound : offset < prime) :
    (decrementBlock start prime positiveTarget zeroTarget)[prime + 1 + offset]? =
      some (.increment .one (start + prime + offset + 2)) := by
  simp only [decrementBlock, List.getElem?_append, List.length_map,
    List.length_range, List.length_append, List.length_cons, List.length_nil]
  rw [if_pos (by omega)]
  rw [if_neg (by omega)]
  simp [bound]

@[simp] theorem decrementBlock_get_failureTransfer
    (start prime positiveTarget zeroTarget : Nat) :
    (decrementBlock start prime positiveTarget zeroTarget)[2 * prime + 1]? =
      some (.decrement .zero (start + prime + 1) zeroTarget) := by
  simp only [decrementBlock, List.getElem?_append, List.length_map,
    List.length_range, List.length_append, List.length_cons, List.length_nil]
  rw [if_neg (by omega)]
  have indexEq : 2 * prime + 1 - (prime + 1 + prime) = 0 := by omega
  rw [indexEq]
  rfl

@[simp] theorem decrementBlock_get_successTransfer
    (start prime positiveTarget zeroTarget : Nat) :
    (decrementBlock start prime positiveTarget zeroTarget)[2 * prime + 2]? =
      some (.decrement .zero (start + 2 * prime + 3) positiveTarget) := by
  simp only [decrementBlock, List.getElem?_append, List.length_map,
    List.length_range, List.length_append, List.length_cons, List.length_nil]
  rw [if_neg (by omega)]
  have indexEq : 2 * prime + 2 - (prime + 1 + prime) = 1 := by omega
  rw [indexEq]
  rfl

@[simp] theorem decrementBlock_get_successRestore
    (start prime positiveTarget zeroTarget : Nat) :
    (decrementBlock start prime positiveTarget zeroTarget)[2 * prime + 3]? =
      some (.increment .one (start + 2 * prime + 2)) := by
  simp only [decrementBlock, List.getElem?_append, List.length_map,
    List.length_range, List.length_append, List.length_cons, List.length_nil]
  rw [if_neg (by omega)]
  have indexEq : 2 * prime + 3 - (prime + 1 + prime) = 2 := by omega
  rw [indexEq]
  rfl

/-- A positive prefix of a divisibility test consumes the requested number
of primary units. -/
theorem decrementBlock_positivePrefix
    {program : FourCounter.Program}
    {start prime positiveTarget zeroTarget offset count scratch primary : Nat}
    (realizes : RealizesBlock program start
      (decrementBlock start prime positiveTarget zeroTarget))
    (within : offset + count ≤ prime)
    (startPositive : 0 < start) :
    Reaches (TotalTwoCounter.step (compile program))
      (blockConfiguration (start + offset) scratch (primary + count))
      (blockConfiguration (start + offset + count) scratch primary) := by
  induction count generalizing offset primary with
  | zero =>
      simpa using Reaches.refl
        (blockConfiguration (start + offset) scratch primary)
  | succ count inductionHypothesis =>
      have offsetBound : offset < prime := by omega
      have blockBound : offset <
          (decrementBlock start prime positiveTarget zeroTarget).length := by
        simp
        omega
      have lookup := realizes offset blockBound
      rw [decrementBlock_get_test start prime positiveTarget zeroTarget offset
        offsetBound] at lookup
      have firstStep :
          TotalTwoCounter.step (compile program)
              (blockConfiguration (start + offset) scratch
                (primary + (count + 1))) =
            some (blockConfiguration (start + (offset + 1)) scratch
              (primary + count)) := by
        rw [targetStep_of_lookup (program := program)
          (configuration := blockConfiguration (start + offset) scratch
            (primary + (count + 1)))
          (by simp [blockConfiguration]; omega)
          (by simpa [blockConfiguration] using lookup)]
        simp [TotalTwoCounter.execute, blockConfiguration]
        omega
      have suffix := inductionHypothesis (offset := offset + 1)
        (primary := primary) (by omega)
      exact (Reaches.single (by simpa [Nat.add_assoc] using firstStep)).trans (by
        simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using suffix)

/-- One complete divisibility cycle subtracts `prime` from the primary
counter and records one quotient unit in scratch. -/
theorem decrementBlock_cycle
    {program : FourCounter.Program}
    {start prime positiveTarget zeroTarget scratch primary : Nat}
    (positivePrime : 0 < prime)
    (realizes : RealizesBlock program start
      (decrementBlock start prime positiveTarget zeroTarget))
    (startPositive : 0 < start) :
    Reaches (TotalTwoCounter.step (compile program))
      (blockConfiguration start scratch (primary + prime))
      (blockConfiguration start (scratch + 1) primary) := by
  have scan := decrementBlock_positivePrefix realizes
    (offset := 0) (count := prime) (scratch := scratch) (primary := primary)
    (by omega) startPositive
  have blockBound : prime <
      (decrementBlock start prime positiveTarget zeroTarget).length := by
    simp
    omega
  have lookup := realizes prime blockBound
  rw [decrementBlock_get_scratch] at lookup
  have scratchStep :
      TotalTwoCounter.step (compile program)
          (blockConfiguration (start + prime) scratch primary) =
        some (blockConfiguration start (scratch + 1) primary) := by
    rw [targetStep_of_lookup (program := program)
      (configuration := blockConfiguration (start + prime) scratch primary)
      (by simp [blockConfiguration]; omega)
      (by simpa [blockConfiguration] using lookup)]
    simp [TotalTwoCounter.execute, blockConfiguration]
  have scan' : Reaches (TotalTwoCounter.step (compile program))
      (blockConfiguration start scratch (primary + prime))
      (blockConfiguration (start + prime) scratch primary) := by
    simpa using scan
  exact scan'.trans (Reaches.single scratchStep)

/-- Consume complete prime-sized groups, leaving the remainder in primary
and accumulating the quotient in scratch. -/
theorem decrementBlock_consumeGroups
    {program : FourCounter.Program}
    {start prime positiveTarget zeroTarget quotient remainder scratch : Nat}
    (positivePrime : 0 < prime)
    (realizes : RealizesBlock program start
      (decrementBlock start prime positiveTarget zeroTarget))
    (startPositive : 0 < start) :
    Reaches (TotalTwoCounter.step (compile program))
      (blockConfiguration start scratch (remainder + prime * quotient))
      (blockConfiguration start (scratch + quotient) remainder) := by
  induction quotient generalizing scratch with
  | zero => exact .refl _
  | succ quotient inductionHypothesis =>
      have cycle := decrementBlock_cycle positivePrime realizes startPositive
        (scratch := scratch) (primary := remainder + prime * quotient)
      have cycle' : Reaches (TotalTwoCounter.step (compile program))
          (blockConfiguration start scratch
            (remainder + prime * (quotient + 1)))
          (blockConfiguration start (scratch + 1)
            (remainder + prime * quotient)) := by
        simpa [Nat.mul_succ, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
          using cycle
      exact cycle'.trans (by
        simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
          using inductionHypothesis (scratch := scratch + 1))

/-- On exact division, move the quotient from scratch back to primary. -/
theorem decrementBlock_successTransfer
    {program : FourCounter.Program}
    {start prime positiveTarget zeroTarget scratch primary : Nat}
    (realizes : RealizesBlock program start
      (decrementBlock start prime positiveTarget zeroTarget)) :
    Reaches (TotalTwoCounter.step (compile program))
      (blockConfiguration (start + 2 * prime + 2) scratch primary)
      (blockConfiguration positiveTarget 0 (scratch + primary)) := by
  induction scratch generalizing primary with
  | zero =>
      have blockBound : 2 * prime + 2 <
          (decrementBlock start prime positiveTarget zeroTarget).length := by
        simp
      have lookup := realizes (2 * prime + 2) blockBound
      rw [decrementBlock_get_successTransfer] at lookup
      apply Reaches.single
      rw [targetStep_of_lookup (program := program)
        (configuration := blockConfiguration (start + 2 * prime + 2)
          0 primary)
        (by simp [blockConfiguration])
        (by simpa [blockConfiguration, Nat.add_assoc] using lookup)]
      simp [TotalTwoCounter.execute, blockConfiguration]
  | succ scratch inductionHypothesis =>
      have transferBound : 2 * prime + 2 <
          (decrementBlock start prime positiveTarget zeroTarget).length := by
        simp
      have transferLookup := realizes (2 * prime + 2) transferBound
      rw [decrementBlock_get_successTransfer] at transferLookup
      have firstStep :
          TotalTwoCounter.step (compile program)
              (blockConfiguration (start + 2 * prime + 2)
                (scratch + 1) primary) =
            some (blockConfiguration (start + 2 * prime + 3)
              scratch primary) := by
        rw [targetStep_of_lookup (program := program)
          (configuration := blockConfiguration (start + 2 * prime + 2)
            (scratch + 1) primary)
          (by simp [blockConfiguration])
          (by simpa [blockConfiguration, Nat.add_assoc] using transferLookup)]
        simp [TotalTwoCounter.execute, blockConfiguration]
        omega
      have restoreBound : 2 * prime + 3 <
          (decrementBlock start prime positiveTarget zeroTarget).length := by
        simp
      have restoreLookup := realizes (2 * prime + 3) restoreBound
      rw [decrementBlock_get_successRestore] at restoreLookup
      have secondStep :
          TotalTwoCounter.step (compile program)
              (blockConfiguration (start + 2 * prime + 3)
                scratch primary) =
            some (blockConfiguration (start + 2 * prime + 2)
              scratch (primary + 1)) := by
        rw [targetStep_of_lookup (program := program)
          (configuration := blockConfiguration (start + 2 * prime + 3)
            scratch primary)
          (by simp [blockConfiguration])
          (by simpa [blockConfiguration, Nat.add_assoc] using restoreLookup)]
        simp [TotalTwoCounter.execute, blockConfiguration]
        omega
      exact (Reaches.single firstStep).trans <|
        (Reaches.single secondStep).trans (by
          simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
            using inductionHypothesis (primary := primary + 1))

/-- Exact divisibility takes the positive source branch and divides the
prime-exponent code by `prime`. -/
theorem decrementBlock_success
    {program : FourCounter.Program}
    {start prime positiveTarget zeroTarget quotient : Nat}
    (positivePrime : 0 < prime)
    (realizes : RealizesBlock program start
      (decrementBlock start prime positiveTarget zeroTarget))
    (startPositive : 0 < start) :
    Reaches (TotalTwoCounter.step (compile program))
      (blockConfiguration start 0 (prime * quotient))
      (blockConfiguration positiveTarget 0 quotient) := by
  have consume := decrementBlock_consumeGroups positivePrime realizes
    startPositive (quotient := quotient) (remainder := 0) (scratch := 0)
  have entryBound : 0 <
      (decrementBlock start prime positiveTarget zeroTarget).length := by simp
  have entryLookup := realizes 0 entryBound
  rw [decrementBlock_get_test start prime positiveTarget zeroTarget 0
    positivePrime] at entryLookup
  have zeroStep :
      TotalTwoCounter.step (compile program)
          (blockConfiguration start quotient 0) =
        some (blockConfiguration (start + 2 * prime + 2) quotient 0) := by
    rw [targetStep_of_lookup (program := program)
      (configuration := blockConfiguration start quotient 0)
      (by simpa [blockConfiguration] using startPositive)
      (by simpa [blockConfiguration] using entryLookup)]
    simp [TotalTwoCounter.execute, blockConfiguration]
  have consume' : Reaches (TotalTwoCounter.step (compile program))
      (blockConfiguration start 0 (prime * quotient))
      (blockConfiguration start quotient 0) := by
    simpa [Nat.add_comm] using consume
  exact consume'.trans <| (Reaches.single zeroStep).trans (by
    simpa using decrementBlock_successTransfer realizes
      (scratch := quotient) (primary := 0))

/-- Restore a nonzero remainder after the first failed subtraction. -/
theorem decrementBlock_restoreRemainder
    {program : FourCounter.Program}
    {start prime positiveTarget zeroTarget offset remaining scratch primary : Nat}
    (realizes : RealizesBlock program start
      (decrementBlock start prime positiveTarget zeroTarget))
    (sum : offset + remaining = prime) :
    Reaches (TotalTwoCounter.step (compile program))
      (blockConfiguration (start + prime + 1 + offset) scratch primary)
      (blockConfiguration (start + 2 * prime + 1) scratch
        (primary + remaining)) := by
  induction remaining generalizing offset primary with
  | zero =>
      have stateEq : start + prime + 1 + offset =
          start + 2 * prime + 1 := by omega
      simpa [stateEq] using Reaches.refl
        (blockConfiguration (start + 2 * prime + 1) scratch primary)
  | succ remaining inductionHypothesis =>
      have offsetBound : offset < prime := by omega
      have blockBound : prime + 1 + offset <
          (decrementBlock start prime positiveTarget zeroTarget).length := by
        simp
        omega
      have lookup := realizes (prime + 1 + offset) blockBound
      rw [decrementBlock_get_restoreIncrement start prime positiveTarget
        zeroTarget offset offsetBound] at lookup
      have firstStep :
          TotalTwoCounter.step (compile program)
              (blockConfiguration (start + prime + 1 + offset)
                scratch primary) =
            some (blockConfiguration (start + prime + 1 + (offset + 1))
              scratch (primary + 1)) := by
        rw [targetStep_of_lookup (program := program)
          (configuration := blockConfiguration (start + prime + 1 + offset)
            scratch primary)
          (by simp [blockConfiguration]; omega)
          (by simpa [blockConfiguration, Nat.add_assoc] using lookup)]
        simp [TotalTwoCounter.execute, blockConfiguration]
        omega
      exact (Reaches.single firstStep).trans (by
        simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
          using inductionHypothesis (offset := offset + 1)
            (primary := primary + 1) (by omega))

/-- On the failed-divisibility branch, restore `prime` primary units for
each quotient unit held in scratch and take the source zero branch. -/
theorem decrementBlock_failureTransfer
    {program : FourCounter.Program}
    {start prime positiveTarget zeroTarget scratch primary : Nat}
    (realizes : RealizesBlock program start
      (decrementBlock start prime positiveTarget zeroTarget)) :
    Reaches (TotalTwoCounter.step (compile program))
      (blockConfiguration (start + 2 * prime + 1) scratch primary)
      (blockConfiguration zeroTarget 0 (primary + prime * scratch)) := by
  induction scratch generalizing primary with
  | zero =>
      have blockBound : 2 * prime + 1 <
          (decrementBlock start prime positiveTarget zeroTarget).length := by
        simp
      have lookup := realizes (2 * prime + 1) blockBound
      rw [decrementBlock_get_failureTransfer] at lookup
      apply Reaches.single
      rw [targetStep_of_lookup (program := program)
        (configuration := blockConfiguration (start + 2 * prime + 1)
          0 primary)
        (by simp [blockConfiguration])
        (by simpa [blockConfiguration, Nat.add_assoc] using lookup)]
      simp [TotalTwoCounter.execute, blockConfiguration]
  | succ scratch inductionHypothesis =>
      have transferBound : 2 * prime + 1 <
          (decrementBlock start prime positiveTarget zeroTarget).length := by
        simp
      have transferLookup := realizes (2 * prime + 1) transferBound
      rw [decrementBlock_get_failureTransfer] at transferLookup
      have firstStep :
          TotalTwoCounter.step (compile program)
              (blockConfiguration (start + 2 * prime + 1)
                (scratch + 1) primary) =
            some (blockConfiguration (start + prime + 1) scratch primary) := by
        rw [targetStep_of_lookup (program := program)
          (configuration := blockConfiguration (start + 2 * prime + 1)
            (scratch + 1) primary)
          (by simp [blockConfiguration])
          (by simpa [blockConfiguration, Nat.add_assoc] using transferLookup)]
        simp [TotalTwoCounter.execute, blockConfiguration]
        omega
      have restore := decrementBlock_restoreRemainder realizes
        (offset := 0) (remaining := prime) (scratch := scratch)
        (primary := primary) (by omega)
      have restore' : Reaches (TotalTwoCounter.step (compile program))
          (blockConfiguration (start + prime + 1) scratch primary)
          (blockConfiguration (start + 2 * prime + 1) scratch
            (primary + prime)) := by
        simpa using restore
      exact (Reaches.single firstStep).trans <| restore'.trans (by
        simpa [Nat.mul_succ, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
          using inductionHypothesis (primary := primary + prime))

/-- A nonzero remainder restores the original encoded value and takes the
source zero branch. -/
theorem decrementBlock_failure
    {program : FourCounter.Program}
    {start prime positiveTarget zeroTarget quotient remainder : Nat}
    (positivePrime : 0 < prime)
    (positiveRemainder : 0 < remainder)
    (remainderBound : remainder < prime)
    (realizes : RealizesBlock program start
      (decrementBlock start prime positiveTarget zeroTarget))
    (startPositive : 0 < start) :
    Reaches (TotalTwoCounter.step (compile program))
      (blockConfiguration start 0 (remainder + prime * quotient))
      (blockConfiguration zeroTarget 0 (remainder + prime * quotient)) := by
  have consume := decrementBlock_consumeGroups positivePrime realizes
    startPositive (quotient := quotient) (remainder := remainder) (scratch := 0)
  have prefixRun := decrementBlock_positivePrefix realizes
    (offset := 0) (count := remainder) (scratch := quotient) (primary := 0)
    (by omega) startPositive
  have testBound : remainder <
      (decrementBlock start prime positiveTarget zeroTarget).length := by
    simp
    omega
  have testLookup := realizes remainder testBound
  rw [decrementBlock_get_test start prime positiveTarget zeroTarget remainder
    remainderBound] at testLookup
  have nonzeroOffset : remainder ≠ 0 := by omega
  have failureStep :
      TotalTwoCounter.step (compile program)
          (blockConfiguration (start + remainder) quotient 0) =
        some (blockConfiguration (start + 2 * prime + 1 - remainder)
          quotient 0) := by
    rw [targetStep_of_lookup (program := program)
      (configuration := blockConfiguration (start + remainder) quotient 0)
      (by simp [blockConfiguration]; omega)
      (by simpa [blockConfiguration] using testLookup)]
    simp [TotalTwoCounter.execute, blockConfiguration, nonzeroOffset]
  have restore := decrementBlock_restoreRemainder realizes
    (offset := prime - remainder) (remaining := remainder)
    (scratch := quotient) (primary := 0) (by omega)
  have transfer := decrementBlock_failureTransfer realizes
    (scratch := quotient) (primary := remainder)
  have consume' : Reaches (TotalTwoCounter.step (compile program))
      (blockConfiguration start 0 (remainder + prime * quotient))
      (blockConfiguration start quotient remainder) := by
    simpa using consume
  have prefixRun' : Reaches (TotalTwoCounter.step (compile program))
      (blockConfiguration start quotient remainder)
      (blockConfiguration (start + remainder) quotient 0) := by
    simpa using prefixRun
  have restore' : Reaches (TotalTwoCounter.step (compile program))
      (blockConfiguration (start + 2 * prime + 1 - remainder) quotient 0)
      (blockConfiguration (start + 2 * prime + 1) quotient remainder) := by
    have startEq : start + 2 * prime + 1 - remainder =
        start + prime + 1 + (prime - remainder) := by omega
    simpa [startEq] using restore
  exact consume'.trans <| prefixRun'.trans <|
    (Reaches.single failureStep).trans <| restore'.trans (by
      simpa using transfer)

/-- A run with one explicitly marked successful step has a positive exact
iteration length, even when its endpoints happen to coincide. -/
theorem positive_iteration_of_reaches_step_reaches
    {alpha : Type} {step : alpha → Option alpha}
    {start middle next finish : alpha}
    (initialRun : Reaches step start middle)
    (marked : step middle = some next)
    (suffix : Reaches step next finish) :
    ∃ fuel, 0 < fuel ∧ iterate step fuel start = some finish := by
  obtain ⟨prefixFuel, prefixExecution⟩ :=
    reaches_iff_exists_iterate.mp initialRun
  obtain ⟨suffixFuel, suffixExecution⟩ := reaches_iff_exists_iterate.mp suffix
  refine ⟨prefixFuel + 1 + suffixFuel, by omega, ?_⟩
  have fuelEq : prefixFuel + 1 + suffixFuel =
      prefixFuel + (1 + suffixFuel) := by omega
  rw [fuelEq, iterate_add, prefixExecution]
  change iterate step (1 + suffixFuel) middle = some finish
  rw [iterate_add]
  simp [iterate, marked, suffixExecution]

theorem positive_iteration_of_reaches_of_ne
    {alpha : Type} {step : alpha → Option alpha} {start finish : alpha}
    (run : Reaches step start finish) (distinct : start ≠ finish) :
    ∃ fuel, 0 < fuel ∧ iterate step fuel start = some finish := by
  obtain ⟨fuel, execution⟩ := reaches_iff_exists_iterate.mp run
  refine ⟨fuel, ?_, execution⟩
  by_cases fuelZero : fuel = 0
  · subst fuel
    simp [iterate] at execution
    exact (distinct execution).elim
  · omega

/-- Exact positive-length form of failed divisibility.  The explicitly
marked failed subtraction makes the bound independent of whether the source
zero branch is a control-state self-loop. -/
theorem decrementBlock_failure_iteration
    {program : FourCounter.Program}
    {start prime positiveTarget zeroTarget quotient remainder : Nat}
    (positivePrime : 0 < prime)
    (positiveRemainder : 0 < remainder)
    (remainderBound : remainder < prime)
    (realizes : RealizesBlock program start
      (decrementBlock start prime positiveTarget zeroTarget))
    (startPositive : 0 < start) :
    ∃ fuel, 0 < fuel ∧
      iterate (TotalTwoCounter.step (compile program)) fuel
          (blockConfiguration start 0 (remainder + prime * quotient)) =
        some (blockConfiguration zeroTarget 0
          (remainder + prime * quotient)) := by
  have consume := decrementBlock_consumeGroups positivePrime realizes
    startPositive (quotient := quotient) (remainder := remainder) (scratch := 0)
  have prefixRun := decrementBlock_positivePrefix realizes
    (offset := 0) (count := remainder) (scratch := quotient) (primary := 0)
    (by omega) startPositive
  have testBound : remainder <
      (decrementBlock start prime positiveTarget zeroTarget).length := by
    simp
    omega
  have testLookup := realizes remainder testBound
  rw [decrementBlock_get_test start prime positiveTarget zeroTarget remainder
    remainderBound] at testLookup
  have nonzeroOffset : remainder ≠ 0 := by omega
  have failureStep :
      TotalTwoCounter.step (compile program)
          (blockConfiguration (start + remainder) quotient 0) =
        some (blockConfiguration (start + 2 * prime + 1 - remainder)
          quotient 0) := by
    rw [targetStep_of_lookup (program := program)
      (configuration := blockConfiguration (start + remainder) quotient 0)
      (by simp [blockConfiguration]; omega)
      (by simpa [blockConfiguration] using testLookup)]
    simp [TotalTwoCounter.execute, blockConfiguration, nonzeroOffset]
  have restore := decrementBlock_restoreRemainder realizes
    (offset := prime - remainder) (remaining := remainder)
    (scratch := quotient) (primary := 0) (by omega)
  have transfer := decrementBlock_failureTransfer realizes
    (scratch := quotient) (primary := remainder)
  have initialRun : Reaches (TotalTwoCounter.step (compile program))
      (blockConfiguration start 0 (remainder + prime * quotient))
      (blockConfiguration (start + remainder) quotient 0) := by
    have consume' : Reaches (TotalTwoCounter.step (compile program))
        (blockConfiguration start 0 (remainder + prime * quotient))
        (blockConfiguration start quotient remainder) := by
      simpa using consume
    have prefixRun' : Reaches (TotalTwoCounter.step (compile program))
        (blockConfiguration start quotient remainder)
        (blockConfiguration (start + remainder) quotient 0) := by
      simpa using prefixRun
    exact consume'.trans prefixRun'
  have suffix : Reaches (TotalTwoCounter.step (compile program))
      (blockConfiguration (start + 2 * prime + 1 - remainder) quotient 0)
      (blockConfiguration zeroTarget 0 (remainder + prime * quotient)) := by
    have restore' : Reaches (TotalTwoCounter.step (compile program))
        (blockConfiguration (start + 2 * prime + 1 - remainder) quotient 0)
        (blockConfiguration (start + 2 * prime + 1) quotient remainder) := by
      have startEq : start + 2 * prime + 1 - remainder =
          start + prime + 1 + (prime - remainder) := by omega
      simpa [startEq] using restore
    exact restore'.trans (by simpa using transfer)
  exact positive_iteration_of_reaches_step_reaches initialRun failureStep suffix

/-- A zero logical register takes the source zero branch and restores the
complete prime-exponent code. -/
theorem compile_decrement_zero
    {program : FourCounter.Program} {configuration : FourCounter.Configuration}
    {register : Register} {zeroTarget positiveTarget : Nat}
    (lookup : program configuration.state =
      some (.decrement register zeroTarget positiveTarget))
    (zero : configuration.registers.get register = 0) :
    Reaches (TotalTwoCounter.step (compile program))
      (encodeConfiguration configuration)
      (encodeConfiguration ⟨zeroTarget, configuration.registers⟩) := by
  let prime := registerPrime register
  let value := encode configuration.registers
  let remainder := value % prime
  let quotient := value / prime
  have primePositive : 0 < prime :=
    Nat.zero_lt_of_lt (registerPrime_large register)
  have remainderPositive : 0 < remainder := by
    exact encode_mod_prime_positive_of_get_zero configuration.registers
      register zero
  have remainderBound : remainder < prime := Nat.mod_lt value primePositive
  have decomposition : remainder + prime * quotient = value := by
    exact Nat.mod_add_div value prime
  have run := decrementBlock_failure primePositive remainderPositive
    remainderBound (realizes_decrementBlock lookup)
    (entry_positive configuration.state)
    (quotient := quotient)
  simpa [encodeConfiguration, prime, value, decomposition] using run

theorem compile_decrement_zero_iteration
    {program : FourCounter.Program} {configuration : FourCounter.Configuration}
    {register : Register} {zeroTarget positiveTarget : Nat}
    (lookup : program configuration.state =
      some (.decrement register zeroTarget positiveTarget))
    (zero : configuration.registers.get register = 0) :
    ∃ fuel, 0 < fuel ∧
      iterate (TotalTwoCounter.step (compile program)) fuel
          (encodeConfiguration configuration) =
        some (encodeConfiguration ⟨zeroTarget, configuration.registers⟩) := by
  let prime := registerPrime register
  let value := encode configuration.registers
  let remainder := value % prime
  let quotient := value / prime
  have primePositive : 0 < prime :=
    Nat.zero_lt_of_lt (registerPrime_large register)
  have remainderPositive : 0 < remainder := by
    exact encode_mod_prime_positive_of_get_zero configuration.registers
      register zero
  have remainderBound : remainder < prime := Nat.mod_lt value primePositive
  have decomposition : remainder + prime * quotient = value := by
    exact Nat.mod_add_div value prime
  have run := decrementBlock_failure_iteration primePositive remainderPositive
    remainderBound (realizes_decrementBlock lookup)
    (entry_positive configuration.state)
    (quotient := quotient)
  simpa [encodeConfiguration, prime, value, decomposition] using run

/-- A positive logical register takes the source positive branch and divides
the prime-exponent code by exactly one assigned prime. -/
theorem compile_decrement_positive
    {program : FourCounter.Program} {configuration : FourCounter.Configuration}
    {register : Register} {zeroTarget positiveTarget : Nat}
    (lookup : program configuration.state =
      some (.decrement register zeroTarget positiveTarget))
    (positive : 0 < configuration.registers.get register) :
    Reaches (TotalTwoCounter.step (compile program))
      (encodeConfiguration configuration)
      (encodeConfiguration
        ⟨positiveTarget, configuration.registers.decrement register⟩) := by
  have run := decrementBlock_success
    (program := program)
    (positivePrime := Nat.zero_lt_of_lt (registerPrime_large register))
    (realizes_decrementBlock lookup)
    (entry_positive configuration.state)
    (quotient := encode (configuration.registers.decrement register))
  have codeEq := encode_decrement_mul_prime configuration.registers register
    positive
  rw [codeEq] at run
  simpa [encodeConfiguration] using run

theorem encoded_increment_distinct
    (configuration : FourCounter.Configuration) (register : Register)
    (target : Nat) :
    encodeConfiguration configuration ≠
      encodeConfiguration
        ⟨target, configuration.registers.increment register⟩ := by
  intro equality
  have codeEquality := congrArg SourceMachine.Configuration.counterOne equality
  have codePositive := encode_positive configuration.registers
  simp [encodeConfiguration, blockConfiguration, encode_increment] at codeEquality
  cases register <;>
    simp [FourCounterEncoding.registerPrime] at codeEquality <;> omega

theorem encoded_decrement_distinct
    (configuration : FourCounter.Configuration) (register : Register)
    (target : Nat) (positive : 0 < configuration.registers.get register) :
    encodeConfiguration configuration ≠
      encodeConfiguration
        ⟨target, configuration.registers.decrement register⟩ := by
  intro equality
  have codeEquality := congrArg SourceMachine.Configuration.counterOne equality
  have reducedPositive := encode_positive (configuration.registers.decrement register)
  have codeEq := encode_decrement_mul_prime configuration.registers register
    positive
  simp [encodeConfiguration, blockConfiguration] at codeEquality
  cases register <;>
    simp [FourCounterEncoding.registerPrime] at codeEq <;> omega

/-- Every successful four-counter step expands to a positive number of
ordinary two-counter steps. -/
theorem compile_step_iteration
    {program : FourCounter.Program}
    {before after : FourCounter.Configuration}
    (stepEq : FourCounter.step program before = some after) :
    ∃ fuel, 0 < fuel ∧
      iterate (TotalTwoCounter.step (compile program)) fuel
          (encodeConfiguration before) = some (encodeConfiguration after) := by
  cases before with
  | mk state registers =>
      cases lookup : program state with
      | none => simp [FourCounter.step, lookup] at stepEq
      | some instruction =>
          cases instruction with
          | increment register target =>
              simp [FourCounter.step, lookup] at stepEq
              subst after
              exact positive_iteration_of_reaches_of_ne
                (compile_increment lookup)
                (encoded_increment_distinct _ register target)
          | decrement register zeroTarget positiveTarget =>
              by_cases zero : registers.get register = 0
              · simp [FourCounter.step, lookup, zero] at stepEq
                subst after
                exact compile_decrement_zero_iteration lookup zero
              · have positive : 0 < registers.get register := by omega
                simp [FourCounter.step, lookup, zero] at stepEq
                subst after
                exact positive_iteration_of_reaches_of_ne
                  (compile_decrement_positive lookup positive)
                  (encoded_decrement_distinct _ register positiveTarget positive)

/-- Every successful four-counter step compiles to a finite two-counter
run between encoded source boundaries. -/
theorem compile_step
    {program : FourCounter.Program}
    {before after : FourCounter.Configuration}
    (stepEq : FourCounter.step program before = some after) :
    Reaches (TotalTwoCounter.step (compile program))
      (encodeConfiguration before) (encodeConfiguration after) := by
  cases before with
  | mk state registers =>
      cases lookup : program state with
      | none => simp [FourCounter.step, lookup] at stepEq
      | some instruction =>
          cases instruction with
          | increment register target =>
              simp [FourCounter.step, lookup] at stepEq
              subst after
              exact compile_increment lookup
          | decrement register zeroTarget positiveTarget =>
              by_cases zero : registers.get register = 0
              · simp [FourCounter.step, lookup, zero] at stepEq
                subst after
                exact compile_decrement_zero lookup zero
              · have positive : 0 < registers.get register := by omega
                simp [FourCounter.step, lookup, zero] at stepEq
                subst after
                exact compile_decrement_positive lookup positive

/-- Compile every step of a finite four-counter run. -/
theorem compile_run
    {program : FourCounter.Program}
    {start finish : FourCounter.Configuration}
    (run : Reaches (FourCounter.step program) start finish) :
    Reaches (TotalTwoCounter.step (compile program))
      (encodeConfiguration start) (encodeConfiguration finish) := by
  induction run with
  | refl => exact .refl _
  | @tail middle finish prefixRun finalStep inductionHypothesis =>
      exact inductionHypothesis.trans (compile_step finalStep)

def TargetHaltsFrom (program : TotalTwoCounter.Program)
    (start : TotalTwoCounter.Configuration) : Prop :=
  ∃ counterZero counterOne,
    Reaches (TotalTwoCounter.step program) start
      (TotalTwoCounter.haltConfiguration counterZero counterOne)

/-- Forward halting preservation, including the final transition from a
missing four-counter instruction to two-counter state zero. -/
theorem sourceHalts_implies_targetHalts
    (program : FourCounter.Program) (start : FourCounter.Configuration) :
    FourCounter.HaltsFrom program start →
      TargetHaltsFrom (compile program) (encodeConfiguration start) := by
  rintro ⟨terminal, sourceRun, terminalStep⟩
  have compiledRun := compile_run sourceRun
  have lookupNone := (FourCounter.terminal_iff_lookup_none program terminal).mp
    terminalStep
  have finalStep := compile_terminal (configuration := terminal) lookupNone
  refine ⟨1, encode terminal.registers, compiledRun.trans ?_⟩
  simpa [TotalTwoCounter.haltConfiguration, blockConfiguration] using
    Reaches.single finalStep

/-- Compile an exact finite source iteration and retain a lower bound on the
target runtime. -/
theorem compile_iterate
    {program : FourCounter.Program}
    {source finish : FourCounter.Configuration} {sourceFuel : Nat}
    (sourceExecution :
      iterate (FourCounter.step program) sourceFuel source = some finish) :
    ∃ targetFuel,
      sourceFuel ≤ targetFuel ∧
      iterate (TotalTwoCounter.step (compile program)) targetFuel
          (encodeConfiguration source) = some (encodeConfiguration finish) := by
  induction sourceFuel generalizing finish with
  | zero =>
      simp [iterate] at sourceExecution
      subst finish
      exact ⟨0, by omega, rfl⟩
  | succ sourceFuel inductionHypothesis =>
      simp only [iterate] at sourceExecution
      cases prefixEq : iterate (FourCounter.step program) sourceFuel source with
      | none => simp [prefixEq] at sourceExecution
      | some middle =>
          have finalStep : FourCounter.step program middle = some finish := by
            simpa [prefixEq] using sourceExecution
          obtain ⟨prefixFuel, prefixBound, compiledPrefix⟩ :=
            inductionHypothesis prefixEq
          obtain ⟨stepFuel, stepPositive, compiledStep⟩ :=
            compile_step_iteration finalStep
          refine ⟨prefixFuel + stepFuel, by omega, ?_⟩
          rw [iterate_add, compiledPrefix]
          simpa using compiledStep

/-- If the partial four-counter run never reaches a terminal state, every
finite exact iteration is defined. -/
theorem source_iterate_exists_of_not_halts
    (program : FourCounter.Program) (start : FourCounter.Configuration)
    (notHalts : ¬FourCounter.HaltsFrom program start) :
    ∀ fuel, ∃ finish,
      iterate (FourCounter.step program) fuel start = some finish := by
  intro fuel
  induction fuel with
  | zero => exact ⟨_, rfl⟩
  | succ fuel inductionHypothesis =>
      obtain ⟨middle, middleExecution⟩ := inductionHypothesis
      cases finalStep : FourCounter.step program middle with
      | none =>
          have middleRun := reaches_iff_exists_iterate.mpr
            ⟨fuel, middleExecution⟩
          exact (notHalts ⟨middle, middleRun, finalStep⟩).elim
      | some finish =>
          refine ⟨finish, ?_⟩
          simp [iterate, middleExecution, finalStep]

/-- The prime-exponent compiler preserves and reflects terminal reachability
from every encoded four-counter configuration. -/
theorem targetHalts_iff_sourceHalts
    (program : FourCounter.Program) (start : FourCounter.Configuration) :
    TargetHaltsFrom (compile program) (encodeConfiguration start) ↔
      FourCounter.HaltsFrom program start := by
  constructor
  · intro targetHalts
    by_cases sourceHalts : FourCounter.HaltsFrom program start
    · exact sourceHalts
    · exfalso
      obtain ⟨counterZero, counterOne, targetRun⟩ := targetHalts
      obtain ⟨haltFuel, haltExecution⟩ :=
        reaches_iff_exists_iterate.mp targetRun
      obtain ⟨sourceFinish, sourceExecution⟩ :=
        source_iterate_exists_of_not_halts program start sourceHalts
          (haltFuel + 1)
      obtain ⟨targetFuel, fuelBound, compiledExecution⟩ :=
        compile_iterate sourceExecution
      have cannotPassHalt := successful_iterations_before_halt
        (step := TotalTwoCounter.step (compile program))
        (haltEq := TotalTwoCounter.step_halt (compile program)
          counterZero counterOne)
        haltExecution compiledExecution
      omega
  · exact sourceHalts_implies_targetHalts program start

end Mortality.SourceMachine.FourCounterToTwoCounter
