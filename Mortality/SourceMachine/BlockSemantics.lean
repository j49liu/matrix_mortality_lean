import Mortality.SourceMachine.U20Compilation

/-!
# Semantic correctness of the generic Minsky blocks

The compiler emits two kinds of finite instruction blocks.  This file proves
their counter-level meaning independently of the twenty concrete source
instructions.  A `RealizesBlock` hypothesis says that a block occupies the
claimed interval of the printed U2 table.  The increment proof below then
shows that the block multiplies counter zero by the assigned prime and
returns counter one to zero.
-/

namespace Mortality.SourceMachine.U20Compilation

open Mortality.SourceMachine

/-- A compact constructor for the configurations used in block proofs. -/
def blockConfiguration (state counterZero counterOne : Nat) : Configuration :=
  { state, counterZero, counterOne }

/-- The U2 table contains `block` starting at the one-based address `start`. -/
def RealizesBlock (start : Nat) (block : List RawInstruction) : Prop :=
  ∀ offset, offset < block.length →
    u2At (start + offset) = block[offset]?

theorem incrementBlock_get_zero (start prime target : Nat) :
    (incrementBlock start prime target)[0]? =
      some (.dec .zero (start + 1) (start + prime + 1)) := by
  simp [incrementBlock]

theorem incrementBlock_get_inc (start prime target offset : Nat)
    (bound : offset < prime) :
    (incrementBlock start prime target)[offset + 1]? =
      some (.inc .one
        (if offset + 1 = prime then start else start + offset + 2)) := by
  simp [incrementBlock, List.getElem?_append, bound]

theorem incrementBlock_get_transfer (start prime target : Nat) :
    (incrementBlock start prime target)[prime + 1]? =
      some (.dec .one (start + prime + 2) target) := by
  simp [incrementBlock]

theorem incrementBlock_get_restore (start prime target : Nat) :
    (incrementBlock start prime target)[prime + 2]? =
      some (.inc .zero (start + prime + 1)) := by
  simp [incrementBlock]

/-- Execute one instruction once its table lookup has been identified. -/
theorem u2Step_of_lookup {configuration : Configuration}
    {instruction : RawInstruction}
    (lookup : u2At configuration.state = some instruction) :
    u2Step configuration = execute instruction configuration := by
  simp [u2Step, lookup]

/-- The consecutive counter-one increments in a multiplication block. -/
theorem incrementBlock_scratchScan
    {start prime target offset remaining x y : Nat}
    (realizes : RealizesBlock start (incrementBlock start prime target))
    (sum : offset + remaining = prime)
    (positiveRemaining : 0 < remaining) :
    Reaches u2Step
      (blockConfiguration (start + offset + 1) x y)
      (blockConfiguration start x (y + remaining)) := by
  induction remaining generalizing offset y with
  | zero => omega
  | succ remaining inductionHypothesis =>
      have offsetBound : offset < prime := by omega
      have blockBound : offset + 1 < (incrementBlock start prime target).length := by
        simp
        omega
      have lookup := realizes (offset + 1) blockBound
      rw [incrementBlock_get_inc start prime target offset offsetBound] at lookup
      by_cases noRemainder : remaining = 0
      · subst remaining
        have last : offset + 1 = prime := by omega
        apply Reaches.single
        rw [u2Step_of_lookup (configuration :=
          blockConfiguration (start + offset + 1) x y) (by simpa [blockConfiguration,
            Nat.add_assoc] using lookup)]
        simp [execute, blockConfiguration, Configuration.readCounter,
          Configuration.setCounter, Configuration.setState, last]
      · have notLast : offset + 1 ≠ prime := by omega
        have firstStep :
            u2Step (blockConfiguration (start + offset + 1) x y) =
              some (blockConfiguration (start + (offset + 1) + 1) x (y + 1)) := by
          rw [u2Step_of_lookup (configuration :=
            blockConfiguration (start + offset + 1) x y) (by simpa [blockConfiguration,
              Nat.add_assoc] using lookup)]
          simp [execute, blockConfiguration, Configuration.readCounter,
            Configuration.setCounter, Configuration.setState, notLast]
          omega
        have suffix := inductionHypothesis (offset := offset + 1) (y := y + 1)
          (by omega) (by omega)
        exact (Reaches.single firstStep).trans (by
          simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using suffix)

/-- One trip around the multiplication loop consumes one unit of counter
zero and adds `prime` units to the scratch counter. -/
theorem incrementBlock_cycle
    {start prime target x y : Nat}
    (positivePrime : 0 < prime)
    (realizes : RealizesBlock start (incrementBlock start prime target)) :
    Reaches u2Step
      (blockConfiguration start (x + 1) y)
      (blockConfiguration start x (y + prime)) := by
  have blockBound : 0 < (incrementBlock start prime target).length := by simp
  have lookup := realizes 0 blockBound
  rw [incrementBlock_get_zero] at lookup
  have firstStep :
      u2Step (blockConfiguration start (x + 1) y) =
        some (blockConfiguration (start + 1) x y) := by
    rw [u2Step_of_lookup (configuration := blockConfiguration start (x + 1) y)
      (by simpa [blockConfiguration] using lookup)]
    simp [execute, blockConfiguration, Configuration.readCounter,
      Configuration.setCounter, Configuration.setState]
  exact (Reaches.single firstStep).trans
    (incrementBlock_scratchScan realizes (offset := 0)
      (remaining := prime) (x := x) (y := y) (by omega) positivePrime)

/-- The multiplication loop consumes the whole first counter. -/
theorem incrementBlock_consume
    {start prime target x y : Nat}
    (positivePrime : 0 < prime)
    (realizes : RealizesBlock start (incrementBlock start prime target)) :
    Reaches u2Step
      (blockConfiguration start x y)
      (blockConfiguration (start + prime + 1) 0 (y + prime * x)) := by
  induction x generalizing y with
  | zero =>
      have blockBound : 0 < (incrementBlock start prime target).length := by simp
      have lookup := realizes 0 blockBound
      rw [incrementBlock_get_zero] at lookup
      apply Reaches.single
      rw [u2Step_of_lookup (configuration := blockConfiguration start 0 y)
        (by simpa [blockConfiguration] using lookup)]
      simp [execute, blockConfiguration, Configuration.readCounter,
        Configuration.setState]
  | succ x inductionHypothesis =>
      exact (incrementBlock_cycle positivePrime realizes (x := x) (y := y)).trans (by
        simpa [Nat.mul_succ, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
          using inductionHypothesis (y := y + prime))

/-- The two-instruction transfer loop moves the scratch counter back to
counter zero and exits to the compiled target. -/
theorem incrementBlock_transfer
    {start prime target x y : Nat}
    (realizes : RealizesBlock start (incrementBlock start prime target)) :
    Reaches u2Step
      (blockConfiguration (start + prime + 1) x y)
      (blockConfiguration target (x + y) 0) := by
  induction y generalizing x with
  | zero =>
      have blockBound : prime + 1 <
          (incrementBlock start prime target).length := by simp
      have lookup := realizes (prime + 1) blockBound
      rw [incrementBlock_get_transfer] at lookup
      apply Reaches.single
      rw [u2Step_of_lookup (configuration :=
        blockConfiguration (start + prime + 1) x 0)
        (by simpa [blockConfiguration, Nat.add_assoc] using lookup)]
      simp [execute, blockConfiguration, Configuration.readCounter,
        Configuration.setState]
  | succ y inductionHypothesis =>
      have transferBound : prime + 1 <
          (incrementBlock start prime target).length := by simp
      have transferLookup := realizes (prime + 1) transferBound
      rw [incrementBlock_get_transfer] at transferLookup
      have transferLookup' :
          u2At (start + prime + 1) =
            some (.dec .one (start + prime + 2) target) := by
        simpa only [Nat.add_assoc] using transferLookup
      have firstStep :
          u2Step (blockConfiguration (start + prime + 1) x (y + 1)) =
            some (blockConfiguration (start + prime + 2) x y) := by
        rw [u2Step_of_lookup (configuration :=
          blockConfiguration (start + prime + 1) x (y + 1))
          transferLookup']
        simp [execute, blockConfiguration, Configuration.readCounter,
          Configuration.setCounter, Configuration.setState]
      have restoreBound : prime + 2 <
          (incrementBlock start prime target).length := by simp
      have restoreLookup := realizes (prime + 2) restoreBound
      rw [incrementBlock_get_restore] at restoreLookup
      have restoreLookup' :
          u2At (start + prime + 2) =
            some (.inc .zero (start + prime + 1)) := by
        simpa only [Nat.add_assoc] using restoreLookup
      have secondStep :
          u2Step (blockConfiguration (start + prime + 2) x y) =
            some (blockConfiguration (start + prime + 1) (x + 1) y) := by
        rw [u2Step_of_lookup (configuration :=
          blockConfiguration (start + prime + 2) x y)
          restoreLookup']
        simp [execute, blockConfiguration, Configuration.readCounter,
          Configuration.setCounter, Configuration.setState]
      exact (Reaches.single firstStep).trans <|
        (Reaches.single secondStep).trans (by
          simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
            using inductionHypothesis (x := x + 1))

/-- Semantic correctness of every realized increment block. -/
theorem incrementBlock_correct
    {start prime target input : Nat}
    (positivePrime : 0 < prime)
    (realizes : RealizesBlock start (incrementBlock start prime target)) :
    Reaches u2Step
      (blockConfiguration start input 0)
      (blockConfiguration target (prime * input) 0) := by
  exact (incrementBlock_consume positivePrime realizes (x := input) (y := 0)).trans (by
    simpa using incrementBlock_transfer realizes
      (x := 0) (y := prime * input))

theorem decrementBlock_get_test
    (start prime positiveTarget zeroTarget offset : Nat)
    (bound : offset < prime) :
    (decrementBlock start prime positiveTarget zeroTarget)[offset]? =
      some (.dec .zero (start + offset + 1)
        (if offset = 0 then start + 2 * prime + 2
        else start + 2 * prime + 1 - offset)) := by
  simp [decrementBlock, List.getElem?_append, bound]

theorem decrementBlock_get_scratch
    (start prime positiveTarget zeroTarget : Nat) :
    (decrementBlock start prime positiveTarget zeroTarget)[prime]? =
      some (.inc .one start) := by
  simp [decrementBlock]

theorem decrementBlock_get_restoreInc
    (start prime positiveTarget zeroTarget offset : Nat)
    (bound : offset < prime) :
    (decrementBlock start prime positiveTarget zeroTarget)[prime + 1 + offset]? =
      some (.inc .zero (start + prime + offset + 2)) := by
  simp only [decrementBlock, List.getElem?_append, List.length_map,
    List.length_range, List.length_append, List.length_cons, List.length_nil]
  rw [if_pos (by omega)]
  rw [if_neg (by omega)]
  simp [bound]

theorem decrementBlock_get_failureTransfer
    (start prime positiveTarget zeroTarget : Nat) :
    (decrementBlock start prime positiveTarget zeroTarget)[2 * prime + 1]? =
      some (.dec .one (start + prime + 1) zeroTarget) := by
  simp only [decrementBlock, List.getElem?_append, List.length_map,
    List.length_range, List.length_append, List.length_cons, List.length_nil]
  rw [if_neg (by omega)]
  have indexEq : 2 * prime + 1 - (prime + 1 + prime) = 0 := by omega
  rw [indexEq]
  rfl

theorem decrementBlock_get_successTransfer
    (start prime positiveTarget zeroTarget : Nat) :
    (decrementBlock start prime positiveTarget zeroTarget)[2 * prime + 2]? =
      some (.dec .one (start + 2 * prime + 3) positiveTarget) := by
  simp only [decrementBlock, List.getElem?_append, List.length_map,
    List.length_range, List.length_append, List.length_cons, List.length_nil]
  rw [if_neg (by omega)]
  have indexEq : 2 * prime + 2 - (prime + 1 + prime) = 1 := by omega
  rw [indexEq]
  rfl

theorem decrementBlock_get_successRestore
    (start prime positiveTarget zeroTarget : Nat) :
    (decrementBlock start prime positiveTarget zeroTarget)[2 * prime + 3]? =
      some (.inc .zero (start + 2 * prime + 2)) := by
  simp only [decrementBlock, List.getElem?_append, List.length_map,
    List.length_range, List.length_append, List.length_cons, List.length_nil]
  rw [if_neg (by omega)]
  have indexEq : 2 * prime + 3 - (prime + 1 + prime) = 2 := by omega
  rw [indexEq]
  rfl

/-- A positive prefix of the divisibility test consumes the requested number
of counter-zero units. -/
theorem decrementBlock_positivePrefix
    {start prime positiveTarget zeroTarget offset count x y : Nat}
    (realizes : RealizesBlock start
      (decrementBlock start prime positiveTarget zeroTarget))
    (within : offset + count ≤ prime) :
    Reaches u2Step
      (blockConfiguration (start + offset) (x + count) y)
      (blockConfiguration (start + offset + count) x y) := by
  induction count generalizing offset x with
  | zero =>
      simpa using Reaches.refl
        (blockConfiguration (start + offset) x y)
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
          u2Step (blockConfiguration (start + offset) (x + (count + 1)) y) =
            some (blockConfiguration (start + (offset + 1)) (x + count) y) := by
        rw [u2Step_of_lookup (configuration :=
          blockConfiguration (start + offset) (x + (count + 1)) y)
          (by simpa [blockConfiguration] using lookup)]
        simp [execute, blockConfiguration, Configuration.readCounter,
          Configuration.setCounter, Configuration.setState]
        omega
      have suffix := inductionHypothesis (offset := offset + 1) (x := x)
        (by omega)
      exact (Reaches.single (by simpa [Nat.add_assoc] using firstStep)).trans (by
        simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using suffix)

/-- One complete divisibility-test cycle subtracts `prime` and records one
unit in the scratch counter. -/
theorem decrementBlock_cycle
    {start prime positiveTarget zeroTarget x y : Nat}
    (positivePrime : 0 < prime)
    (realizes : RealizesBlock start
      (decrementBlock start prime positiveTarget zeroTarget)) :
    Reaches u2Step
      (blockConfiguration start (x + prime) y)
      (blockConfiguration start x (y + 1)) := by
  have scan := decrementBlock_positivePrefix realizes
    (offset := 0) (count := prime) (x := x) (y := y) (by omega)
  have blockBound : prime <
      (decrementBlock start prime positiveTarget zeroTarget).length := by
    simp
    omega
  have lookup := realizes prime blockBound
  rw [decrementBlock_get_scratch] at lookup
  have scratchStep :
      u2Step (blockConfiguration (start + prime) x y) =
        some (blockConfiguration start x (y + 1)) := by
    rw [u2Step_of_lookup (configuration :=
      blockConfiguration (start + prime) x y)
      (by simpa [blockConfiguration] using lookup)]
    simp [execute, blockConfiguration, Configuration.readCounter,
      Configuration.setCounter, Configuration.setState]
  have scan' : Reaches u2Step
      (blockConfiguration start (x + prime) y)
      (blockConfiguration (start + prime) x y) := by
    simpa using scan
  exact scan'.trans (Reaches.single scratchStep)

/-- Consume `quotient` complete groups, leaving the remainder at the entry
test and accumulating the quotient in counter one. -/
theorem decrementBlock_consumeGroups
    {start prime positiveTarget zeroTarget quotient remainder scratch : Nat}
    (positivePrime : 0 < prime)
    (realizes : RealizesBlock start
      (decrementBlock start prime positiveTarget zeroTarget)) :
    Reaches u2Step
      (blockConfiguration start (remainder + prime * quotient) scratch)
      (blockConfiguration start remainder (scratch + quotient)) := by
  induction quotient generalizing scratch with
  | zero => exact .refl _
  | succ quotient inductionHypothesis =>
      have cycle := decrementBlock_cycle positivePrime realizes
        (x := remainder + prime * quotient) (y := scratch)
      have cycle' : Reaches u2Step
          (blockConfiguration start
            (remainder + prime * (quotient + 1)) scratch)
          (blockConfiguration start (remainder + prime * quotient)
            (scratch + 1)) := by
        simpa [Nat.mul_succ, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
          using cycle
      exact cycle'.trans (by
        simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
          using inductionHypothesis (scratch := scratch + 1))

/-- The exact-division transfer moves the quotient back to counter zero. -/
theorem decrementBlock_successTransfer
    {start prime positiveTarget zeroTarget x y : Nat}
    (realizes : RealizesBlock start
      (decrementBlock start prime positiveTarget zeroTarget)) :
    Reaches u2Step
      (blockConfiguration (start + 2 * prime + 2) x y)
      (blockConfiguration positiveTarget (x + y) 0) := by
  induction y generalizing x with
  | zero =>
      have blockBound : 2 * prime + 2 <
          (decrementBlock start prime positiveTarget zeroTarget).length := by
        simp
      have lookup := realizes (2 * prime + 2) blockBound
      rw [decrementBlock_get_successTransfer] at lookup
      apply Reaches.single
      rw [u2Step_of_lookup (configuration :=
        blockConfiguration (start + 2 * prime + 2) x 0)
        (by simpa [blockConfiguration, Nat.add_assoc] using lookup)]
      simp [execute, blockConfiguration, Configuration.readCounter,
        Configuration.setState]
  | succ y inductionHypothesis =>
      have transferBound : 2 * prime + 2 <
          (decrementBlock start prime positiveTarget zeroTarget).length := by
        simp
      have transferLookup := realizes (2 * prime + 2) transferBound
      rw [decrementBlock_get_successTransfer] at transferLookup
      have transferLookup' :
          u2At (start + 2 * prime + 2) =
            some (.dec .one (start + 2 * prime + 3) positiveTarget) := by
        simpa only [Nat.add_assoc] using transferLookup
      have firstStep :
          u2Step (blockConfiguration (start + 2 * prime + 2) x (y + 1)) =
            some (blockConfiguration (start + 2 * prime + 3) x y) := by
        rw [u2Step_of_lookup (configuration :=
          blockConfiguration (start + 2 * prime + 2) x (y + 1))
          transferLookup']
        simp [execute, blockConfiguration, Configuration.readCounter,
          Configuration.setCounter, Configuration.setState]
      have restoreBound : 2 * prime + 3 <
          (decrementBlock start prime positiveTarget zeroTarget).length := by
        simp
      have restoreLookup := realizes (2 * prime + 3) restoreBound
      rw [decrementBlock_get_successRestore] at restoreLookup
      have restoreLookup' :
          u2At (start + 2 * prime + 3) =
            some (.inc .zero (start + 2 * prime + 2)) := by
        simpa only [Nat.add_assoc] using restoreLookup
      have secondStep :
          u2Step (blockConfiguration (start + 2 * prime + 3) x y) =
            some (blockConfiguration (start + 2 * prime + 2) (x + 1) y) := by
        rw [u2Step_of_lookup (configuration :=
          blockConfiguration (start + 2 * prime + 3) x y)
          restoreLookup']
        simp [execute, blockConfiguration, Configuration.readCounter,
          Configuration.setCounter, Configuration.setState]
      exact (Reaches.single firstStep).trans <|
        (Reaches.single secondStep).trans (by
          simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
            using inductionHypothesis (x := x + 1))

/-- If the tested value is an exact multiple of `prime`, the block divides
it and takes the positive branch. -/
theorem decrementBlock_success
    {start prime positiveTarget zeroTarget quotient : Nat}
    (positivePrime : 0 < prime)
    (realizes : RealizesBlock start
      (decrementBlock start prime positiveTarget zeroTarget)) :
    Reaches u2Step
      (blockConfiguration start (prime * quotient) 0)
      (blockConfiguration positiveTarget quotient 0) := by
  have consume := decrementBlock_consumeGroups positivePrime realizes
    (quotient := quotient) (remainder := 0) (scratch := 0)
  have entryBound : 0 <
      (decrementBlock start prime positiveTarget zeroTarget).length := by simp
  have entryLookup := realizes 0 entryBound
  rw [decrementBlock_get_test start prime positiveTarget zeroTarget 0 positivePrime]
    at entryLookup
  have zeroStep :
      u2Step (blockConfiguration start 0 quotient) =
        some (blockConfiguration (start + 2 * prime + 2) 0 quotient) := by
    rw [u2Step_of_lookup (configuration :=
      blockConfiguration start 0 quotient)
      (by simpa [blockConfiguration] using entryLookup)]
    simp [execute, blockConfiguration, Configuration.readCounter,
      Configuration.setState]
  have consume' : Reaches u2Step
      (blockConfiguration start (prime * quotient) 0)
      (blockConfiguration start 0 quotient) := by
    simpa [Nat.add_comm] using consume
  exact consume'.trans <| (Reaches.single zeroStep).trans (by
      simpa using decrementBlock_successTransfer realizes
        (x := 0) (y := quotient))

/-- Restore a nonzero remainder after its first failing zero branch. -/
theorem decrementBlock_restoreRemainder
    {start prime positiveTarget zeroTarget offset remaining x y : Nat}
    (realizes : RealizesBlock start
      (decrementBlock start prime positiveTarget zeroTarget))
    (sum : offset + remaining = prime) :
    Reaches u2Step
      (blockConfiguration (start + prime + 1 + offset) x y)
      (blockConfiguration (start + 2 * prime + 1) (x + remaining) y) := by
  induction remaining generalizing offset x with
  | zero =>
      have stateEq : start + prime + 1 + offset =
          start + 2 * prime + 1 := by omega
      simpa [stateEq] using Reaches.refl
        (blockConfiguration (start + 2 * prime + 1) x y)
  | succ remaining inductionHypothesis =>
      have offsetBound : offset < prime := by omega
      have blockBound : prime + 1 + offset <
          (decrementBlock start prime positiveTarget zeroTarget).length := by
        simp
        omega
      have lookup := realizes (prime + 1 + offset) blockBound
      rw [decrementBlock_get_restoreInc start prime positiveTarget zeroTarget
        offset offsetBound] at lookup
      have firstStep :
          u2Step (blockConfiguration (start + prime + 1 + offset) x y) =
            some (blockConfiguration (start + prime + 1 + (offset + 1))
              (x + 1) y) := by
        rw [u2Step_of_lookup (configuration :=
          blockConfiguration (start + prime + 1 + offset) x y)
          (by simpa [blockConfiguration, Nat.add_assoc] using lookup)]
        simp [execute, blockConfiguration, Configuration.readCounter,
          Configuration.setCounter, Configuration.setState]
        omega
      exact (Reaches.single firstStep).trans (by
        simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
          using inductionHypothesis (offset := offset + 1) (x := x + 1)
            (by omega))

/-- The failure-side loop restores `prime` units for every complete group
previously recorded in counter one, then takes the zero branch. -/
theorem decrementBlock_failureTransfer
    {start prime positiveTarget zeroTarget x y : Nat}
    (realizes : RealizesBlock start
      (decrementBlock start prime positiveTarget zeroTarget)) :
    Reaches u2Step
      (blockConfiguration (start + 2 * prime + 1) x y)
      (blockConfiguration zeroTarget (x + prime * y) 0) := by
  induction y generalizing x with
  | zero =>
      have blockBound : 2 * prime + 1 <
          (decrementBlock start prime positiveTarget zeroTarget).length := by
        simp
      have lookup := realizes (2 * prime + 1) blockBound
      rw [decrementBlock_get_failureTransfer] at lookup
      apply Reaches.single
      rw [u2Step_of_lookup (configuration :=
        blockConfiguration (start + 2 * prime + 1) x 0)
        (by simpa [blockConfiguration, Nat.add_assoc] using lookup)]
      simp [execute, blockConfiguration, Configuration.readCounter,
        Configuration.setState]
  | succ y inductionHypothesis =>
      have transferBound : 2 * prime + 1 <
          (decrementBlock start prime positiveTarget zeroTarget).length := by
        simp
      have transferLookup := realizes (2 * prime + 1) transferBound
      rw [decrementBlock_get_failureTransfer] at transferLookup
      have transferLookup' :
          u2At (start + 2 * prime + 1) =
            some (.dec .one (start + prime + 1) zeroTarget) := by
        simpa only [Nat.add_assoc] using transferLookup
      have firstStep :
          u2Step (blockConfiguration (start + 2 * prime + 1) x (y + 1)) =
            some (blockConfiguration (start + prime + 1) x y) := by
        rw [u2Step_of_lookup (configuration :=
          blockConfiguration (start + 2 * prime + 1) x (y + 1))
          transferLookup']
        simp [execute, blockConfiguration, Configuration.readCounter,
          Configuration.setCounter, Configuration.setState]
      have restore := decrementBlock_restoreRemainder realizes
        (offset := 0) (remaining := prime) (x := x) (y := y) (by omega)
      have restore' : Reaches u2Step
          (blockConfiguration (start + prime + 1) x y)
          (blockConfiguration (start + 2 * prime + 1) (x + prime) y) := by
        simpa using restore
      exact (Reaches.single firstStep).trans <| restore'.trans (by
        simpa [Nat.mul_succ, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
          using inductionHypothesis (x := x + prime))

/-- If the tested value has a nonzero remainder, the block restores it
exactly and takes the zero branch. -/
theorem decrementBlock_failure
    {start prime positiveTarget zeroTarget quotient remainder : Nat}
    (positivePrime : 0 < prime)
    (positiveRemainder : 0 < remainder)
    (remainderBound : remainder < prime)
    (realizes : RealizesBlock start
      (decrementBlock start prime positiveTarget zeroTarget)) :
    Reaches u2Step
      (blockConfiguration start (remainder + prime * quotient) 0)
      (blockConfiguration zeroTarget (remainder + prime * quotient) 0) := by
  have consume := decrementBlock_consumeGroups positivePrime realizes
    (quotient := quotient) (remainder := remainder) (scratch := 0)
  have prefixRun := decrementBlock_positivePrefix realizes
    (offset := 0) (count := remainder) (x := 0) (y := quotient)
    (by omega)
  have testBound : remainder <
      (decrementBlock start prime positiveTarget zeroTarget).length := by
    simp
    omega
  have testLookup := realizes remainder testBound
  rw [decrementBlock_get_test start prime positiveTarget zeroTarget remainder
    remainderBound] at testLookup
  have nonzeroOffset : remainder ≠ 0 := by omega
  have failureStep :
      u2Step (blockConfiguration (start + remainder) 0 quotient) =
        some (blockConfiguration (start + 2 * prime + 1 - remainder)
          0 quotient) := by
    rw [u2Step_of_lookup (configuration :=
      blockConfiguration (start + remainder) 0 quotient)
      (by simpa [blockConfiguration] using testLookup)]
    simp [execute, blockConfiguration, Configuration.readCounter,
      Configuration.setState, nonzeroOffset]
  have restore := decrementBlock_restoreRemainder realizes
    (offset := prime - remainder) (remaining := remainder)
    (x := 0) (y := quotient) (by omega)
  have transfer := decrementBlock_failureTransfer realizes
    (x := remainder) (y := quotient)
  have consume' : Reaches u2Step
      (blockConfiguration start (remainder + prime * quotient) 0)
      (blockConfiguration start remainder quotient) := by
    simpa using consume
  have prefixRun' : Reaches u2Step
      (blockConfiguration start remainder quotient)
      (blockConfiguration (start + remainder) 0 quotient) := by
    simpa using prefixRun
  have restore' : Reaches u2Step
      (blockConfiguration (start + 2 * prime + 1 - remainder) 0 quotient)
      (blockConfiguration (start + 2 * prime + 1) remainder quotient) := by
      have startEq : start + 2 * prime + 1 - remainder =
          start + prime + 1 + (prime - remainder) := by omega
      simpa [startEq] using restore
  exact consume'.trans <| prefixRun'.trans <|
    (Reaches.single failureStep).trans <| restore'.trans (by simpa using transfer)

end Mortality.SourceMachine.U20Compilation
