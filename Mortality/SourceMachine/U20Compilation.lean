import Mortality.SourceMachine.U20Semantics

/-!
# Executable Minsky compilation of Korec U20 into Ivanov U2

Ivanov describes the standard two-register exponential simulation on printed
pages 98--99 of his 2014 thesis and prints the resulting 278-state program on
pages 128--129.  This file makes that construction executable.  Each simulated
register is assigned one of the first seven primes.  An increment block
multiplies the exponential code by its prime; a decrement block divides when
possible and otherwise restores the input.  The final finite theorem checks
that flattening the twenty blocks gives Ivanov's printed table exactly.
-/

namespace Mortality.SourceMachine.U20Compilation

open Mortality.SourceMachine
open Mortality.SourceMachine.KorecU20

set_option maxRecDepth 100000

/-- Prime assignment chosen in Ivanov's printed construction.  The most
frequently tested registers receive the three smallest primes. -/
def registerPrime : Fin 8 → Nat
  | 0 => 7
  | 1 => 11
  | 2 => 13
  | 3 => 19
  | 4 => 5
  | 5 => 2
  | 6 => 3
  | 7 => 17

/-- Entry address of each compiled U20 instruction.  Stop is U2 state 278. -/
def compiledState : Nat → Nat
  | 0 => 278
  | 1 => 1
  | 3 => 27
  | 4 => 47
  | 6 => 55
  | 7 => 61
  | 9 => 71
  | 10 => 76
  | 12 => 114
  | 13 => 128
  | 14 => 138
  | 15 => 272
  | 16 => 152
  | 18 => 160
  | 20 => 168
  | 22 => 176
  | 23 => 184
  | 27 => 202
  | 30 => 232
  | 31 => 242
  | 32 => 258
  | _ => 278

/-- The source order used by the appendix.  The restorative instruction `q15`
introduced in the `U19`-to-`U20` conversion is placed last. -/
def compilationOrder : List Nat :=
  [1, 3, 4, 6, 7, 9, 10, 12, 13, 14,
    16, 18, 20, 22, 23, 27, 30, 31, 32, 15]

/-- Multiply the first counter by `prime`, using the second as scratch. -/
def incrementBlock (start prime target : Nat) : List RawInstruction :=
  [RawInstruction.dec .zero (start + 1) (start + prime + 1)] ++
    ((List.range prime).map fun offset =>
      RawInstruction.inc .one
        (if offset + 1 = prime then start else start + offset + 2)) ++
    [RawInstruction.dec .one (start + prime + 2) target,
      RawInstruction.inc .zero (start + prime + 1)]

/-- Test divisibility by `prime`.  On success divide by `prime`; on failure
restore the original first counter.  The second counter is zero at both exits. -/
def decrementBlock (start prime positiveTarget zeroTarget : Nat) :
    List RawInstruction :=
  ((List.range prime).map fun offset =>
      RawInstruction.dec .zero (start + offset + 1)
        (if offset = 0 then start + 2 * prime + 2
        else start + 2 * prime + 1 - offset)) ++
    [RawInstruction.inc .one start] ++
    ((List.range prime).map fun offset =>
      RawInstruction.inc .zero (start + prime + offset + 2)) ++
    [RawInstruction.dec .one (start + prime + 1) zeroTarget,
      RawInstruction.dec .one (start + 2 * prime + 3) positiveTarget,
      RawInstruction.inc .zero (start + 2 * prime + 2)]

@[simp] theorem incrementBlock_length (start prime target : Nat) :
    (incrementBlock start prime target).length = prime + 3 := by
  simp [incrementBlock]

@[simp] theorem decrementBlock_length
    (start prime positiveTarget zeroTarget : Nat) :
    (decrementBlock start prime positiveTarget zeroTarget).length =
      2 * prime + 4 := by
  simp [decrementBlock]
  omega

def compileInstruction (state : Nat) : List RawInstruction :=
  match KorecU20.instruction state with
  | some (.increment register target) =>
      incrementBlock (compiledState state) (registerPrime register)
        (compiledState target)
  | some (.decrement register positiveTarget zeroTarget) =>
      decrementBlock (compiledState state) (registerPrime register)
        (compiledState positiveTarget) (compiledState zeroTarget)
  | some .halt | none => []

def compiledTable : List RawInstruction :=
  compilationOrder.flatMap compileInstruction ++ [.halt]

theorem compilationOrder_eq_states :
    compilationOrder.Perm KorecU20.states := by
  decide

theorem compiledTable_length : compiledTable.length = 278 := by
  decide

/-- The executable generic construction is byte-for-byte the printed U2
instruction table already used by the rest of the formalization. -/
theorem compiledTable_eq_u2Table : compiledTable = u2Table := by
  decide

/-- Lookups in the printed table may be replaced by lookups in the structured
compiler output.  This avoids unfolding the 278-line literal table in later
semantic proofs. -/
theorem u2At_eq_compiledTable (state : Nat) :
    u2At state =
      if state = 0 then none else compiledTable[state - 1]? := by
  simp only [u2At]
  rw [compiledTable_eq_u2Table]

theorem compiled_counts :
    instructionCounts compiledTable =
      { incZero := 92, incOne := 73, decZero := 80, decOne := 32 } := by
  decide

end Mortality.SourceMachine.U20Compilation
