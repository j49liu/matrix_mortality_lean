import Mortality.SourceMachine.R2Embedding

/-!
# A finite program for Korec's entry chain

Korec's arithmetic construction chooses `3m + 1` control labels.  Every
successive group of four labels describes one register-preserving `GOTO`:
increment both registers, decrement the first, and decrement the second.  This
file turns such a label sequence into an executable finite R2 entry program.

The only separation hypothesis is injectivity of the label sequence.  The
later arithmetic construction obtains it from strict increase.
-/

namespace Mortality.SourceMachine.KorecEntryProgram

open Mortality.SourceMachine
open Mortality.SourceMachine.KorecR2
open Mortality.SourceMachine.R2Embedding

/-- Install `macroCount` consecutive three-instruction `GOTO` macros.  The
recursive tail sees the label sequence shifted by three positions. -/
def entryProgram : (Nat → Nat) → Nat → KorecR2.Program
  | _, 0 => fun _ => none
  | labels, macroCount + 1 => fun state =>
      if state = labels 0 then some (.incrementBoth (labels 1))
      else if state = labels 1 then some (.decrement .zero (labels 2))
      else if state = labels 2 then some (.decrement .one (labels 3))
      else entryProgram (fun position => labels (position + 3)) macroCount state

/-- Every block of an injectively labelled entry program has its three
advertised instruction lookups. -/
theorem entryProgram_lookups
    {labels : Nat → Nat} {macroCount index : Nat}
    (labelsInjective : Function.Injective labels)
    (indexBound : index < macroCount) :
    entryProgram labels macroCount (labels (3 * index)) =
        some (.incrementBoth (labels (3 * index + 1))) ∧
      entryProgram labels macroCount (labels (3 * index + 1)) =
        some (.decrement .zero (labels (3 * index + 2))) ∧
      entryProgram labels macroCount (labels (3 * index + 2)) =
        some (.decrement .one (labels (3 * index + 3))) := by
  induction macroCount generalizing labels index with
  | zero => omega
  | succ macroCount inductionHypothesis =>
      cases index with
      | zero =>
          have labelOneNeZero : labels 1 ≠ labels 0 := by
            intro equality
            have := labelsInjective equality
            omega
          have labelTwoNeZero : labels 2 ≠ labels 0 := by
            intro equality
            have := labelsInjective equality
            omega
          have labelTwoNeOne : labels 2 ≠ labels 1 := by
            intro equality
            have := labelsInjective equality
            omega
          simp [entryProgram, labelOneNeZero, labelTwoNeZero, labelTwoNeOne]
      | succ index =>
          have indexBound' : index < macroCount := by omega
          let shifted : Nat → Nat := fun position => labels (position + 3)
          have shiftedInjective : Function.Injective shifted := by
            intro left right equality
            have := labelsInjective equality
            omega
          have tail := inductionHypothesis shiftedInjective indexBound'
          have startNeZero : labels (3 + 3 * index) ≠ labels 0 := by
            intro equality
            have := labelsInjective equality
            omega
          have startNeOne : labels (3 + 3 * index) ≠ labels 1 := by
            intro equality
            have := labelsInjective equality
            omega
          have startNeTwo : labels (3 + 3 * index) ≠ labels 2 := by
            intro equality
            have := labelsInjective equality
            omega
          have middleZeroNeZero :
              labels (1 + (3 + 3 * index)) ≠ labels 0 := by
            intro equality
            have := labelsInjective equality
            omega
          have middleZeroNeOne :
              labels (1 + (3 + 3 * index)) ≠ labels 1 := by
            intro equality
            have := labelsInjective equality
            omega
          have middleZeroNeTwo :
              labels (1 + (3 + 3 * index)) ≠ labels 2 := by
            intro equality
            have := labelsInjective equality
            omega
          have middleOneNeZero :
              labels (2 + (3 + 3 * index)) ≠ labels 0 := by
            intro equality
            have := labelsInjective equality
            omega
          have middleOneNeOne :
              labels (2 + (3 + 3 * index)) ≠ labels 1 := by
            intro equality
            have := labelsInjective equality
            omega
          have middleOneNeTwo :
              labels (2 + (3 + 3 * index)) ≠ labels 2 := by
            intro equality
            have := labelsInjective equality
            omega
          simpa [entryProgram, shifted, startNeZero, startNeOne, startNeTwo,
            middleZeroNeZero, middleZeroNeOne, middleZeroNeTwo,
            middleOneNeZero, middleOneNeOne, middleOneNeTwo,
            Nat.mul_succ, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
            using tail

/-- Each block of a positive injective label sequence is an installed
register-preserving `GOTO`. -/
theorem entryProgram_gotoInstalled
    {labels : Nat → Nat} {macroCount index : Nat}
    (labelsInjective : Function.Injective labels)
    (labelsPositive : ∀ position, position < 3 * macroCount →
      0 < labels position)
    (indexBound : index < macroCount) :
    GotoInstalled (entryProgram labels macroCount)
      (labels (3 * index))
      (labels (3 * index + 1))
      (labels (3 * index + 2))
      (labels (3 * index + 3)) := by
  have lookups := entryProgram_lookups labelsInjective indexBound
  exact
    { startPositive := labelsPositive (3 * index) (by omega)
      afterIncrementPositive := labelsPositive (3 * index + 1) (by omega)
      afterFirstDecrementPositive := labelsPositive (3 * index + 2) (by omega)
      incrementLookup := lookups.1
      firstDecrementLookup := lookups.2.1
      secondDecrementLookup := lookups.2.2 }

/-- A finite injective label plan lying in the reserved prefix gives the
general entry-correctness premise for the embedded source program. -/
theorem entryCorrect
    {offset macroCount : Nat} {source : KorecR2.Program}
    {labels : Nat → Nat}
    (labelsInjective : Function.Injective labels)
    (labelsPositive : ∀ position, position < 3 * macroCount →
      0 < labels position)
    (labelsReserved : ∀ position, position < 3 * macroCount →
      labels position ≤ offset)
    (start : labels 0 = 1)
    (finish : labels (3 * macroCount) = offset + 1) :
    EntryCorrect offset (entryProgram labels macroCount) source := by
  apply entryCorrect_of_indexed_gotos labels start finish
  intro index indexBound
  have installed := entryProgram_gotoInstalled labelsInjective labelsPositive
    indexBound
  refine
    { startPositive := installed.startPositive
      afterIncrementPositive := installed.afterIncrementPositive
      afterFirstDecrementPositive := installed.afterFirstDecrementPositive
      incrementLookup := ?_
      firstDecrementLookup := ?_
      secondDecrementLookup := ?_ }
  · simp [embed, Nat.ne_of_gt installed.startPositive,
      labelsReserved (3 * index) (by omega), installed.incrementLookup]
  · simp [embed, Nat.ne_of_gt installed.afterIncrementPositive,
      labelsReserved (3 * index + 1) (by omega),
      installed.firstDecrementLookup]
  · simp [embed, Nat.ne_of_gt installed.afterFirstDecrementPositive,
      labelsReserved (3 * index + 2) (by omega),
      installed.secondDecrementLookup]

end Mortality.SourceMachine.KorecEntryProgram
