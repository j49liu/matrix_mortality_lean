import Mortality.SourceMachine.R2Relocation

/-!
# Embedding an R2 program behind a certified entry program

Korec's numerical program-code construction does not generally enter a
relocated source program through three consecutive control labels.  It uses a
finite chain of register-preserving jumps whose labels are chosen together
with the nondivisors of the program number.  This file separates that entry
chain from the source relocation.

An arbitrary program supplies the reserved labels through `offset`.  Above
that boundary, every positive source label is shifted by `offset`, while
source state zero remains halt.  The sole semantic hypothesis on the entry
program is the one needed later: from state one it reaches shifted source
state one without changing either register, for all register values.  Under
that hypothesis, embedding preserves and reflects halting exactly.
-/

namespace Mortality.SourceMachine.R2Embedding

open Mortality.SourceMachine
open Mortality.SourceMachine.KorecR2
open Mortality.SourceMachine.R2Relocation
open Mortality.SourceMachine.U20Compilation

/-- Overlay `entry` on the reserved positive labels at most `offset`, and put
the shifted source program strictly above that interval. -/
def embed (offset : Nat) (entry source : KorecR2.Program) : KorecR2.Program :=
  fun state =>
    if state = 0 then none
    else if state ≤ offset then entry state
    else (source (state - offset)).map (shiftInstruction offset)

@[simp] theorem embed_zero (offset : Nat) (entry source : KorecR2.Program) :
    embed offset entry source 0 = none := by
  simp [embed]

@[simp] theorem embed_shifted_positive
    (offset : Nat) (entry source : KorecR2.Program) (state : Nat)
    (offsetPositive : 0 < offset) :
    embed offset entry source (shiftState offset (state + 1)) =
      (source (state + 1)).map (shiftInstruction offset) := by
  simp only [shiftState_succ, embed]
  rw [if_neg (by omega : offset + state + 1 ≠ 0)]
  rw [if_neg (by omega : ¬offset + state + 1 ≤ offset)]
  congr 2
  omega

/-- The reserved entry code reaches shifted source state one without
changing the two data registers.  The property is uniform in their values. -/
def EntryCorrect (offset : Nat) (entry source : KorecR2.Program) : Prop :=
  ∀ registerZero registerTwo,
    Reaches (KorecR2.step (embed offset entry source))
      { state := 1
        registerZero := registerZero
        registerTwo := registerTwo }
      { state := offset + 1
        registerZero := registerZero
        registerTwo := registerTwo }

/-- Three installed R2 instructions implementing one unconditional,
register-preserving control transfer. -/
structure GotoInstalled (program : KorecR2.Program)
    (start afterIncrement afterFirstDecrement target : Nat) : Prop where
  startPositive : 0 < start
  afterIncrementPositive : 0 < afterIncrement
  afterFirstDecrementPositive : 0 < afterFirstDecrement
  incrementLookup :
    program start = some (.incrementBoth afterIncrement)
  firstDecrementLookup :
    program afterIncrement =
      some (.decrement .zero afterFirstDecrement)
  secondDecrementLookup :
    program afterFirstDecrement = some (.decrement .one target)

/-- A finite chain of register-preserving `GOTO` macros.  Its labels need not
be consecutive; Korec chooses them from nondivisor ranks. -/
inductive EntryChain (program : KorecR2.Program) : Nat → Nat → Prop where
  | refl (state : Nat) : EntryChain program state state
  | goto {start afterIncrement afterFirstDecrement next finish : Nat}
      (installed : GotoInstalled program start afterIncrement
        afterFirstDecrement next)
      (suffix : EntryChain program next finish) :
      EntryChain program start finish

/-- One installed `GOTO` macro leaves both registers unchanged. -/
theorem goto_reaches
    {program : KorecR2.Program}
    {start afterIncrement afterFirstDecrement target : Nat}
    (installed : GotoInstalled program start afterIncrement
      afterFirstDecrement target)
    (registerZero registerTwo : Nat) :
    Reaches (KorecR2.step program)
      { state := start
        registerZero := registerZero
        registerTwo := registerTwo }
      { state := target
        registerZero := registerZero
        registerTwo := registerTwo } := by
  have first : KorecR2.step program
      { state := start
        registerZero := registerZero
        registerTwo := registerTwo } =
      some
        { state := afterIncrement
          registerZero := registerZero + 1
          registerTwo := registerTwo + 1 } := by
    exact KorecR2.step_incrementBoth installed.startPositive
      installed.incrementLookup
  have second : KorecR2.step program
      { state := afterIncrement
        registerZero := registerZero + 1
        registerTwo := registerTwo + 1 } =
      some
        { state := afterFirstDecrement
          registerZero := registerZero
          registerTwo := registerTwo + 1 } := by
    exact KorecR2.step_decrement_zero_positive
      installed.afterIncrementPositive installed.firstDecrementLookup
  have third : KorecR2.step program
      { state := afterFirstDecrement
        registerZero := registerZero
        registerTwo := registerTwo + 1 } =
      some
        { state := target
          registerZero := registerZero
          registerTwo := registerTwo } := by
    exact KorecR2.step_decrement_two_positive
      installed.afterFirstDecrementPositive
      installed.secondDecrementLookup
  exact (Reaches.single first).trans <|
    (Reaches.single second).trans (Reaches.single third)

/-- Every finite chain of installed `GOTO` macros preserves both registers. -/
theorem entryChain_reaches
    {program : KorecR2.Program} {start finish : Nat}
    (chain : EntryChain program start finish)
    (registerZero registerTwo : Nat) :
    Reaches (KorecR2.step program)
      { state := start
        registerZero := registerZero
        registerTwo := registerTwo }
      { state := finish
        registerZero := registerZero
        registerTwo := registerTwo } := by
  induction chain with
  | refl state => exact .refl _
  | goto installed suffix inductionHypothesis =>
      exact (goto_reaches installed registerZero registerTwo).trans
        inductionHypothesis

/-- A sequence indexed in blocks of three supplies an `EntryChain`.  This is
the form used by Korec: the labels at positions `3i`, `3i+1`, and `3i+2`
implement one register-preserving jump to the label at position `3i+3`. -/
theorem entryChain_of_indexed_gotos
    {program : KorecR2.Program} (labels : Nat → Nat) :
    ∀ macroCount,
      (∀ index, index < macroCount →
        GotoInstalled program
          (labels (3 * index))
          (labels (3 * index + 1))
          (labels (3 * index + 2))
          (labels (3 * index + 3))) →
      EntryChain program (labels 0) (labels (3 * macroCount)) := by
  intro macroCount
  induction macroCount generalizing labels with
  | zero =>
      intro _
      exact .refl _
  | succ macroCount inductionHypothesis =>
      intro installed
      have first := installed 0 (by omega)
      let shifted : Nat → Nat := fun position => labels (position + 3)
      have shiftedInstalled : ∀ index, index < macroCount →
          GotoInstalled program
            (shifted (3 * index))
            (shifted (3 * index + 1))
            (shifted (3 * index + 2))
            (shifted (3 * index + 3)) := by
        intro index indexBound
        simpa [shifted, Nat.mul_succ, Nat.add_assoc, Nat.add_comm,
          Nat.add_left_comm] using installed (index + 1) (by omega)
      have suffix := inductionHypothesis shifted shiftedInstalled
      have suffix' :
          EntryChain program (labels 3) (labels (3 * (macroCount + 1))) := by
        simpa [shifted, Nat.mul_succ, Nat.add_assoc, Nat.add_comm,
          Nat.add_left_comm] using suffix
      exact .goto first suffix'

/-- Indexed concrete `GOTO` lookups discharge the general semantic entry
condition. The number of entry instructions is three times `macroCount`. -/
theorem entryCorrect_of_indexed_gotos
    {offset macroCount : Nat} {entry source : KorecR2.Program}
    (labels : Nat → Nat)
    (start : labels 0 = 1)
    (finish : labels (3 * macroCount) = offset + 1)
    (installed : ∀ index, index < macroCount →
      GotoInstalled (embed offset entry source)
        (labels (3 * index))
        (labels (3 * index + 1))
        (labels (3 * index + 2))
        (labels (3 * index + 3))) :
    EntryCorrect offset entry source := by
  have chain := entryChain_of_indexed_gotos labels macroCount installed
  rw [start, finish] at chain
  intro registerZero registerTwo
  exact entryChain_reaches chain registerZero registerTwo

/-- An installed chain from state one to the shifted source entry discharges
the semantic entry-correctness condition. -/
theorem entryCorrect_of_chain
    {offset : Nat} {entry source : KorecR2.Program}
    (chain : EntryChain (embed offset entry source) 1 (offset + 1)) :
    EntryCorrect offset entry source := by
  intro registerZero registerTwo
  exact entryChain_reaches chain registerZero registerTwo

/-- One source step expands to a nonempty embedded execution.  The exceptional
case is the zero branch of a conditional with positive target zero: R2 sends
that branch to state one, so the certified entry code runs again. -/
theorem embed_step_iteration
    {offset : Nat} {entry source : KorecR2.Program}
    (offsetPositive : 0 < offset)
    (entryCorrect : EntryCorrect offset entry source)
    {before after : KorecR2.Configuration}
    (stepEq : KorecR2.step source before = some after) :
    ∃ fuel, 0 < fuel ∧
      iterate (KorecR2.step (embed offset entry source)) fuel
          (shiftConfiguration offset before) =
        some (shiftConfiguration offset after) := by
  rcases before with ⟨state, registerZero, registerTwo⟩
  have statePositive : 0 < state := by
    by_cases stateZero : state = 0
    · simp [KorecR2.step, stateZero] at stepEq
    · omega
  obtain ⟨state, rfl⟩ := Nat.exists_eq_succ_of_ne_zero
    (Nat.ne_of_gt statePositive)
  have embeddedLookup :=
    embed_shifted_positive offset entry source state offsetPositive
  cases lookup : source (state + 1) with
  | none => simp [KorecR2.step, lookup] at stepEq
  | some operation =>
      rw [lookup] at embeddedLookup
      have embeddedLookup' :
          embed offset entry source (offset + state + 1) =
            some (shiftInstruction offset operation) := by
        simpa [shiftState] using embeddedLookup
      cases operation with
      | incrementBoth target =>
          simp [KorecR2.step, lookup] at stepEq
          subst after
          refine ⟨1, by omega, ?_⟩
          cases target <;>
            simp [iterate, KorecR2.step, embeddedLookup',
              shiftInstruction, shiftConfiguration]
      | decrement register target =>
          cases register with
          | zero =>
              cases registerZero with
              | zero =>
                  simp [KorecR2.step, lookup] at stepEq
                  subst after
                  cases target with
                  | zero =>
                      obtain ⟨entryFuel, entryExecution⟩ :=
                        reaches_iff_exists_iterate.mp
                          (entryCorrect 0 registerTwo)
                      refine ⟨1 + entryFuel, by omega, ?_⟩
                      rw [iterate_add]
                      simp [iterate, KorecR2.step, embeddedLookup',
                        shiftInstruction, shiftConfiguration, entryExecution]
                  | succ target =>
                      refine ⟨1, by omega, ?_⟩
                      simp [iterate, KorecR2.step, embeddedLookup',
                        shiftInstruction, shiftConfiguration]
                      omega
              | succ value =>
                  simp [KorecR2.step, lookup] at stepEq
                  subst after
                  refine ⟨1, by omega, ?_⟩
                  cases target <;>
                    simp [iterate, KorecR2.step, embeddedLookup',
                      shiftInstruction, shiftConfiguration]
          | one =>
              cases registerTwo with
              | zero =>
                  simp [KorecR2.step, lookup] at stepEq
                  subst after
                  cases target with
                  | zero =>
                      obtain ⟨entryFuel, entryExecution⟩ :=
                        reaches_iff_exists_iterate.mp
                          (entryCorrect registerZero 0)
                      refine ⟨1 + entryFuel, by omega, ?_⟩
                      rw [iterate_add]
                      simp [iterate, KorecR2.step, embeddedLookup',
                        shiftInstruction, shiftConfiguration, entryExecution]
                  | succ target =>
                      refine ⟨1, by omega, ?_⟩
                      simp [iterate, KorecR2.step, embeddedLookup',
                        shiftInstruction, shiftConfiguration]
                      omega
              | succ value =>
                  simp [KorecR2.step, lookup] at stepEq
                  subst after
                  refine ⟨1, by omega, ?_⟩
                  cases target <;>
                    simp [iterate, KorecR2.step, embeddedLookup',
                      shiftInstruction, shiftConfiguration]

/-- Compile a finite source execution, retaining a lower bound on the number
of embedded steps. -/
theorem embed_iterate
    {offset : Nat} {entry source : KorecR2.Program}
    (offsetPositive : 0 < offset)
    (entryCorrect : EntryCorrect offset entry source)
    {start finish : KorecR2.Configuration} {sourceFuel : Nat}
    (sourceExecution :
      iterate (KorecR2.step source) sourceFuel start = some finish) :
    ∃ targetFuel, sourceFuel ≤ targetFuel ∧
      iterate (KorecR2.step (embed offset entry source)) targetFuel
          (shiftConfiguration offset start) =
        some (shiftConfiguration offset finish) := by
  induction sourceFuel generalizing finish with
  | zero =>
      simp [iterate] at sourceExecution
      subst finish
      exact ⟨0, by omega, rfl⟩
  | succ sourceFuel inductionHypothesis =>
      simp only [iterate] at sourceExecution
      cases prefixEq : iterate (KorecR2.step source) sourceFuel start with
      | none => simp [prefixEq] at sourceExecution
      | some middle =>
          have lastStep : KorecR2.step source middle = some finish := by
            simpa [prefixEq] using sourceExecution
          obtain ⟨prefixFuel, prefixBound, compiledPrefix⟩ :=
            inductionHypothesis prefixEq
          obtain ⟨stepFuel, stepPositive, compiledStep⟩ :=
            embed_step_iteration offsetPositive entryCorrect lastStep
          refine ⟨prefixFuel + stepFuel, by omega, ?_⟩
          rw [iterate_add, compiledPrefix]
          simpa using compiledStep

/-- Halting equivalence from an already shifted source configuration. -/
theorem shiftedHaltsFrom_iff
    (offset : Nat) (entry source : KorecR2.Program)
    (offsetPositive : 0 < offset)
    (entryCorrect : EntryCorrect offset entry source)
    (operationAt : ∀ state, 0 < state →
      ∃ operation, source state = some operation)
    (start : KorecR2.Configuration) :
    R2Relocation.HaltsFrom (embed offset entry source)
        (shiftConfiguration offset start) ↔
      R2Relocation.HaltsFrom source start := by
  constructor
  · intro embeddedHalts
    by_cases sourceHalts : R2Relocation.HaltsFrom source start
    · exact sourceHalts
    · exfalso
      obtain ⟨registerZero, registerTwo, embeddedRun⟩ := embeddedHalts
      obtain ⟨haltFuel, haltExecution⟩ :=
        reaches_iff_exists_iterate.mp embeddedRun
      obtain ⟨sourceFinish, sourceExecution⟩ :=
        R2Relocation.source_iterate_exists_of_not_haltsFrom
          source operationAt start sourceHalts (haltFuel + 1)
      obtain ⟨targetFuel, fuelBound, embeddedExecution⟩ :=
        embed_iterate offsetPositive entryCorrect sourceExecution
      have cannotPassHalt := successful_iterations_before_halt
        (step := KorecR2.step (embed offset entry source))
        (haltEq := KorecR2.step_halt (embed offset entry source)
          registerZero registerTwo)
        haltExecution embeddedExecution
      omega
  · rintro ⟨registerZero, registerTwo, sourceRun⟩
    obtain ⟨fuel, sourceExecution⟩ :=
      reaches_iff_exists_iterate.mp sourceRun
    obtain ⟨targetFuel, _, targetExecution⟩ :=
      embed_iterate offsetPositive entryCorrect sourceExecution
    exact ⟨registerZero, registerTwo,
      reaches_iff_exists_iterate.mpr
        ⟨targetFuel, by simpa using targetExecution⟩⟩

/-- A certified register-preserving entry chain followed by relocation
preserves and reflects halting from the standard state-one input convention. -/
theorem embeddedHalts_iff
    (offset : Nat) (entry source : KorecR2.Program)
    (offsetPositive : 0 < offset)
    (entryCorrect : EntryCorrect offset entry source)
    (operationAt : ∀ state, 0 < state →
      ∃ operation, source state = some operation)
    (input : Nat) :
    KorecR2.Halts (embed offset entry source) input ↔
      KorecR2.Halts source input := by
  change R2Relocation.HaltsFrom (embed offset entry source)
      (KorecR2.initialConfiguration input) ↔
    R2Relocation.HaltsFrom source (KorecR2.initialConfiguration input)
  have entryPrefix : Reaches (KorecR2.step (embed offset entry source))
      (KorecR2.initialConfiguration input)
      (shiftConfiguration offset (KorecR2.initialConfiguration input)) := by
    simpa [KorecR2.initialConfiguration, shiftConfiguration] using
      (entryCorrect 0 input)
  rw [R2Relocation.haltsFrom_iff_after_prefix _
    entryPrefix]
  exact shiftedHaltsFrom_iff offset entry source offsetPositive entryCorrect
    operationAt (KorecR2.initialConfiguration input)

end Mortality.SourceMachine.R2Embedding
