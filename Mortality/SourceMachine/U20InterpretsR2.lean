import Mortality.SourceMachine.U20Reader
import Mortality.SourceMachine.U20Simulation

/-!
# Semantic interface between an encoded R2 program and Korec U20

`ReaderPlan` is a finite certificate for one instruction lookup.  An
`Encoding` supplies such a plan for every reachable control state and keeps
track of the reader carry `R6` between simulated steps.  This file proves
that any certified `KorecR2` run is simulated by the literal twenty-
instruction U20 table.

The eventual universality proof must construct an `Encoding`; this file does
not assume one as a project axiom or claim that an uninstantiated encoding is
the final result.
-/

namespace Mortality.SourceMachine.KorecU20Interpreter

open Mortality.SourceMachine
open Mortality.SourceMachine.KorecU20
open Mortality.SourceMachine.KorecR2
open Mortality.SourceMachine.U20Compilation

/-- A program-code certificate, including the invariant relating the R2
configuration to the residual reader carry between simulated instructions. -/
structure Encoding (programCode : Nat) (program : KorecR2.Program) where
  Invariant : KorecR2.Configuration → Nat → Prop
  operationAt : ∀ {source carry}, Invariant source carry → 0 < source.state →
    ∃ operation, program source.state = some operation
  reader : ∀ {source target operation carry},
    0 < source.state →
    program source.state = some operation →
    KorecR2.step program source = some target →
    Invariant source carry →
    ∃ nextCarry,
      ReaderPlan programCode carry (source.state - 1) operation.code nextCarry ∧
      Invariant target nextCarry

/-- Construct an encoding directly from the number-theoretic scan relation.
This form cleanly separates Korec's arithmetic program-code theorem from the
operational correctness of the U20 reader. -/
def Encoding.ofNondivisorScan
    (programCode : Nat) (program : KorecR2.Program)
    (Invariant : KorecR2.Configuration → Nat → Prop)
    (operationAt : ∀ {source carry}, Invariant source carry → 0 < source.state →
      ∃ operation, program source.state = some operation)
    (scan : ∀ {source target operation carry},
      0 < source.state →
      program source.state = some operation →
      KorecR2.step program source = some target →
      Invariant source carry →
      ∃ candidate,
        NondivisorScan programCode carry (source.state - 1) candidate ∧
        (programCode + 1) % candidate = operation.code ∧
        Invariant target (candidate - (programCode + 1) % candidate)) :
    Encoding programCode program where
  Invariant := Invariant
  operationAt := operationAt
  reader := by
    intro source target operation carry statePositive lookup stepEq invariant
    obtain ⟨candidate, scanCertificate, codeEq, nextInvariant⟩ :=
      scan statePositive lookup stepEq invariant
    refine ⟨candidate - (programCode + 1) % candidate, ?_, nextInvariant⟩
    have plan := nondivisorScan_to_readerPlan scanCertificate
    simpa [codeEq] using plan

/-- Construct an encoding from executable bounded nondivisor searches.  This
is the interface used by later finite program-code certificates. -/
def Encoding.ofScan
    (programCode : Nat) (program : KorecR2.Program)
    (Invariant : KorecR2.Configuration → Nat → Prop)
    (operationAt : ∀ {source carry}, Invariant source carry → 0 < source.state →
      ∃ operation, program source.state = some operation)
    (scan : ∀ {source target operation carry},
      0 < source.state →
      program source.state = some operation →
      KorecR2.step program source = some target →
      Invariant source carry →
      ∃ fuel candidate,
        scanNondivisor programCode carry (source.state - 1) fuel = some candidate ∧
        (programCode + 1) % candidate = operation.code ∧
        Invariant target (candidate - (programCode + 1) % candidate)) :
    Encoding programCode program where
  Invariant := Invariant
  operationAt := operationAt
  reader := by
    intro source target operation carry statePositive lookup stepEq invariant
    obtain ⟨fuel, candidate, search, codeEq, nextAllowed⟩ :=
      scan statePositive lookup stepEq invariant
    refine ⟨candidate - (programCode + 1) % candidate, ?_, nextAllowed⟩
    have plan := readerPlan_of_scanNondivisor search
    simpa [codeEq] using plan

theorem r2_state_positive_of_step
    {program : KorecR2.Program} {source target : KorecR2.Configuration}
    (stepEq : KorecR2.step program source = some target) :
    0 < source.state := by
  by_cases stateZero : source.state = 0
  · simp [KorecR2.step, stateZero] at stepEq
  · omega

/-- One certified R2 step expands to a nonempty U20 run. -/
theorem encoded_step
    {programCode : Nat} {program : KorecR2.Program}
    (encoding : Encoding programCode program)
    {source target : KorecR2.Configuration} {carry : Nat}
    (sourceInvariant : encoding.Invariant source carry)
    (stepEq : KorecR2.step program source = some target) :
    ∃ nextCarry,
      encoding.Invariant target nextCarry ∧
      Reaches KorecU20.step
        (simulationConfiguration programCode carry source)
        (simulationConfiguration programCode nextCarry target) := by
  have statePositive := r2_state_positive_of_step stepEq
  cases source with
  | mk state registerZero registerTwo =>
      obtain ⟨state, rfl⟩ := Nat.exists_eq_succ_of_ne_zero
        (Nat.ne_of_gt statePositive)
      cases lookup : program (state + 1) with
      | none =>
          simp [KorecR2.step, lookup] at stepEq
      | some operation =>
          obtain ⟨nextCarry, plan, nextAllowed⟩ :=
            encoding.reader (by omega) lookup stepEq sourceInvariant
          have readAndExecute := reader_plan_decode_and_execute operation plan
            registerZero registerTwo 0 carry (by omega)
          have resultEq := decodedResult_of_r2Step (programCode := programCode)
            (carry := nextCarry) (by omega) lookup stepEq
          refine ⟨nextCarry, nextAllowed, ?_⟩
          simpa [simulationConfiguration, resultEq] using readAndExecute

theorem r2_step_exists_of_positive
    {programCode : Nat} {program : KorecR2.Program}
    (encoding : Encoding programCode program)
    (source : KorecR2.Configuration) (carry : Nat)
    (sourceInvariant : encoding.Invariant source carry)
    (statePositive : 0 < source.state) :
    ∃ target nextCarry,
      KorecR2.step program source = some target ∧
      encoding.Invariant target nextCarry := by
  obtain ⟨operation, lookup⟩ :=
    encoding.operationAt sourceInvariant statePositive
  rcases source with ⟨state, registerZero, registerTwo⟩
  cases operation with
  | decrement register target =>
      have stepExists : ∃ result, KorecR2.step program
          { state, registerZero, registerTwo } = some result := by
        cases register <;> cases registerZero <;> cases registerTwo <;>
          simp [KorecR2.step, Nat.ne_of_gt statePositive, lookup]
      obtain ⟨result, stepEq⟩ := stepExists
      obtain ⟨nextCarry, _, nextInvariant⟩ :=
        encoding.reader statePositive lookup stepEq sourceInvariant
      exact ⟨result, nextCarry, stepEq, nextInvariant⟩
  | incrementBoth target =>
      have stepEq : KorecR2.step program
          { state, registerZero, registerTwo } =
        some
          { state := target
            registerZero := registerZero + 1
            registerTwo := registerTwo + 1 } := by
        simp [KorecR2.step, Nat.ne_of_gt statePositive, lookup]
      obtain ⟨nextCarry, _, nextInvariant⟩ :=
        encoding.reader statePositive lookup stepEq sourceInvariant
      exact ⟨_, nextCarry, stepEq, nextInvariant⟩

/-- A certified R2 step consumes at least one concrete U20 instruction.
The positive length comes from the reader prefix, whose endpoints have
different control states (`q1` and `q16`). -/
theorem encoded_step_iteration
    {programCode : Nat} {program : KorecR2.Program}
    (encoding : Encoding programCode program)
    {source target : KorecR2.Configuration} {carry : Nat}
    (sourceInvariant : encoding.Invariant source carry)
    (stepEq : KorecR2.step program source = some target) :
    ∃ nextCarry fuel,
      encoding.Invariant target nextCarry ∧ 0 < fuel ∧
      iterate KorecU20.step fuel
          (simulationConfiguration programCode carry source) =
        some (simulationConfiguration programCode nextCarry target) := by
  have statePositive := r2_state_positive_of_step stepEq
  cases source with
  | mk state registerZero registerTwo =>
      obtain ⟨state, rfl⟩ := Nat.exists_eq_succ_of_ne_zero
        (Nat.ne_of_gt statePositive)
      cases lookup : program (state + 1) with
      | none => simp [KorecR2.step, lookup] at stepEq
      | some operation =>
          obtain ⟨nextCarry, plan, nextAllowed⟩ :=
            encoding.reader (by omega) lookup stepEq sourceInvariant
          have readerRun := reader_plan_correct plan registerZero registerTwo 0 0 carry
            (by omega)
          have decoderRun := decode_and_execute programCode nextCarry registerZero
            registerTwo operation
          obtain ⟨readerFuel, readerExecution⟩ :=
            reaches_iff_exists_iterate.mp readerRun
          obtain ⟨decoderFuel, decoderExecution⟩ :=
            reaches_iff_exists_iterate.mp decoderRun
          have readerExecution' :
              iterate KorecU20.step readerFuel
                  (simulationConfiguration programCode carry
                    { state := state + 1, registerZero, registerTwo }) =
                some (configuration 16 registerZero programCode registerTwo 0 0
                  operation.code nextCarry 0) := by
            simpa [simulationConfiguration] using readerExecution
          have readerFuelPositive : 0 < readerFuel := by
            by_cases readerFuelZero : readerFuel = 0
            · subst readerFuel
              simp [iterate, configuration] at readerExecution
            · omega
          have resultEq := decodedResult_of_r2Step (programCode := programCode)
            (carry := nextCarry) (by omega) lookup stepEq
          refine ⟨nextCarry, readerFuel + decoderFuel, nextAllowed, by omega, ?_⟩
          rw [iterate_add, readerExecution']
          simpa [resultEq] using decoderExecution

/-- Compile a whole finite R2 run while propagating the reader-carry
invariant. -/
theorem encoded_run
    {programCode : Nat} {program : KorecR2.Program}
    (encoding : Encoding programCode program)
    {start finish : KorecR2.Configuration} {carry : Nat}
    (startInvariant : encoding.Invariant start carry)
    (run : Reaches (KorecR2.step program) start finish) :
    ∃ finalCarry,
      encoding.Invariant finish finalCarry ∧
      Reaches KorecU20.step
        (simulationConfiguration programCode carry start)
        (simulationConfiguration programCode finalCarry finish) := by
  induction run generalizing carry with
  | refl => exact ⟨carry, startInvariant, Reaches.refl _⟩
  | @tail middle finish prefixRun lastStep inductionHypothesis =>
      obtain ⟨middleCarry, middleAllowed, compiledPrefix⟩ :=
        inductionHypothesis startInvariant
      obtain ⟨finalCarry, finalAllowed, compiledStep⟩ :=
        encoded_step encoding middleAllowed lastStep
      exact ⟨finalCarry, finalAllowed, compiledPrefix.trans compiledStep⟩

/-- Exact iteration form of `encoded_run`, retaining the lower bound of one
U20 instruction per simulated R2 step. -/
theorem encoded_iterate
    {programCode : Nat} {program : KorecR2.Program}
    (encoding : Encoding programCode program)
    {start finish : KorecR2.Configuration} {carry sourceFuel : Nat}
    (startInvariant : encoding.Invariant start carry)
    (sourceExecution : iterate (KorecR2.step program) sourceFuel start = some finish) :
    ∃ finalCarry targetFuel,
      encoding.Invariant finish finalCarry ∧ sourceFuel ≤ targetFuel ∧
      iterate KorecU20.step targetFuel
          (simulationConfiguration programCode carry start) =
        some (simulationConfiguration programCode finalCarry finish) := by
  induction sourceFuel generalizing finish carry with
  | zero =>
      simp [iterate] at sourceExecution
      subst finish
      exact ⟨carry, 0, startInvariant, by omega, rfl⟩
  | succ sourceFuel inductionHypothesis =>
      simp only [iterate] at sourceExecution
      cases prefixEq : iterate (KorecR2.step program) sourceFuel start with
      | none => simp [prefixEq] at sourceExecution
      | some middle =>
          have lastStep : KorecR2.step program middle = some finish := by
            simpa [prefixEq] using sourceExecution
          obtain ⟨middleCarry, prefixFuel, middleAllowed, prefixBound,
              compiledPrefix⟩ := inductionHypothesis startInvariant prefixEq
          obtain ⟨finalCarry, stepFuel, finalAllowed, stepPositive,
              compiledStep⟩ := encoded_step_iteration encoding middleAllowed lastStep
          refine ⟨finalCarry, prefixFuel + stepFuel, finalAllowed, by omega, ?_⟩
          rw [iterate_add, compiledPrefix]
          simpa using compiledStep

/-- If a certified R2 computation from an arbitrary invariant configuration
does not halt, every finite iteration is defined and preserves the carry
invariant. -/
theorem r2_iterate_exists_of_not_haltsFrom
    {programCode : Nat} {program : KorecR2.Program}
    (encoding : Encoding programCode program)
    (start : KorecR2.Configuration) (initialCarry : Nat)
    (initialInvariant : encoding.Invariant start initialCarry)
    (notHalts : ¬KorecR2.HaltsFrom program start) :
    ∀ fuel, ∃ finish carry,
      iterate (KorecR2.step program) fuel start = some finish ∧
        encoding.Invariant finish carry := by
  intro fuel
  induction fuel with
  | zero => exact ⟨_, initialCarry, rfl, initialInvariant⟩
  | succ fuel inductionHypothesis =>
      obtain ⟨middle, middleCarry, middleExecution, middleInvariant⟩ :=
        inductionHypothesis
      have statePositive : 0 < middle.state := by
        by_cases stateZero : middle.state = 0
        · have middleRun := reaches_iff_exists_iterate.mpr
            ⟨fuel, middleExecution⟩
          have middleEq :
              middle = KorecR2.haltConfiguration middle.registerZero
                middle.registerTwo := by
            cases middle
            simp_all [KorecR2.haltConfiguration]
          apply (notHalts ⟨middle.registerZero, middle.registerTwo, ?_⟩).elim
          rw [← middleEq]
          exact middleRun
        · omega
      obtain ⟨finish, finalCarry, finalStep, finalInvariant⟩ :=
        r2_step_exists_of_positive encoding middle middleCarry
          middleInvariant statePositive
      refine ⟨finish, finalCarry, ?_, finalInvariant⟩
      simp [iterate, middleExecution, finalStep]

/-- Initial-configuration specialization retained for the ordinary two-input
interface. -/
theorem r2_iterate_exists_of_not_halts
    {programCode : Nat} {program : KorecR2.Program}
    (encoding : Encoding programCode program) (input : Nat)
    (initialInvariant :
      encoding.Invariant (KorecR2.initialConfiguration input) 0)
    (notHalts : ¬KorecR2.Halts program input) :
    ∀ fuel, ∃ finish carry,
      iterate (KorecR2.step program) fuel (KorecR2.initialConfiguration input) =
        some finish ∧ encoding.Invariant finish carry := by
  exact r2_iterate_exists_of_not_haltsFrom encoding
    (KorecR2.initialConfiguration input) 0 initialInvariant notHalts

/-- Exact halting equivalence from an arbitrary positive R2 boundary
configuration.  The U20 register vector directly supplies the simulated
state through `R4` and the incoming reader carry through `R6`. -/
theorem u20HaltsFrom_simulation_iff_r2HaltsFrom
    {programCode : Nat} {program : KorecR2.Program}
    (encoding : Encoding programCode program)
    (start : KorecR2.Configuration) (carry : Nat)
    (statePositive : 0 < start.state)
    (initialInvariant : encoding.Invariant start carry) :
    KorecU20.HaltsFrom
        (registers start.registerZero programCode start.registerTwo 0
          (start.state - 1) 0 carry 0) ↔
      KorecR2.HaltsFrom program start := by
  have startEq :
      simulationConfiguration programCode carry start =
        { state := 1
          registers := registers start.registerZero programCode
            start.registerTwo 0 (start.state - 1) 0 carry 0 } := by
    cases start with
    | mk state registerZero registerTwo =>
        cases state with
        | zero => simp at statePositive
        | succ state => simp [simulationConfiguration, configuration]
  constructor
  · intro u20Halts
    by_cases sourceHalts : KorecR2.HaltsFrom program start
    · exact sourceHalts
    · exfalso
      obtain ⟨finalRegisters, u20Run⟩ := u20Halts
      obtain ⟨haltFuel, haltExecution⟩ :=
        reaches_iff_exists_iterate.mp u20Run
      obtain ⟨sourceFinish, _, sourceExecution, _⟩ :=
        r2_iterate_exists_of_not_haltsFrom encoding start carry
          initialInvariant sourceHalts (haltFuel + 1)
      obtain ⟨finalCarry, targetFuel, _, fuelBound, compiledExecution⟩ :=
        encoded_iterate encoding initialInvariant sourceExecution
      rw [startEq] at compiledExecution
      have cannotPassHalt := successful_iterations_before_halt
        (step := KorecU20.step)
        (haltEq := KorecU20.step_halt finalRegisters)
        haltExecution compiledExecution
      omega
  · rintro ⟨registerZero, registerTwo, sourceRun⟩
    obtain ⟨finalCarry, _, compiledRun⟩ :=
      encoded_run encoding initialInvariant sourceRun
    refine ⟨registers registerZero programCode registerTwo 0 0 0
      finalCarry 0, ?_⟩
    rw [← startEq]
    simpa [KorecU20.haltConfiguration, KorecR2.haltConfiguration,
      simulationConfiguration, configuration] using compiledRun

/-- Arbitrary simulated control and carry, encoded as one U2 input integer.
This is the interface needed to enter a shifted R2 program directly, without
an arithmetic `GOTO` chain from simulated state one. -/
theorem u2Halts_encodeSimulation_iff_r2HaltsFrom
    {programCode : Nat} {program : KorecR2.Program}
    (encoding : Encoding programCode program)
    (start : KorecR2.Configuration) (carry : Nat)
    (statePositive : 0 < start.state)
    (initialInvariant : encoding.Invariant start carry) :
    U2Halts
        (U20Compilation.encodeRegisters
          (registers start.registerZero programCode start.registerTwo 0
            (start.state - 1) 0 carry 0)) ↔
      KorecR2.HaltsFrom program start :=
  (U20Compilation.u2Halts_encodeRegisters_iff_u20HaltsFrom _).trans
    (u20HaltsFrom_simulation_iff_r2HaltsFrom encoding start carry
      statePositive initialInvariant)

/-- Every halting computation of a certified R2 program yields a halting
computation of the exact U20 machine under Korec's two-input convention. -/
theorem r2Halts_implies_u20HaltsTwo
    {programCode : Nat} {program : KorecR2.Program}
    (encoding : Encoding programCode program) (input : Nat)
    (initialInvariant :
      encoding.Invariant (KorecR2.initialConfiguration input) 0) :
    KorecR2.Halts program input → KorecU20.HaltsTwo programCode input := by
  rintro ⟨registerZero, registerTwo, sourceRun⟩
  obtain ⟨finalCarry, _, compiledRun⟩ :=
    encoded_run encoding initialInvariant sourceRun
  refine ⟨registers registerZero programCode registerTwo 0 0 0 finalCarry 0, ?_⟩
  simpa [KorecU20.HaltsTwo, KorecU20.HaltsFrom,
    KorecU20.initialRegistersTwo, KorecU20.haltConfiguration,
    KorecR2.initialConfiguration, KorecR2.haltConfiguration,
    simulationConfiguration, configuration, registers,
    initialRegistersTwo_eq_registers] using compiledRun

/-- Exact halting equivalence for every certified program code.  Reflection
uses determinism: a nonhalting total R2 execution supplies arbitrarily long
U20 prefixes, which cannot pass through U20's terminal state. -/
theorem u20HaltsTwo_iff_r2Halts
    {programCode : Nat} {program : KorecR2.Program}
    (encoding : Encoding programCode program) (input : Nat)
    (initialInvariant :
      encoding.Invariant (KorecR2.initialConfiguration input) 0) :
    KorecU20.HaltsTwo programCode input ↔ KorecR2.Halts program input := by
  constructor
  · intro u20Halts
    by_cases sourceHalts : KorecR2.Halts program input
    · exact sourceHalts
    · exfalso
      obtain ⟨finalRegisters, u20Run⟩ := u20Halts
      obtain ⟨haltFuel, haltExecution⟩ := reaches_iff_exists_iterate.mp u20Run
      obtain ⟨sourceFinish, _, sourceExecution, _⟩ :=
        r2_iterate_exists_of_not_halts encoding input initialInvariant sourceHalts
          (haltFuel + 1)
      obtain ⟨finalCarry, targetFuel, _, fuelBound, compiledExecution⟩ :=
        encoded_iterate encoding initialInvariant sourceExecution
      have startEq :
          simulationConfiguration programCode 0 (KorecR2.initialConfiguration input) =
            { state := 1,
              registers := KorecU20.initialRegistersTwo programCode input } := by
        simp [simulationConfiguration, KorecR2.initialConfiguration, configuration,
          initialRegistersTwo_eq_registers]
      rw [startEq] at compiledExecution
      have cannotPassHalt := successful_iterations_before_halt
        (step := KorecU20.step)
        (haltEq := KorecU20.step_halt finalRegisters)
        haltExecution compiledExecution
      omega
  · exact r2Halts_implies_u20HaltsTwo encoding input initialInvariant

end Mortality.SourceMachine.KorecU20Interpreter
