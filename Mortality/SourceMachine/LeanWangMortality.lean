import LeanWang.Kari.Hooper.CounterControlAbstractTrace
import LeanWang.Kari.Hooper.StackEncodingComputable
import Mortality.Main
import Mortality.SourceMachine.KorecPrimeSystemExistence
import Mortality.SourceMachine.LeanWangBridge

/-!
# The fixed-source mortality reduction

This file composes the fixed universal counter program from `lean-wang` with
the project's checked four-counter-to-matrix pipeline.  The parameterized
theorems preserve the dependency boundary at
`KorecPrimeSystem.ExistsForEverySpan`; the final theorems discharge that
boundary using the analytic construction in `KorecPrimeSystemExistence`.
-/

namespace Mortality.SourceMachine.LeanWangMortality

open LeanWang.Kari.Hooper
open Mortality.SourceMachine

noncomputable section

/-- An exclusive bound for the control states of the fixed source program. -/
def sourceBound : Nat := CounterControlPlan.logicalSpan

theorem sourceBound_positive : 0 < sourceBound := by
  have stateBound :=
    CounterControlAbstractTrace.canonicalCounterCfg_state_lt_logicalSpan
      (default : Nat.Partrec.Code)
  unfold sourceBound
  exact Nat.zero_lt_of_lt stateBound

/-- Every transition of the fixed four-counter program stays below the
fixed control bound. -/
theorem fixedProgram_closedBelow :
    FourCounter.ClosedBelow LeanWangBridge.fixedProgram sourceBound := by
  intro state instruction _ lookup
  unfold LeanWangBridge.fixedProgram at lookup
  cases upstreamLookup :
      CounterMachine.lookupInstruction GlobalSourceProgram.program state with
  | none => simp [upstreamLookup] at lookup
  | some upstreamInstruction =>
      simp only [upstreamLookup, Option.map_some, Option.some.injEq] at lookup
      subst instruction
      have ruleMem := CounterProgram.rule_mem_of_lookupInstruction_eq_some
        upstreamLookup
      cases upstreamInstruction with
      | increment register target =>
          exact CounterControlPlan.state_lt_logicalSpan
            (CounterControlAbstractTrace.target_mem_programStates ruleMem
              (by simp [CounterControlPlan.instructionTargets]))
      | decrement register zeroTarget positiveTarget =>
          constructor
          · exact CounterControlPlan.state_lt_logicalSpan
              (CounterControlAbstractTrace.target_mem_programStates ruleMem
                (by simp [CounterControlPlan.instructionTargets]))
          · exact CounterControlPlan.state_lt_logicalSpan
              (CounterControlAbstractTrace.target_mem_programStates ruleMem
                (by simp [CounterControlPlan.instructionTargets]))

/-- The initializer must assign a source state even to its final, unused
tag.  Out-of-range tags are sent to state zero. -/
def boundedTarget (tag : Nat) : Nat :=
  if tag < sourceBound then tag else 0

theorem boundedTarget_lt (tag : Nat) : boundedTarget tag < sourceBound := by
  unfold boundedTarget
  split
  · assumption
  · exact sourceBound_positive

@[simp] theorem boundedTarget_eq_self {tag : Nat} (tagBound : tag < sourceBound) :
    boundedTarget tag = tag := by
  simp [boundedTarget, tagBound]

/-- The fixed control span of the normalized two-register program. -/
def reductionSpan : Nat :=
  UniversalPipeline.normalizedR2StateBound sourceBound sourceBound

theorem reductionSpan_large : 2 < reductionSpan := by
  exact UniversalPipeline.normalizedR2StateBound_large sourceBound_positive

/-- Choose the one finite prime system needed by this fixed program.  The
choice is a constant; it does not depend on the machine input. -/
def primeSystem (existence : KorecPrimeSystem.ExistsForEverySpan) :
    KorecPrimeSystem.System reductionSpan :=
  Classical.choice (existence reductionSpan reductionSpan_large)

theorem normalizedProgram_closedBelow :
    KorecR2.ClosedBelow
      (UniversalPipeline.normalizedR2Program sourceBound boundedTarget
        LeanWangBridge.fixedProgram)
      reductionSpan := by
  exact UniversalPipeline.normalizedR2Program_closedBelow
    sourceBound_positive (fun tag _ => boundedTarget_lt tag)
    fixedProgram_closedBelow

/-- The four registers of the canonical fixed-program start. -/
def sourceRegisters (code : Nat.Partrec.Code) : FourCounter.Registers :=
  LeanWangBridge.encodeRegisters
    (GlobalSourceSemantics.canonicalCounterCfg code).registers

/-- The control tag of the canonical fixed-program start. -/
def sourceTag (code : Nat.Partrec.Code) : Nat :=
  (GlobalSourceSemantics.canonicalCounterCfg code).state

theorem sourceTag_lt (code : Nat.Partrec.Code) : sourceTag code < sourceBound := by
  exact CounterControlAbstractTrace.canonicalCounterCfg_state_lt_logicalSpan code

private theorem nat_pow_primrec :
    Primrec₂ ((· ^ ·) : Nat → Nat → Nat) :=
  Primrec₂.unpaired'.1 Nat.Primrec.pow

theorem sourceRegisters_right_primrec :
    Primrec fun code : Nat.Partrec.Code => (sourceRegisters code).right := by
  exact StackEncoding.sourceInitialRegisters_right_primrec.of_eq fun _ => rfl

theorem sourceTag_primrec : Primrec sourceTag := by
  exact (Primrec.nat_add.comp
    (Primrec.nat_mul.comp
      (Primrec.const
        (SourceControl.encodeState (default : SourceMachine.State)))
      (Primrec.const SourceControl.numSymbols))
    (LeanWang.UniversalTM0Semantic.input_head_nat_primrec
      SourceControl.symbolDigit)).of_eq fun code => by
        rw [sourceTag, GlobalSourceSemantics.canonicalCounterCfg_state]
        rfl

/-- The prime-exponent code of the canonical four-counter input. -/
def sourceData (code : Nat.Partrec.Code) : Nat :=
  3 ^ (sourceRegisters code).right * 5 ^ sourceTag code

theorem sourceData_primrec : Primrec sourceData := by
  exact Primrec.nat_mul.comp
    (nat_pow_primrec.comp (Primrec.const 3) sourceRegisters_right_primrec)
    (nat_pow_primrec.comp (Primrec.const 5) sourceTag_primrec)

theorem dataInput_eq_sourceData (code : Nat.Partrec.Code) :
    UniversalPipeline.dataInput (sourceRegisters code) (sourceTag code) =
      sourceData code := by
  simp [UniversalPipeline.dataInput, FourCounterEncoding.encode,
    FourCounterInitializer.withTemp, sourceData, sourceRegisters,
    LeanWangBridge.encodeRegisters, GlobalSourceSemantics.canonicalCounterCfg,
    SourceProgram.logicalRegisters, SourceRegisterSemantics.canonical]

/-- The fixed U20 program numeral selected by the analytic prime system. -/
def fixedProgramNumber
    (existence : KorecPrimeSystem.ExistsForEverySpan) : Nat :=
  (UniversalPipeline.normalizedPrimeSystemLayout sourceBound boundedTarget
    LeanWangBridge.fixedProgram reductionSpan (primeSystem existence)
    normalizedProgram_closedBelow).crtProgramCode

/-- The natural-number input passed to the fixed 5,799-matrix family. -/
def mortalityInput
    (existence : KorecPrimeSystem.ExistsForEverySpan)
    (code : Nat.Partrec.Code) : Nat :=
  11 ^ fixedProgramNumber existence * 13 ^ sourceData code *
    5 ^ ((primeSystem existence).offset + 1)

theorem mortalityInput_primrec
    (existence : KorecPrimeSystem.ExistsForEverySpan) :
    Primrec (mortalityInput existence) := by
  exact Primrec.nat_mul.comp
    (Primrec.nat_mul.comp
      (nat_pow_primrec.comp (Primrec.const 11)
        (Primrec.const (fixedProgramNumber existence)))
      (nat_pow_primrec.comp (Primrec.const 13) sourceData_primrec))
    (nat_pow_primrec.comp (Primrec.const 5)
      (Primrec.const ((primeSystem existence).offset + 1)))

theorem mortalityInput_eq_encoded
    (existence : KorecPrimeSystem.ExistsForEverySpan)
    (code : Nat.Partrec.Code) :
    mortalityInput existence code =
      U20Compilation.encodeRegisters
        (KorecU20Interpreter.registers 0 (fixedProgramNumber existence)
          (UniversalPipeline.dataInput (sourceRegisters code) (sourceTag code)) 0
          ((primeSystem existence).offset + 1) 0 0 0) := by
  rw [dataInput_eq_sourceData]
  simp [mortalityInput, U20Compilation.encodeRegisters]

theorem initializedStart_eq (code : Nat.Partrec.Code) :
    (⟨boundedTarget (sourceTag code),
        FourCounterInitializer.withTemp (sourceRegisters code) 0⟩ :
      FourCounter.Configuration) =
      LeanWangBridge.encodeConfiguration
        (GlobalSourceSemantics.canonicalCounterCfg code) := by
  rw [boundedTarget_eq_self (sourceTag_lt code)]
  unfold sourceTag sourceRegisters LeanWangBridge.encodeConfiguration
  have tempZero := GlobalSourceSemantics.canonicalCounterCfg_temp code
  generalize canonical :
      GlobalSourceSemantics.canonicalCounterCfg code = configuration at tempZero ⊢
  cases configuration with
  | mk state registers =>
      cases registers with
      | mk left right temp clock =>
          change temp = 0 at tempZero
          subst temp
          rfl

/-- The fully composed semantic reduction.  Its sole assumption is the
analytic prime-system existence statement. -/
theorem mortality_iff_evalDom
    (existence : KorecPrimeSystem.ExistsForEverySpan)
    (code : Nat.Partrec.Code) :
    IntegerMortal (Mortality.Main.mortalityFamily
      (mortalityInput existence code)) ↔
      (Nat.Partrec.Code.eval code 0).Dom := by
  rw [mortalityInput_eq_encoded]
  unfold fixedProgramNumber
  rw [Mortality.Main.mortalityFamily_iff_fourCounterHalts_normalizedRelocated_of_primeSystem
    sourceBound boundedTarget LeanWangBridge.fixedProgram
    (sourceRegisters code) (sourceTag code) (sourceTag_lt code)
    reductionSpan reductionSpan_large (primeSystem existence)
    normalizedProgram_closedBelow]
  rw [initializedStart_eq]
  exact LeanWangBridge.fixedProgram_halts_iff_evalDom code

/-- The composed mortality predicate on source codes is not computable. -/
theorem mortalityOnCodes_not_computable
    (existence : KorecPrimeSystem.ExistsForEverySpan) :
    ¬ ComputablePred fun code : Nat.Partrec.Code =>
      IntegerMortal (Mortality.Main.mortalityFamily
        (mortalityInput existence code)) := by
  intro computableMortality
  exact ComputablePred.halting_problem 0
    (computableMortality.of_eq (mortality_iff_evalDom existence))

/-- The ordinary halting problem many-one reduces to mortality for the one
fixed 5,799-matrix template.  Only its integer input parameter varies. -/
theorem halting_manyOneReducible_mortalityFamily
    (existence : KorecPrimeSystem.ExistsForEverySpan) :
    (fun code : Nat.Partrec.Code => (Nat.Partrec.Code.eval code 0).Dom) ≤₀
      (fun input : Nat =>
        IntegerMortal (Mortality.Main.mortalityFamily input)) := by
  exact ⟨mortalityInput existence, (mortalityInput_primrec existence).to_comp,
    fun code => (mortality_iff_evalDom existence code).symm⟩

/-- Conditional undecidability of mortality for the explicit fixed-size
integer family.  The condition is exactly the isolated prime-system
existence statement. -/
theorem mortalityFamily_not_computable
    (existence : KorecPrimeSystem.ExistsForEverySpan) :
    ¬ ComputablePred fun input : Nat =>
      IntegerMortal (Mortality.Main.mortalityFamily input) := by
  intro computableMortality
  exact ComputablePred.halting_problem 0
    (ComputablePred.computable_of_manyOneReducible
      (halting_manyOneReducible_mortalityFamily existence)
      computableMortality)

/-- The kernel-checked analytic construction supplies the formerly isolated
prime-system premise. -/
theorem mortality_iff_evalDom_unconditional (code : Nat.Partrec.Code) :
    IntegerMortal (Mortality.Main.mortalityFamily
      (mortalityInput KorecPrimeSystem.existsForEverySpan code)) ↔
      (Nat.Partrec.Code.eval code 0).Dom :=
  mortality_iff_evalDom KorecPrimeSystem.existsForEverySpan code

/-- Unconditional many-one reduction to the fixed 5,799-matrix family. -/
theorem halting_manyOneReducible_mortalityFamily_unconditional :
    (fun code : Nat.Partrec.Code => (Nat.Partrec.Code.eval code 0).Dom) ≤₀
      (fun input : Nat =>
        IntegerMortal (Mortality.Main.mortalityFamily input)) :=
  halting_manyOneReducible_mortalityFamily
    KorecPrimeSystem.existsForEverySpan

/-- Mortality for the explicit family of exactly 5,799 two-by-two integer
matrices is not a computable predicate. -/
theorem mortalityFamily_not_computable_unconditional :
    ¬ ComputablePred fun input : Nat =>
      IntegerMortal (Mortality.Main.mortalityFamily input) :=
  mortalityFamily_not_computable KorecPrimeSystem.existsForEverySpan

end

end Mortality.SourceMachine.LeanWangMortality
