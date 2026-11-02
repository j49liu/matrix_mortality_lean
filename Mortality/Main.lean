import Mortality.Compiler.GlobalConverse
import Mortality.Compiler.DistinctCertificate
import Mortality.IntegerMatrix2
import Mortality.SourceMachine.U20Simulation
import Mortality.SourceMachine.UniversalPipeline

/-!
# The exact 5,799-matrix reduction

This file converts the checked fixed-family projective compiler into an
integer mortality instance.  The source-machine universality theorem is kept
separate: the equivalence below is the complete matrix-side many-one
reduction from `U2Halts`.
-/

namespace Mortality.Main

open Mortality
open Mortality.OneCounter
open Mortality.PeriodicCode
open Mortality.Compiler
open Mortality.Compiler.FixedAllocation

/-- An integral homogeneous representative of the guarded unary code of a
fixed-program configuration. -/
def integerEncodedConfiguration (configuration : Configuration Nat) :
    IntVec2 :=
  let digits := unaryDigits configuration.counter
  let denominator := periodicIntegerDenominator codingPrime digits
  let numerator := integerDigitPolynomial codingPrime digits
  { x := numerator + phaseShift (boundaryPhase configuration.state) *
      denominator
    y := denominator }

/-- The integral and affine configuration encodings represent the same
rational projective line. -/
theorem encodedConfiguration_sameLine_integer
    (configuration : Configuration Nat) :
    SameLine (Compiler.FixedForward.encodedConfiguration configuration)
      (integerEncodedConfiguration configuration).cast := by
  let digits := unaryDigits configuration.counter
  let numerator := integerDigitPolynomial codingPrime digits
  let denominator := periodicIntegerDenominator codingPrime digits
  have digitsNonempty : digits ≠ [] := by
    simp [digits, unaryDigits]
  have codeSame := periodicCode_sameLine_integerVector codingPrime digits
    codingPrime_isPrime.1 digitsNonempty
  have charted := codeSame.apply
    (IntMatrix2.cast (chart (boundaryPhase configuration.state)))
  rw [chart_apply] at charted
  change SameLine
      (phaseAffine (boundaryPhase configuration.state)
        (periodicCode (codingPrime : Rat) digits))
      (phasePoint (boundaryPhase configuration.state) numerator denominator)
      at charted
  rw [phasePoint_eq_integerVector] at charted
  simpa [Compiler.FixedForward.encodedConfiguration,
    integerEncodedConfiguration, digits, numerator, denominator, unaryCode,
    IntVec2.cast, integerVector, Rat.intCast_add, Rat.intCast_mul] using charted

theorem integerEncodedConfiguration_nonzero
    (configuration : Configuration Nat) :
    (integerEncodedConfiguration configuration).Nonzero := by
  right
  change periodicIntegerDenominator codingPrime
    (unaryDigits configuration.counter) ≠ 0
  exact periodicIntegerDenominator_nonzero codingPrime
    (unaryDigits configuration.counter) codingPrime_isPrime.1
    (by simp [unaryDigits])

/-- Projective reachability depends only on the source and target lines. -/
theorem projectivelyReachable_congr
    {alphabet : List Matrix2}
    {firstSource secondSource firstTarget secondTarget : Vec2}
    (sourceSame : SameLine firstSource secondSource)
    (targetSame : SameLine firstTarget secondTarget) :
    ProjectivelyReachable alphabet firstSource firstTarget ↔
      ProjectivelyReachable alphabet secondSource secondTarget := by
  constructor
  · rintro ⟨word, wordOver, run⟩
    refine ⟨word, wordOver, ?_⟩
    exact (sourceSame.apply (matrixWordProduct word)).symm.trans
      (run.trans targetSame)
  · rintro ⟨word, wordOver, run⟩
    refine ⟨word, wordOver, ?_⟩
    exact (sourceSame.apply (matrixWordProduct word)).trans
      (run.trans targetSame.symm)

/-- The variable integer rank-one generator.  Its image line is represented
by the fixed first argument; only its kernel line depends on `input`. -/
def inputRankOneMatrix (input : Nat) : IntMatrix2 :=
  integerRankOneMatrix
    (integerEncodedConfiguration zeroHaltConfiguration)
    (integerEncodedConfiguration (inputConfiguration input))

/-- The exact integer mortality instance for one natural input. -/
def mortalityFamily (input : Nat) : List IntMatrix2 :=
  inputRankOneMatrix input :: listedMatrices

theorem inputRankOneMatrix_cast (input : Nat) :
    (inputRankOneMatrix input).cast =
      rankOneMatrix
        (integerEncodedConfiguration zeroHaltConfiguration).cast
        (integerEncodedConfiguration (inputConfiguration input)).cast := by
  simp [inputRankOneMatrix, cast_integerRankOneMatrix]

/-- Every value of the variable matrix has image contained in one fixed
projective line, independent of the input. -/
theorem inputRankOneMatrix_fixed_image (input : Nat) (vector : Vec2) :
    Matrix2.apply (inputRankOneMatrix input).cast vector =
      Vec2.scale
        (Vec2.dot
          (targetRow
            (integerEncodedConfiguration (inputConfiguration input)).cast)
          vector)
        (integerEncodedConfiguration zeroHaltConfiguration).cast := by
  rw [inputRankOneMatrix_cast]
  exact rankOneMatrix_apply _ _ _

theorem integerProjectivelyReachable_iff_u2Halts (input : Nat) :
    IntegerProjectivelyReachable listedMatrices
        (integerEncodedConfiguration zeroHaltConfiguration)
        (integerEncodedConfiguration (inputConfiguration input)) ↔
      SourceMachine.U2Halts input := by
  unfold IntegerProjectivelyReachable
  rw [← Compiler.GlobalConverse.projectivelyReachable_iff_u2Halts input]
  exact (projectivelyReachable_congr
    (encodedConfiguration_sameLine_integer zeroHaltConfiguration)
    (encodedConfiguration_sameLine_integer
      (inputConfiguration input))).symm

/-- Complete matrix-side reduction: the 5,799-matrix integer family is
mortal exactly on the halting inputs of the fixed source machine. -/
theorem mortalityFamily_iff_u2Halts (input : Nat) :
    IntegerMortal (mortalityFamily input) ↔ SourceMachine.U2Halts input := by
  rw [mortalityFamily, inputRankOneMatrix]
  exact (one_integer_rankOne_mortality_iff listedMatrices
    (integerEncodedConfiguration zeroHaltConfiguration)
    (integerEncodedConfiguration (inputConfiguration input))
    listedMatrices_nonsingular
    (integerEncodedConfiguration_nonzero zeroHaltConfiguration)
    (integerEncodedConfiguration_nonzero (inputConfiguration input))).trans
      (integerProjectivelyReachable_iff_u2Halts input)

/-- The matrix reduction composed with the fully checked
Korec-U20-to-Ivanov-U2 compiler. -/
theorem mortalityFamily_power_input_iff_u20Halts (input : Nat) :
    IntegerMortal (mortalityFamily (13 ^ input)) ↔
      SourceMachine.KorecU20.Halts input := by
  rw [mortalityFamily_iff_u2Halts]
  exact SourceMachine.U20Compilation.u2Halts_iff_u20Halts input

/-- The specialization matching Korec's two-input universality convention. -/
theorem mortalityFamily_twoInput_iff_u20HaltsTwo
    (programInput dataInput : Nat) :
    IntegerMortal
        (mortalityFamily (11 ^ programInput * 13 ^ dataInput)) ↔
      SourceMachine.KorecU20.HaltsTwo programInput dataInput := by
  rw [mortalityFamily_iff_u2Halts]
  exact SourceMachine.U20Compilation.u2Halts_iff_u20HaltsTwo
    programInput dataInput

/-- The matrix theorem composed with the checked four-counter-to-U2
pipeline.  The only extra hypotheses are the explicit Korec arithmetic
certificate and its relevance at this particular encoded source input. -/
theorem mortalityFamily_iff_fourCounterHalts
    (tagBound : Nat) (target : Nat → Nat)
    (program : SourceMachine.FourCounter.Program)
    (registers : SourceMachine.FourCounter.Registers) (tag : Nat)
    (tagInRange : tag < tagBound)
    (programCode leastNondivisor : Nat)
    (certificate : SourceMachine.KorecProgramCode.Certificate
      programCode leastNondivisor
      (SourceMachine.UniversalPipeline.r2Program tagBound target program))
    (initialRelevant : certificate.Relevant
      (SourceMachine.KorecR2.initialConfiguration
        (SourceMachine.UniversalPipeline.dataInput registers tag))) :
    IntegerMortal
        (mortalityFamily
          (11 ^ programCode *
            13 ^ SourceMachine.UniversalPipeline.dataInput registers tag)) ↔
      SourceMachine.FourCounter.HaltsFrom program
        ⟨target tag,
          SourceMachine.FourCounterInitializer.withTemp registers 0⟩ := by
  rw [mortalityFamily_iff_u2Halts]
  exact SourceMachine.UniversalPipeline.u2Halts_iff_fourCounterHalts
    tagBound target program registers tag tagInRange programCode
      leastNondivisor certificate initialRelevant

/-- Matrix-side reduction with the program code computed by the verified
finite CRT solver from a congruence layout. -/
theorem mortalityFamily_iff_fourCounterHalts_of_congruenceLayout
    (tagBound : Nat) (target : Nat → Nat)
    (program : SourceMachine.FourCounter.Program)
    (registers : SourceMachine.FourCounter.Registers) (tag : Nat)
    (tagInRange : tag < tagBound)
    (leastNondivisor : Nat)
    (layout : SourceMachine.KorecProgramCode.CongruenceLayout
      leastNondivisor
      (SourceMachine.UniversalPipeline.r2Program tagBound target program))
    (initialRelevant : layout.Relevant
      (SourceMachine.KorecR2.initialConfiguration
        (SourceMachine.UniversalPipeline.dataInput registers tag))) :
    IntegerMortal
        (mortalityFamily
          (11 ^ layout.crtProgramCode *
            13 ^ SourceMachine.UniversalPipeline.dataInput registers tag)) ↔
      SourceMachine.FourCounter.HaltsFrom program
        ⟨target tag,
          SourceMachine.FourCounterInitializer.withTemp registers 0⟩ := by
  rw [mortalityFamily_iff_u2Halts]
  exact
    SourceMachine.UniversalPipeline.u2Halts_iff_fourCounterHalts_of_congruenceLayout
      tagBound target program registers tag tagInRange leastNondivisor layout
      initialRelevant

/-- The matrix theorem for the simple three-state relocation specialization. -/
theorem mortalityFamily_iff_fourCounterHalts_relocated
    (offset tagBound : Nat) (target : Nat → Nat)
    (program : SourceMachine.FourCounter.Program)
    (registers : SourceMachine.FourCounter.Registers) (tag : Nat)
    (offsetLarge : 3 ≤ offset)
    (tagInRange : tag < tagBound)
    (programCode leastNondivisor : Nat)
    (certificate : SourceMachine.KorecProgramCode.Certificate
      programCode leastNondivisor
      (SourceMachine.UniversalPipeline.relocatedR2Program
        offset tagBound target program))
    (initialRelevant : certificate.Relevant
      (SourceMachine.KorecR2.initialConfiguration
        (SourceMachine.UniversalPipeline.dataInput registers tag))) :
    IntegerMortal
        (mortalityFamily
          (11 ^ programCode *
            13 ^ SourceMachine.UniversalPipeline.dataInput registers tag)) ↔
      SourceMachine.FourCounter.HaltsFrom program
        ⟨target tag,
          SourceMachine.FourCounterInitializer.withTemp registers 0⟩ := by
  rw [mortalityFamily_iff_u2Halts]
  exact
    SourceMachine.UniversalPipeline.u2Halts_iff_fourCounterHalts_relocated
      offset tagBound target program registers tag offsetLarge tagInRange
      programCode leastNondivisor certificate initialRelevant

/-- Matrix-side reduction entered directly at a relocated R2 state and an
arbitrary reader carry.  This removes the arithmetic entry-chain obligation;
the remaining hypothesis is exactly the carry-sensitive local-rank
certificate consumed by the verified U20 reader. -/
theorem mortalityFamily_iff_fourCounterHalts_relocated_localRank
    (offset tagBound : Nat) (target : Nat → Nat)
    (program : SourceMachine.FourCounter.Program)
    (registers : SourceMachine.FourCounter.Registers) (tag : Nat)
    (offsetLarge : 3 ≤ offset)
    (tagInRange : tag < tagBound)
    (programCode carry : Nat)
    (certificate : SourceMachine.KorecProgramCode.LocalRankCertificate
      programCode
      (SourceMachine.UniversalPipeline.relocatedR2Program
        offset tagBound target program))
    (initialRelevant : certificate.Relevant
      (SourceMachine.R2Relocation.shiftConfiguration offset
        (SourceMachine.KorecR2.initialConfiguration
          (SourceMachine.UniversalPipeline.dataInput registers tag))) carry) :
    IntegerMortal
        (mortalityFamily
          (SourceMachine.U20Compilation.encodeRegisters
            (SourceMachine.KorecU20Interpreter.registers 0 programCode
              (SourceMachine.UniversalPipeline.dataInput registers tag) 0
              offset 0 carry 0))) ↔
      SourceMachine.FourCounter.HaltsFrom program
        ⟨target tag,
          SourceMachine.FourCounterInitializer.withTemp registers 0⟩ := by
  rw [mortalityFamily_iff_u2Halts]
  exact
    SourceMachine.UniversalPipeline.u2Halts_iff_fourCounterHalts_relocated_localRank
      offset tagBound target program registers tag offsetLarge tagInRange
      programCode carry certificate initialRelevant

/-- Direct-entry matrix reduction whose numerical program code is computed
by the verified finite CRT solver from a carry-sensitive congruence layout. -/
theorem mortalityFamily_iff_fourCounterHalts_relocated_of_localCongruenceLayout
    (offset tagBound : Nat) (target : Nat → Nat)
    (program : SourceMachine.FourCounter.Program)
    (registers : SourceMachine.FourCounter.Registers) (tag : Nat)
    (offsetLarge : 3 ≤ offset)
    (tagInRange : tag < tagBound)
    (carry : Nat)
    (layout : SourceMachine.KorecLocalProgramCode.LocalCongruenceLayout
      (SourceMachine.UniversalPipeline.relocatedR2Program
        offset tagBound target program))
    (initialRelevant : layout.Relevant
      (SourceMachine.R2Relocation.shiftConfiguration offset
        (SourceMachine.KorecR2.initialConfiguration
          (SourceMachine.UniversalPipeline.dataInput registers tag))) carry) :
    IntegerMortal
        (mortalityFamily
          (SourceMachine.U20Compilation.encodeRegisters
            (SourceMachine.KorecU20Interpreter.registers 0
              layout.crtProgramCode
              (SourceMachine.UniversalPipeline.dataInput registers tag) 0
              offset 0 carry 0))) ↔
      SourceMachine.FourCounter.HaltsFrom program
        ⟨target tag,
          SourceMachine.FourCounterInitializer.withTemp registers 0⟩ := by
  rw [mortalityFamily_iff_u2Halts]
  exact
    SourceMachine.UniversalPipeline.u2Halts_iff_fourCounterHalts_relocated_of_localCongruenceLayout
      offset tagBound target program registers tag offsetLarge tagInRange carry
      layout initialRelevant

/-- Direct-entry matrix reduction from the compact local LCM layout. -/
theorem mortalityFamily_iff_fourCounterHalts_relocated_of_localLCMLayout
    (offset tagBound : Nat) (target : Nat → Nat)
    (program : SourceMachine.FourCounter.Program)
    (registers : SourceMachine.FourCounter.Registers) (tag : Nat)
    (offsetLarge : 3 ≤ offset)
    (tagInRange : tag < tagBound)
    (carry bound : Nat)
    (layout : SourceMachine.KorecLocalProgramCode.LocalLCMLayout bound
      (SourceMachine.UniversalPipeline.relocatedR2Program
        offset tagBound target program))
    (initialRelevant : layout.Relevant
      (SourceMachine.R2Relocation.shiftConfiguration offset
        (SourceMachine.KorecR2.initialConfiguration
          (SourceMachine.UniversalPipeline.dataInput registers tag))) carry) :
    IntegerMortal
        (mortalityFamily
          (SourceMachine.U20Compilation.encodeRegisters
            (SourceMachine.KorecU20Interpreter.registers 0
              layout.crtProgramCode
              (SourceMachine.UniversalPipeline.dataInput registers tag) 0
              offset 0 carry 0))) ↔
      SourceMachine.FourCounter.HaltsFrom program
        ⟨target tag,
          SourceMachine.FourCounterInitializer.withTemp registers 0⟩ := by
  rw [mortalityFamily_iff_u2Halts]
  exact
    SourceMachine.UniversalPipeline.u2Halts_iff_fourCounterHalts_relocated_of_localLCMLayout
      offset tagBound target program registers tag offsetLarge tagInRange carry
      bound layout initialRelevant

/-- The matrix reduction obtained directly from Korec's original global-rank
LCM layout.  Carry zero turns that layout into the local direct-entry layout,
so no arithmetic certificate for the relocation prefix is needed. -/
theorem mortalityFamily_iff_fourCounterHalts_relocated_of_globalLCMLayout
    (offset tagBound : Nat) (target : Nat → Nat)
    (program : SourceMachine.FourCounter.Program)
    (registers : SourceMachine.FourCounter.Registers) (tag : Nat)
    (offsetLarge : 3 ≤ offset)
    (tagInRange : tag < tagBound)
    (leastNondivisor bound : Nat)
    (layout : SourceMachine.KorecProgramCode.LCMLayout
      leastNondivisor bound
      (SourceMachine.UniversalPipeline.relocatedR2Program
        offset tagBound target program))
    (initialRelevant : layout.Relevant
      (SourceMachine.R2Relocation.shiftConfiguration offset
        (SourceMachine.KorecR2.initialConfiguration
          (SourceMachine.UniversalPipeline.dataInput registers tag)))) :
    IntegerMortal
        (mortalityFamily
          (SourceMachine.U20Compilation.encodeRegisters
            (SourceMachine.KorecU20Interpreter.registers 0
              layout.crtProgramCode
              (SourceMachine.UniversalPipeline.dataInput registers tag) 0
              offset 0 0 0))) ↔
      SourceMachine.FourCounter.HaltsFrom program
        ⟨target tag,
          SourceMachine.FourCounterInitializer.withTemp registers 0⟩ := by
  rw [mortalityFamily_iff_u2Halts]
  exact
    SourceMachine.UniversalPipeline.u2Halts_iff_fourCounterHalts_relocated_of_globalLCMLayout
      offset tagBound target program registers tag offsetLarge tagInRange
      leastNondivisor bound layout initialRelevant

/-- Uniform matrix reduction from Korec's global-rank arithmetic layout,
projected to finite control states. -/
theorem mortalityFamily_iff_fourCounterHalts_relocated_of_controlLCMLayout
    (offset tagBound : Nat) (target : Nat → Nat)
    (program : SourceMachine.FourCounter.Program)
    (registers : SourceMachine.FourCounter.Registers) (tag : Nat)
    (offsetLarge : 3 ≤ offset)
    (tagInRange : tag < tagBound)
    (leastNondivisor bound : Nat)
    (layout : SourceMachine.KorecLocalProgramCode.ControlLCMLayout
      leastNondivisor bound
      (SourceMachine.UniversalPipeline.relocatedR2Program
        offset tagBound target program))
    (initialRelevant : layout.Relevant (offset + 1)) :
    IntegerMortal
        (mortalityFamily
          (SourceMachine.U20Compilation.encodeRegisters
            (SourceMachine.KorecU20Interpreter.registers 0
              layout.crtProgramCode
              (SourceMachine.UniversalPipeline.dataInput registers tag) 0
              offset 0 0 0))) ↔
      SourceMachine.FourCounter.HaltsFrom program
        ⟨target tag,
          SourceMachine.FourCounterInitializer.withTemp registers 0⟩ := by
  rw [mortalityFamily_iff_u2Halts]
  exact
    SourceMachine.UniversalPipeline.u2Halts_iff_fourCounterHalts_relocated_of_controlLCMLayout
      offset tagBound target program registers tag offsetLarge tagInRange
      leastNondivisor bound layout initialRelevant

/-- Matrix reduction from a literal finite-state instance of Korec's
global-rank layout. -/
theorem mortalityFamily_iff_fourCounterHalts_relocated_of_finiteControlLCMLayout
    (offset tagBound : Nat) (target : Nat → Nat)
    (program : SourceMachine.FourCounter.Program)
    (registers : SourceMachine.FourCounter.Registers) (tag : Nat)
    (offsetLarge : 3 ≤ offset)
    (tagInRange : tag < tagBound)
    (leastNondivisor bound : Nat)
    (layout : SourceMachine.KorecLocalProgramCode.FiniteControlLCMLayout
      leastNondivisor bound
      (SourceMachine.UniversalPipeline.relocatedR2Program
        offset tagBound target program) (offset + 1)) :
    IntegerMortal
        (mortalityFamily
          (SourceMachine.U20Compilation.encodeRegisters
            (SourceMachine.KorecU20Interpreter.registers 0
              layout.crtProgramCode
              (SourceMachine.UniversalPipeline.dataInput registers tag) 0
              offset 0 0 0))) ↔
      SourceMachine.FourCounter.HaltsFrom program
        ⟨target tag,
          SourceMachine.FourCounterInitializer.withTemp registers 0⟩ := by
  rw [mortalityFamily_iff_u2Halts]
  exact
    SourceMachine.UniversalPipeline.u2Halts_iff_fourCounterHalts_relocated_of_finiteControlLCMLayout
      offset tagBound target program registers tag offsetLarge tagInRange
      leastNondivisor bound layout

/-- Branch-sensitive uniform matrix reduction.  The finite abstraction tracks
whether each unbounded R2 register is zero or positive. -/
theorem mortalityFamily_iff_fourCounterHalts_relocated_of_abstractControlLCMLayout
    (offset tagBound : Nat) (target : Nat → Nat)
    (program : SourceMachine.FourCounter.Program)
    (registers : SourceMachine.FourCounter.Registers) (tag : Nat)
    (offsetLarge : 3 ≤ offset)
    (tagInRange : tag < tagBound)
    (leastNondivisor bound : Nat)
    (layout : SourceMachine.KorecLocalProgramCode.AbstractControlLCMLayout
      leastNondivisor bound
      (SourceMachine.UniversalPipeline.relocatedR2Program
        offset tagBound target program))
    (initialRelevant : layout.Relevant
      { state := offset + 1
        registerZero :=
          SourceMachine.KorecLocalProgramCode.ZeroClass.zero
        registerTwo :=
          SourceMachine.KorecLocalProgramCode.ZeroClass.positive }) :
    IntegerMortal
        (mortalityFamily
          (SourceMachine.U20Compilation.encodeRegisters
            (SourceMachine.KorecU20Interpreter.registers 0
              layout.crtProgramCode
              (SourceMachine.UniversalPipeline.dataInput registers tag) 0
              offset 0 0 0))) ↔
      SourceMachine.FourCounter.HaltsFrom program
        ⟨target tag,
          SourceMachine.FourCounterInitializer.withTemp registers 0⟩ := by
  rw [mortalityFamily_iff_u2Halts]
  exact
    SourceMachine.UniversalPipeline.u2Halts_iff_fourCounterHalts_relocated_of_abstractControlLCMLayout
      offset tagBound target program registers tag offsetLarge tagInRange
      leastNondivisor bound layout initialRelevant

/-- Matrix reduction from a literal finite list of zero/positive abstract
control configurations and its global-rank arithmetic data. -/
theorem mortalityFamily_iff_fourCounterHalts_relocated_of_finiteAbstractControlLCMLayout
    (offset tagBound : Nat) (target : Nat → Nat)
    (program : SourceMachine.FourCounter.Program)
    (registers : SourceMachine.FourCounter.Registers) (tag : Nat)
    (offsetLarge : 3 ≤ offset)
    (tagInRange : tag < tagBound)
    (leastNondivisor bound : Nat)
    (layout : SourceMachine.KorecLocalProgramCode.FiniteAbstractControlLCMLayout
      leastNondivisor bound
      (SourceMachine.UniversalPipeline.relocatedR2Program
        offset tagBound target program)
      { state := offset + 1
        registerZero :=
          SourceMachine.KorecLocalProgramCode.ZeroClass.zero
        registerTwo :=
          SourceMachine.KorecLocalProgramCode.ZeroClass.positive }) :
    IntegerMortal
        (mortalityFamily
          (SourceMachine.U20Compilation.encodeRegisters
            (SourceMachine.KorecU20Interpreter.registers 0
              layout.crtProgramCode
              (SourceMachine.UniversalPipeline.dataInput registers tag) 0
              offset 0 0 0))) ↔
      SourceMachine.FourCounter.HaltsFrom program
        ⟨target tag,
          SourceMachine.FourCounterInitializer.withTemp registers 0⟩ := by
  rw [mortalityFamily_iff_u2Halts]
  exact
    SourceMachine.UniversalPipeline.u2Halts_iff_fourCounterHalts_relocated_of_finiteAbstractControlLCMLayout
      offset tagBound target program registers tag offsetLarge tagInRange
      leastNondivisor bound layout

/-- Exact matrix-family reduction after the one-state positive-target
normalization.  The only arithmetic hypothesis is a bounded Korec rank
shell; control closure generates the full LCM layout automatically. -/
theorem mortalityFamily_iff_fourCounterHalts_normalizedRelocated_of_rankShell
    (offset tagBound : Nat) (target : Nat → Nat)
    (program : SourceMachine.FourCounter.Program)
    (registers : SourceMachine.FourCounter.Registers) (tag : Nat)
    (offsetLarge : 3 ≤ offset)
    (tagInRange : tag < tagBound)
    (span leastNondivisor bound : Nat)
    (spanLarge : 2 < span)
    (normalizedClosed : SourceMachine.KorecR2.ClosedBelow
      (SourceMachine.UniversalPipeline.normalizedR2Program
        tagBound target program) span)
    (shell : SourceMachine.KorecNormalizedShell.RankShell offset span
      leastNondivisor bound
      (SourceMachine.UniversalPipeline.normalizedR2Program
        tagBound target program)) :
    IntegerMortal
        (mortalityFamily
          (SourceMachine.U20Compilation.encodeRegisters
            (SourceMachine.KorecU20Interpreter.registers 0
              ((shell.toControlLCMLayout offsetLarge
                (fun state statePositive _ =>
                  SourceMachine.R2PositiveTargets.normalize_operationAt
                    (SourceMachine.TwoCounterToKorecR2.compile_operationAt
                      (SourceMachine.UniversalPipeline.initializedTwoCounterProgram
                        tagBound target program))
                    state statePositive)
                (fun statePositive stateBounded lookup =>
                  SourceMachine.R2PositiveTargets.targetsBelow_of_closedBelow_lookup
                    normalizedClosed statePositive stateBounded lookup)
                (fun lookup =>
                  SourceMachine.R2PositiveTargets.normalize_decrement_target_positive
                    lookup))).crtProgramCode
              (SourceMachine.UniversalPipeline.dataInput registers tag) 0
              (offset + 1) 0 0 0))) ↔
      SourceMachine.FourCounter.HaltsFrom program
        ⟨target tag,
          SourceMachine.FourCounterInitializer.withTemp registers 0⟩ := by
  rw [mortalityFamily_iff_u2Halts]
  exact
    SourceMachine.UniversalPipeline.u2Halts_iff_fourCounterHalts_normalizedRelocated_of_rankShell
      offset tagBound target program registers tag offsetLarge tagInRange
      span leastNondivisor bound spanLarge normalizedClosed shell

/-- Program-independent arithmetic endpoint.  The rank frame contains only
selected factors, quotient ranks, primality-style divisor facts, and the two
candidate envelopes.  Residues, control closure, and carry invariants are
constructed by the preceding verified layers. -/
theorem mortalityFamily_iff_fourCounterHalts_normalizedRelocated_of_rankFrame
    (offset tagBound : Nat) (target : Nat → Nat)
    (program : SourceMachine.FourCounter.Program)
    (registers : SourceMachine.FourCounter.Registers) (tag : Nat)
    (offsetLarge : 3 ≤ offset)
    (tagInRange : tag < tagBound)
    (span leastNondivisor bound : Nat)
    (spanLarge : 2 < span)
    (normalizedClosed : SourceMachine.KorecR2.ClosedBelow
      (SourceMachine.UniversalPipeline.normalizedR2Program
        tagBound target program) span)
    (frame : SourceMachine.KorecNormalizedShell.RankFrame offset span
      leastNondivisor bound) :
    IntegerMortal
        (mortalityFamily
          (SourceMachine.U20Compilation.encodeRegisters
            (SourceMachine.KorecU20Interpreter.registers 0
              (SourceMachine.UniversalPipeline.normalizedRankFrameLayout
                offset tagBound target program offsetLarge span
                leastNondivisor bound normalizedClosed frame).crtProgramCode
              (SourceMachine.UniversalPipeline.dataInput registers tag) 0
              (offset + 1) 0 0 0))) ↔
      SourceMachine.FourCounter.HaltsFrom program
        ⟨target tag,
          SourceMachine.FourCounterInitializer.withTemp registers 0⟩ := by
  rw [mortalityFamily_iff_u2Halts]
  exact
    SourceMachine.UniversalPipeline.u2Halts_iff_fourCounterHalts_normalizedRelocated_of_rankFrame
      offset tagBound target program registers tag offsetLarge tagInRange
      span leastNondivisor bound spanLarge normalizedClosed frame

/-- Exact matrix-family reduction from the finite ordered-prime conclusions
of Korec's Lemma 6.1. -/
theorem mortalityFamily_iff_fourCounterHalts_normalizedRelocated_of_primeSystem
    (tagBound : Nat) (target : Nat → Nat)
    (program : SourceMachine.FourCounter.Program)
    (registers : SourceMachine.FourCounter.Registers) (tag : Nat)
    (tagInRange : tag < tagBound)
    (span : Nat) (spanLarge : 2 < span)
    (system : SourceMachine.KorecPrimeSystem.System span)
    (normalizedClosed : SourceMachine.KorecR2.ClosedBelow
      (SourceMachine.UniversalPipeline.normalizedR2Program
        tagBound target program) span) :
    IntegerMortal
        (mortalityFamily
          (SourceMachine.U20Compilation.encodeRegisters
            (SourceMachine.KorecU20Interpreter.registers 0
              (SourceMachine.UniversalPipeline.normalizedPrimeSystemLayout
                tagBound target program span system normalizedClosed).crtProgramCode
              (SourceMachine.UniversalPipeline.dataInput registers tag) 0
              (system.offset + 1) 0 0 0))) ↔
      SourceMachine.FourCounter.HaltsFrom program
        ⟨target tag,
          SourceMachine.FourCounterInitializer.withTemp registers 0⟩ := by
  rw [mortalityFamily_iff_u2Halts]
  exact
    SourceMachine.UniversalPipeline.u2Halts_iff_fourCounterHalts_normalizedRelocated_of_primeSystem
      tagBound target program registers tag tagInRange span spanLarge system
      normalizedClosed

/-- Uniform matrix reduction from a finite control-and-carry arithmetic
layout.  Its hypotheses are independent of the unbounded source registers. -/
theorem mortalityFamily_iff_fourCounterHalts_relocated_of_controlLocalLCMLayout
    (offset tagBound : Nat) (target : Nat → Nat)
    (program : SourceMachine.FourCounter.Program)
    (registers : SourceMachine.FourCounter.Registers) (tag : Nat)
    (offsetLarge : 3 ≤ offset)
    (tagInRange : tag < tagBound)
    (carry bound : Nat)
    (layout : SourceMachine.KorecLocalProgramCode.ControlLocalLCMLayout bound
      (SourceMachine.UniversalPipeline.relocatedR2Program
        offset tagBound target program))
    (initialRelevant : layout.Relevant (offset + 1) carry) :
    IntegerMortal
        (mortalityFamily
          (SourceMachine.U20Compilation.encodeRegisters
            (SourceMachine.KorecU20Interpreter.registers 0
              layout.crtProgramCode
              (SourceMachine.UniversalPipeline.dataInput registers tag) 0
              offset 0 carry 0))) ↔
      SourceMachine.FourCounter.HaltsFrom program
        ⟨target tag,
          SourceMachine.FourCounterInitializer.withTemp registers 0⟩ := by
  rw [mortalityFamily_iff_u2Halts]
  exact
    SourceMachine.UniversalPipeline.u2Halts_iff_fourCounterHalts_relocated_of_controlLocalLCMLayout
      offset tagBound target program registers tag offsetLarge tagInRange carry
      bound layout initialRelevant

/-- Matrix reduction from a literal finite control/carry and factor
certificate.  Every arithmetic premise is a bounded list condition when the
program and certificate data are executable. -/
theorem mortalityFamily_iff_fourCounterHalts_relocated_of_finiteControlLocalLCMLayout
    (offset tagBound : Nat) (target : Nat → Nat)
    (program : SourceMachine.FourCounter.Program)
    (registers : SourceMachine.FourCounter.Registers) (tag : Nat)
    (offsetLarge : 3 ≤ offset)
    (tagInRange : tag < tagBound)
    (carry bound : Nat)
    (layout : SourceMachine.KorecLocalProgramCode.FiniteControlLocalLCMLayout
      bound
      (SourceMachine.UniversalPipeline.relocatedR2Program
        offset tagBound target program)
      (offset + 1) carry) :
    IntegerMortal
        (mortalityFamily
          (SourceMachine.U20Compilation.encodeRegisters
            (SourceMachine.KorecU20Interpreter.registers 0
              layout.crtProgramCode
              (SourceMachine.UniversalPipeline.dataInput registers tag) 0
              offset 0 carry 0))) ↔
      SourceMachine.FourCounter.HaltsFrom program
        ⟨target tag,
          SourceMachine.FourCounterInitializer.withTemp registers 0⟩ := by
  rw [mortalityFamily_iff_u2Halts]
  exact
    SourceMachine.UniversalPipeline.u2Halts_iff_fourCounterHalts_relocated_of_finiteControlLocalLCMLayout
      offset tagBound target program registers tag offsetLarge tagInRange carry
      bound layout

/-- Final matrix equivalence for the general register-preserving entry chain
chosen by Korec's arithmetic encoding. -/
theorem mortalityFamily_iff_fourCounterHalts_embedded
    (offset : Nat) (entry : SourceMachine.KorecR2.Program)
    (tagBound : Nat) (target : Nat → Nat)
    (program : SourceMachine.FourCounter.Program)
    (registers : SourceMachine.FourCounter.Registers) (tag : Nat)
    (offsetPositive : 0 < offset)
    (entryCorrect : SourceMachine.R2Embedding.EntryCorrect offset entry
      (SourceMachine.UniversalPipeline.r2Program tagBound target program))
    (tagInRange : tag < tagBound)
    (programCode leastNondivisor : Nat)
    (certificate : SourceMachine.KorecProgramCode.Certificate
      programCode leastNondivisor
      (SourceMachine.UniversalPipeline.embeddedR2Program
        offset entry tagBound target program))
    (initialRelevant : certificate.Relevant
      (SourceMachine.KorecR2.initialConfiguration
        (SourceMachine.UniversalPipeline.dataInput registers tag))) :
    IntegerMortal
        (mortalityFamily
          (11 ^ programCode *
            13 ^ SourceMachine.UniversalPipeline.dataInput registers tag)) ↔
      SourceMachine.FourCounter.HaltsFrom program
        ⟨target tag,
          SourceMachine.FourCounterInitializer.withTemp registers 0⟩ := by
  rw [mortalityFamily_iff_u2Halts]
  exact
    SourceMachine.UniversalPipeline.u2Halts_iff_fourCounterHalts_embedded
      offset entry tagBound target program registers tag offsetPositive
      entryCorrect tagInRange programCode leastNondivisor certificate
      initialRelevant

/-- General-entry-chain matrix reduction with an executable CRT program
code. -/
theorem mortalityFamily_iff_fourCounterHalts_embedded_of_congruenceLayout
    (offset : Nat) (entry : SourceMachine.KorecR2.Program)
    (tagBound : Nat) (target : Nat → Nat)
    (program : SourceMachine.FourCounter.Program)
    (registers : SourceMachine.FourCounter.Registers) (tag : Nat)
    (offsetPositive : 0 < offset)
    (entryCorrect : SourceMachine.R2Embedding.EntryCorrect offset entry
      (SourceMachine.UniversalPipeline.r2Program tagBound target program))
    (tagInRange : tag < tagBound)
    (leastNondivisor : Nat)
    (layout : SourceMachine.KorecProgramCode.CongruenceLayout
      leastNondivisor
      (SourceMachine.UniversalPipeline.embeddedR2Program
        offset entry tagBound target program))
    (initialRelevant : layout.Relevant
      (SourceMachine.KorecR2.initialConfiguration
        (SourceMachine.UniversalPipeline.dataInput registers tag))) :
    IntegerMortal
        (mortalityFamily
          (11 ^ layout.crtProgramCode *
            13 ^ SourceMachine.UniversalPipeline.dataInput registers tag)) ↔
      SourceMachine.FourCounter.HaltsFrom program
        ⟨target tag,
          SourceMachine.FourCounterInitializer.withTemp registers 0⟩ := by
  rw [mortalityFamily_iff_u2Halts]
  exact
    SourceMachine.UniversalPipeline.u2Halts_iff_fourCounterHalts_embedded_of_congruenceLayout
      offset entry tagBound target program registers tag offsetPositive
      entryCorrect tagInRange leastNondivisor layout initialRelevant

/-- General-entry-chain matrix reduction using one verified unmarked-LCM
cover and the executable CRT code. -/
theorem mortalityFamily_iff_fourCounterHalts_embedded_of_lcmLayout
    (offset : Nat) (entry : SourceMachine.KorecR2.Program)
    (tagBound : Nat) (target : Nat → Nat)
    (program : SourceMachine.FourCounter.Program)
    (registers : SourceMachine.FourCounter.Registers) (tag : Nat)
    (offsetPositive : 0 < offset)
    (entryCorrect : SourceMachine.R2Embedding.EntryCorrect offset entry
      (SourceMachine.UniversalPipeline.r2Program tagBound target program))
    (tagInRange : tag < tagBound)
    (leastNondivisor bound : Nat)
    (layout : SourceMachine.KorecProgramCode.LCMLayout
      leastNondivisor bound
      (SourceMachine.UniversalPipeline.embeddedR2Program
        offset entry tagBound target program))
    (initialRelevant : layout.Relevant
      (SourceMachine.KorecR2.initialConfiguration
        (SourceMachine.UniversalPipeline.dataInput registers tag))) :
    IntegerMortal
        (mortalityFamily
          (11 ^ layout.crtProgramCode *
            13 ^ SourceMachine.UniversalPipeline.dataInput registers tag)) ↔
      SourceMachine.FourCounter.HaltsFrom program
        ⟨target tag,
          SourceMachine.FourCounterInitializer.withTemp registers 0⟩ := by
  rw [mortalityFamily_iff_u2Halts]
  exact
    SourceMachine.UniversalPipeline.u2Halts_iff_fourCounterHalts_embedded_of_lcmLayout
      offset entry tagBound target program registers tag offsetPositive
      entryCorrect tagInRange leastNondivisor bound layout initialRelevant

/-- Final conditional matrix equivalence from an arithmetic label plan and
its LCM layout.  The finite entry program, CRT program code, U2 simulation,
and 5,799-matrix family are all constructed internally. -/
theorem mortalityFamily_iff_fourCounterHalts_of_labelled_lcmLayout
    (offset macroCount : Nat) (labels : Nat → Nat)
    (tagBound : Nat) (target : Nat → Nat)
    (program : SourceMachine.FourCounter.Program)
    (registers : SourceMachine.FourCounter.Registers) (tag : Nat)
    (offsetPositive : 0 < offset)
    (labelsInjective : Function.Injective labels)
    (labelsPositive : ∀ position, position < 3 * macroCount →
      0 < labels position)
    (labelsReserved : ∀ position, position < 3 * macroCount →
      labels position ≤ offset)
    (labelsStart : labels 0 = 1)
    (labelsFinish : labels (3 * macroCount) = offset + 1)
    (tagInRange : tag < tagBound)
    (leastNondivisor bound : Nat)
    (layout : SourceMachine.KorecProgramCode.LCMLayout
      leastNondivisor bound
      (SourceMachine.UniversalPipeline.embeddedR2Program offset
        (SourceMachine.KorecEntryProgram.entryProgram labels macroCount)
        tagBound target program))
    (initialRelevant : layout.Relevant
      (SourceMachine.KorecR2.initialConfiguration
        (SourceMachine.UniversalPipeline.dataInput registers tag))) :
    IntegerMortal
        (mortalityFamily
          (11 ^ layout.crtProgramCode *
            13 ^ SourceMachine.UniversalPipeline.dataInput registers tag)) ↔
      SourceMachine.FourCounter.HaltsFrom program
        ⟨target tag,
          SourceMachine.FourCounterInitializer.withTemp registers 0⟩ := by
  rw [mortalityFamily_iff_u2Halts]
  exact
    SourceMachine.UniversalPipeline.u2Halts_iff_fourCounterHalts_of_labelled_lcmLayout
      offset macroCount labels tagBound target program registers tag
      offsetPositive labelsInjective labelsPositive labelsReserved labelsStart
      labelsFinish tagInRange leastNondivisor bound layout initialRelevant

theorem mortalityFamily_length (input : Nat) :
    (mortalityFamily input).length = 5799 := by
  simpa [mortalityFamily, inputRankOneMatrix] using
    (integer_rankOne_family_count
      (source := integerEncodedConfiguration zeroHaltConfiguration)
      (target := integerEncodedConfiguration (inputConfiguration input))
      listedMatrices_length)

theorem mortalityFamily_nodup (input : Nat) :
    (mortalityFamily input).Nodup := by
  unfold mortalityFamily inputRankOneMatrix
  exact integer_rankOne_cons_nodup
    Compiler.DistinctCertificate.listedMatrices_nodup
    listedMatrices_nonsingular

theorem inputRankOneMatrix_rankOne (input : Nat) :
    (inputRankOneMatrix input).RankOne := by
  unfold inputRankOneMatrix
  exact integerRankOneMatrix_rankOne
    (integerEncodedConfiguration_nonzero zeroHaltConfiguration)
    (integerEncodedConfiguration_nonzero (inputConfiguration input))

@[simp] theorem inputRankOneMatrix_det (input : Nat) :
    (inputRankOneMatrix input).det = 0 := by
  simp [inputRankOneMatrix]

end Mortality.Main
