import Mortality.SourceMachine.FourCounterInitializer
import Mortality.SourceMachine.FiniteControlBounds
import Mortality.SourceMachine.KorecEntryProgram
import Mortality.SourceMachine.KorecLocalProgramCode
import Mortality.SourceMachine.KorecNormalizedShell
import Mortality.SourceMachine.KorecPrimeSystem
import Mortality.SourceMachine.KorecProgramCode
import Mortality.SourceMachine.R2Embedding
import Mortality.SourceMachine.R2PositiveTargets
import Mortality.SourceMachine.R2Relocation
import Mortality.SourceMachine.TwoCounterToKorecR2

/-!
# End-to-end fixed-machine pipeline

This file composes the verified transformations:

* finite-control initialization of a four-counter program;
* prime-exponent compilation to an ordinary two-counter program;
* the eight-address compilation to Korec's R2 language;
* a certified numerical R2 program code interpreted by U20; and
* the exact U20-to-Ivanov-U2 simulation.

The theorem is parameterized only by the finite source program and its
number-theoretic Korec code certificate.  No semantic simulation hypothesis
is left between those endpoints.
-/

namespace Mortality.SourceMachine.UniversalPipeline

open Mortality.SourceMachine
open Mortality.SourceMachine.FourCounter
open Mortality.SourceMachine.FourCounterEncoding
open Mortality.SourceMachine.FourCounterInitializer
open Mortality.SourceMachine.KorecProgramCode
open Mortality.SourceMachine.KorecLocalProgramCode
open Mortality.SourceMachine.KorecU20Interpreter
open Mortality.SourceMachine.U20Compilation

def initializedTwoCounterProgram
    (tagBound : Nat) (target : Nat → Nat) (program : FourCounter.Program) :
    TotalTwoCounter.Program :=
  FourCounterToTwoCounter.compile
    (initializedProgram tagBound target program)

def r2Program
    (tagBound : Nat) (target : Nat → Nat) (program : FourCounter.Program) :
    KorecR2.Program :=
  Mortality.SourceMachine.TwoCounterToKorecR2.compile
    (initializedTwoCounterProgram tagBound target program)

/-- A simple three-state relocation layout.  States one through three form a
register-preserving entry macro, and all compiled source states are translated
above `offset`.  `embeddedR2Program` below is the general Korec interface. -/
def relocatedR2Program
    (offset tagBound : Nat) (target : Nat → Nat)
    (program : FourCounter.Program) : KorecR2.Program :=
  R2Relocation.relocate offset (r2Program tagBound target program)

/-- Insert one unconditional halt gateway before relocation.  Conditional
decrements in this program never advertise target zero. -/
def normalizedR2Program
    (tagBound : Nat) (target : Nat → Nat) (program : FourCounter.Program) :
    KorecR2.Program :=
  R2PositiveTargets.normalize (r2Program tagBound target program)

/-- Relocate the positive-target-normalized program.  Direct entry starts at
state `offset + 2`; the relocation prefix is unreachable from that state. -/
def normalizedRelocatedR2Program
    (offset tagBound : Nat) (target : Nat → Nat)
    (program : FourCounter.Program) : KorecR2.Program :=
  R2Relocation.relocate offset
    (normalizedR2Program tagBound target program)

/-- The general control layout used by the arithmetic construction.  Its
reserved prefix is supplied separately because Korec chooses the entry-chain
labels together with the nondivisors of the numerical program code. -/
def embeddedR2Program
    (offset : Nat) (entry : KorecR2.Program) (tagBound : Nat)
    (target : Nat → Nat) (program : FourCounter.Program) : KorecR2.Program :=
  R2Embedding.embed offset entry (r2Program tagBound target program)

def dataInput (registers : FourCounter.Registers) (tag : Nat) : Nat :=
  encode (withTemp registers tag)

/-- Exclusive control bound for the compiled R2 program, given an exclusive
bound on the original four-counter source states. -/
def r2StateBound (tagBound sourceBound : Nat) : Nat :=
  Mortality.SourceMachine.TwoCounterToKorecR2.compiledStateBound
    (FourCounterToTwoCounter.compiledStateBound
      (FourCounterInitializer.initializedStateBound tagBound sourceBound))

/-- The positive-target normalization adds one control state. -/
def normalizedR2StateBound (tagBound sourceBound : Nat) : Nat :=
  r2StateBound tagBound sourceBound + 1

theorem r2StateBound_large
    {tagBound sourceBound : Nat} (sourceBoundPositive : 0 < sourceBound) :
    1 < r2StateBound tagBound sourceBound := by
  apply Mortality.SourceMachine.TwoCounterToKorecR2.compiledStateBound_initial
  unfold FourCounterToTwoCounter.compiledStateBound
  simp [FourCounterInitializer.initializedStateBound,
    FourCounterInitializer.sourceOffset,
    FourCounterToTwoCounter.entry, FourCounterToTwoCounter.blockStride]
  omega

theorem normalizedR2StateBound_large
    {tagBound sourceBound : Nat} (sourceBoundPositive : 0 < sourceBound) :
    2 < normalizedR2StateBound tagBound sourceBound := by
  unfold normalizedR2StateBound
  have := r2StateBound_large (tagBound := tagBound) sourceBoundPositive
  omega

/-- The composed compiler preserves finite control.  The extra initializer
state at `tagBound` is included, although valid inputs use smaller tags. -/
theorem r2Program_closedBelow
    {tagBound sourceBound : Nat} {target : Nat → Nat}
    {program : FourCounter.Program}
    (sourceBoundPositive : 0 < sourceBound)
    (targetBounded : ∀ tag, tag < sourceOffset tagBound →
      target tag < sourceBound)
    (programClosed : FourCounter.ClosedBelow program sourceBound) :
    KorecR2.ClosedBelow (r2Program tagBound target program)
      (r2StateBound tagBound sourceBound) := by
  have initializedClosed : FourCounter.ClosedBelow
      (initializedProgram tagBound target program)
      (FourCounterInitializer.initializedStateBound tagBound sourceBound) :=
    initializedProgram_closedBelow sourceBoundPositive targetBounded
      programClosed
  have twoCounterClosed : TotalTwoCounter.ClosedBelow
      (FourCounterToTwoCounter.compile
        (initializedProgram tagBound target program))
      (FourCounterToTwoCounter.compiledStateBound
        (FourCounterInitializer.initializedStateBound tagBound sourceBound)) :=
    FourCounterToTwoCounter.compile_closedBelow initializedClosed
  have initializedBoundPositive :
      0 < FourCounterInitializer.initializedStateBound tagBound sourceBound := by
    simp [FourCounterInitializer.initializedStateBound, sourceOffset]
    omega
  have twoCounterBoundLarge :
      1 < FourCounterToTwoCounter.compiledStateBound
        (FourCounterInitializer.initializedStateBound tagBound sourceBound) := by
    unfold FourCounterToTwoCounter.compiledStateBound
    simp [FourCounterToTwoCounter.entry, FourCounterToTwoCounter.blockStride]
    omega
  change KorecR2.ClosedBelow
    (Mortality.SourceMachine.TwoCounterToKorecR2.compile
      (FourCounterToTwoCounter.compile
        (initializedProgram tagBound target program)))
    (Mortality.SourceMachine.TwoCounterToKorecR2.compiledStateBound
      (FourCounterToTwoCounter.compiledStateBound
        (FourCounterInitializer.initializedStateBound tagBound sourceBound)))
  exact Mortality.SourceMachine.TwoCounterToKorecR2.compile_closedBelow
    twoCounterBoundLarge twoCounterClosed

/-- The normalized program remains closed below the bound enlarged by one. -/
theorem normalizedR2Program_closedBelow
    {tagBound sourceBound : Nat} {target : Nat → Nat}
    {program : FourCounter.Program}
    (sourceBoundPositive : 0 < sourceBound)
    (targetBounded : ∀ tag, tag < sourceOffset tagBound →
      target tag < sourceBound)
    (programClosed : FourCounter.ClosedBelow program sourceBound) :
    KorecR2.ClosedBelow (normalizedR2Program tagBound target program)
      (normalizedR2StateBound tagBound sourceBound) := by
  exact R2PositiveTargets.normalize_closedBelow
    (r2Program_closedBelow sourceBoundPositive targetBounded programClosed)

/-- Exact halting equivalence from a finite four-counter source computation
to the literal 278-state Ivanov machine. -/
theorem u2Halts_iff_fourCounterHalts
    (tagBound : Nat) (target : Nat → Nat) (program : FourCounter.Program)
    (registers : FourCounter.Registers) (tag : Nat)
    (tagInRange : tag < tagBound)
    (programCode leastNondivisor : Nat)
    (certificate : Certificate programCode leastNondivisor
      (r2Program tagBound target program))
    (initialRelevant : certificate.Relevant
      (KorecR2.initialConfiguration (dataInput registers tag))) :
    U2Halts (11 ^ programCode * 13 ^ dataInput registers tag) ↔
      FourCounter.HaltsFrom program
        ⟨target tag, withTemp registers 0⟩ := by
  rw [u2Halts_iff_u20HaltsTwo]
  rw [u20HaltsTwo_iff_r2Halts certificate.toEncoding _
    (certificate.initialEncodingInvariant _ initialRelevant)]
  change KorecR2.Halts
      (Mortality.SourceMachine.TwoCounterToKorecR2.compile
        (initializedTwoCounterProgram tagBound target program))
      (encode (withTemp registers tag)) ↔ _
  rw [Mortality.SourceMachine.TwoCounterToKorecR2.compiledHalts_iff]
  change TotalTwoCounter.Halts
      (FourCounterToTwoCounter.compile
        (initializedProgram tagBound target program))
      (encode (withTemp registers tag)) ↔ _
  exact compiledInitializedHalts_iff tagBound target program registers tag
    tagInRange

/-- End-to-end specialization in which the finite CRT solver computes the
program code from a certified congruence layout. -/
theorem u2Halts_iff_fourCounterHalts_of_congruenceLayout
    (tagBound : Nat) (target : Nat → Nat) (program : FourCounter.Program)
    (registers : FourCounter.Registers) (tag : Nat)
    (tagInRange : tag < tagBound)
    (leastNondivisor : Nat)
    (layout : CongruenceLayout leastNondivisor
      (r2Program tagBound target program))
    (initialRelevant : layout.Relevant
      (KorecR2.initialConfiguration (dataInput registers tag))) :
    U2Halts
        (11 ^ layout.crtProgramCode * 13 ^ dataInput registers tag) ↔
      FourCounter.HaltsFrom program
        ⟨target tag, withTemp registers 0⟩ :=
  u2Halts_iff_fourCounterHalts tagBound target program registers tag
    tagInRange layout.crtProgramCode leastNondivisor
    layout.toCertificateByCRT initialRelevant

/-- End-to-end halting equivalence in the relocated control layout required
by Korec's numerical encoding construction.  The relocation theorem is
semantic: it accounts explicitly for the restart through state one on the
zero branch of an R2 conditional whose positive target is halt. -/
theorem u2Halts_iff_fourCounterHalts_relocated
    (offset tagBound : Nat) (target : Nat → Nat)
    (program : FourCounter.Program)
    (registers : FourCounter.Registers) (tag : Nat)
    (offsetLarge : 3 ≤ offset)
    (tagInRange : tag < tagBound)
    (programCode leastNondivisor : Nat)
    (certificate : Certificate programCode leastNondivisor
      (relocatedR2Program offset tagBound target program))
    (initialRelevant : certificate.Relevant
      (KorecR2.initialConfiguration (dataInput registers tag))) :
    U2Halts (11 ^ programCode * 13 ^ dataInput registers tag) ↔
      FourCounter.HaltsFrom program
        ⟨target tag, withTemp registers 0⟩ := by
  rw [u2Halts_iff_u20HaltsTwo]
  rw [u20HaltsTwo_iff_r2Halts certificate.toEncoding _
    (certificate.initialEncodingInvariant _ initialRelevant)]
  change KorecR2.Halts
      (R2Relocation.relocate offset
        (r2Program tagBound target program))
      (dataInput registers tag) ↔ _
  rw [R2Relocation.relocatedHalts_iff offset
    (r2Program tagBound target program) offsetLarge
    (Mortality.SourceMachine.TwoCounterToKorecR2.compile_operationAt
      (initializedTwoCounterProgram tagBound target program))]
  change KorecR2.Halts
      (Mortality.SourceMachine.TwoCounterToKorecR2.compile
        (initializedTwoCounterProgram tagBound target program))
      (encode (withTemp registers tag)) ↔ _
  rw [Mortality.SourceMachine.TwoCounterToKorecR2.compiledHalts_iff]
  change TotalTwoCounter.Halts
      (FourCounterToTwoCounter.compile
        (initializedProgram tagBound target program))
      (encode (withTemp registers tag)) ↔ _
  exact compiledInitializedHalts_iff tagBound target program registers tag
    tagInRange

/-- End-to-end halting equivalence entered directly at the relocated source
state.  The input supplies both the shifted control value in U20 register
`R4` and an arbitrary incoming instruction-reader carry in `R6`.  Thus the
arithmetic certificate need only verify the local increase in nondivisor
rank from that carry; no numerical encoding of the three-state entry macro
is required. -/
theorem u2Halts_iff_fourCounterHalts_relocated_localRank
    (offset tagBound : Nat) (target : Nat → Nat)
    (program : FourCounter.Program)
    (registers : FourCounter.Registers) (tag : Nat)
    (offsetLarge : 3 ≤ offset)
    (tagInRange : tag < tagBound)
    (programCode carry : Nat)
    (certificate : LocalRankCertificate programCode
      (relocatedR2Program offset tagBound target program))
    (initialRelevant : certificate.Relevant
      (R2Relocation.shiftConfiguration offset
        (KorecR2.initialConfiguration (dataInput registers tag))) carry) :
    U2Halts
        (U20Compilation.encodeRegisters
          (KorecU20Interpreter.registers 0 programCode
            (dataInput registers tag) 0 offset 0 carry 0)) ↔
      FourCounter.HaltsFrom program
        ⟨target tag, withTemp registers 0⟩ := by
  let start := KorecR2.initialConfiguration (dataInput registers tag)
  let shiftedStart := R2Relocation.shiftConfiguration offset start
  have shiftedPositive : 0 < shiftedStart.state := by
    change 0 < offset + 1
    omega
  have simulation := u2Halts_encodeSimulation_iff_r2HaltsFrom
    certificate.toEncoding shiftedStart carry shiftedPositive initialRelevant
  have simulation' :
      U2Halts
          (U20Compilation.encodeRegisters
            (KorecU20Interpreter.registers 0 programCode
              (dataInput registers tag) 0 offset 0 carry 0)) ↔
        KorecR2.HaltsFrom
          (relocatedR2Program offset tagBound target program) shiftedStart := by
    simpa [shiftedStart, start, R2Relocation.shiftConfiguration,
      R2Relocation.shiftState, KorecR2.initialConfiguration] using simulation
  rw [simulation']
  change R2Relocation.HaltsFrom
      (R2Relocation.relocate offset
        (r2Program tagBound target program))
      (R2Relocation.shiftConfiguration offset start) ↔ _
  rw [R2Relocation.shiftedHaltsFrom_iff offset
    (r2Program tagBound target program) offsetLarge
    (Mortality.SourceMachine.TwoCounterToKorecR2.compile_operationAt
      (initializedTwoCounterProgram tagBound target program)) start]
  change KorecR2.Halts
      (Mortality.SourceMachine.TwoCounterToKorecR2.compile
        (initializedTwoCounterProgram tagBound target program))
      (encode (withTemp registers tag)) ↔ _
  rw [Mortality.SourceMachine.TwoCounterToKorecR2.compiledHalts_iff]
  change TotalTwoCounter.Halts
      (FourCounterToTwoCounter.compile
        (initializedProgram tagBound target program))
      (encode (withTemp registers tag)) ↔ _
  exact compiledInitializedHalts_iff tagBound target program registers tag
    tagInRange

/-- Direct-entry pipeline after eliminating zero targets from conditional
decrements.  The normalized R2 start is state two, hence its relocated state
is `offset + 2` and U20 register `R4` initially stores `offset + 1`.

The normalization makes the relocation prefix unreachable: every conditional
destination is positive, while the sole target-zero instruction is the
unconditional halt gateway. -/
theorem u2Halts_iff_fourCounterHalts_normalizedRelocated_localRank
    (offset tagBound : Nat) (target : Nat → Nat)
    (program : FourCounter.Program)
    (registers : FourCounter.Registers) (tag : Nat)
    (offsetLarge : 3 ≤ offset)
    (tagInRange : tag < tagBound)
    (programCode carry : Nat)
    (certificate : LocalRankCertificate programCode
      (normalizedRelocatedR2Program offset tagBound target program))
    (initialRelevant : certificate.Relevant
      (R2Relocation.shiftConfiguration offset
        (R2PositiveTargets.shiftConfiguration
          (KorecR2.initialConfiguration (dataInput registers tag)))) carry) :
    U2Halts
        (U20Compilation.encodeRegisters
          (KorecU20Interpreter.registers 0 programCode
            (dataInput registers tag) 0 (offset + 1) 0 carry 0)) ↔
      FourCounter.HaltsFrom program
        ⟨target tag, withTemp registers 0⟩ := by
  let sourceStart := KorecR2.initialConfiguration (dataInput registers tag)
  let normalizedStart := R2PositiveTargets.shiftConfiguration sourceStart
  let shiftedStart := R2Relocation.shiftConfiguration offset normalizedStart
  have shiftedPositive : 0 < shiftedStart.state := by
    change 0 < offset + 2
    omega
  have simulation := u2Halts_encodeSimulation_iff_r2HaltsFrom
    certificate.toEncoding shiftedStart carry shiftedPositive initialRelevant
  have simulation' :
      U2Halts
          (U20Compilation.encodeRegisters
            (KorecU20Interpreter.registers 0 programCode
              (dataInput registers tag) 0 (offset + 1) 0 carry 0)) ↔
        KorecR2.HaltsFrom
          (normalizedRelocatedR2Program offset tagBound target program)
          shiftedStart := by
    simpa [shiftedStart, normalizedStart, sourceStart,
      R2Relocation.shiftConfiguration, R2Relocation.shiftState,
      R2PositiveTargets.shiftConfiguration, R2PositiveTargets.shiftState,
      KorecR2.initialConfiguration] using simulation
  rw [simulation']
  change R2Relocation.HaltsFrom
      (R2Relocation.relocate offset
        (R2PositiveTargets.normalize
          (r2Program tagBound target program)))
      (R2Relocation.shiftConfiguration offset normalizedStart) ↔ _
  rw [R2Relocation.shiftedHaltsFrom_iff offset
    (R2PositiveTargets.normalize (r2Program tagBound target program))
    offsetLarge (fun state statePositive => by
      by_cases stateOne : state = 1
      · subst state
        exact ⟨.incrementBoth 0, by simp⟩
      · have oldStatePositive : 0 < state - 1 := by omega
        obtain ⟨operation, lookup⟩ :=
          Mortality.SourceMachine.TwoCounterToKorecR2.compile_operationAt
            (initializedTwoCounterProgram tagBound target program)
            (state - 1) oldStatePositive
        exact ⟨R2PositiveTargets.shiftInstruction operation, by
          simp [R2PositiveTargets.normalize, Nat.ne_of_gt statePositive,
            stateOne, r2Program, lookup]⟩)
    normalizedStart]
  change KorecR2.HaltsFrom
      (R2PositiveTargets.normalize
        (r2Program tagBound target program))
      (R2PositiveTargets.shiftConfiguration sourceStart) ↔ _
  rw [R2PositiveTargets.normalizedHaltsFrom_iff
    (r2Program tagBound target program)
    (Mortality.SourceMachine.TwoCounterToKorecR2.compile_operationAt
      (initializedTwoCounterProgram tagBound target program)) sourceStart]
  change KorecR2.Halts
      (Mortality.SourceMachine.TwoCounterToKorecR2.compile
        (initializedTwoCounterProgram tagBound target program))
      (encode (withTemp registers tag)) ↔ _
  rw [Mortality.SourceMachine.TwoCounterToKorecR2.compiledHalts_iff]
  change TotalTwoCounter.Halts
      (FourCounterToTwoCounter.compile
        (initializedProgram tagBound target program))
      (encode (withTemp registers tag)) ↔ _
  exact compiledInitializedHalts_iff tagBound target program registers tag
    tagInRange

/-- The normalized direct-entry pipeline accepts Korec's original
global-rank LCM layout.  Carry zero converts it to the local-rank interface. -/
theorem u2Halts_iff_fourCounterHalts_normalizedRelocated_of_globalLCMLayout
    (offset tagBound : Nat) (target : Nat → Nat)
    (program : FourCounter.Program)
    (registers : FourCounter.Registers) (tag : Nat)
    (offsetLarge : 3 ≤ offset)
    (tagInRange : tag < tagBound)
    (leastNondivisor bound : Nat)
    (layout : KorecProgramCode.LCMLayout leastNondivisor bound
      (normalizedRelocatedR2Program offset tagBound target program))
    (initialRelevant : layout.Relevant
      (R2Relocation.shiftConfiguration offset
        (R2PositiveTargets.shiftConfiguration
          (KorecR2.initialConfiguration (dataInput registers tag))))) :
    U2Halts
        (U20Compilation.encodeRegisters
          (KorecU20Interpreter.registers 0 layout.crtProgramCode
            (dataInput registers tag) 0 (offset + 1) 0 0 0)) ↔
      FourCounter.HaltsFrom program
        ⟨target tag, withTemp registers 0⟩ := by
  exact
    u2Halts_iff_fourCounterHalts_normalizedRelocated_localRank
      offset tagBound target program registers tag offsetLarge tagInRange
      layout.crtProgramCode 0
      (LocalLCMLayout.ofGlobalLayout layout).toLocalRankCertificateByCRT
      (LocalLCMLayout.ofGlobalLayout_relevant_zero layout initialRelevant)

/-- A bounded rank shell is now the entire remaining arithmetic input for
the normalized reduction.  Finite control closure supplies all layout fields
that depend on transitions. -/
theorem u2Halts_iff_fourCounterHalts_normalizedRelocated_of_rankShell
    (offset tagBound : Nat) (target : Nat → Nat)
    (program : FourCounter.Program)
    (registers : FourCounter.Registers) (tag : Nat)
    (offsetLarge : 3 ≤ offset)
    (tagInRange : tag < tagBound)
    (span leastNondivisor bound : Nat)
    (spanLarge : 2 < span)
    (normalizedClosed : KorecR2.ClosedBelow
      (normalizedR2Program tagBound target program) span)
    (shell : KorecNormalizedShell.RankShell offset span
      leastNondivisor bound
      (normalizedR2Program tagBound target program)) :
    U2Halts
        (U20Compilation.encodeRegisters
          (KorecU20Interpreter.registers 0
            ((shell.toControlLCMLayout offsetLarge
              (fun state statePositive _stateBounded =>
                R2PositiveTargets.normalize_operationAt
                  (Mortality.SourceMachine.TwoCounterToKorecR2.compile_operationAt
                    (initializedTwoCounterProgram tagBound target program))
                  state statePositive)
              (fun statePositive stateBounded lookup =>
                R2PositiveTargets.targetsBelow_of_closedBelow_lookup
                  normalizedClosed statePositive stateBounded lookup)
              (fun lookup =>
                R2PositiveTargets.normalize_decrement_target_positive lookup))).crtProgramCode
            (dataInput registers tag) 0 (offset + 1) 0 0 0)) ↔
      FourCounter.HaltsFrom program
        ⟨target tag, withTemp registers 0⟩ := by
  let layout := shell.toControlLCMLayout offsetLarge
    (fun state statePositive _ =>
      R2PositiveTargets.normalize_operationAt
        (Mortality.SourceMachine.TwoCounterToKorecR2.compile_operationAt
          (initializedTwoCounterProgram tagBound target program))
        state statePositive)
    (fun statePositive stateBounded lookup =>
      R2PositiveTargets.targetsBelow_of_closedBelow_lookup
        normalizedClosed statePositive stateBounded lookup)
    (fun lookup =>
      R2PositiveTargets.normalize_decrement_target_positive lookup)
  apply
    u2Halts_iff_fourCounterHalts_normalizedRelocated_of_globalLCMLayout
      offset tagBound target program registers tag offsetLarge tagInRange
      leastNondivisor bound layout.toLCMLayout
  change KorecNormalizedShell.Relevant offset span
    (R2Relocation.shiftConfiguration offset
      (R2PositiveTargets.shiftConfiguration
        (KorecR2.initialConfiguration (dataInput registers tag)))).state
  right
  simp [R2Relocation.shiftConfiguration, R2Relocation.shiftState,
    R2PositiveTargets.shiftConfiguration, R2PositiveTargets.shiftState,
    KorecR2.initialConfiguration]
  omega

/-- Compiler-specialized rank-shell endpoint.  The source control bound
automatically supplies the normalized R2 span and its closure proof. -/
theorem u2Halts_iff_fourCounterHalts_normalizedRelocated_of_closedSourceRankShell
    (offset tagBound sourceBound : Nat) (target : Nat → Nat)
    (program : FourCounter.Program)
    (registers : FourCounter.Registers) (tag : Nat)
    (offsetLarge : 3 ≤ offset)
    (tagInRange : tag < tagBound)
    (sourceBoundPositive : 0 < sourceBound)
    (targetBounded : ∀ inputTag, inputTag < sourceOffset tagBound →
      target inputTag < sourceBound)
    (programClosed : FourCounter.ClosedBelow program sourceBound)
    (leastNondivisor bound : Nat)
    (shell : KorecNormalizedShell.RankShell offset
      (normalizedR2StateBound tagBound sourceBound)
      leastNondivisor bound
      (normalizedR2Program tagBound target program)) :
    U2Halts
        (U20Compilation.encodeRegisters
          (KorecU20Interpreter.registers 0
            ((shell.toControlLCMLayout offsetLarge
              (fun state statePositive _ =>
                R2PositiveTargets.normalize_operationAt
                  (Mortality.SourceMachine.TwoCounterToKorecR2.compile_operationAt
                    (initializedTwoCounterProgram tagBound target program))
                  state statePositive)
              (fun statePositive stateBounded lookup =>
                R2PositiveTargets.targetsBelow_of_closedBelow_lookup
                  (normalizedR2Program_closedBelow sourceBoundPositive
                    targetBounded programClosed)
                  statePositive stateBounded lookup)
              (fun lookup =>
                R2PositiveTargets.normalize_decrement_target_positive lookup))).crtProgramCode
            (dataInput registers tag) 0 (offset + 1) 0 0 0)) ↔
      FourCounter.HaltsFrom program
        ⟨target tag, withTemp registers 0⟩ := by
  exact u2Halts_iff_fourCounterHalts_normalizedRelocated_of_rankShell
    offset tagBound target program registers tag offsetLarge tagInRange
    (normalizedR2StateBound tagBound sourceBound) leastNondivisor bound
    (normalizedR2StateBound_large sourceBoundPositive)
    (normalizedR2Program_closedBelow sourceBoundPositive targetBounded
      programClosed)
    shell

/-- Assemble the normalized control layout from the program-independent
number-theoretic frame. -/
noncomputable def normalizedRankFrameLayout
    (offset tagBound : Nat) (target : Nat → Nat)
    (program : FourCounter.Program)
    (offsetLarge : 3 ≤ offset)
    (span leastNondivisor bound : Nat)
    (normalizedClosed : KorecR2.ClosedBelow
      (normalizedR2Program tagBound target program) span)
    (frame : KorecNormalizedShell.RankFrame offset span
      leastNondivisor bound) :
    ControlLCMLayout leastNondivisor bound
      (normalizedRelocatedR2Program offset tagBound target program) :=
  let operationAt : ∀ state, 0 < state → state < span →
      ∃ operation,
        normalizedR2Program tagBound target program state = some operation :=
    fun state statePositive _ =>
      R2PositiveTargets.normalize_operationAt
        (Mortality.SourceMachine.TwoCounterToKorecR2.compile_operationAt
          (initializedTwoCounterProgram tagBound target program))
        state statePositive
  let targetsBelow : ∀ {state operation}, 0 < state → state < span →
      normalizedR2Program tagBound target program state = some operation →
      operation.TargetsBelow span :=
    fun statePositive stateBounded lookup =>
      R2PositiveTargets.targetsBelow_of_closedBelow_lookup
        normalizedClosed statePositive stateBounded lookup
  let codePositive : ∀ {state operation}, 0 < state → state < span →
      normalizedR2Program tagBound target program state = some operation →
      0 < operation.code :=
    fun _ _ lookup => R2PositiveTargets.normalize_code_positive lookup
  (frame.toRankShell operationAt targetsBelow codePositive).toControlLCMLayout
    offsetLarge operationAt targetsBelow
    (fun lookup =>
      R2PositiveTargets.normalize_decrement_target_positive lookup)

/-- End-to-end direct-entry theorem whose sole arithmetic input is a
program-independent rank frame. -/
theorem u2Halts_iff_fourCounterHalts_normalizedRelocated_of_rankFrame
    (offset tagBound : Nat) (target : Nat → Nat)
    (program : FourCounter.Program)
    (registers : FourCounter.Registers) (tag : Nat)
    (offsetLarge : 3 ≤ offset)
    (tagInRange : tag < tagBound)
    (span leastNondivisor bound : Nat)
    (spanLarge : 2 < span)
    (normalizedClosed : KorecR2.ClosedBelow
      (normalizedR2Program tagBound target program) span)
    (frame : KorecNormalizedShell.RankFrame offset span
      leastNondivisor bound) :
    U2Halts
        (U20Compilation.encodeRegisters
          (KorecU20Interpreter.registers 0
            ((normalizedRankFrameLayout offset tagBound target program
              offsetLarge span leastNondivisor bound normalizedClosed frame).crtProgramCode)
            (dataInput registers tag) 0 (offset + 1) 0 0 0)) ↔
      FourCounter.HaltsFrom program
        ⟨target tag, withTemp registers 0⟩ := by
  let layout := normalizedRankFrameLayout offset tagBound target program
    offsetLarge span leastNondivisor bound normalizedClosed frame
  apply
    u2Halts_iff_fourCounterHalts_normalizedRelocated_of_globalLCMLayout
      offset tagBound target program registers tag offsetLarge tagInRange
      leastNondivisor bound layout.toLCMLayout
  change KorecNormalizedShell.Relevant offset span
    (R2Relocation.shiftConfiguration offset
      (R2PositiveTargets.shiftConfiguration
        (KorecR2.initialConfiguration (dataInput registers tag)))).state
  right
  simp [R2Relocation.shiftConfiguration, R2Relocation.shiftState,
    R2PositiveTargets.shiftConfiguration, R2PositiveTargets.shiftState,
    KorecR2.initialConfiguration]
  omega

/-- Assemble the normalized control layout directly from the finite
conclusions of Korec's Lemma 6.1. -/
noncomputable def normalizedPrimeSystemLayout
    (tagBound : Nat) (target : Nat → Nat)
    (program : FourCounter.Program)
    (span : Nat) (system : KorecPrimeSystem.System span)
    (normalizedClosed : KorecR2.ClosedBelow
      (normalizedR2Program tagBound target program) span) :
    ControlLCMLayout system.least system.bound
      (normalizedRelocatedR2Program system.offset tagBound target program) :=
  normalizedRankFrameLayout system.offset tagBound target program
    system.offset_large
    span system.least system.bound normalizedClosed system.toRankFrame

/-- End-to-end theorem from Korec's ordered-prime system.  Conditions
(6.1.6)--(6.1.7), which serve only the original numerical entry chain, do not
occur in this direct-entry formulation. -/
theorem u2Halts_iff_fourCounterHalts_normalizedRelocated_of_primeSystem
    (tagBound : Nat) (target : Nat → Nat)
    (program : FourCounter.Program)
    (registers : FourCounter.Registers) (tag : Nat)
    (tagInRange : tag < tagBound)
    (span : Nat) (spanLarge : 2 < span)
    (system : KorecPrimeSystem.System span)
    (normalizedClosed : KorecR2.ClosedBelow
      (normalizedR2Program tagBound target program) span) :
    U2Halts
        (U20Compilation.encodeRegisters
          (KorecU20Interpreter.registers 0
            ((normalizedPrimeSystemLayout tagBound target program span system
              normalizedClosed).crtProgramCode)
            (dataInput registers tag) 0 (system.offset + 1) 0 0 0)) ↔
      FourCounter.HaltsFrom program
        ⟨target tag, withTemp registers 0⟩ := by
  exact u2Halts_iff_fourCounterHalts_normalizedRelocated_of_rankFrame
    system.offset tagBound target program registers tag system.offset_large tagInRange
    span system.least system.bound spanLarge normalizedClosed system.toRankFrame

/-- Direct-entry specialization with an executable program code produced by
the verified finite CRT solver.  The hypotheses are now finite congruence,
factor-count, and control-flow conditions. -/
theorem u2Halts_iff_fourCounterHalts_relocated_of_localCongruenceLayout
    (offset tagBound : Nat) (target : Nat → Nat)
    (program : FourCounter.Program)
    (registers : FourCounter.Registers) (tag : Nat)
    (offsetLarge : 3 ≤ offset)
    (tagInRange : tag < tagBound)
    (carry : Nat)
    (layout : LocalCongruenceLayout
      (relocatedR2Program offset tagBound target program))
    (initialRelevant : layout.Relevant
      (R2Relocation.shiftConfiguration offset
        (KorecR2.initialConfiguration (dataInput registers tag))) carry) :
    U2Halts
        (U20Compilation.encodeRegisters
          (KorecU20Interpreter.registers 0 layout.crtProgramCode
            (dataInput registers tag) 0 offset 0 carry 0)) ↔
      FourCounter.HaltsFrom program
        ⟨target tag, withTemp registers 0⟩ :=
  u2Halts_iff_fourCounterHalts_relocated_localRank
    offset tagBound target program registers tag offsetLarge tagInRange
    layout.crtProgramCode carry layout.toLocalRankCertificateByCRT
    initialRelevant

/-- Direct-entry specialization in which a single unmarked-value LCM covers
all bounded divisors.  Only the selected-factor quotient counts, residues,
and carry invariant remain to be supplied. -/
theorem u2Halts_iff_fourCounterHalts_relocated_of_localLCMLayout
    (offset tagBound : Nat) (target : Nat → Nat)
    (program : FourCounter.Program)
    (registers : FourCounter.Registers) (tag : Nat)
    (offsetLarge : 3 ≤ offset)
    (tagInRange : tag < tagBound)
    (carry bound : Nat)
    (layout : LocalLCMLayout bound
      (relocatedR2Program offset tagBound target program))
    (initialRelevant : layout.Relevant
      (R2Relocation.shiftConfiguration offset
        (KorecR2.initialConfiguration (dataInput registers tag))) carry) :
    U2Halts
        (U20Compilation.encodeRegisters
          (KorecU20Interpreter.registers 0 layout.crtProgramCode
            (dataInput registers tag) 0 offset 0 carry 0)) ↔
      FourCounter.HaltsFrom program
        ⟨target tag, withTemp registers 0⟩ :=
  u2Halts_iff_fourCounterHalts_relocated_localRank
    offset tagBound target program registers tag offsetLarge tagInRange
    layout.crtProgramCode carry layout.toLocalRankCertificateByCRT
    initialRelevant

/-- Direct entry also accepts Korec's original global-rank LCM layout.  The
reader starts with carry zero, below the least selected factor; the global
rank equation therefore specializes to the carry-sensitive equation.  This
bridge reuses the published number-theoretic layout without encoding the
three-state arithmetic entry prefix. -/
theorem u2Halts_iff_fourCounterHalts_relocated_of_globalLCMLayout
    (offset tagBound : Nat) (target : Nat → Nat)
    (program : FourCounter.Program)
    (registers : FourCounter.Registers) (tag : Nat)
    (offsetLarge : 3 ≤ offset)
    (tagInRange : tag < tagBound)
    (leastNondivisor bound : Nat)
    (layout : KorecProgramCode.LCMLayout leastNondivisor bound
      (relocatedR2Program offset tagBound target program))
    (initialRelevant : layout.Relevant
      (R2Relocation.shiftConfiguration offset
        (KorecR2.initialConfiguration (dataInput registers tag)))) :
    U2Halts
        (U20Compilation.encodeRegisters
          (KorecU20Interpreter.registers 0 layout.crtProgramCode
            (dataInput registers tag) 0 offset 0 0 0)) ↔
      FourCounter.HaltsFrom program
        ⟨target tag, withTemp registers 0⟩ := by
  exact u2Halts_iff_fourCounterHalts_relocated_of_localLCMLayout
    offset tagBound target program registers tag offsetLarge tagInRange 0
    bound (LocalLCMLayout.ofGlobalLayout layout)
    (LocalLCMLayout.ofGlobalLayout_relevant_zero layout initialRelevant)

/-- Uniform form of the global Korec layout.  One finite control-state
invariant covers every valuation of the two R2 registers and hence every
encoded source input. -/
theorem u2Halts_iff_fourCounterHalts_relocated_of_controlLCMLayout
    (offset tagBound : Nat) (target : Nat → Nat)
    (program : FourCounter.Program)
    (registers : FourCounter.Registers) (tag : Nat)
    (offsetLarge : 3 ≤ offset)
    (tagInRange : tag < tagBound)
    (leastNondivisor bound : Nat)
    (layout : ControlLCMLayout leastNondivisor bound
      (relocatedR2Program offset tagBound target program))
    (initialRelevant : layout.Relevant (offset + 1)) :
    U2Halts
        (U20Compilation.encodeRegisters
          (KorecU20Interpreter.registers 0 layout.crtProgramCode
            (dataInput registers tag) 0 offset 0 0 0)) ↔
      FourCounter.HaltsFrom program
        ⟨target tag, withTemp registers 0⟩ := by
  apply u2Halts_iff_fourCounterHalts_relocated_of_globalLCMLayout
    offset tagBound target program registers tag offsetLarge tagInRange
    leastNondivisor bound layout.toLCMLayout
  change layout.Relevant (offset + 1)
  exact initialRelevant

/-- Fully finite form of the original global-rank arithmetic certificate. -/
theorem u2Halts_iff_fourCounterHalts_relocated_of_finiteControlLCMLayout
    (offset tagBound : Nat) (target : Nat → Nat)
    (program : FourCounter.Program)
    (registers : FourCounter.Registers) (tag : Nat)
    (offsetLarge : 3 ≤ offset)
    (tagInRange : tag < tagBound)
    (leastNondivisor bound : Nat)
    (layout : FiniteControlLCMLayout leastNondivisor bound
      (relocatedR2Program offset tagBound target program) (offset + 1)) :
    U2Halts
        (U20Compilation.encodeRegisters
          (KorecU20Interpreter.registers 0 layout.crtProgramCode
            (dataInput registers tag) 0 offset 0 0 0)) ↔
      FourCounter.HaltsFrom program
        ⟨target tag, withTemp registers 0⟩ :=
  u2Halts_iff_fourCounterHalts_relocated_of_controlLCMLayout
    offset tagBound target program registers tag offsetLarge tagInRange
    leastNondivisor bound layout.toControlLCMLayout layout.initialRelevant

/-- Branch-sensitive uniform form of the global layout.  Zero/positive
register classes exclude impossible decrement branches while remaining
finite and valid for every register magnitude. -/
theorem u2Halts_iff_fourCounterHalts_relocated_of_abstractControlLCMLayout
    (offset tagBound : Nat) (target : Nat → Nat)
    (program : FourCounter.Program)
    (registers : FourCounter.Registers) (tag : Nat)
    (offsetLarge : 3 ≤ offset)
    (tagInRange : tag < tagBound)
    (leastNondivisor bound : Nat)
    (layout : AbstractControlLCMLayout leastNondivisor bound
      (relocatedR2Program offset tagBound target program))
    (initialRelevant : layout.Relevant
      { state := offset + 1
        registerZero := .zero
        registerTwo := .positive }) :
    U2Halts
        (U20Compilation.encodeRegisters
          (KorecU20Interpreter.registers 0 layout.crtProgramCode
            (dataInput registers tag) 0 offset 0 0 0)) ↔
      FourCounter.HaltsFrom program
        ⟨target tag, withTemp registers 0⟩ := by
  apply u2Halts_iff_fourCounterHalts_relocated_of_globalLCMLayout
    offset tagBound target program registers tag offsetLarge tagInRange
    leastNondivisor bound layout.toLCMLayout
  change layout.Relevant
    (abstractConfiguration
      (R2Relocation.shiftConfiguration offset
        (KorecR2.initialConfiguration (dataInput registers tag))))
  simp only [abstractConfiguration, R2Relocation.shiftConfiguration,
    R2Relocation.shiftState, KorecR2.initialConfiguration,
    ZeroClass.classifyNat_zero]
  rw [show ZeroClass.classifyNat (dataInput registers tag) =
      .positive from
    ZeroClass.classifyNat_eq_positive_of_pos
      (FourCounterEncoding.encode_positive (withTemp registers tag))]
  exact initialRelevant

/-- Literal finite certificate for the exact zero/positive control graph. -/
theorem u2Halts_iff_fourCounterHalts_relocated_of_finiteAbstractControlLCMLayout
    (offset tagBound : Nat) (target : Nat → Nat)
    (program : FourCounter.Program)
    (registers : FourCounter.Registers) (tag : Nat)
    (offsetLarge : 3 ≤ offset)
    (tagInRange : tag < tagBound)
    (leastNondivisor bound : Nat)
    (layout : FiniteAbstractControlLCMLayout leastNondivisor bound
      (relocatedR2Program offset tagBound target program)
      { state := offset + 1
        registerZero := .zero
        registerTwo := .positive }) :
    U2Halts
        (U20Compilation.encodeRegisters
          (KorecU20Interpreter.registers 0 layout.crtProgramCode
            (dataInput registers tag) 0 offset 0 0 0)) ↔
      FourCounter.HaltsFrom program
        ⟨target tag, withTemp registers 0⟩ :=
  u2Halts_iff_fourCounterHalts_relocated_of_abstractControlLCMLayout
    offset tagBound target program registers tag offsetLarge tagInRange
    leastNondivisor bound layout.toAbstractControlLCMLayout
    layout.initialRelevant

/-- Uniform direct-entry specialization whose arithmetic invariant depends
only on the finite R2 control state and reader carry.  The same layout covers
every counter value, hence every source input. -/
theorem u2Halts_iff_fourCounterHalts_relocated_of_controlLocalLCMLayout
    (offset tagBound : Nat) (target : Nat → Nat)
    (program : FourCounter.Program)
    (registers : FourCounter.Registers) (tag : Nat)
    (offsetLarge : 3 ≤ offset)
    (tagInRange : tag < tagBound)
    (carry bound : Nat)
    (layout : ControlLocalLCMLayout bound
      (relocatedR2Program offset tagBound target program))
    (initialRelevant : layout.Relevant (offset + 1) carry) :
    U2Halts
        (U20Compilation.encodeRegisters
          (KorecU20Interpreter.registers 0 layout.crtProgramCode
            (dataInput registers tag) 0 offset 0 carry 0)) ↔
      FourCounter.HaltsFrom program
        ⟨target tag, withTemp registers 0⟩ := by
  apply u2Halts_iff_fourCounterHalts_relocated_of_localLCMLayout
    offset tagBound target program registers tag offsetLarge tagInRange carry
    bound layout.toLocalLCMLayout
  change layout.Relevant (offset + 1) carry
  exact initialRelevant

/-- Fully finite arithmetic specialization.  A literal list of relevant
control/carry pairs, together with finite factor and residue checks, computes
the numerical U2 input and proves the source halting equivalence. -/
theorem u2Halts_iff_fourCounterHalts_relocated_of_finiteControlLocalLCMLayout
    (offset tagBound : Nat) (target : Nat → Nat)
    (program : FourCounter.Program)
    (registers : FourCounter.Registers) (tag : Nat)
    (offsetLarge : 3 ≤ offset)
    (tagInRange : tag < tagBound)
    (carry bound : Nat)
    (layout : FiniteControlLocalLCMLayout bound
      (relocatedR2Program offset tagBound target program)
      (offset + 1) carry) :
    U2Halts
        (U20Compilation.encodeRegisters
          (KorecU20Interpreter.registers 0 layout.crtProgramCode
            (dataInput registers tag) 0 offset 0 carry 0)) ↔
      FourCounter.HaltsFrom program
        ⟨target tag, withTemp registers 0⟩ :=
  u2Halts_iff_fourCounterHalts_relocated_of_controlLocalLCMLayout
    offset tagBound target program registers tag offsetLarge tagInRange carry
    bound layout.toControlLocalLCMLayout layout.initialRelevant

/-- End-to-end equivalence for a general certified Korec entry chain.  This
is the semantic interface used by the number-theoretic program-code proof. -/
theorem u2Halts_iff_fourCounterHalts_embedded
    (offset : Nat) (entry : KorecR2.Program) (tagBound : Nat)
    (target : Nat → Nat) (program : FourCounter.Program)
    (registers : FourCounter.Registers) (tag : Nat)
    (offsetPositive : 0 < offset)
    (entryCorrect : R2Embedding.EntryCorrect offset entry
      (r2Program tagBound target program))
    (tagInRange : tag < tagBound)
    (programCode leastNondivisor : Nat)
    (certificate : Certificate programCode leastNondivisor
      (embeddedR2Program offset entry tagBound target program))
    (initialRelevant : certificate.Relevant
      (KorecR2.initialConfiguration (dataInput registers tag))) :
    U2Halts (11 ^ programCode * 13 ^ dataInput registers tag) ↔
      FourCounter.HaltsFrom program
        ⟨target tag, withTemp registers 0⟩ := by
  rw [u2Halts_iff_u20HaltsTwo]
  rw [u20HaltsTwo_iff_r2Halts certificate.toEncoding _
    (certificate.initialEncodingInvariant _ initialRelevant)]
  change KorecR2.Halts
      (R2Embedding.embed offset entry
        (r2Program tagBound target program))
      (dataInput registers tag) ↔ _
  rw [R2Embedding.embeddedHalts_iff offset entry
    (r2Program tagBound target program) offsetPositive entryCorrect
    (Mortality.SourceMachine.TwoCounterToKorecR2.compile_operationAt
      (initializedTwoCounterProgram tagBound target program))]
  change KorecR2.Halts
      (Mortality.SourceMachine.TwoCounterToKorecR2.compile
        (initializedTwoCounterProgram tagBound target program))
      (encode (withTemp registers tag)) ↔ _
  rw [Mortality.SourceMachine.TwoCounterToKorecR2.compiledHalts_iff]
  change TotalTwoCounter.Halts
      (FourCounterToTwoCounter.compile
        (initializedProgram tagBound target program))
      (encode (withTemp registers tag)) ↔ _
  exact compiledInitializedHalts_iff tagBound target program registers tag
    tagInRange

/-- General-entry-chain specialization with an executable CRT program code. -/
theorem u2Halts_iff_fourCounterHalts_embedded_of_congruenceLayout
    (offset : Nat) (entry : KorecR2.Program) (tagBound : Nat)
    (target : Nat → Nat) (program : FourCounter.Program)
    (registers : FourCounter.Registers) (tag : Nat)
    (offsetPositive : 0 < offset)
    (entryCorrect : R2Embedding.EntryCorrect offset entry
      (r2Program tagBound target program))
    (tagInRange : tag < tagBound)
    (leastNondivisor : Nat)
    (layout : CongruenceLayout leastNondivisor
      (embeddedR2Program offset entry tagBound target program))
    (initialRelevant : layout.Relevant
      (KorecR2.initialConfiguration (dataInput registers tag))) :
    U2Halts
        (11 ^ layout.crtProgramCode * 13 ^ dataInput registers tag) ↔
      FourCounter.HaltsFrom program
        ⟨target tag, withTemp registers 0⟩ :=
  u2Halts_iff_fourCounterHalts_embedded offset entry tagBound target program
    registers tag offsetPositive entryCorrect tagInRange
    layout.crtProgramCode leastNondivisor layout.toCertificateByCRT
    initialRelevant

/-- General-entry-chain specialization using the single unmarked-LCM cover.
The finite CRT program code is executable. -/
theorem u2Halts_iff_fourCounterHalts_embedded_of_lcmLayout
    (offset : Nat) (entry : KorecR2.Program) (tagBound : Nat)
    (target : Nat → Nat) (program : FourCounter.Program)
    (registers : FourCounter.Registers) (tag : Nat)
    (offsetPositive : 0 < offset)
    (entryCorrect : R2Embedding.EntryCorrect offset entry
      (r2Program tagBound target program))
    (tagInRange : tag < tagBound)
    (leastNondivisor bound : Nat)
    (layout : LCMLayout leastNondivisor bound
      (embeddedR2Program offset entry tagBound target program))
    (initialRelevant : layout.Relevant
      (KorecR2.initialConfiguration (dataInput registers tag))) :
    U2Halts
        (11 ^ layout.crtProgramCode * 13 ^ dataInput registers tag) ↔
      FourCounter.HaltsFrom program
        ⟨target tag, withTemp registers 0⟩ :=
  u2Halts_iff_fourCounterHalts_embedded_of_congruenceLayout
    offset entry tagBound target program registers tag offsetPositive
    entryCorrect tagInRange leastNondivisor layout.toCongruenceLayout
    initialRelevant

/-- Fully finite entry-chain specialization.  The entry program and its
semantic correctness are derived from the injective `3m + 1` label plan; the
remaining arithmetic input is the corresponding LCM layout. -/
theorem u2Halts_iff_fourCounterHalts_of_labelled_lcmLayout
    (offset macroCount : Nat) (labels : Nat → Nat) (tagBound : Nat)
    (target : Nat → Nat) (program : FourCounter.Program)
    (registers : FourCounter.Registers) (tag : Nat)
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
    (layout : LCMLayout leastNondivisor bound
      (embeddedR2Program offset
        (KorecEntryProgram.entryProgram labels macroCount)
        tagBound target program))
    (initialRelevant : layout.Relevant
      (KorecR2.initialConfiguration (dataInput registers tag))) :
    U2Halts
        (11 ^ layout.crtProgramCode * 13 ^ dataInput registers tag) ↔
      FourCounter.HaltsFrom program
        ⟨target tag, withTemp registers 0⟩ := by
  exact u2Halts_iff_fourCounterHalts_embedded_of_lcmLayout
    offset (KorecEntryProgram.entryProgram labels macroCount) tagBound target
    program registers tag offsetPositive
    (KorecEntryProgram.entryCorrect labelsInjective labelsPositive
      labelsReserved labelsStart labelsFinish)
    tagInRange leastNondivisor bound layout initialRelevant

/-- Finite-state specialization of the end-to-end theorem.  This is the
interface for either a literal bounded-search certificate or Korec's finite
number-theoretic construction. -/
theorem u2Halts_iff_fourCounterHalts_of_boundedCertificate
    (tagBound sourceBound : Nat) (target : Nat → Nat)
    (program : FourCounter.Program)
    (registers : FourCounter.Registers) (tag : Nat)
    (tagInRange : tag < tagBound)
    (programCode leastNondivisor : Nat)
    (certificate : BoundedCertificate programCode leastNondivisor
      (r2StateBound tagBound sourceBound)
      (r2Program tagBound target program)) :
    U2Halts (11 ^ programCode * 13 ^ dataInput registers tag) ↔
      FourCounter.HaltsFrom program
        ⟨target tag, withTemp registers 0⟩ :=
  u2Halts_iff_fourCounterHalts tagBound target program registers tag
    tagInRange programCode leastNondivisor certificate.toCertificate
    (certificate.initialRelevant _)

/-- Executable-certificate specialization.  Each nondivisor rank may be
verified by reducing the bounded search in `scanNondivisor`; unreachable
labels below `stateBound` are excluded by `certificate.Relevant`. -/
theorem u2Halts_iff_fourCounterHalts_of_finiteSearchCertificate
    (tagBound stateBound : Nat) (target : Nat → Nat)
    (program : FourCounter.Program)
    (registers : FourCounter.Registers) (tag : Nat)
    (tagInRange : tag < tagBound)
    (programCode leastNondivisor : Nat)
    (certificate : FiniteSearchCertificate programCode leastNondivisor
      stateBound (r2Program tagBound target program))
    (initialRelevant : certificate.Relevant
      (KorecR2.initialConfiguration (dataInput registers tag))) :
    U2Halts (11 ^ programCode * 13 ^ dataInput registers tag) ↔
      FourCounter.HaltsFrom program
        ⟨target tag, withTemp registers 0⟩ :=
  u2Halts_iff_fourCounterHalts tagBound target program registers tag
    tagInRange programCode leastNondivisor certificate.toCertificate
    initialRelevant

end Mortality.SourceMachine.UniversalPipeline
