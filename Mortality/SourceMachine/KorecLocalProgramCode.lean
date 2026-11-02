import Mortality.SourceMachine.KorecProgramCode

/-!
# Finite CRT certificates for carry-sensitive Korec codes

The ordinary Korec certificate restarts every instruction scan below the
first positive nondivisor.  Direct entry into an arbitrary U20 simulation
state permits a weaker invariant: the number of nondivisors strictly after
the incoming carry and through the selected candidate must equal the current
R2 state.

This file connects that local-rank condition to the same finite
selected-factor and Chinese-remainder machinery used by the global-rank
construction.  Its endpoint is an executable program code and a
`LocalRankCertificate`; no operational simulation premise remains.
-/

namespace Mortality.SourceMachine.KorecLocalProgramCode

open Mortality.SourceMachine
open Mortality.SourceMachine.KorecR2
open Mortality.SourceMachine.KorecNondivisorRank
open Mortality.SourceMachine.KorecCRT
open Mortality.SourceMachine.KorecProgramCode

/-- A selected-factor description of a carry-sensitive program code.  The
marking rule is required to characterize divisibility only through the
candidate used at the current boundary configuration. -/
structure LocalDivisorListCertificate (programCode : Nat)
    (program : KorecR2.Program) where
  Relevant : KorecR2.Configuration → Nat → Prop
  operationAt : ∀ {source carry}, Relevant source carry →
    0 < source.state → ∃ operation, program source.state = some operation
  selectedFactors : List Nat
  selectedNotDivides : ∀ factor, factor ∈ selectedFactors →
    ¬factor ∣ programCode + 1
  candidate : Nat → Nat
  candidatePositive : ∀ {source carry}, Relevant source carry →
    0 < source.state → 0 < candidate source.state
  carryBelowCandidate : ∀ {source carry}, Relevant source carry →
    0 < source.state → carry < candidate source.state
  unmarkedDivides : ∀ {source carry}, Relevant source carry →
    0 < source.state →
    ∀ value, 0 < value → value ≤ candidate source.state →
      markedByDivisorList selectedFactors value = false →
      value ∣ programCode + 1
  candidateMarked : ∀ {source carry}, Relevant source carry →
    0 < source.state →
    markedByDivisorList selectedFactors (candidate source.state) = true
  candidateRankDifference : ∀ {source carry}, Relevant source carry →
    0 < source.state →
    markedCount (markedByDivisorList selectedFactors)
        (candidate source.state) =
      markedCount (markedByDivisorList selectedFactors) carry + source.state
  residue : ∀ {source carry operation}, Relevant source carry →
    0 < source.state → program source.state = some operation →
    (programCode + 1) % candidate source.state = operation.code
  nextRelevant : ∀ {source target carry operation},
    Relevant source carry →
    program source.state = some operation →
    KorecR2.step program source = some target →
    Relevant target (candidate source.state - operation.code)

/-- Exact finite marking data imply the global-count difference required by
the carry-sensitive instruction reader. -/
def LocalDivisorListCertificate.toLocalRankCertificate
    {programCode : Nat} {program : KorecR2.Program}
    (certificate : LocalDivisorListCertificate programCode program) :
    LocalRankCertificate programCode program where
  Relevant := certificate.Relevant
  operationAt := certificate.operationAt
  candidate := certificate.candidate
  candidatePositive := certificate.candidatePositive
  carryBelowCandidate := certificate.carryBelowCandidate
  candidateNotDivides := by
    intro source carry relevant statePositive
    exact (markedByDivisorList_iff_not_dvd
      certificate.selectedNotDivides
      (certificate.unmarkedDivides relevant statePositive)
      (certificate.candidatePositive relevant statePositive) (by omega)).mp
      (certificate.candidateMarked relevant statePositive)
  candidateRankDifference := by
    intro source carry relevant statePositive
    have agrees : ∀ value, 0 < value →
        value ≤ certificate.candidate source.state →
        (markedByDivisorList certificate.selectedFactors value = true ↔
          ¬value ∣ programCode + 1) := by
      intro value valuePositive valueBounded
      exact markedByDivisorList_iff_not_dvd
        certificate.selectedNotDivides
        (certificate.unmarkedDivides relevant statePositive)
        valuePositive valueBounded
    have atCandidate :
        nondivisorCount programCode (certificate.candidate source.state) =
          markedCount (markedByDivisorList certificate.selectedFactors)
            (certificate.candidate source.state) :=
      nondivisorCount_eq_markedCount agrees
    have carryBound : carry ≤ certificate.candidate source.state :=
      Nat.le_of_lt (certificate.carryBelowCandidate relevant statePositive)
    have atCarry :
        nondivisorCount programCode carry =
          markedCount (markedByDivisorList certificate.selectedFactors)
            carry :=
      nondivisorCount_eq_markedCount
        (fun value positive bounded => agrees value positive
          (Nat.le_trans bounded carryBound))
    rw [atCandidate, atCarry]
    exact certificate.candidateRankDifference relevant statePositive
  residue := certificate.residue
  nextRelevant := certificate.nextRelevant

/-- A concrete CRT solution together with the finite factor-count
obligations.  Product separation makes the count of marked values a sum of
quotients both at the incoming carry and at the selected candidate. -/
structure LocalFactorLayoutCertificate (programCode : Nat)
    (program : KorecR2.Program) where
  Relevant : KorecR2.Configuration → Nat → Prop
  operationAt : ∀ {source carry}, Relevant source carry →
    0 < source.state → ∃ operation, program source.state = some operation
  selectedFactors : List Nat
  selectedResidue : Nat → Nat
  selectedResiduePositive : ∀ factor, factor ∈ selectedFactors →
    0 < selectedResidue factor
  selectedRemainder : ∀ factor, factor ∈ selectedFactors →
    (programCode + 1) % factor = selectedResidue factor
  coveringModuli : List Nat
  coveringModuliDivide : ∀ modulus, modulus ∈ coveringModuli →
    modulus ∣ programCode + 1
  coveringModuliPairwise : coveringModuli.Pairwise Nat.Coprime
  candidate : Nat → Nat
  candidatePositive : ∀ {source carry}, Relevant source carry →
    0 < source.state → 0 < candidate source.state
  carryBelowCandidate : ∀ {source carry}, Relevant source carry →
    0 < source.state → carry < candidate source.state
  candidateSeparated : ∀ {source carry}, Relevant source carry →
    0 < source.state →
    selectedFactors.Pairwise fun left right =>
      left.Coprime right ∧ candidate source.state < left * right
  candidateCover : ∀ {source carry}, Relevant source carry →
    0 < source.state →
    ∀ value, 0 < value → value ≤ candidate source.state →
      markedByDivisorList selectedFactors value = false →
      value ∣ KorecCRT.modulusProduct coveringModuli
  candidateMarked : ∀ {source carry}, Relevant source carry →
    0 < source.state →
    markedByDivisorList selectedFactors (candidate source.state) = true
  candidateRankDifferenceSum : ∀ {source carry}, Relevant source carry →
    0 < source.state →
    (selectedFactors.map fun factor => candidate source.state / factor).sum =
      (selectedFactors.map fun factor => carry / factor).sum + source.state
  residue : ∀ {source carry operation}, Relevant source carry →
    0 < source.state → program source.state = some operation →
    (programCode + 1) % candidate source.state = operation.code
  nextRelevant : ∀ {source target carry operation},
    Relevant source carry →
    program source.state = some operation →
    KorecR2.step program source = some target →
    Relevant target (candidate source.state - operation.code)

/-- A factor layout yields the exact finite marking certificate. -/
def LocalFactorLayoutCertificate.toLocalDivisorListCertificate
    {programCode : Nat} {program : KorecR2.Program}
    (certificate : LocalFactorLayoutCertificate programCode program) :
    LocalDivisorListCertificate programCode program where
  Relevant := certificate.Relevant
  operationAt := certificate.operationAt
  selectedFactors := certificate.selectedFactors
  selectedNotDivides :=
    selectedNotDivides_of_positive_residues
      certificate.selectedResiduePositive certificate.selectedRemainder
  candidate := certificate.candidate
  candidatePositive := certificate.candidatePositive
  carryBelowCandidate := certificate.carryBelowCandidate
  unmarkedDivides := by
    have productDivides :
        KorecCRT.modulusProduct certificate.coveringModuli ∣
          programCode + 1 :=
      KorecCRT.modulusProduct_dvd certificate.coveringModuliPairwise
        certificate.coveringModuliDivide
    intro source carry relevant statePositive value valuePositive valueBounded
      unmarked
    exact Nat.dvd_trans
      (certificate.candidateCover relevant statePositive value valuePositive
        valueBounded unmarked)
      productDivides
  candidateMarked := certificate.candidateMarked
  candidateRankDifference := by
    intro source carry relevant statePositive
    have separatedAtCandidate :=
      certificate.candidateSeparated relevant statePositive
    have carryBound : carry ≤ certificate.candidate source.state :=
      Nat.le_of_lt (certificate.carryBelowCandidate relevant statePositive)
    have separatedAtCarry : certificate.selectedFactors.Pairwise
        (fun left right => left.Coprime right ∧ carry < left * right) :=
      separatedAtCandidate.imp fun pair =>
        ⟨pair.1, Nat.lt_of_le_of_lt carryBound pair.2⟩
    rw [markedCount_divisorList_eq_sum_of_pairwise separatedAtCandidate,
      markedCount_divisorList_eq_sum_of_pairwise separatedAtCarry]
    exact certificate.candidateRankDifferenceSum relevant statePositive
  residue := certificate.residue
  nextRelevant := certificate.nextRelevant

/-- Factor layouts feed the operational U20 reader through the local-rank
interface. -/
def LocalFactorLayoutCertificate.toLocalRankCertificate
    {programCode : Nat} {program : KorecR2.Program}
    (certificate : LocalFactorLayoutCertificate programCode program) :
    LocalRankCertificate programCode program :=
  certificate.toLocalDivisorListCertificate.toLocalRankCertificate

/-- Finite congruence data before choosing the coded integer.  All fields
other than the congruence solution are elementary finite conditions on the
selected factors, the carries, and the R2 control graph. -/
structure LocalCongruenceLayout (program : KorecR2.Program) where
  Relevant : KorecR2.Configuration → Nat → Prop
  operationAt : ∀ {source carry}, Relevant source carry →
    0 < source.state → ∃ operation, program source.state = some operation
  congruenceModuli : List Nat
  congruenceResidue : Nat → Nat
  congruenceModuliPositive : ∀ modulus, modulus ∈ congruenceModuli →
    0 < modulus
  congruenceModuliPairwise : congruenceModuli.Pairwise Nat.Coprime
  selectedFactors : List Nat
  selectedResidue : Nat → Nat
  selectedResiduePositive : ∀ factor, factor ∈ selectedFactors →
    0 < selectedResidue factor
  selectedResidueBelow : ∀ factor, factor ∈ selectedFactors →
    selectedResidue factor < factor
  selectedCongruence : ∀ factor, factor ∈ selectedFactors →
    factor ∈ congruenceModuli ∧
      congruenceResidue factor = selectedResidue factor
  coveringModuli : List Nat
  coveringCongruence : ∀ modulus, modulus ∈ coveringModuli →
    modulus ∈ congruenceModuli ∧ congruenceResidue modulus = 0
  coveringModuliSublist : coveringModuli.Sublist congruenceModuli
  candidate : Nat → Nat
  candidatePositive : ∀ {source carry}, Relevant source carry →
    0 < source.state → 0 < candidate source.state
  carryBelowCandidate : ∀ {source carry}, Relevant source carry →
    0 < source.state → carry < candidate source.state
  candidateSeparated : ∀ {source carry}, Relevant source carry →
    0 < source.state →
    selectedFactors.Pairwise fun left right =>
      left.Coprime right ∧ candidate source.state < left * right
  candidateCover : ∀ {source carry}, Relevant source carry →
    0 < source.state →
    ∀ value, 0 < value → value ≤ candidate source.state →
      markedByDivisorList selectedFactors value = false →
      value ∣ KorecCRT.modulusProduct coveringModuli
  candidateMarked : ∀ {source carry}, Relevant source carry →
    0 < source.state →
    markedByDivisorList selectedFactors (candidate source.state) = true
  candidateRankDifferenceSum : ∀ {source carry}, Relevant source carry →
    0 < source.state →
    (selectedFactors.map fun factor => candidate source.state / factor).sum =
      (selectedFactors.map fun factor => carry / factor).sum + source.state
  candidateCongruence : ∀ {source carry operation}, Relevant source carry →
    0 < source.state → program source.state = some operation →
    candidate source.state ∈ congruenceModuli ∧
      congruenceResidue (candidate source.state) = operation.code ∧
      operation.code < candidate source.state
  nextRelevant : ∀ {source target carry operation},
    Relevant source carry →
    program source.state = some operation →
    KorecR2.step program source = some target →
    Relevant target (candidate source.state - operation.code)

/-- A simultaneous CRT solution supplies the concrete local factor layout. -/
def LocalCongruenceLayout.toLocalFactorLayoutCertificate
    {program : KorecR2.Program} (layout : LocalCongruenceLayout program)
    (programCode : Nat)
    (satisfies : SatisfiesCongruences (programCode + 1)
      layout.congruenceModuli layout.congruenceResidue) :
    LocalFactorLayoutCertificate programCode program where
  Relevant := layout.Relevant
  operationAt := layout.operationAt
  selectedFactors := layout.selectedFactors
  selectedResidue := layout.selectedResidue
  selectedResiduePositive := layout.selectedResiduePositive
  selectedRemainder := by
    intro factor factorMem
    obtain ⟨modulusMem, residueEquality⟩ :=
      layout.selectedCongruence factor factorMem
    have prescribedBelow : layout.congruenceResidue factor < factor := by
      rw [residueEquality]
      exact layout.selectedResidueBelow factor factorMem
    have exactResidue := satisfies.exact modulusMem prescribedBelow
    simpa [residueEquality] using exactResidue
  coveringModuli := layout.coveringModuli
  coveringModuliDivide := by
    intro modulus modulusMem
    obtain ⟨congruenceMem, residueZero⟩ :=
      layout.coveringCongruence modulus modulusMem
    exact satisfies.dvd_of_residue_zero congruenceMem residueZero
  coveringModuliPairwise :=
    layout.congruenceModuliPairwise.sublist layout.coveringModuliSublist
  candidate := layout.candidate
  candidatePositive := layout.candidatePositive
  carryBelowCandidate := layout.carryBelowCandidate
  candidateSeparated := layout.candidateSeparated
  candidateCover := layout.candidateCover
  candidateMarked := layout.candidateMarked
  candidateRankDifferenceSum := layout.candidateRankDifferenceSum
  residue := by
    intro source carry operation relevant statePositive lookup
    obtain ⟨modulusMem, residueEquality, residueBelow⟩ :=
      layout.candidateCongruence relevant statePositive lookup
    have prescribedBelow :
        layout.congruenceResidue (layout.candidate source.state) <
          layout.candidate source.state := by
      rw [residueEquality]
      exact residueBelow
    have exactResidue := satisfies.exact modulusMem prescribedBelow
    simpa [residueEquality] using exactResidue
  nextRelevant := layout.nextRelevant

/-- Executable coded program obtained from the finite congruence layout. -/
def LocalCongruenceLayout.crtProgramCode
    {program : KorecR2.Program} (layout : LocalCongruenceLayout program) : Nat :=
  KorecCRT.programCode layout.congruenceModuli layout.congruenceResidue

/-- The verified finite CRT solver constructs the concrete factor layout. -/
def LocalCongruenceLayout.toLocalFactorLayoutCertificateByCRT
    {program : KorecR2.Program} (layout : LocalCongruenceLayout program) :
    LocalFactorLayoutCertificate layout.crtProgramCode program :=
  layout.toLocalFactorLayoutCertificate layout.crtProgramCode
    (KorecCRT.programCode_spec layout.congruenceModuliPositive
      layout.congruenceModuliPairwise)

/-- A finite local congruence layout supplies the exact carry-sensitive
certificate consumed by the U20 simulation. -/
def LocalCongruenceLayout.toLocalRankCertificateByCRT
    {program : KorecR2.Program} (layout : LocalCongruenceLayout program) :
    LocalRankCertificate layout.crtProgramCode program :=
  layout.toLocalFactorLayoutCertificateByCRT.toLocalRankCertificate

/-- A compact local layout using the LCM of all bounded unmarked values as
its sole zero-residue covering modulus. -/
structure LocalLCMLayout (bound : Nat) (program : KorecR2.Program) where
  Relevant : KorecR2.Configuration → Nat → Prop
  operationAt : ∀ {source carry}, Relevant source carry →
    0 < source.state → ∃ operation, program source.state = some operation
  selectedFactors : List Nat
  selectedNodup : selectedFactors.Nodup
  selectedProductSeparated : selectedFactors.Pairwise fun left right =>
    bound < left * right
  selectedAtMostBound : ∀ factor, factor ∈ selectedFactors →
    factor ≤ bound
  selectedResidue : Nat → Nat
  selectedResiduePositive : ∀ factor, factor ∈ selectedFactors →
    0 < selectedResidue factor
  selectedResidueBelow : ∀ factor, factor ∈ selectedFactors →
    selectedResidue factor < factor
  selectedDivisorClassification : ∀ factor, factor ∈ selectedFactors →
    ∀ divisor, divisor ∣ factor → divisor = 1 ∨ divisor = factor
  candidate : Nat → Nat
  candidateMem : ∀ {source carry}, Relevant source carry →
    0 < source.state → candidate source.state ∈ selectedFactors
  carryBelowCandidate : ∀ {source carry}, Relevant source carry →
    0 < source.state → carry < candidate source.state
  candidateRankDifferenceSum : ∀ {source carry}, Relevant source carry →
    0 < source.state →
    (selectedFactors.map fun factor => candidate source.state / factor).sum =
      (selectedFactors.map fun factor => carry / factor).sum + source.state
  operationResidue : ∀ {source carry operation}, Relevant source carry →
    0 < source.state → program source.state = some operation →
    selectedResidue (candidate source.state) = operation.code
  nextRelevant : ∀ {source target carry operation},
    Relevant source carry →
    program source.state = some operation →
    KorecR2.step program source = some target →
    Relevant target (candidate source.state - operation.code)

/-- A global Korec layout also supplies the carry-sensitive layout whenever
the incoming carry is below its least selected factor.  At such a carry every
selected-factor quotient is zero, so the global rank equation is exactly the
required local rank-difference equation.  The implication on the carry bound
is vacuous at the halting state, where the reader is never entered again. -/
def LocalLCMLayout.ofGlobalLayout
    {leastNondivisor bound : Nat} {program : KorecR2.Program}
    (layout : KorecProgramCode.LCMLayout leastNondivisor bound program) :
    LocalLCMLayout bound program where
  Relevant source carry :=
    layout.Relevant source ∧ (0 < source.state → carry < leastNondivisor)
  operationAt := fun relevant statePositive =>
    layout.operationAt relevant.1 statePositive
  selectedFactors := layout.selectedFactors
  selectedNodup := layout.selectedNodup
  selectedProductSeparated := layout.selectedProductSeparated
  selectedAtMostBound := layout.selectedAtMostBound
  selectedResidue := layout.selectedResidue
  selectedResiduePositive := layout.selectedResiduePositive
  selectedResidueBelow := layout.selectedResidueBelow
  selectedDivisorClassification := layout.selectedDivisorClassification
  candidate := layout.candidate
  candidateMem := fun relevant statePositive =>
    layout.candidateMem relevant.1 statePositive
  carryBelowCandidate := by
    intro source carry relevant statePositive
    have carryBelowLeast := relevant.2 statePositive
    have leastBelowCandidate := layout.selectedAtLeastLeast
      (layout.candidate source.state)
      (layout.candidateMem relevant.1 statePositive)
    exact Nat.lt_of_lt_of_le carryBelowLeast leastBelowCandidate
  candidateRankDifferenceSum := by
    intro source carry relevant statePositive
    have carryQuotientsZero :
        (layout.selectedFactors.map fun factor => carry / factor) =
          layout.selectedFactors.map fun _ => 0 := by
      apply List.map_congr_left
      intro factor factorMem
      exact Nat.div_eq_of_lt <|
        Nat.lt_of_lt_of_le (relevant.2 statePositive)
          (layout.selectedAtLeastLeast factor factorMem)
    rw [layout.candidateRankSum relevant.1 statePositive,
      carryQuotientsZero]
    have zeroSum : ∀ factors : List Nat,
        (factors.map fun _ => 0).sum = 0 := by
      intro factors
      induction factors with
      | nil => rfl
      | cons factor factors inductionHypothesis =>
          rw [List.map_cons, List.sum_cons, inductionHypothesis,
            Nat.zero_add]
    rw [zeroSum, Nat.zero_add]
  operationResidue := fun relevant statePositive lookup =>
    layout.operationResidue relevant.1 statePositive lookup
  nextRelevant := by
    intro source target carry operation relevant lookup stepEq
    constructor
    · exact layout.nextRelevant relevant.1 lookup stepEq
    · intro targetPositive
      exact layout.nextCarryBelow relevant.1 lookup stepEq targetPositive

@[simp] theorem LocalLCMLayout.ofGlobalLayout_relevant_zero
    {leastNondivisor bound : Nat} {program : KorecR2.Program}
    (layout : KorecProgramCode.LCMLayout leastNondivisor bound program)
    {source : KorecR2.Configuration} (relevant : layout.Relevant source) :
    (LocalLCMLayout.ofGlobalLayout layout).Relevant source 0 := by
  exact ⟨relevant, fun _ => layout.leastPositive⟩

/-- The control states that one R2 instruction can reach.  A conditional
decrement uses its advertised target on the positive branch and the following
state on the zero branch. -/
def possibleTargets : KorecR2.Instruction → List Nat
  | .incrementBoth target => [target]
  | .decrement _ positiveTarget => [positiveTarget, positiveTarget + 1]

/-- Nondeterministic control-and-carry step obtained by forgetting the two
counter values.  A decrement therefore retains both possible branches. -/
def controlStep (program : KorecR2.Program) (candidate : Nat → Nat)
    (before after : Nat × Nat) : Prop :=
  ∃ operation,
    program before.1 = some operation ∧
    after.1 ∈ possibleTargets operation ∧
    after.2 = candidate before.1 - operation.code

inductive ControlReachable (program : KorecR2.Program)
    (candidate : Nat → Nat) (initial : Nat × Nat) : Nat → Nat → Prop
  | refl : ControlReachable program candidate initial initial.1 initial.2
  | tail {state carry target nextCarry : Nat} :
      ControlReachable program candidate initial state carry →
      controlStep program candidate (state, carry) (target, nextCarry) →
      ControlReachable program candidate initial target nextCarry

theorem step_state_mem_possibleTargets
    {program : KorecR2.Program}
    {source target : KorecR2.Configuration}
    {operation : KorecR2.Instruction}
    (lookup : program source.state = some operation)
    (stepEq : KorecR2.step program source = some target) :
    target.state ∈ possibleTargets operation := by
  rcases source with ⟨state, registerZero, registerTwo⟩
  have statePositive : 0 < state := by
    by_cases stateZero : state = 0
    · simp [KorecR2.step, stateZero] at stepEq
    · omega
  cases operation with
  | incrementBoth next =>
      simp [KorecR2.step, Nat.ne_of_gt statePositive, lookup] at stepEq
      subst target
      simp [possibleTargets]
  | decrement register next =>
      cases register with
      | zero =>
          cases registerZero <;>
            simp [KorecR2.step, Nat.ne_of_gt statePositive, lookup] at stepEq <;>
            subst target <;> simp [possibleTargets]
      | one =>
          cases registerTwo <;>
            simp [KorecR2.step, Nat.ne_of_gt statePositive, lookup] at stepEq <;>
            subst target <;> simp [possibleTargets]

/-- Exact zero/positive information for one unbounded R2 register. -/
inductive ZeroClass where
  | zero
  | positive
  deriving DecidableEq, Repr

def ZeroClass.classifyNat : Nat → ZeroClass
  | 0 => .zero
  | _ + 1 => .positive

@[simp] theorem ZeroClass.classifyNat_zero :
    ZeroClass.classifyNat 0 = .zero :=
  rfl

theorem ZeroClass.classifyNat_eq_positive_of_pos {value : Nat}
    (positive : 0 < value) :
    ZeroClass.classifyNat value = .positive := by
  obtain ⟨predecessor, rfl⟩ := Nat.exists_eq_succ_of_ne_zero
    (Nat.ne_of_gt positive)
  rfl

structure AbstractConfiguration where
  state : Nat
  registerZero : ZeroClass
  registerTwo : ZeroClass
  deriving DecidableEq, Repr

def abstractConfiguration (configuration : KorecR2.Configuration) :
    AbstractConfiguration :=
  { state := configuration.state
    registerZero := ZeroClass.classifyNat configuration.registerZero
    registerTwo := ZeroClass.classifyNat configuration.registerTwo }

/-- Exact finite successors of one abstract R2 configuration after the
instruction lookup has succeeded.  Decrementing a positive register may
leave either zero or a positive value; all other zero tests are determined. -/
def abstractSuccessors (operation : KorecR2.Instruction)
    (source : AbstractConfiguration) : List AbstractConfiguration :=
  match operation with
  | .incrementBoth target =>
      [{ state := target
         registerZero := .positive
         registerTwo := .positive }]
  | .decrement .zero target =>
      match source.registerZero with
      | .zero =>
          [{ source with state := target + 1 }]
      | .positive =>
          [{ state := target
             registerZero := .zero
             registerTwo := source.registerTwo },
           { state := target
             registerZero := .positive
             registerTwo := source.registerTwo }]
  | .decrement .one target =>
      match source.registerTwo with
      | .zero =>
          [{ source with state := target + 1 }]
      | .positive =>
          [{ state := target
             registerZero := source.registerZero
             registerTwo := .zero },
           { state := target
             registerZero := source.registerZero
             registerTwo := .positive }]

/-- The zero/positive abstraction contains the abstraction of every concrete
R2 successor. -/
theorem abstractConfiguration_mem_abstractSuccessors
    {program : KorecR2.Program}
    {source target : KorecR2.Configuration}
    {operation : KorecR2.Instruction}
    (lookup : program source.state = some operation)
    (stepEq : KorecR2.step program source = some target) :
    abstractConfiguration target ∈
      abstractSuccessors operation (abstractConfiguration source) := by
  rcases source with ⟨state, registerZero, registerTwo⟩
  have statePositive : 0 < state := by
    by_cases stateZero : state = 0
    · simp [KorecR2.step, stateZero] at stepEq
    · omega
  cases operation with
  | incrementBoth next =>
      simp [KorecR2.step, Nat.ne_of_gt statePositive, lookup] at stepEq
      subst target
      simp [abstractConfiguration, abstractSuccessors, ZeroClass.classifyNat]
  | decrement register next =>
      cases register with
      | zero =>
          cases registerZero with
          | zero =>
              simp [KorecR2.step, Nat.ne_of_gt statePositive, lookup] at stepEq
              subst target
              simp [abstractConfiguration, abstractSuccessors, ZeroClass.classifyNat]
          | succ value =>
              simp [KorecR2.step, Nat.ne_of_gt statePositive, lookup] at stepEq
              subst target
              cases value <;>
                simp [abstractConfiguration, abstractSuccessors,
                  ZeroClass.classifyNat]
      | one =>
          cases registerTwo with
          | zero =>
              simp [KorecR2.step, Nat.ne_of_gt statePositive, lookup] at stepEq
              subst target
              simp [abstractConfiguration, abstractSuccessors, ZeroClass.classifyNat]
          | succ value =>
              simp [KorecR2.step, Nat.ne_of_gt statePositive, lookup] at stepEq
              subst target
              cases value <;>
                simp [abstractConfiguration, abstractSuccessors,
                  ZeroClass.classifyNat]

/-- Korec's original global-rank layout projected to finite control.  Its
arithmetic data are independent of the two unbounded register values. -/
structure ControlLCMLayout (leastNondivisor bound : Nat)
    (program : KorecR2.Program) where
  Relevant : Nat → Prop
  leastPositive : 0 < leastNondivisor
  leastBounded : leastNondivisor ≤ bound
  operationAt : ∀ {state}, Relevant state → 0 < state →
    ∃ operation, program state = some operation
  selectedFactors : List Nat
  selectedNodup : selectedFactors.Nodup
  selectedProductSeparated : selectedFactors.Pairwise fun left right =>
    bound < left * right
  selectedAtLeastLeast : ∀ factor, factor ∈ selectedFactors →
    leastNondivisor ≤ factor
  selectedAtMostBound : ∀ factor, factor ∈ selectedFactors →
    factor ≤ bound
  selectedResidue : Nat → Nat
  selectedResiduePositive : ∀ factor, factor ∈ selectedFactors →
    0 < selectedResidue factor
  selectedResidueBelow : ∀ factor, factor ∈ selectedFactors →
    selectedResidue factor < factor
  selectedDivisorClassification : ∀ factor, factor ∈ selectedFactors →
    ∀ divisor, divisor ∣ factor → divisor = 1 ∨ divisor = factor
  candidate : Nat → Nat
  candidateMem : ∀ {state}, Relevant state → 0 < state →
    candidate state ∈ selectedFactors
  candidateRankSum : ∀ {state}, Relevant state → 0 < state →
    (selectedFactors.map fun factor => candidate state / factor).sum = state
  operationResidue : ∀ {state operation}, Relevant state → 0 < state →
    program state = some operation →
    selectedResidue (candidate state) = operation.code
  nextRelevant : ∀ {state target operation}, Relevant state →
    program state = some operation → target ∈ possibleTargets operation →
    Relevant target
  nextCarryBelow : ∀ {state target operation}, Relevant state →
    program state = some operation → target ∈ possibleTargets operation →
    0 < target → candidate state - operation.code < leastNondivisor

/-- Lift a control-only global layout to every register valuation. -/
def ControlLCMLayout.toLCMLayout
    {leastNondivisor bound : Nat} {program : KorecR2.Program}
    (layout : ControlLCMLayout leastNondivisor bound program) :
    KorecProgramCode.LCMLayout leastNondivisor bound program where
  Relevant source := layout.Relevant source.state
  leastPositive := layout.leastPositive
  leastBounded := layout.leastBounded
  operationAt := layout.operationAt
  selectedFactors := layout.selectedFactors
  selectedNodup := layout.selectedNodup
  selectedProductSeparated := layout.selectedProductSeparated
  selectedAtLeastLeast := layout.selectedAtLeastLeast
  selectedAtMostBound := layout.selectedAtMostBound
  selectedResidue := layout.selectedResidue
  selectedResiduePositive := layout.selectedResiduePositive
  selectedResidueBelow := layout.selectedResidueBelow
  selectedDivisorClassification := layout.selectedDivisorClassification
  candidate := layout.candidate
  candidateMem := layout.candidateMem
  candidateRankSum := layout.candidateRankSum
  operationResidue := layout.operationResidue
  nextRelevant := by
    intro source target operation relevant lookup stepEq
    exact layout.nextRelevant relevant lookup
      (step_state_mem_possibleTargets lookup stepEq)
  nextCarryBelow := by
    intro source target operation relevant lookup stepEq targetPositive
    exact layout.nextCarryBelow relevant lookup
      (step_state_mem_possibleTargets lookup stepEq) targetPositive

def ControlLCMLayout.crtProgramCode
    {leastNondivisor bound : Nat} {program : KorecR2.Program}
    (layout : ControlLCMLayout leastNondivisor bound program) : Nat :=
  layout.toLCMLayout.crtProgramCode

/-- A literal finite-state form of the global Korec layout.  Once program
lookup and the numerical data are executable, all fields reduce to bounded
list and arithmetic checks. -/
structure FiniteControlLCMLayout (leastNondivisor bound : Nat)
    (program : KorecR2.Program) (initialState : Nat) where
  relevantStates : List Nat
  initialMem : initialState ∈ relevantStates
  leastPositive : 0 < leastNondivisor
  leastBounded : leastNondivisor ≤ bound
  operationAt : ∀ {state}, state ∈ relevantStates → 0 < state →
    ∃ operation, program state = some operation
  selectedFactors : List Nat
  selectedNodup : selectedFactors.Nodup
  selectedProductSeparated : selectedFactors.Pairwise fun left right =>
    bound < left * right
  selectedAtLeastLeast : ∀ factor, factor ∈ selectedFactors →
    leastNondivisor ≤ factor
  selectedAtMostBound : ∀ factor, factor ∈ selectedFactors →
    factor ≤ bound
  selectedResidue : Nat → Nat
  selectedResiduePositive : ∀ factor, factor ∈ selectedFactors →
    0 < selectedResidue factor
  selectedResidueBelow : ∀ factor, factor ∈ selectedFactors →
    selectedResidue factor < factor
  selectedDivisorClassification : ∀ factor, factor ∈ selectedFactors →
    ∀ divisor, divisor ∣ factor → divisor = 1 ∨ divisor = factor
  candidate : Nat → Nat
  candidateMem : ∀ {state}, state ∈ relevantStates → 0 < state →
    candidate state ∈ selectedFactors
  candidateRankSum : ∀ {state}, state ∈ relevantStates → 0 < state →
    (selectedFactors.map fun factor => candidate state / factor).sum = state
  operationResidue : ∀ {state operation}, state ∈ relevantStates →
    0 < state → program state = some operation →
    selectedResidue (candidate state) = operation.code
  nextMem : ∀ {state target operation}, state ∈ relevantStates →
    program state = some operation → target ∈ possibleTargets operation →
    target ∈ relevantStates
  nextCarryBelow : ∀ {state target operation}, state ∈ relevantStates →
    program state = some operation → target ∈ possibleTargets operation →
    0 < target → candidate state - operation.code < leastNondivisor

def FiniteControlLCMLayout.toControlLCMLayout
    {leastNondivisor bound initialState : Nat} {program : KorecR2.Program}
    (layout : FiniteControlLCMLayout leastNondivisor bound program
      initialState) :
    ControlLCMLayout leastNondivisor bound program where
  Relevant state := state ∈ layout.relevantStates
  leastPositive := layout.leastPositive
  leastBounded := layout.leastBounded
  operationAt := layout.operationAt
  selectedFactors := layout.selectedFactors
  selectedNodup := layout.selectedNodup
  selectedProductSeparated := layout.selectedProductSeparated
  selectedAtLeastLeast := layout.selectedAtLeastLeast
  selectedAtMostBound := layout.selectedAtMostBound
  selectedResidue := layout.selectedResidue
  selectedResiduePositive := layout.selectedResiduePositive
  selectedResidueBelow := layout.selectedResidueBelow
  selectedDivisorClassification := layout.selectedDivisorClassification
  candidate := layout.candidate
  candidateMem := layout.candidateMem
  candidateRankSum := layout.candidateRankSum
  operationResidue := layout.operationResidue
  nextRelevant := layout.nextMem
  nextCarryBelow := layout.nextCarryBelow

@[simp] theorem FiniteControlLCMLayout.initialRelevant
    {leastNondivisor bound initialState : Nat} {program : KorecR2.Program}
    (layout : FiniteControlLCMLayout leastNondivisor bound program
      initialState) :
    layout.toControlLCMLayout.Relevant initialState :=
  layout.initialMem

def FiniteControlLCMLayout.crtProgramCode
    {leastNondivisor bound initialState : Nat} {program : KorecR2.Program}
    (layout : FiniteControlLCMLayout leastNondivisor bound program
      initialState) : Nat :=
  layout.toControlLCMLayout.crtProgramCode

/-- A finite zero/positive control abstraction for Korec's global-rank
layout.  Unlike `ControlLCMLayout`, it does not retain a zero branch when the
tested register is known positive, or a positive branch when it is known
zero. -/
structure AbstractControlLCMLayout (leastNondivisor bound : Nat)
    (program : KorecR2.Program) where
  Relevant : AbstractConfiguration → Prop
  leastPositive : 0 < leastNondivisor
  leastBounded : leastNondivisor ≤ bound
  operationAt : ∀ {source}, Relevant source → 0 < source.state →
    ∃ operation, program source.state = some operation
  selectedFactors : List Nat
  selectedNodup : selectedFactors.Nodup
  selectedProductSeparated : selectedFactors.Pairwise fun left right =>
    bound < left * right
  selectedAtLeastLeast : ∀ factor, factor ∈ selectedFactors →
    leastNondivisor ≤ factor
  selectedAtMostBound : ∀ factor, factor ∈ selectedFactors →
    factor ≤ bound
  selectedResidue : Nat → Nat
  selectedResiduePositive : ∀ factor, factor ∈ selectedFactors →
    0 < selectedResidue factor
  selectedResidueBelow : ∀ factor, factor ∈ selectedFactors →
    selectedResidue factor < factor
  selectedDivisorClassification : ∀ factor, factor ∈ selectedFactors →
    ∀ divisor, divisor ∣ factor → divisor = 1 ∨ divisor = factor
  candidate : Nat → Nat
  candidateMem : ∀ {source}, Relevant source → 0 < source.state →
    candidate source.state ∈ selectedFactors
  candidateRankSum : ∀ {source}, Relevant source → 0 < source.state →
    (selectedFactors.map fun factor => candidate source.state / factor).sum =
      source.state
  operationResidue : ∀ {source operation}, Relevant source →
    0 < source.state → program source.state = some operation →
    selectedResidue (candidate source.state) = operation.code
  nextRelevant : ∀ {source target operation}, Relevant source →
    program source.state = some operation →
    target ∈ abstractSuccessors operation source → Relevant target
  nextCarryBelow : ∀ {source target operation}, Relevant source →
    program source.state = some operation →
    target ∈ abstractSuccessors operation source → 0 < target.state →
    candidate source.state - operation.code < leastNondivisor

/-- Every concrete register valuation satisfying the abstract invariant is
covered by the global configuration-level layout. -/
def AbstractControlLCMLayout.toLCMLayout
    {leastNondivisor bound : Nat} {program : KorecR2.Program}
    (layout : AbstractControlLCMLayout leastNondivisor bound program) :
    KorecProgramCode.LCMLayout leastNondivisor bound program where
  Relevant source := layout.Relevant (abstractConfiguration source)
  leastPositive := layout.leastPositive
  leastBounded := layout.leastBounded
  operationAt := layout.operationAt
  selectedFactors := layout.selectedFactors
  selectedNodup := layout.selectedNodup
  selectedProductSeparated := layout.selectedProductSeparated
  selectedAtLeastLeast := layout.selectedAtLeastLeast
  selectedAtMostBound := layout.selectedAtMostBound
  selectedResidue := layout.selectedResidue
  selectedResiduePositive := layout.selectedResiduePositive
  selectedResidueBelow := layout.selectedResidueBelow
  selectedDivisorClassification := layout.selectedDivisorClassification
  candidate := layout.candidate
  candidateMem := layout.candidateMem
  candidateRankSum := layout.candidateRankSum
  operationResidue := layout.operationResidue
  nextRelevant := by
    intro source target operation relevant lookup stepEq
    exact layout.nextRelevant relevant lookup
      (abstractConfiguration_mem_abstractSuccessors lookup stepEq)
  nextCarryBelow := by
    intro source target operation relevant lookup stepEq targetPositive
    exact layout.nextCarryBelow relevant lookup
      (abstractConfiguration_mem_abstractSuccessors lookup stepEq)
      targetPositive

def AbstractControlLCMLayout.crtProgramCode
    {leastNondivisor bound : Nat} {program : KorecR2.Program}
    (layout : AbstractControlLCMLayout leastNondivisor bound program) : Nat :=
  layout.toLCMLayout.crtProgramCode

/-- Literal finite version of the zero/positive abstract layout. -/
structure FiniteAbstractControlLCMLayout (leastNondivisor bound : Nat)
    (program : KorecR2.Program) (initial : AbstractConfiguration) where
  relevantConfigurations : List AbstractConfiguration
  initialMem : initial ∈ relevantConfigurations
  leastPositive : 0 < leastNondivisor
  leastBounded : leastNondivisor ≤ bound
  operationAt : ∀ {source}, source ∈ relevantConfigurations →
    0 < source.state → ∃ operation, program source.state = some operation
  selectedFactors : List Nat
  selectedNodup : selectedFactors.Nodup
  selectedProductSeparated : selectedFactors.Pairwise fun left right =>
    bound < left * right
  selectedAtLeastLeast : ∀ factor, factor ∈ selectedFactors →
    leastNondivisor ≤ factor
  selectedAtMostBound : ∀ factor, factor ∈ selectedFactors →
    factor ≤ bound
  selectedResidue : Nat → Nat
  selectedResiduePositive : ∀ factor, factor ∈ selectedFactors →
    0 < selectedResidue factor
  selectedResidueBelow : ∀ factor, factor ∈ selectedFactors →
    selectedResidue factor < factor
  selectedDivisorClassification : ∀ factor, factor ∈ selectedFactors →
    ∀ divisor, divisor ∣ factor → divisor = 1 ∨ divisor = factor
  candidate : Nat → Nat
  candidateMem : ∀ {source}, source ∈ relevantConfigurations →
    0 < source.state → candidate source.state ∈ selectedFactors
  candidateRankSum : ∀ {source}, source ∈ relevantConfigurations →
    0 < source.state →
    (selectedFactors.map fun factor => candidate source.state / factor).sum =
      source.state
  operationResidue : ∀ {source operation},
    source ∈ relevantConfigurations → 0 < source.state →
    program source.state = some operation →
    selectedResidue (candidate source.state) = operation.code
  nextMem : ∀ {source target operation},
    source ∈ relevantConfigurations →
    program source.state = some operation →
    target ∈ abstractSuccessors operation source →
    target ∈ relevantConfigurations
  nextCarryBelow : ∀ {source target operation},
    source ∈ relevantConfigurations →
    program source.state = some operation →
    target ∈ abstractSuccessors operation source → 0 < target.state →
    candidate source.state - operation.code < leastNondivisor

def FiniteAbstractControlLCMLayout.toAbstractControlLCMLayout
    {leastNondivisor bound : Nat} {program : KorecR2.Program}
    {initial : AbstractConfiguration}
    (layout : FiniteAbstractControlLCMLayout leastNondivisor bound program
      initial) :
    AbstractControlLCMLayout leastNondivisor bound program where
  Relevant source := source ∈ layout.relevantConfigurations
  leastPositive := layout.leastPositive
  leastBounded := layout.leastBounded
  operationAt := layout.operationAt
  selectedFactors := layout.selectedFactors
  selectedNodup := layout.selectedNodup
  selectedProductSeparated := layout.selectedProductSeparated
  selectedAtLeastLeast := layout.selectedAtLeastLeast
  selectedAtMostBound := layout.selectedAtMostBound
  selectedResidue := layout.selectedResidue
  selectedResiduePositive := layout.selectedResiduePositive
  selectedResidueBelow := layout.selectedResidueBelow
  selectedDivisorClassification := layout.selectedDivisorClassification
  candidate := layout.candidate
  candidateMem := layout.candidateMem
  candidateRankSum := layout.candidateRankSum
  operationResidue := layout.operationResidue
  nextRelevant := layout.nextMem
  nextCarryBelow := layout.nextCarryBelow

@[simp] theorem FiniteAbstractControlLCMLayout.initialRelevant
    {leastNondivisor bound : Nat} {program : KorecR2.Program}
    {initial : AbstractConfiguration}
    (layout : FiniteAbstractControlLCMLayout leastNondivisor bound program
      initial) :
    layout.toAbstractControlLCMLayout.Relevant initial :=
  layout.initialMem

def FiniteAbstractControlLCMLayout.crtProgramCode
    {leastNondivisor bound : Nat} {program : KorecR2.Program}
    {initial : AbstractConfiguration}
    (layout : FiniteAbstractControlLCMLayout leastNondivisor bound program
      initial) : Nat :=
  layout.toAbstractControlLCMLayout.crtProgramCode

/-- The compact arithmetic layout projected to finite control and carry.
Counter contents do not affect the selected candidate or its reader rank;
they choose only one of the two listed targets of a decrement instruction. -/
structure ControlLocalLCMLayout (bound : Nat)
    (program : KorecR2.Program) where
  Relevant : Nat → Nat → Prop
  operationAt : ∀ {state carry}, Relevant state carry →
    0 < state → ∃ operation, program state = some operation
  selectedFactors : List Nat
  selectedNodup : selectedFactors.Nodup
  selectedProductSeparated : selectedFactors.Pairwise fun left right =>
    bound < left * right
  selectedAtMostBound : ∀ factor, factor ∈ selectedFactors →
    factor ≤ bound
  selectedResidue : Nat → Nat
  selectedResiduePositive : ∀ factor, factor ∈ selectedFactors →
    0 < selectedResidue factor
  selectedResidueBelow : ∀ factor, factor ∈ selectedFactors →
    selectedResidue factor < factor
  selectedDivisorClassification : ∀ factor, factor ∈ selectedFactors →
    ∀ divisor, divisor ∣ factor → divisor = 1 ∨ divisor = factor
  candidate : Nat → Nat
  candidateMem : ∀ {state carry}, Relevant state carry →
    0 < state → candidate state ∈ selectedFactors
  carryBelowCandidate : ∀ {state carry}, Relevant state carry →
    0 < state → carry < candidate state
  candidateRankDifferenceSum : ∀ {state carry}, Relevant state carry →
    0 < state →
    (selectedFactors.map fun factor => candidate state / factor).sum =
      (selectedFactors.map fun factor => carry / factor).sum + state
  operationResidue : ∀ {state carry operation}, Relevant state carry →
    0 < state → program state = some operation →
    selectedResidue (candidate state) = operation.code
  nextRelevant : ∀ {state target carry operation}, Relevant state carry →
    program state = some operation → target ∈ possibleTargets operation →
    Relevant target (candidate state - operation.code)

/-- A literal finite certificate for the control-and-carry layout.  Membership
in `relevantPairs` replaces an abstract invariant, so every remaining field is
a finite arithmetic or lookup condition when the supplied data are
executable. -/
structure FiniteControlLocalLCMLayout (bound : Nat)
    (program : KorecR2.Program) (initialState initialCarry : Nat) where
  relevantPairs : List (Nat × Nat)
  initialMem : (initialState, initialCarry) ∈ relevantPairs
  operationAt : ∀ {state carry}, (state, carry) ∈ relevantPairs →
    0 < state → ∃ operation, program state = some operation
  selectedFactors : List Nat
  selectedNodup : selectedFactors.Nodup
  selectedProductSeparated : selectedFactors.Pairwise fun left right =>
    bound < left * right
  selectedAtMostBound : ∀ factor, factor ∈ selectedFactors →
    factor ≤ bound
  selectedResidue : Nat → Nat
  selectedResiduePositive : ∀ factor, factor ∈ selectedFactors →
    0 < selectedResidue factor
  selectedResidueBelow : ∀ factor, factor ∈ selectedFactors →
    selectedResidue factor < factor
  selectedDivisorClassification : ∀ factor, factor ∈ selectedFactors →
    ∀ divisor, divisor ∣ factor → divisor = 1 ∨ divisor = factor
  candidate : Nat → Nat
  candidateMem : ∀ {state carry}, (state, carry) ∈ relevantPairs →
    0 < state → candidate state ∈ selectedFactors
  carryBelowCandidate : ∀ {state carry},
    (state, carry) ∈ relevantPairs →
    0 < state → carry < candidate state
  candidateRankDifferenceSum : ∀ {state carry},
    (state, carry) ∈ relevantPairs →
    0 < state →
    (selectedFactors.map fun factor => candidate state / factor).sum =
      (selectedFactors.map fun factor => carry / factor).sum + state
  operationResidue : ∀ {state carry operation},
    (state, carry) ∈ relevantPairs →
    0 < state → program state = some operation →
    selectedResidue (candidate state) = operation.code
  nextMem : ∀ {state target carry operation},
    (state, carry) ∈ relevantPairs →
    program state = some operation → target ∈ possibleTargets operation →
    (target, candidate state - operation.code) ∈ relevantPairs

/-- Interpret a literal finite certificate as the uniform abstract layout. -/
def FiniteControlLocalLCMLayout.toControlLocalLCMLayout
    {bound initialState initialCarry : Nat} {program : KorecR2.Program}
    (layout : FiniteControlLocalLCMLayout bound program
      initialState initialCarry) :
    ControlLocalLCMLayout bound program where
  Relevant state carry := (state, carry) ∈ layout.relevantPairs
  operationAt := layout.operationAt
  selectedFactors := layout.selectedFactors
  selectedNodup := layout.selectedNodup
  selectedProductSeparated := layout.selectedProductSeparated
  selectedAtMostBound := layout.selectedAtMostBound
  selectedResidue := layout.selectedResidue
  selectedResiduePositive := layout.selectedResiduePositive
  selectedResidueBelow := layout.selectedResidueBelow
  selectedDivisorClassification := layout.selectedDivisorClassification
  candidate := layout.candidate
  candidateMem := layout.candidateMem
  carryBelowCandidate := layout.carryBelowCandidate
  candidateRankDifferenceSum := layout.candidateRankDifferenceSum
  operationResidue := layout.operationResidue
  nextRelevant := layout.nextMem

@[simp] theorem FiniteControlLocalLCMLayout.initialRelevant
    {bound initialState initialCarry : Nat} {program : KorecR2.Program}
    (layout : FiniteControlLocalLCMLayout bound program
      initialState initialCarry) :
    layout.toControlLocalLCMLayout.Relevant initialState initialCarry :=
  layout.initialMem

/-- Construct the control layout on the full branch-closed orbit of one
initial state and carry.  This orbit is independent of the simulated counter
values and therefore covers all encoded inputs. -/
def ControlLocalLCMLayout.ofReachable
    (bound : Nat) (program : KorecR2.Program) (candidate : Nat → Nat)
    (initial : Nat × Nat) (selectedFactors : List Nat)
    (selectedNodup : selectedFactors.Nodup)
    (selectedProductSeparated : selectedFactors.Pairwise fun left right =>
      bound < left * right)
    (selectedAtMostBound : ∀ factor, factor ∈ selectedFactors →
      factor ≤ bound)
    (selectedResidue : Nat → Nat)
    (selectedResiduePositive : ∀ factor, factor ∈ selectedFactors →
      0 < selectedResidue factor)
    (selectedResidueBelow : ∀ factor, factor ∈ selectedFactors →
      selectedResidue factor < factor)
    (selectedDivisorClassification :
      ∀ factor, factor ∈ selectedFactors →
        ∀ divisor, divisor ∣ factor → divisor = 1 ∨ divisor = factor)
    (operationAt : ∀ {state carry},
      ControlReachable program candidate initial state carry →
      0 < state → ∃ operation, program state = some operation)
    (candidateMem : ∀ {state carry},
      ControlReachable program candidate initial state carry →
      0 < state → candidate state ∈ selectedFactors)
    (carryBelowCandidate : ∀ {state carry},
      ControlReachable program candidate initial state carry →
      0 < state → carry < candidate state)
    (candidateRankDifferenceSum : ∀ {state carry},
      ControlReachable program candidate initial state carry →
      0 < state →
      (selectedFactors.map fun factor => candidate state / factor).sum =
        (selectedFactors.map fun factor => carry / factor).sum + state)
    (operationResidue : ∀ {state carry operation},
      ControlReachable program candidate initial state carry →
      0 < state → program state = some operation →
      selectedResidue (candidate state) = operation.code) :
    ControlLocalLCMLayout bound program where
  Relevant := ControlReachable program candidate initial
  operationAt := operationAt
  selectedFactors := selectedFactors
  selectedNodup := selectedNodup
  selectedProductSeparated := selectedProductSeparated
  selectedAtMostBound := selectedAtMostBound
  selectedResidue := selectedResidue
  selectedResiduePositive := selectedResiduePositive
  selectedResidueBelow := selectedResidueBelow
  selectedDivisorClassification := selectedDivisorClassification
  candidate := candidate
  candidateMem := candidateMem
  carryBelowCandidate := carryBelowCandidate
  candidateRankDifferenceSum := candidateRankDifferenceSum
  operationResidue := operationResidue
  nextRelevant := by
    intro state target carry operation reachable lookup targetMem
    exact ControlReachable.tail reachable
      ⟨operation, lookup, targetMem, rfl⟩

@[simp] theorem ControlLocalLCMLayout.ofReachable_initialRelevant
    (bound : Nat) (program : KorecR2.Program) (candidate : Nat → Nat)
    (initial : Nat × Nat) (selectedFactors : List Nat)
    (selectedNodup : selectedFactors.Nodup)
    (selectedProductSeparated : selectedFactors.Pairwise fun left right =>
      bound < left * right)
    (selectedAtMostBound : ∀ factor, factor ∈ selectedFactors →
      factor ≤ bound)
    (selectedResidue : Nat → Nat)
    (selectedResiduePositive : ∀ factor, factor ∈ selectedFactors →
      0 < selectedResidue factor)
    (selectedResidueBelow : ∀ factor, factor ∈ selectedFactors →
      selectedResidue factor < factor)
    (selectedDivisorClassification :
      ∀ factor, factor ∈ selectedFactors →
        ∀ divisor, divisor ∣ factor → divisor = 1 ∨ divisor = factor)
    (operationAt : ∀ {state carry},
      ControlReachable program candidate initial state carry →
      0 < state → ∃ operation, program state = some operation)
    (candidateMem : ∀ {state carry},
      ControlReachable program candidate initial state carry →
      0 < state → candidate state ∈ selectedFactors)
    (carryBelowCandidate : ∀ {state carry},
      ControlReachable program candidate initial state carry →
      0 < state → carry < candidate state)
    (candidateRankDifferenceSum : ∀ {state carry},
      ControlReachable program candidate initial state carry →
      0 < state →
      (selectedFactors.map fun factor => candidate state / factor).sum =
        (selectedFactors.map fun factor => carry / factor).sum + state)
    (operationResidue : ∀ {state carry operation},
      ControlReachable program candidate initial state carry →
      0 < state → program state = some operation →
      selectedResidue (candidate state) = operation.code) :
    (ControlLocalLCMLayout.ofReachable bound program candidate initial
      selectedFactors selectedNodup selectedProductSeparated
      selectedAtMostBound selectedResidue selectedResiduePositive
      selectedResidueBelow selectedDivisorClassification operationAt
      candidateMem carryBelowCandidate candidateRankDifferenceSum
      operationResidue).Relevant initial.1 initial.2 := by
  exact ControlReachable.refl

/-- A control-and-carry layout supplies the configuration-level layout for
all register values simultaneously. -/
def ControlLocalLCMLayout.toLocalLCMLayout
    {bound : Nat} {program : KorecR2.Program}
    (layout : ControlLocalLCMLayout bound program) :
    LocalLCMLayout bound program where
  Relevant source carry := layout.Relevant source.state carry
  operationAt := layout.operationAt
  selectedFactors := layout.selectedFactors
  selectedNodup := layout.selectedNodup
  selectedProductSeparated := layout.selectedProductSeparated
  selectedAtMostBound := layout.selectedAtMostBound
  selectedResidue := layout.selectedResidue
  selectedResiduePositive := layout.selectedResiduePositive
  selectedResidueBelow := layout.selectedResidueBelow
  selectedDivisorClassification := layout.selectedDivisorClassification
  candidate := layout.candidate
  candidateMem := layout.candidateMem
  carryBelowCandidate := layout.carryBelowCandidate
  candidateRankDifferenceSum := layout.candidateRankDifferenceSum
  operationResidue := layout.operationResidue
  nextRelevant := by
    intro source target carry operation relevant lookup stepEq
    exact layout.nextRelevant relevant lookup
      (step_state_mem_possibleTargets lookup stepEq)

def LocalLCMLayout.coveringModulus
    {bound : Nat} {program : KorecR2.Program}
    (layout : LocalLCMLayout bound program) : Nat :=
  unmarkedLCM layout.selectedFactors bound

def LocalLCMLayout.assignedResidue
    {bound : Nat} {program : KorecR2.Program}
    (layout : LocalLCMLayout bound program) (modulus : Nat) : Nat :=
  if modulus = layout.coveringModulus then 0
  else layout.selectedResidue modulus

theorem LocalLCMLayout.selectedPairwise
    {bound : Nat} {program : KorecR2.Program}
    (layout : LocalLCMLayout bound program) :
    layout.selectedFactors.Pairwise Nat.Coprime := by
  apply pairwise_coprime_of_nodup_and_divisor_classification
    layout.selectedNodup
  · intro factor factorMem
    have positive := layout.selectedResiduePositive factor factorMem
    have below := layout.selectedResidueBelow factor factorMem
    omega
  · exact layout.selectedDivisorClassification

theorem LocalLCMLayout.selectedCoprimeUnmarked
    {bound : Nat} {program : KorecR2.Program}
    (layout : LocalLCMLayout bound program)
    {factor value : Nat} (factorMem : factor ∈ layout.selectedFactors)
    (unmarked : markedByDivisorList layout.selectedFactors value = false) :
    Nat.Coprime factor value := by
  have factorNotDivides : ¬factor ∣ value :=
    (markedByDivisorList_eq_false_iff layout.selectedFactors value).mp
      unmarked factor factorMem
  exact coprime_of_not_dvd_of_divisor_classification
    (layout.selectedDivisorClassification factor factorMem)
    factorNotDivides

theorem LocalLCMLayout.selected_ne_coveringModulus
    {bound : Nat} {program : KorecR2.Program}
    (layout : LocalLCMLayout bound program)
    {factor : Nat} (factorMem : factor ∈ layout.selectedFactors) :
    factor ≠ layout.coveringModulus := by
  intro equality
  have factorCoprimeCover : Nat.Coprime factor layout.coveringModulus :=
    coprime_unmarkedLCM
      (fun value _ _ unmarked =>
        layout.selectedCoprimeUnmarked factorMem unmarked)
  have factorDividesCover : factor ∣ layout.coveringModulus := by
    rw [equality]
    exact Nat.dvd_refl _
  have factorOne := factorCoprimeCover.eq_one_of_dvd factorDividesCover
  have positive := layout.selectedResiduePositive factor factorMem
  have below := layout.selectedResidueBelow factor factorMem
  omega

/-- The unmarked-LCM construction discharges the covering and coprimality
fields of the local congruence layout. -/
def LocalLCMLayout.toLocalCongruenceLayout
    {bound : Nat} {program : KorecR2.Program}
    (layout : LocalLCMLayout bound program) :
    LocalCongruenceLayout program where
  Relevant := layout.Relevant
  operationAt := layout.operationAt
  congruenceModuli := layout.coveringModulus :: layout.selectedFactors
  congruenceResidue := layout.assignedResidue
  congruenceModuliPositive := by
    intro modulus modulusMem
    simp only [List.mem_cons] at modulusMem
    rcases modulusMem with rfl | factorMem
    · exact unmarkedLCM_positive layout.selectedFactors bound
    · have positive := layout.selectedResiduePositive modulus factorMem
      have below := layout.selectedResidueBelow modulus factorMem
      omega
  congruenceModuliPairwise := by
    rw [List.pairwise_cons]
    constructor
    · intro factor factorMem
      exact (coprime_unmarkedLCM
        (fun value _ _ unmarked =>
          layout.selectedCoprimeUnmarked factorMem unmarked)).symm
    · exact layout.selectedPairwise
  selectedFactors := layout.selectedFactors
  selectedResidue := layout.selectedResidue
  selectedResiduePositive := layout.selectedResiduePositive
  selectedResidueBelow := layout.selectedResidueBelow
  selectedCongruence := by
    intro factor factorMem
    constructor
    · simp [factorMem]
    · simp [LocalLCMLayout.assignedResidue,
        layout.selected_ne_coveringModulus factorMem]
  coveringModuli := [layout.coveringModulus]
  coveringCongruence := by
    intro modulus modulusMem
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at modulusMem
    subst modulus
    constructor
    · simp
    · simp [LocalLCMLayout.assignedResidue]
  coveringModuliSublist :=
    List.Sublist.cons_cons layout.coveringModulus
      (List.nil_sublist layout.selectedFactors)
  candidate := layout.candidate
  candidatePositive := by
    intro source carry relevant statePositive
    have candidateMem := layout.candidateMem relevant statePositive
    have positive := layout.selectedResiduePositive
      (layout.candidate source.state) candidateMem
    have below := layout.selectedResidueBelow
      (layout.candidate source.state) candidateMem
    omega
  carryBelowCandidate := layout.carryBelowCandidate
  candidateSeparated := by
    intro source carry relevant statePositive
    have candidateBounded := layout.selectedAtMostBound
      (layout.candidate source.state)
      (layout.candidateMem relevant statePositive)
    have candidateProducts : layout.selectedFactors.Pairwise
        (fun left right => layout.candidate source.state < left * right) :=
      layout.selectedProductSeparated.imp fun separated =>
        Nat.lt_of_le_of_lt candidateBounded separated
    exact layout.selectedPairwise.and candidateProducts
  candidateCover := by
    intro source carry relevant statePositive value valuePositive valueBounded
      unmarked
    have candidateBounded := layout.selectedAtMostBound
      (layout.candidate source.state)
      (layout.candidateMem relevant statePositive)
    have boundValue : value ≤ bound := Nat.le_trans valueBounded candidateBounded
    have valueDivides := dvd_unmarkedLCM valuePositive boundValue unmarked
    simpa [KorecCRT.modulusProduct, LocalLCMLayout.coveringModulus] using
      valueDivides
  candidateMarked := by
    intro source carry relevant statePositive
    apply (markedByDivisorList_eq_true_iff layout.selectedFactors
      (layout.candidate source.state)).mpr
    exact ⟨layout.candidate source.state,
      layout.candidateMem relevant statePositive, Nat.dvd_refl _⟩
  candidateRankDifferenceSum := layout.candidateRankDifferenceSum
  candidateCongruence := by
    intro source carry operation relevant statePositive lookup
    have candidateMem := layout.candidateMem relevant statePositive
    have candidateNotCover :=
      layout.selected_ne_coveringModulus candidateMem
    constructor
    · simp [candidateMem]
    constructor
    · simpa [LocalLCMLayout.assignedResidue, candidateNotCover] using
        layout.operationResidue relevant statePositive lookup
    · have residueBelow := layout.selectedResidueBelow
        (layout.candidate source.state) candidateMem
      rw [layout.operationResidue relevant statePositive lookup]
        at residueBelow
      exact residueBelow
  nextRelevant := layout.nextRelevant

def LocalLCMLayout.crtProgramCode
    {bound : Nat} {program : KorecR2.Program}
    (layout : LocalLCMLayout bound program) : Nat :=
  layout.toLocalCongruenceLayout.crtProgramCode

@[simp] theorem LocalLCMLayout.ofGlobalLayout_crtProgramCode
    {leastNondivisor bound : Nat} {program : KorecR2.Program}
    (layout : KorecProgramCode.LCMLayout leastNondivisor bound program) :
    (LocalLCMLayout.ofGlobalLayout layout).crtProgramCode =
      layout.crtProgramCode :=
  rfl

/-- A local LCM layout constructs both the program integer and its exact
carry-sensitive reader certificate. -/
def LocalLCMLayout.toLocalRankCertificateByCRT
    {bound : Nat} {program : KorecR2.Program}
    (layout : LocalLCMLayout bound program) :
    LocalRankCertificate layout.crtProgramCode program :=
  layout.toLocalCongruenceLayout.toLocalRankCertificateByCRT

def ControlLocalLCMLayout.crtProgramCode
    {bound : Nat} {program : KorecR2.Program}
    (layout : ControlLocalLCMLayout bound program) : Nat :=
  layout.toLocalLCMLayout.crtProgramCode

/-- The finite control-and-carry layout constructs one reader certificate
valid for every counter valuation in its relevant control region. -/
def ControlLocalLCMLayout.toLocalRankCertificateByCRT
    {bound : Nat} {program : KorecR2.Program}
    (layout : ControlLocalLCMLayout bound program) :
    LocalRankCertificate layout.crtProgramCode program :=
  layout.toLocalLCMLayout.toLocalRankCertificateByCRT

def FiniteControlLocalLCMLayout.crtProgramCode
    {bound initialState initialCarry : Nat} {program : KorecR2.Program}
    (layout : FiniteControlLocalLCMLayout bound program
      initialState initialCarry) : Nat :=
  layout.toControlLocalLCMLayout.crtProgramCode

/-- A literal finite certificate constructs the executable reader code. -/
def FiniteControlLocalLCMLayout.toLocalRankCertificateByCRT
    {bound initialState initialCarry : Nat} {program : KorecR2.Program}
    (layout : FiniteControlLocalLCMLayout bound program
      initialState initialCarry) :
    LocalRankCertificate layout.crtProgramCode program :=
  layout.toControlLocalLCMLayout.toLocalRankCertificateByCRT

/-- One simulated R2 boundary step, including the reader carry produced by
the decoded operation. -/
def boundaryStep (program : KorecR2.Program) (candidate : Nat → Nat) :
    KorecR2.Configuration × Nat → Option (KorecR2.Configuration × Nat)
  | (source, _) =>
      match program source.state with
      | none => none
      | some operation =>
          (KorecR2.step program source).map fun target =>
            (target, candidate source.state - operation.code)

/-- Construct a local LCM layout on the exact boundary orbit of one initial
configuration and carry.  Forward invariance is then a structural fact of
reachability rather than an independent arithmetic premise. -/
def LocalLCMLayout.ofReachable
    (bound : Nat) (program : KorecR2.Program) (candidate : Nat → Nat)
    (initial : KorecR2.Configuration × Nat)
    (selectedFactors : List Nat)
    (selectedNodup : selectedFactors.Nodup)
    (selectedProductSeparated : selectedFactors.Pairwise fun left right =>
      bound < left * right)
    (selectedAtMostBound : ∀ factor, factor ∈ selectedFactors →
      factor ≤ bound)
    (selectedResidue : Nat → Nat)
    (selectedResiduePositive : ∀ factor, factor ∈ selectedFactors →
      0 < selectedResidue factor)
    (selectedResidueBelow : ∀ factor, factor ∈ selectedFactors →
      selectedResidue factor < factor)
    (selectedDivisorClassification :
      ∀ factor, factor ∈ selectedFactors →
        ∀ divisor, divisor ∣ factor → divisor = 1 ∨ divisor = factor)
    (operationAt : ∀ {source carry},
      Reaches (boundaryStep program candidate) initial (source, carry) →
      0 < source.state →
      ∃ operation, program source.state = some operation)
    (candidateMem : ∀ {source carry},
      Reaches (boundaryStep program candidate) initial (source, carry) →
      0 < source.state → candidate source.state ∈ selectedFactors)
    (carryBelowCandidate : ∀ {source carry},
      Reaches (boundaryStep program candidate) initial (source, carry) →
      0 < source.state → carry < candidate source.state)
    (candidateRankDifferenceSum : ∀ {source carry},
      Reaches (boundaryStep program candidate) initial (source, carry) →
      0 < source.state →
      (selectedFactors.map fun factor => candidate source.state / factor).sum =
        (selectedFactors.map fun factor => carry / factor).sum + source.state)
    (operationResidue : ∀ {source carry operation},
      Reaches (boundaryStep program candidate) initial (source, carry) →
      0 < source.state → program source.state = some operation →
      selectedResidue (candidate source.state) = operation.code) :
    LocalLCMLayout bound program where
  Relevant source carry :=
    Reaches (boundaryStep program candidate) initial (source, carry)
  operationAt := operationAt
  selectedFactors := selectedFactors
  selectedNodup := selectedNodup
  selectedProductSeparated := selectedProductSeparated
  selectedAtMostBound := selectedAtMostBound
  selectedResidue := selectedResidue
  selectedResiduePositive := selectedResiduePositive
  selectedResidueBelow := selectedResidueBelow
  selectedDivisorClassification := selectedDivisorClassification
  candidate := candidate
  candidateMem := candidateMem
  carryBelowCandidate := carryBelowCandidate
  candidateRankDifferenceSum := candidateRankDifferenceSum
  operationResidue := operationResidue
  nextRelevant := by
    intro source target carry operation run lookup stepEq
    apply Reaches.tail run
    simp [boundaryStep, lookup, stepEq]

@[simp] theorem LocalLCMLayout.ofReachable_initialRelevant
    (bound : Nat) (program : KorecR2.Program) (candidate : Nat → Nat)
    (initial : KorecR2.Configuration × Nat)
    (selectedFactors : List Nat)
    (selectedNodup : selectedFactors.Nodup)
    (selectedProductSeparated : selectedFactors.Pairwise fun left right =>
      bound < left * right)
    (selectedAtMostBound : ∀ factor, factor ∈ selectedFactors →
      factor ≤ bound)
    (selectedResidue : Nat → Nat)
    (selectedResiduePositive : ∀ factor, factor ∈ selectedFactors →
      0 < selectedResidue factor)
    (selectedResidueBelow : ∀ factor, factor ∈ selectedFactors →
      selectedResidue factor < factor)
    (selectedDivisorClassification :
      ∀ factor, factor ∈ selectedFactors →
        ∀ divisor, divisor ∣ factor → divisor = 1 ∨ divisor = factor)
    (operationAt : ∀ {source carry},
      Reaches (boundaryStep program candidate) initial (source, carry) →
      0 < source.state →
      ∃ operation, program source.state = some operation)
    (candidateMem : ∀ {source carry},
      Reaches (boundaryStep program candidate) initial (source, carry) →
      0 < source.state → candidate source.state ∈ selectedFactors)
    (carryBelowCandidate : ∀ {source carry},
      Reaches (boundaryStep program candidate) initial (source, carry) →
      0 < source.state → carry < candidate source.state)
    (candidateRankDifferenceSum : ∀ {source carry},
      Reaches (boundaryStep program candidate) initial (source, carry) →
      0 < source.state →
      (selectedFactors.map fun factor => candidate source.state / factor).sum =
        (selectedFactors.map fun factor => carry / factor).sum + source.state)
    (operationResidue : ∀ {source carry operation},
      Reaches (boundaryStep program candidate) initial (source, carry) →
      0 < source.state → program source.state = some operation →
      selectedResidue (candidate source.state) = operation.code) :
    (LocalLCMLayout.ofReachable bound program candidate initial
      selectedFactors selectedNodup selectedProductSeparated
      selectedAtMostBound selectedResidue selectedResiduePositive
      selectedResidueBelow selectedDivisorClassification operationAt
      candidateMem carryBelowCandidate candidateRankDifferenceSum
      operationResidue).Relevant initial.1 initial.2 := by
  exact Reaches.refl initial

end Mortality.SourceMachine.KorecLocalProgramCode
