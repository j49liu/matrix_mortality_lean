import Mortality.SourceMachine.U20InterpretsR2
import Mortality.SourceMachine.NondivisorRank
import Mortality.SourceMachine.KorecCRT

/-!
# Number-theoretic certificates for Korec program codes

Korec's instruction reader selects the `state`-th positive nondivisor of
`programCode + 1`.  After reading an operation code, it retains the
difference between the selected nondivisor and the remainder as a carry.
The next scan is correct whenever that carry lies below the least positive
nondivisor.

This file packages exactly those arithmetic obligations.  It contains no
machine-simulation assumption: a certificate produces the `Encoding` used by
the already verified U20 interpreter.
-/

namespace Mortality.SourceMachine.KorecProgramCode

open Mortality.SourceMachine
open Mortality.SourceMachine.KorecR2
open Mortality.SourceMachine.KorecU20Interpreter
open Mortality.SourceMachine.KorecNondivisorRank
open Mortality.SourceMachine.KorecCRT

/-- If all positive integers through `carry` divide `programCode + 1`, a
global nondivisor scan may begin after that divisor-only prefix. -/
theorem nondivisorScan_drop_initial_divisors
    {programCode remaining candidate : Nat} (carry : Nat)
    (allDivisors : ∀ divisor, 0 < divisor → divisor ≤ carry →
      divisor ∣ programCode + 1)
    (globalScan : NondivisorScan programCode 0 remaining candidate) :
    NondivisorScan programCode carry remaining candidate := by
  induction carry with
  | zero => simpa using globalScan
  | succ carry inductionHypothesis =>
      have scanAtCarry := inductionHypothesis
        (fun divisor positive bound => allDivisors divisor positive (by omega))
      cases scanAtCarry with
      | found previous notDivides =>
          exact (notDivides (allDivisors (carry + 1) (by omega) (by omega))).elim
      | divisor divides suffix => exact suffix
      | skip notDivides suffix =>
          exact (notDivides (allDivisors (carry + 1) (by omega) (by omega))).elim

/-- A carry-sensitive arithmetic certificate.  Unlike `Certificate` below,
this interface does not require every carry to lie below the first positive
nondivisor.  Instead, it states the exact increase in global nondivisor rank
from the incoming carry to the selected candidate. -/
structure LocalRankCertificate (programCode : Nat)
    (program : KorecR2.Program) where
  Relevant : KorecR2.Configuration → Nat → Prop
  operationAt : ∀ {source carry}, Relevant source carry →
    0 < source.state → ∃ operation, program source.state = some operation
  candidate : Nat → Nat
  candidatePositive : ∀ {source carry}, Relevant source carry →
    0 < source.state → 0 < candidate source.state
  carryBelowCandidate : ∀ {source carry}, Relevant source carry →
    0 < source.state → carry < candidate source.state
  candidateNotDivides : ∀ {source carry}, Relevant source carry →
    0 < source.state → ¬candidate source.state ∣ programCode + 1
  candidateRankDifference : ∀ {source carry}, Relevant source carry →
    0 < source.state →
    nondivisorCount programCode (candidate source.state) =
      nondivisorCount programCode carry + source.state
  residue : ∀ {source carry operation}, Relevant source carry →
    0 < source.state → program source.state = some operation →
    (programCode + 1) % candidate source.state = operation.code
  nextRelevant : ∀ {source target carry operation}, Relevant source carry →
    program source.state = some operation →
    KorecR2.step program source = some target →
    Relevant target (candidate source.state - operation.code)

/-- A local-rank certificate supplies the exact carry-dependent encoding used
by the verified U20 reader. -/
def LocalRankCertificate.toEncoding
    {programCode : Nat} {program : KorecR2.Program}
    (certificate : LocalRankCertificate programCode program) :
    Encoding programCode program :=
  Encoding.ofNondivisorScan programCode program certificate.Relevant
    certificate.operationAt (by
      intro source target operation carry statePositive lookup stepEq relevant
      let selected := certificate.candidate source.state
      have scan : NondivisorScan programCode carry (source.state - 1)
          selected :=
        nondivisorScan_of_rank_difference statePositive
          (certificate.carryBelowCandidate relevant statePositive)
          (certificate.candidateNotDivides relevant statePositive)
          (certificate.candidateRankDifference relevant statePositive)
      refine ⟨selected, scan,
        certificate.residue relevant statePositive lookup, ?_⟩
      simpa [selected, certificate.residue relevant statePositive lookup] using
        certificate.nextRelevant relevant lookup stepEq)

/-- A complete finite arithmetic certificate for one numerical encoding of
an R2 program. `Relevant` is the forward-invariant region needed by the
simulation; no arithmetic data is required for unreachable filler states.
`candidate state` is the globally selected nondivisor for a relevant positive
state. -/
structure Certificate (programCode leastNondivisor : Nat)
    (program : KorecR2.Program) where
  Relevant : KorecR2.Configuration → Prop
  leastPositive : 0 < leastNondivisor
  divisorsBelow : ∀ divisor, 0 < divisor → divisor < leastNondivisor →
    divisor ∣ programCode + 1
  operationAt : ∀ {source}, Relevant source → 0 < source.state →
    ∃ operation, program source.state = some operation
  candidate : Nat → Nat
  globalScan : ∀ {source operation}, Relevant source → 0 < source.state →
    program source.state = some operation →
    NondivisorScan programCode 0 (source.state - 1)
      (candidate source.state)
  residue : ∀ {source operation}, Relevant source → 0 < source.state →
    program source.state = some operation →
    (programCode + 1) % candidate source.state = operation.code
  nextRelevant : ∀ {source target operation}, Relevant source →
    program source.state = some operation →
    KorecR2.step program source = some target → Relevant target
  nextCarryBelow : ∀ {source target operation},
    Relevant source →
    program source.state = some operation →
    KorecR2.step program source = some target → 0 < target.state →
    candidate source.state - operation.code < leastNondivisor

/-- A rank-based form of `Certificate`, matching the notation in Korec's
Section 6. Instead of carrying an inductive reader scan, it states that the
candidate is a positive nondivisor and that its one-based count among all
positive nondivisors is the source state. -/
structure RankCertificate (programCode leastNondivisor : Nat)
    (program : KorecR2.Program) where
  Relevant : KorecR2.Configuration → Prop
  leastPositive : 0 < leastNondivisor
  divisorsBelow : ∀ divisor, 0 < divisor → divisor < leastNondivisor →
    divisor ∣ programCode + 1
  operationAt : ∀ {source}, Relevant source → 0 < source.state →
    ∃ operation, program source.state = some operation
  candidate : Nat → Nat
  candidatePositive : ∀ {source}, Relevant source → 0 < source.state →
    0 < candidate source.state
  candidateNotDivides : ∀ {source}, Relevant source → 0 < source.state →
    ¬candidate source.state ∣ programCode + 1
  candidateRank : ∀ {source}, Relevant source → 0 < source.state →
    nondivisorCount programCode (candidate source.state) = source.state
  residue : ∀ {source operation}, Relevant source → 0 < source.state →
    program source.state = some operation →
    (programCode + 1) % candidate source.state = operation.code
  nextRelevant : ∀ {source target operation}, Relevant source →
    program source.state = some operation →
    KorecR2.step program source = some target → Relevant target
  nextCarryBelow : ∀ {source target operation}, Relevant source →
    program source.state = some operation →
    KorecR2.step program source = some target → 0 < target.state →
    candidate source.state - operation.code < leastNondivisor

/-- A one-based nondivisor-rank certificate supplies the exact inductive scan
expected by the verified instruction reader. -/
def RankCertificate.toCertificate
    {programCode leastNondivisor : Nat} {program : KorecR2.Program}
    (certificate : RankCertificate programCode leastNondivisor program) :
    Certificate programCode leastNondivisor program where
  Relevant := certificate.Relevant
  leastPositive := certificate.leastPositive
  divisorsBelow := certificate.divisorsBelow
  operationAt := certificate.operationAt
  candidate := certificate.candidate
  globalScan := by
    intro source operation relevant statePositive lookup
    exact nondivisorScan_of_oneBasedRank statePositive
      (certificate.candidatePositive relevant statePositive)
      (certificate.candidateNotDivides relevant statePositive)
      (certificate.candidateRank relevant statePositive)
  residue := certificate.residue
  nextRelevant := certificate.nextRelevant
  nextCarryBelow := certificate.nextCarryBelow

/-- A selected-factor form of the arithmetic certificate. It matches the
middle of Korec's proof: the selected primes do not divide the coded number,
every bounded integer containing none of them does divide it, and the function
`h` is the count of integers marked by a selected factor. -/
structure DivisorListCertificate (programCode leastNondivisor : Nat)
    (program : KorecR2.Program) where
  Relevant : KorecR2.Configuration → Prop
  leastPositive : 0 < leastNondivisor
  divisorsBelow : ∀ divisor, 0 < divisor → divisor < leastNondivisor →
    divisor ∣ programCode + 1
  operationAt : ∀ {source}, Relevant source → 0 < source.state →
    ∃ operation, program source.state = some operation
  selectedFactors : List Nat
  selectedNotDivides : ∀ factor, factor ∈ selectedFactors →
    ¬factor ∣ programCode + 1
  candidate : Nat → Nat
  candidatePositive : ∀ {source}, Relevant source → 0 < source.state →
    0 < candidate source.state
  unmarkedDivides : ∀ {source}, Relevant source → 0 < source.state →
    ∀ value, 0 < value → value ≤ candidate source.state →
      markedByDivisorList selectedFactors value = false →
      value ∣ programCode + 1
  candidateMarked : ∀ {source}, Relevant source → 0 < source.state →
    markedByDivisorList selectedFactors (candidate source.state) = true
  candidateRank : ∀ {source}, Relevant source → 0 < source.state →
    markedCount (markedByDivisorList selectedFactors)
      (candidate source.state) = source.state
  residue : ∀ {source operation}, Relevant source → 0 < source.state →
    program source.state = some operation →
    (programCode + 1) % candidate source.state = operation.code
  nextRelevant : ∀ {source target operation}, Relevant source →
    program source.state = some operation →
    KorecR2.step program source = some target → Relevant target
  nextCarryBelow : ∀ {source target operation}, Relevant source →
    program source.state = some operation →
    KorecR2.step program source = some target → 0 < target.state →
    candidate source.state - operation.code < leastNondivisor

/-- The finite selected-factor conditions imply the rank-based certificate. -/
def DivisorListCertificate.toRankCertificate
    {programCode leastNondivisor : Nat} {program : KorecR2.Program}
    (certificate :
      DivisorListCertificate programCode leastNondivisor program) :
    RankCertificate programCode leastNondivisor program where
  Relevant := certificate.Relevant
  leastPositive := certificate.leastPositive
  divisorsBelow := certificate.divisorsBelow
  operationAt := certificate.operationAt
  candidate := certificate.candidate
  candidatePositive := certificate.candidatePositive
  candidateNotDivides := by
    intro source relevant statePositive
    exact (markedByDivisorList_iff_not_dvd
      certificate.selectedNotDivides
      (certificate.unmarkedDivides relevant statePositive)
      (certificate.candidatePositive relevant statePositive) (by omega)).mp
      (certificate.candidateMarked relevant statePositive)
  candidateRank := by
    intro source relevant statePositive
    have agrees : ∀ value, 0 < value →
        value ≤ certificate.candidate source.state →
        (markedByDivisorList certificate.selectedFactors value = true ↔
          ¬value ∣ programCode + 1) := by
      intro value valuePositive valueBounded
      exact markedByDivisorList_iff_not_dvd
        certificate.selectedNotDivides
        (certificate.unmarkedDivides relevant statePositive)
        valuePositive valueBounded
    rw [nondivisorCount_eq_markedCount agrees]
    exact certificate.candidateRank relevant statePositive
  residue := certificate.residue
  nextRelevant := certificate.nextRelevant
  nextCarryBelow := certificate.nextCarryBelow

/-- Selected-factor certificates feed the verified U20 reader through the
rank interface. -/
def DivisorListCertificate.toCertificate
    {programCode leastNondivisor : Nat} {program : KorecR2.Program}
    (certificate :
      DivisorListCertificate programCode leastNondivisor program) :
    Certificate programCode leastNondivisor program :=
  certificate.toRankCertificate.toCertificate

/-- A CRT-layout form of the certificate. Positive residues exclude the
selected factors; covering moduli supply divisibility of every unmarked
integer; pairwise coprimality and the product bound turn Korec's quotient sum
into the exact nondivisor rank. -/
structure FactorLayoutCertificate (programCode leastNondivisor : Nat)
    (program : KorecR2.Program) where
  Relevant : KorecR2.Configuration → Prop
  leastPositive : 0 < leastNondivisor
  divisorsBelow : ∀ divisor, 0 < divisor → divisor < leastNondivisor →
    divisor ∣ programCode + 1
  operationAt : ∀ {source}, Relevant source → 0 < source.state →
    ∃ operation, program source.state = some operation
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
  candidatePositive : ∀ {source}, Relevant source → 0 < source.state →
    0 < candidate source.state
  candidateSeparated : ∀ {source}, Relevant source → 0 < source.state →
    selectedFactors.Pairwise fun left right =>
      left.Coprime right ∧ candidate source.state < left * right
  candidateCover : ∀ {source}, Relevant source → 0 < source.state →
    ∀ value, 0 < value → value ≤ candidate source.state →
      markedByDivisorList selectedFactors value = false →
      value ∣ KorecCRT.modulusProduct coveringModuli
  candidateMarked : ∀ {source}, Relevant source → 0 < source.state →
    markedByDivisorList selectedFactors (candidate source.state) = true
  candidateRankSum : ∀ {source}, Relevant source → 0 < source.state →
    (selectedFactors.map fun factor => candidate source.state / factor).sum =
      source.state
  residue : ∀ {source operation}, Relevant source → 0 < source.state →
    program source.state = some operation →
    (programCode + 1) % candidate source.state = operation.code
  nextRelevant : ∀ {source target operation}, Relevant source →
    program source.state = some operation →
    KorecR2.step program source = some target → Relevant target
  nextCarryBelow : ∀ {source target operation}, Relevant source →
    program source.state = some operation →
    KorecR2.step program source = some target → 0 < target.state →
    candidate source.state - operation.code < leastNondivisor

/-- The CRT-layout obligations imply the selected-factor certificate. -/
def FactorLayoutCertificate.toDivisorListCertificate
    {programCode leastNondivisor : Nat} {program : KorecR2.Program}
    (certificate : FactorLayoutCertificate programCode leastNondivisor program) :
    DivisorListCertificate programCode leastNondivisor program where
  Relevant := certificate.Relevant
  leastPositive := certificate.leastPositive
  divisorsBelow := certificate.divisorsBelow
  operationAt := certificate.operationAt
  selectedFactors := certificate.selectedFactors
  selectedNotDivides :=
    selectedNotDivides_of_positive_residues
      certificate.selectedResiduePositive certificate.selectedRemainder
  candidate := certificate.candidate
  candidatePositive := certificate.candidatePositive
  unmarkedDivides := by
    have productDivides :
        KorecCRT.modulusProduct certificate.coveringModuli ∣
          programCode + 1 :=
      KorecCRT.modulusProduct_dvd certificate.coveringModuliPairwise
        certificate.coveringModuliDivide
    intro source relevant statePositive value valuePositive valueBounded
      unmarked
    exact Nat.dvd_trans
      (certificate.candidateCover relevant statePositive value valuePositive
        valueBounded unmarked)
      productDivides
  candidateMarked := certificate.candidateMarked
  candidateRank := by
    intro source relevant statePositive
    rw [markedCount_divisorList_eq_sum_of_pairwise
      (certificate.candidateSeparated relevant statePositive)]
    exact certificate.candidateRankSum relevant statePositive
  residue := certificate.residue
  nextRelevant := certificate.nextRelevant
  nextCarryBelow := certificate.nextCarryBelow

/-- A finite CRT layout supplies the operational program-code certificate. -/
def FactorLayoutCertificate.toCertificate
    {programCode leastNondivisor : Nat} {program : KorecR2.Program}
    (certificate : FactorLayoutCertificate programCode leastNondivisor program) :
    Certificate programCode leastNondivisor program :=
  certificate.toDivisorListCertificate.toCertificate

/-- The arithmetic layout before the Chinese remainder theorem chooses a
program code.  Every required divisibility, selected-factor residue, and
instruction residue is assigned to one finite list of positive pairwise
coprime moduli.  The remaining fields are precisely Korec's finite
factor-count, control-flow, and carry obligations.

`divisorCover` allows the zero-residue moduli to be prime powers: a smaller
integer need only divide their product.  This matches congruence (6.2.1),
where Korec uses the largest relevant power of each omitted prime rather than
every composite divisor as a separate, non-coprime modulus. -/
structure CongruenceLayout (leastNondivisor : Nat)
    (program : KorecR2.Program) where
  Relevant : KorecR2.Configuration → Prop
  leastPositive : 0 < leastNondivisor
  operationAt : ∀ {source}, Relevant source → 0 < source.state →
    ∃ operation, program source.state = some operation
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
  divisorCover : ∀ divisor, 0 < divisor → divisor < leastNondivisor →
    divisor ∣ KorecCRT.modulusProduct coveringModuli
  candidate : Nat → Nat
  candidatePositive : ∀ {source}, Relevant source → 0 < source.state →
    0 < candidate source.state
  candidateSeparated : ∀ {source}, Relevant source → 0 < source.state →
    selectedFactors.Pairwise fun left right =>
      left.Coprime right ∧ candidate source.state < left * right
  candidateCover : ∀ {source}, Relevant source → 0 < source.state →
    ∀ value, 0 < value → value ≤ candidate source.state →
      markedByDivisorList selectedFactors value = false →
      value ∣ KorecCRT.modulusProduct coveringModuli
  candidateMarked : ∀ {source}, Relevant source → 0 < source.state →
    markedByDivisorList selectedFactors (candidate source.state) = true
  candidateRankSum : ∀ {source}, Relevant source → 0 < source.state →
    (selectedFactors.map fun factor => candidate source.state / factor).sum =
      source.state
  candidateCongruence : ∀ {source operation}, Relevant source →
    0 < source.state → program source.state = some operation →
    candidate source.state ∈ congruenceModuli ∧
      congruenceResidue (candidate source.state) = operation.code ∧
      operation.code < candidate source.state
  nextRelevant : ∀ {source target operation}, Relevant source →
    program source.state = some operation →
    KorecR2.step program source = some target → Relevant target
  nextCarryBelow : ∀ {source target operation}, Relevant source →
    program source.state = some operation →
    KorecR2.step program source = some target → 0 < target.state →
    candidate source.state - operation.code < leastNondivisor

/-- A simpler finite layout using one zero-residue modulus: the LCM of all
positive unmarked values through `bound`.  This avoids separately listing
maximal powers of every omitted prime.  The selected factors remain the
nonzero-residue moduli. -/
structure LCMLayout (leastNondivisor bound : Nat)
    (program : KorecR2.Program) where
  Relevant : KorecR2.Configuration → Prop
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
    KorecR2.step program source = some target → Relevant target
  nextCarryBelow : ∀ {source target operation}, Relevant source →
    program source.state = some operation →
    KorecR2.step program source = some target → 0 < target.state →
    candidate source.state - operation.code < leastNondivisor

/-- The single zero-residue covering modulus used by an `LCMLayout`. -/
def LCMLayout.coveringModulus
    {leastNondivisor bound : Nat} {program : KorecR2.Program}
    (layout : LCMLayout leastNondivisor bound program) : Nat :=
  unmarkedLCM layout.selectedFactors bound

/-- Residue assignment for the LCM construction. -/
def LCMLayout.assignedResidue
    {leastNondivisor bound : Nat} {program : KorecR2.Program}
    (layout : LCMLayout leastNondivisor bound program) (modulus : Nat) : Nat :=
  if modulus = layout.coveringModulus then 0
  else layout.selectedResidue modulus

/-- Distinct nonunit selected factors with prime-like divisor classification
are pairwise coprime. -/
theorem LCMLayout.selectedPairwise
    {leastNondivisor bound : Nat} {program : KorecR2.Program}
    (layout : LCMLayout leastNondivisor bound program) :
    layout.selectedFactors.Pairwise Nat.Coprime := by
  apply pairwise_coprime_of_nodup_and_divisor_classification
    layout.selectedNodup
  · intro factor factorMem
    have residuePositive := layout.selectedResiduePositive factor factorMem
    have residueBelow := layout.selectedResidueBelow factor factorMem
    omega
  · exact layout.selectedDivisorClassification

/-- Selected prime-like factors are pointwise coprime to every unmarked
value. -/
theorem LCMLayout.selectedCoprimeUnmarked
    {leastNondivisor bound : Nat} {program : KorecR2.Program}
    (layout : LCMLayout leastNondivisor bound program)
    {factor value : Nat} (factorMem : factor ∈ layout.selectedFactors)
    (unmarked : markedByDivisorList layout.selectedFactors value = false) :
    Nat.Coprime factor value := by
  have factorNotDivides : ¬factor ∣ value :=
    (markedByDivisorList_eq_false_iff layout.selectedFactors value).mp
      unmarked factor factorMem
  exact coprime_of_not_dvd_of_divisor_classification
    (layout.selectedDivisorClassification factor factorMem)
    factorNotDivides

theorem LCMLayout.selected_ne_coveringModulus
    {leastNondivisor bound : Nat} {program : KorecR2.Program}
    (layout : LCMLayout leastNondivisor bound program)
    {factor : Nat} (factorMem : factor ∈ layout.selectedFactors) :
    factor ≠ layout.coveringModulus := by
  intro equality
  have factorCoprimeCover :
      Nat.Coprime factor layout.coveringModulus :=
    coprime_unmarkedLCM
      (fun value _ _ unmarked =>
        layout.selectedCoprimeUnmarked factorMem unmarked)
  have factorDividesCover : factor ∣ layout.coveringModulus := by
    rw [equality]
    exact Nat.dvd_refl _
  have factorOne := factorCoprimeCover.eq_one_of_dvd factorDividesCover
  have residuePositive := layout.selectedResiduePositive factor factorMem
  have residueBelow := layout.selectedResidueBelow factor factorMem
  omega

/-- The unmarked-LCM construction supplies every field of the finite
congruence layout. -/
def LCMLayout.toCongruenceLayout
    {leastNondivisor bound : Nat} {program : KorecR2.Program}
    (layout : LCMLayout leastNondivisor bound program) :
    CongruenceLayout leastNondivisor program where
  Relevant := layout.Relevant
  leastPositive := layout.leastPositive
  operationAt := layout.operationAt
  congruenceModuli := layout.coveringModulus :: layout.selectedFactors
  congruenceResidue := layout.assignedResidue
  congruenceModuliPositive := by
    intro modulus modulusMem
    simp only [List.mem_cons] at modulusMem
    rcases modulusMem with rfl | factorMem
    · exact unmarkedLCM_positive layout.selectedFactors bound
    · have residuePositive :=
        layout.selectedResiduePositive modulus factorMem
      have residueBelow := layout.selectedResidueBelow modulus factorMem
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
    · simp [LCMLayout.assignedResidue,
        layout.selected_ne_coveringModulus factorMem]
  coveringModuli := [layout.coveringModulus]
  coveringCongruence := by
    intro modulus modulusMem
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at modulusMem
    subst modulus
    constructor
    · simp
    · simp [LCMLayout.assignedResidue]
  coveringModuliSublist :=
    List.Sublist.cons_cons layout.coveringModulus
      (List.nil_sublist layout.selectedFactors)
  divisorCover := by
    intro divisor divisorPositive divisorBelow
    have divisorUnmarked :
        markedByDivisorList layout.selectedFactors divisor = false := by
      apply (markedByDivisorList_eq_false_iff
        layout.selectedFactors divisor).mpr
      intro factor factorMem factorDivides
      have factorAtLeast := layout.selectedAtLeastLeast factor factorMem
      have factorAtMost := Nat.le_of_dvd divisorPositive factorDivides
      omega
    have divisorBounded : divisor ≤ bound :=
      Nat.le_trans (Nat.le_of_lt divisorBelow) layout.leastBounded
    have divisorDivides := dvd_unmarkedLCM divisorPositive divisorBounded
      divisorUnmarked
    simpa [KorecCRT.modulusProduct, LCMLayout.coveringModulus] using
      divisorDivides
  candidate := layout.candidate
  candidatePositive := by
    intro source relevant statePositive
    have candidateMem := layout.candidateMem relevant statePositive
    have residuePositive := layout.selectedResiduePositive
      (layout.candidate source.state) candidateMem
    have residueBelow := layout.selectedResidueBelow
      (layout.candidate source.state) candidateMem
    omega
  candidateSeparated := by
    intro source relevant statePositive
    have candidateBounded := layout.selectedAtMostBound
      (layout.candidate source.state)
      (layout.candidateMem relevant statePositive)
    have candidateProducts : layout.selectedFactors.Pairwise
        (fun left right => layout.candidate source.state < left * right) :=
      layout.selectedProductSeparated.imp fun separated =>
        Nat.lt_of_le_of_lt candidateBounded separated
    exact layout.selectedPairwise.and candidateProducts
  candidateCover := by
    intro source relevant statePositive value valuePositive valueBounded
      unmarked
    have candidateBounded := layout.selectedAtMostBound
      (layout.candidate source.state)
      (layout.candidateMem relevant statePositive)
    have boundValue : value ≤ bound := Nat.le_trans valueBounded candidateBounded
    have valueDivides := dvd_unmarkedLCM valuePositive boundValue unmarked
    simpa [KorecCRT.modulusProduct, LCMLayout.coveringModulus] using
      valueDivides
  candidateMarked := by
    intro source relevant statePositive
    apply (markedByDivisorList_eq_true_iff layout.selectedFactors
      (layout.candidate source.state)).mpr
    exact ⟨layout.candidate source.state,
      layout.candidateMem relevant statePositive, Nat.dvd_refl _⟩
  candidateRankSum := layout.candidateRankSum
  candidateCongruence := by
    intro source operation relevant statePositive lookup
    have candidateMem := layout.candidateMem relevant statePositive
    have candidateNotCover :=
      layout.selected_ne_coveringModulus candidateMem
    constructor
    · simp [candidateMem]
    constructor
    · simpa [LCMLayout.assignedResidue, candidateNotCover] using
        layout.operationResidue relevant statePositive lookup
    · have residueBelow := layout.selectedResidueBelow
        (layout.candidate source.state) candidateMem
      rw [layout.operationResidue relevant statePositive lookup]
        at residueBelow
      exact residueBelow
  nextRelevant := layout.nextRelevant
  nextCarryBelow := layout.nextCarryBelow

/-- A simultaneous solution of the layout's congruences supplies every field
of the factor-layout certificate. -/
def CongruenceLayout.toFactorLayoutCertificate
    {leastNondivisor : Nat} {program : KorecR2.Program}
    (layout : CongruenceLayout leastNondivisor program)
    (programCode : Nat)
    (satisfies : SatisfiesCongruences (programCode + 1)
      layout.congruenceModuli layout.congruenceResidue) :
    FactorLayoutCertificate programCode leastNondivisor program where
  Relevant := layout.Relevant
  leastPositive := layout.leastPositive
  divisorsBelow := by
    intro divisor divisorPositive divisorBelow
    have eachCoveringDivides : ∀ modulus,
        modulus ∈ layout.coveringModuli → modulus ∣ programCode + 1 := by
      intro modulus modulusMem
      obtain ⟨congruenceMem, residueZero⟩ :=
        layout.coveringCongruence modulus modulusMem
      exact satisfies.dvd_of_residue_zero congruenceMem residueZero
    have productDivides :
        KorecCRT.modulusProduct layout.coveringModuli ∣ programCode + 1 :=
      KorecCRT.modulusProduct_dvd
        (layout.congruenceModuliPairwise.sublist layout.coveringModuliSublist)
        eachCoveringDivides
    exact Nat.dvd_trans
      (layout.divisorCover divisor divisorPositive divisorBelow)
      productDivides
  operationAt := layout.operationAt
  selectedFactors := layout.selectedFactors
  selectedResidue := layout.selectedResidue
  selectedResiduePositive := layout.selectedResiduePositive
  selectedRemainder := by
    intro factor factorMem
    obtain ⟨modulusMem, residueEquality⟩ :=
      layout.selectedCongruence factor factorMem
    have residueBelow : layout.congruenceResidue factor < factor := by
      rw [residueEquality]
      exact layout.selectedResidueBelow factor factorMem
    have exactResidue := satisfies.exact modulusMem residueBelow
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
  candidateSeparated := layout.candidateSeparated
  candidateCover := layout.candidateCover
  candidateMarked := layout.candidateMarked
  candidateRankSum := layout.candidateRankSum
  residue := by
    intro source operation relevant statePositive lookup
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
  nextCarryBelow := layout.nextCarryBelow

/-- The executable CRT program code attached to a congruence layout. -/
def CongruenceLayout.crtProgramCode
    {leastNondivisor : Nat} {program : KorecR2.Program}
    (layout : CongruenceLayout leastNondivisor program) : Nat :=
  KorecCRT.programCode layout.congruenceModuli layout.congruenceResidue

/-- The executable CRT solver turns a layout directly into a factor-layout
certificate.  Its program-code definition does not select a noncomputable
witness. -/
def CongruenceLayout.toFactorLayoutCertificateByCRT
    {leastNondivisor : Nat} {program : KorecR2.Program}
    (layout : CongruenceLayout leastNondivisor program) :
    FactorLayoutCertificate layout.crtProgramCode leastNondivisor program :=
  layout.toFactorLayoutCertificate layout.crtProgramCode
    (KorecCRT.programCode_spec layout.congruenceModuliPositive
      layout.congruenceModuliPairwise)

/-- Fully operational program-code certificate obtained by the executable
finite CRT solver. -/
def CongruenceLayout.toCertificateByCRT
    {leastNondivisor : Nat} {program : KorecR2.Program}
    (layout : CongruenceLayout leastNondivisor program) :
    Certificate layout.crtProgramCode leastNondivisor program :=
  layout.toFactorLayoutCertificateByCRT.toCertificate

/-- Executable program code for the unmarked-LCM specialization. -/
def LCMLayout.crtProgramCode
    {leastNondivisor bound : Nat} {program : KorecR2.Program}
    (layout : LCMLayout leastNondivisor bound program) : Nat :=
  layout.toCongruenceLayout.crtProgramCode

/-- The unmarked-LCM specialization feeds the operational reader without any
additional CRT or divisor-cover premise. -/
def LCMLayout.toCertificateByCRT
    {leastNondivisor bound : Nat} {program : KorecR2.Program}
    (layout : LCMLayout leastNondivisor bound program) :
    Certificate layout.crtProgramCode leastNondivisor program :=
  layout.toCongruenceLayout.toCertificateByCRT

/-- Finite CRT discharges program-code existence for every congruence layout.
Thus the unresolved arithmetic no longer includes the Chinese remainder
theorem itself. -/
theorem CongruenceLayout.exists_factorLayoutCertificate
    {leastNondivisor : Nat} {program : KorecR2.Program}
    (layout : CongruenceLayout leastNondivisor program) :
    ∃ programCode,
      Nonempty
        (FactorLayoutCertificate programCode leastNondivisor program) := by
  obtain ⟨programCode, satisfies⟩ := exists_programCode
    layout.congruenceModuliPositive layout.congruenceModuliPairwise
  exact ⟨programCode,
    ⟨layout.toFactorLayoutCertificate programCode satisfies⟩⟩

/-- Congruence layouts feed the verified instruction reader after the finite
CRT and factor-count conversions. -/
theorem CongruenceLayout.exists_certificate
    {leastNondivisor : Nat} {program : KorecR2.Program}
    (layout : CongruenceLayout leastNondivisor program) :
    ∃ programCode,
      Nonempty (Certificate programCode leastNondivisor program) := by
  obtain ⟨programCode, ⟨factorCertificate⟩⟩ :=
    layout.exists_factorLayoutCertificate
  exact ⟨programCode, ⟨factorCertificate.toCertificate⟩⟩

/-- Build a certificate whose invariant region is exactly the finite-run
orbit of one reduction input.  Forward invariance and initial relevance are
then structural facts, leaving only the arithmetic obligations on
configurations that can actually occur. -/
def Certificate.ofReachable
    (programCode leastNondivisor input : Nat) (program : KorecR2.Program)
    (leastPositive : 0 < leastNondivisor)
    (divisorsBelow : ∀ divisor, 0 < divisor →
      divisor < leastNondivisor → divisor ∣ programCode + 1)
    (operationAt : ∀ {source},
      Reaches (KorecR2.step program) (KorecR2.initialConfiguration input)
        source →
      0 < source.state →
      ∃ operation, program source.state = some operation)
    (candidate : Nat → Nat)
    (globalScan : ∀ {source operation},
      Reaches (KorecR2.step program) (KorecR2.initialConfiguration input)
        source →
      0 < source.state →
      program source.state = some operation →
      NondivisorScan programCode 0 (source.state - 1)
        (candidate source.state))
    (residue : ∀ {source operation},
      Reaches (KorecR2.step program) (KorecR2.initialConfiguration input)
        source →
      0 < source.state →
      program source.state = some operation →
      (programCode + 1) % candidate source.state = operation.code)
    (nextCarryBelow : ∀ {source target operation},
      Reaches (KorecR2.step program) (KorecR2.initialConfiguration input)
        source →
      program source.state = some operation →
      KorecR2.step program source = some target →
      0 < target.state →
      candidate source.state - operation.code < leastNondivisor) :
    Certificate programCode leastNondivisor program where
  Relevant := Reaches (KorecR2.step program)
    (KorecR2.initialConfiguration input)
  leastPositive := leastPositive
  divisorsBelow := divisorsBelow
  operationAt := operationAt
  candidate := candidate
  globalScan := globalScan
  residue := residue
  nextRelevant := by
    intro source target operation run _ stepEq
    exact .tail run stepEq
  nextCarryBelow := nextCarryBelow

/-- A finite-state form of `Certificate`.  Only states below `stateBound`
must be encoded, and `closed` proves that this finite region contains every
successor of a relevant configuration. -/
structure BoundedCertificate (programCode leastNondivisor stateBound : Nat)
    (program : KorecR2.Program) where
  initialStateBound : 1 < stateBound
  closed : ∀ {source target}, source.state < stateBound →
    KorecR2.step program source = some target → target.state < stateBound
  leastPositive : 0 < leastNondivisor
  divisorsBelow : ∀ divisor, 0 < divisor → divisor < leastNondivisor →
    divisor ∣ programCode + 1
  operationAt : ∀ state, 0 < state → state < stateBound →
    ∃ operation, program state = some operation
  candidate : Nat → Nat
  globalScan : ∀ {state operation}, 0 < state → state < stateBound →
    program state = some operation →
    NondivisorScan programCode 0 (state - 1) (candidate state)
  residue : ∀ {state operation}, 0 < state → state < stateBound →
    program state = some operation →
    (programCode + 1) % candidate state = operation.code
  nextCarryBelow : ∀ {source target operation},
    source.state < stateBound →
    program source.state = some operation →
    KorecR2.step program source = some target → 0 < target.state →
    candidate source.state - operation.code < leastNondivisor

/-- Executable variant of `BoundedCertificate`.  A concrete program number
can discharge each nondivisor-rank obligation by reducing `scanNondivisor`
with the supplied finite fuel. -/
structure BoundedSearchCertificate
    (programCode leastNondivisor stateBound : Nat)
    (program : KorecR2.Program) where
  initialStateBound : 1 < stateBound
  closed : ∀ {source target}, source.state < stateBound →
    KorecR2.step program source = some target → target.state < stateBound
  leastPositive : 0 < leastNondivisor
  divisorsBelow : ∀ divisor, 0 < divisor → divisor < leastNondivisor →
    divisor ∣ programCode + 1
  operationAt : ∀ state, 0 < state → state < stateBound →
    ∃ operation, program state = some operation
  candidate : Nat → Nat
  scanFuel : Nat → Nat
  globalSearch : ∀ {state operation}, 0 < state → state < stateBound →
    program state = some operation →
    scanNondivisor programCode 0 (state - 1) (scanFuel state) =
      some (candidate state)
  residue : ∀ {state operation}, 0 < state → state < stateBound →
    program state = some operation →
    (programCode + 1) % candidate state = operation.code
  nextCarryBelow : ∀ {source target operation},
    source.state < stateBound →
    program source.state = some operation →
    KorecR2.step program source = some target → 0 < target.state →
    candidate source.state - operation.code < leastNondivisor

/-- Executable certificate over an arbitrary forward-invariant relevant
region. `stateBound` proves that only finitely many control labels occur, but
unreachable padding labels below the bound create no encoding obligations. -/
structure FiniteSearchCertificate
    (programCode leastNondivisor stateBound : Nat)
    (program : KorecR2.Program) where
  Relevant : KorecR2.Configuration → Prop
  relevantBound : ∀ {configuration}, Relevant configuration →
    configuration.state < stateBound
  leastPositive : 0 < leastNondivisor
  divisorsBelow : ∀ divisor, 0 < divisor → divisor < leastNondivisor →
    divisor ∣ programCode + 1
  operationAt : ∀ {source}, Relevant source → 0 < source.state →
    ∃ operation, program source.state = some operation
  candidate : Nat → Nat
  scanFuel : Nat → Nat
  globalSearch : ∀ {source operation}, Relevant source → 0 < source.state →
    program source.state = some operation →
    scanNondivisor programCode 0 (source.state - 1)
      (scanFuel source.state) = some (candidate source.state)
  residue : ∀ {source operation}, Relevant source → 0 < source.state →
    program source.state = some operation →
    (programCode + 1) % candidate source.state = operation.code
  nextRelevant : ∀ {source target operation}, Relevant source →
    program source.state = some operation →
    KorecR2.step program source = some target → Relevant target
  nextCarryBelow : ∀ {source target operation}, Relevant source →
    program source.state = some operation →
    KorecR2.step program source = some target → 0 < target.state →
    candidate source.state - operation.code < leastNondivisor

/-- Successful executable searches supply the inductive reader scans in the
general invariant-aware certificate. -/
def FiniteSearchCertificate.toCertificate
    {programCode leastNondivisor stateBound : Nat}
    {program : KorecR2.Program}
    (certificate : FiniteSearchCertificate programCode leastNondivisor
      stateBound program) :
    Certificate programCode leastNondivisor program where
  Relevant := certificate.Relevant
  leastPositive := certificate.leastPositive
  divisorsBelow := certificate.divisorsBelow
  operationAt := certificate.operationAt
  candidate := certificate.candidate
  globalScan := by
    intro source operation relevant positive lookup
    exact scanNondivisor_sound
      (certificate.globalSearch relevant positive lookup)
  residue := certificate.residue
  nextRelevant := certificate.nextRelevant
  nextCarryBelow := certificate.nextCarryBelow

/-- Kernel-checked bounded searches imply the corresponding inductive scan
certificates. -/
def BoundedSearchCertificate.toBoundedCertificate
    {programCode leastNondivisor stateBound : Nat}
    {program : KorecR2.Program}
    (certificate : BoundedSearchCertificate programCode leastNondivisor
      stateBound program) :
    BoundedCertificate programCode leastNondivisor stateBound program where
  initialStateBound := certificate.initialStateBound
  closed := certificate.closed
  leastPositive := certificate.leastPositive
  divisorsBelow := certificate.divisorsBelow
  operationAt := certificate.operationAt
  candidate := certificate.candidate
  globalScan := by
    intro state operation positive bounded lookup
    exact scanNondivisor_sound
      (certificate.globalSearch positive bounded lookup)
  residue := certificate.residue
  nextCarryBelow := certificate.nextCarryBelow

/-- A bounded arithmetic certificate supplies the forward-invariant region
required by the operational interpreter. -/
def BoundedCertificate.toCertificate
    {programCode leastNondivisor stateBound : Nat}
    {program : KorecR2.Program}
    (certificate : BoundedCertificate programCode leastNondivisor stateBound
      program) :
    Certificate programCode leastNondivisor program where
  Relevant := fun configuration => configuration.state < stateBound
  leastPositive := certificate.leastPositive
  divisorsBelow := certificate.divisorsBelow
  operationAt := by
    intro source relevant positive
    exact certificate.operationAt source.state positive relevant
  candidate := certificate.candidate
  globalScan := by
    intro source operation relevant positive lookup
    exact certificate.globalScan positive relevant lookup
  residue := by
    intro source operation relevant positive lookup
    exact certificate.residue positive relevant lookup
  nextRelevant := by
    intro source target operation relevant _ stepEq
    exact certificate.closed relevant stepEq
  nextCarryBelow := by
    intro source target operation relevant lookup stepEq targetPositive
    exact certificate.nextCarryBelow relevant lookup stepEq targetPositive

/-- Korec's least-nondivisor condition is sufficient for the concrete U20
reader invariant. -/
def Certificate.toEncoding
    {programCode leastNondivisor : Nat} {program : KorecR2.Program}
    (certificate : Certificate programCode leastNondivisor program) :
    Encoding programCode program :=
  Encoding.ofNondivisorScan programCode program
    (fun source carry => certificate.Relevant source ∧
      (source.state = 0 ∨ carry < leastNondivisor))
    (fun {source : KorecR2.Configuration} {carry : Nat}
        (invariant : certificate.Relevant source ∧
        (source.state = 0 ∨ carry < leastNondivisor)) statePositive =>
      certificate.operationAt invariant.1 statePositive)
    (by
      intro source target operation carry statePositive lookup stepEq carrySmall
      let selected := certificate.candidate source.state
      have carryBelow : carry < leastNondivisor := by
        rcases carrySmall.2 with sourceHalt | carryBelow
        · omega
        · exact carryBelow
      have initialDivisors : ∀ divisor, 0 < divisor → divisor ≤ carry →
          divisor ∣ programCode + 1 := by
        intro divisor positive bound
        exact certificate.divisorsBelow divisor positive
          (by omega)
      have scan := nondivisorScan_drop_initial_divisors carry initialDivisors
        (certificate.globalScan carrySmall.1 statePositive lookup)
      refine ⟨selected, scan,
        certificate.residue carrySmall.1 statePositive lookup, ?_⟩
      refine ⟨certificate.nextRelevant carrySmall.1 lookup stepEq, ?_⟩
      by_cases targetHalt : target.state = 0
      · exact Or.inl targetHalt
      · refine Or.inr ?_
        rw [certificate.residue carrySmall.1 statePositive lookup]
        exact certificate.nextCarryBelow carrySmall.1 lookup stepEq (by omega))

/-- A relevance proof for one input supplies exactly the initial reader
invariant used by the halting-equivalence theorem.  Certificates need not
cover unrelated natural inputs. -/
theorem Certificate.initialEncodingInvariant
    {programCode leastNondivisor : Nat} {program : KorecR2.Program}
    (certificate : Certificate programCode leastNondivisor program)
    (input : Nat)
    (relevant : certificate.Relevant (KorecR2.initialConfiguration input)) :
    certificate.toEncoding.Invariant (KorecR2.initialConfiguration input) 0 := by
  exact ⟨relevant, Or.inr certificate.leastPositive⟩

/-- The state-bound certificate regards every ordinary R2 input as
relevant, since the initial state is one. -/
theorem BoundedCertificate.initialRelevant
    {programCode leastNondivisor stateBound : Nat}
    {program : KorecR2.Program}
    (certificate : BoundedCertificate programCode leastNondivisor stateBound
      program) (input : Nat) :
    certificate.toCertificate.Relevant
      (KorecR2.initialConfiguration input) := by
  simpa [BoundedCertificate.toCertificate, KorecR2.initialConfiguration] using
    certificate.initialStateBound

end Mortality.SourceMachine.KorecProgramCode
