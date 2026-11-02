import Mortality.SourceMachine.KorecLocalProgramCode

/-!
# A literal carry-sensitive Korec certificate

This file checks the finite-certificate interface on the one-instruction R2
program `INCREMENT BOTH; HALT`.  The example is deliberately small enough for
kernel reduction: candidate `3` is the first nondivisor after carry `0`, its
prescribed residue is operation code `2`, and the next boundary is halt with
carry `1`.
-/

namespace Mortality.SourceMachine.KorecLocalProgramCodeExample

open Mortality.SourceMachine
open Mortality.SourceMachine.KorecR2
open Mortality.SourceMachine.KorecProgramCode
open Mortality.SourceMachine.KorecLocalProgramCode

def haltProgram : KorecR2.Program := fun state =>
  if state = 1 then some (.incrementBoth 0) else none

def haltCandidate (_ : Nat) : Nat := 3

def haltGlobalLayout : FiniteControlLCMLayout 3 3 haltProgram 1 where
  relevantStates := [1, 0]
  initialMem := by simp
  leastPositive := by decide
  leastBounded := by decide
  operationAt := by
    intro state relevant statePositive
    simp at relevant
    rcases relevant with rfl | rfl
    · exact ⟨.incrementBoth 0, by simp [haltProgram]⟩
    · omega
  selectedFactors := [3]
  selectedNodup := by decide
  selectedProductSeparated := by simp
  selectedAtLeastLeast := by simp_all
  selectedAtMostBound := by simp_all
  selectedResidue := fun _ => 2
  selectedResiduePositive := by simp
  selectedResidueBelow := by simp
  selectedDivisorClassification := by
    intro factor factorMem divisor divisorDivides
    simp only [List.mem_singleton] at factorMem
    subst factor
    have divisorBound : divisor ≤ 3 := Nat.le_of_dvd (by decide) divisorDivides
    by_cases divisorZero : divisor = 0
    · subst divisor
      simp at divisorDivides
    by_cases divisorOne : divisor = 1
    · exact Or.inl divisorOne
    by_cases divisorTwo : divisor = 2
    · subst divisor
      simp at divisorDivides
    · right
      omega
  candidate := haltCandidate
  candidateMem := by simp [haltCandidate]
  candidateRankSum := by
    intro state relevant statePositive
    simp at relevant
    rcases relevant with rfl | rfl
    · decide
    · omega
  operationResidue := by
    intro state operation relevant statePositive lookup
    simp at relevant
    rcases relevant with rfl | rfl
    · simp [haltProgram] at lookup
      subst operation
      rfl
    · omega
  nextMem := by
    intro state target operation relevant lookup targetMem
    simp at relevant
    rcases relevant with rfl | rfl
    · simp [haltProgram] at lookup
      subst operation
      simp [possibleTargets] at targetMem
      subst target
      simp
    · simp [haltProgram] at lookup
  nextCarryBelow := by
    intro state target operation relevant lookup targetMem targetPositive
    simp at relevant
    rcases relevant with rfl | rfl
    · simp [haltProgram] at lookup
      subst operation
      simp [possibleTargets] at targetMem
      omega
    · simp [haltProgram] at lookup

example : haltGlobalLayout.crtProgramCode = 7 := by decide

/-- The global finite-state certificate reaches the same operational reader
through the checked global-to-local bridge. -/
def haltGlobalEncoding :
    LocalRankCertificate haltGlobalLayout.crtProgramCode haltProgram :=
  (LocalLCMLayout.ofGlobalLayout
    haltGlobalLayout.toControlLCMLayout.toLCMLayout).toLocalRankCertificateByCRT

theorem u2Halts_global_concrete_iff :
    U2Halts
        (U20Compilation.encodeRegisters
          (KorecU20Interpreter.registers 0
            haltGlobalLayout.crtProgramCode 0 0 0 0 0 0)) ↔
      KorecR2.HaltsFrom haltProgram
        { state := 1, registerZero := 0, registerTwo := 0 } := by
  exact KorecU20Interpreter.u2Halts_encodeSimulation_iff_r2HaltsFrom
    haltGlobalEncoding.toEncoding
    { state := 1, registerZero := 0, registerTwo := 0 } 0
    (by decide)
    (LocalLCMLayout.ofGlobalLayout_relevant_zero
      haltGlobalLayout.toControlLCMLayout.toLCMLayout
      haltGlobalLayout.initialRelevant)

def haltLayout : FiniteControlLocalLCMLayout 3 haltProgram 1 0 where
  relevantPairs := [(1, 0), (0, 1)]
  initialMem := by simp
  operationAt := by
    intro state carry relevant statePositive
    have relevant' :
        (state, carry) = (1, 0) ∨ (state, carry) = (0, 1) := by
      simpa using relevant
    rcases relevant' with relevant | relevant
    · have pairEq : (state, carry) = (1, 0) := relevant
      cases pairEq
      exact ⟨.incrementBoth 0, by simp [haltProgram]⟩
    · have pairEq : (state, carry) = (0, 1) := relevant
      cases pairEq
      omega
  selectedFactors := [3]
  selectedNodup := by decide
  selectedProductSeparated := by simp
  selectedAtMostBound := by simp_all
  selectedResidue := fun _ => 2
  selectedResiduePositive := by simp
  selectedResidueBelow := by simp
  selectedDivisorClassification := by
    intro factor factorMem divisor divisorDivides
    simp only [List.mem_singleton] at factorMem
    subst factor
    have divisorBound : divisor ≤ 3 := Nat.le_of_dvd (by decide) divisorDivides
    by_cases divisorZero : divisor = 0
    · subst divisor
      simp at divisorDivides
    by_cases divisorOne : divisor = 1
    · exact Or.inl divisorOne
    by_cases divisorTwo : divisor = 2
    · subst divisor
      simp at divisorDivides
    · right
      omega
  candidate := haltCandidate
  candidateMem := by
    intro state carry relevant statePositive
    simp [haltCandidate]
  carryBelowCandidate := by
    intro state carry relevant statePositive
    have relevant' :
        (state, carry) = (1, 0) ∨ (state, carry) = (0, 1) := by
      simpa using relevant
    rcases relevant' with relevant | relevant
    · cases relevant
      simp [haltCandidate]
    · cases relevant
      omega
  candidateRankDifferenceSum := by
    intro state carry relevant statePositive
    have relevant' :
        (state, carry) = (1, 0) ∨ (state, carry) = (0, 1) := by
      simpa using relevant
    rcases relevant' with relevant | relevant
    · cases relevant
      decide
    · cases relevant
      omega
  operationResidue := by
    intro state carry operation relevant statePositive lookup
    have relevant' :
        (state, carry) = (1, 0) ∨ (state, carry) = (0, 1) := by
      simpa using relevant
    rcases relevant' with relevant | relevant
    · cases relevant
      simp [haltProgram] at lookup
      subst operation
      rfl
    · cases relevant
      omega
  nextMem := by
    intro state target carry operation relevant lookup targetMem
    have relevant' :
        (state, carry) = (1, 0) ∨ (state, carry) = (0, 1) := by
      simpa using relevant
    rcases relevant' with relevant | relevant
    · cases relevant
      simp [haltProgram] at lookup
      subst operation
      simp [possibleTargets] at targetMem
      subst target
      simp [haltCandidate, KorecR2.Instruction.code]
    · cases relevant
      simp [haltProgram] at lookup

example : haltLayout.crtProgramCode = 7 := by decide

/-- The concrete finite certificate produces the exact operational reader
encoding without any supplied arithmetic hypothesis. -/
def haltEncoding : LocalRankCertificate haltLayout.crtProgramCode haltProgram :=
  haltLayout.toLocalRankCertificateByCRT

theorem u2Halts_concrete_iff :
    U2Halts
        (U20Compilation.encodeRegisters
          (KorecU20Interpreter.registers 0 haltLayout.crtProgramCode
            0 0 0 0 0 0)) ↔
      KorecR2.HaltsFrom haltProgram
        { state := 1, registerZero := 0, registerTwo := 0 } := by
  exact KorecU20Interpreter.u2Halts_encodeSimulation_iff_r2HaltsFrom
    haltEncoding.toEncoding
    { state := 1, registerZero := 0, registerTwo := 0 } 0
    (by decide) haltLayout.initialRelevant

end Mortality.SourceMachine.KorecLocalProgramCodeExample
