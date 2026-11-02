import Mortality.Prime
import Mortality.Compiler.Padding

/-!
# Concrete phase and prime parameters

This file connects the executable counts to the phase guard and the
exact-cardinality dummy construction.
-/

namespace Mortality

set_option maxRecDepth 100000

def totalPhaseCount : Nat := genuinePhaseBound + paddingPhaseCount

def unusedPhases : List Nat :=
  (List.range paddingPhaseCount).map fun offset => genuinePhaseBound + offset

theorem totalPhaseCount_eq : totalPhaseCount = 8643 := by
  decide

theorem codingPrime_phase_bound : 6 * totalPhaseCount < codingPrime := by
  decide

theorem unusedPhases_length : unusedPhases.length = 5798 := by
  decide

theorem unusedPhases_nodup : unusedPhases.Nodup := by
  unfold unusedPhases
  apply nodup_map_of_injective
  · intro first second equality
    change genuinePhaseBound + first = genuinePhaseBound + second at equality
    omega
  · exact List.nodup_range

theorem unusedPhase_bounds {phase : Nat} (member : phase ∈ unusedPhases) :
    genuinePhaseBound ≤ phase ∧ phase < totalPhaseCount := by
  unfold unusedPhases at member
  obtain ⟨offset, offsetMem, rfl⟩ := List.mem_map.mp member
  have offsetBound : offset < paddingPhaseCount := by
    simpa using offsetMem
  unfold totalPhaseCount
  omega

theorem fixedDummyMatrices_nodup :
    (Compiler.dummyMatrices codingPrime unusedPhases).Nodup := by
  apply Compiler.dummyMatrices_nodup
  · decide
  · exact unusedPhases_nodup

theorem fixedDummyMatrices_length :
    (Compiler.dummyMatrices codingPrime unusedPhases).length = 5798 := by
  rw [Compiler.dummyMatrices_length, unusedPhases_length]

/-- Every reserved padding phase is separated from every genuine compiler
phase by the common phase guard. -/
theorem fixedDummy_rejects_genuine_phase
    {actualPhase dummyPhase : Nat} {actualDigit : Int}
    {numerator denominator : Int}
    (actualPhaseBound : actualPhase < genuinePhaseBound)
    (dummyMem : dummyPhase ∈ unusedPhases)
    (actualReserved : Compiler.ReservedDigit actualDigit)
    (denominatorNotDivisible : ¬(codingPrime : Int) ∣ denominator)
    (actualResidue :
      (codingPrime : Int) ∣ numerator - actualDigit * denominator) :
    ¬Compiler.LocalAt codingPrime
      (Matrix2.apply
        (IntMatrix2.cast (Compiler.dummyMatrix codingPrime dummyPhase))
        (Compiler.phasePoint actualPhase numerator denominator)) := by
  have dummyBounds := unusedPhase_bounds dummyMem
  apply Compiler.dummyMatrix_rejects_other_phase codingPrime_isPrime
    codingPrime_phase_bound
    (by unfold totalPhaseCount; omega) dummyBounds.2 actualReserved
    denominatorNotDivisible actualResidue
  omega

end Mortality
