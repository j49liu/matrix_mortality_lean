import Mortality.Compiler.PhysicalLetter

/-!
# Separation of phase-and-digit residue blocks

This is the finite-control arithmetic behind the phase guard.  Under the
manuscript's strict bound `p > 6N`, every reserved residue has a unique
phase and digit, with no modular wraparound.
-/

namespace Mortality.Compiler

def ReservedDigit (digit : Int) : Prop := -1 ≤ digit ∧ digit ≤ 4

def phaseResidue (phase : Nat) (digit : Int) : Int :=
  phaseShift phase + digit

theorem phaseResidue_nonnegative {phase : Nat} {digit : Int}
    (reserved : ReservedDigit digit) :
    0 ≤ phaseResidue phase digit := by
  unfold ReservedDigit at reserved
  unfold phaseResidue phaseShift
  omega

theorem phaseResidue_lt_prime {prime phaseCount phase : Nat} {digit : Int}
    (primeBound : 6 * phaseCount < prime) (phaseBound : phase < phaseCount)
    (reserved : ReservedDigit digit) :
    phaseResidue phase digit < (prime : Int) := by
  unfold ReservedDigit at reserved
  unfold phaseResidue phaseShift
  omega

/-- The blocks `6q+1+{-1,0,1,2,3,4}` are disjoint modulo `p`. -/
theorem phase_digit_unique {prime phaseCount firstPhase secondPhase : Nat}
    {firstDigit secondDigit : Int}
    (primeBound : 6 * phaseCount < prime)
    (firstPhaseBound : firstPhase < phaseCount)
    (secondPhaseBound : secondPhase < phaseCount)
    (firstReserved : ReservedDigit firstDigit)
    (secondReserved : ReservedDigit secondDigit)
    (congruent :
      phaseResidue firstPhase firstDigit % (prime : Int) =
        phaseResidue secondPhase secondDigit % (prime : Int)) :
    firstPhase = secondPhase ∧ firstDigit = secondDigit := by
  have firstNonnegative :=
    phaseResidue_nonnegative (phase := firstPhase) firstReserved
  have secondNonnegative :=
    phaseResidue_nonnegative (phase := secondPhase) secondReserved
  have firstBelow := phaseResidue_lt_prime (phase := firstPhase)
    primeBound firstPhaseBound firstReserved
  have secondBelow := phaseResidue_lt_prime (phase := secondPhase)
    primeBound secondPhaseBound secondReserved
  rw [Int.emod_eq_of_lt firstNonnegative firstBelow,
    Int.emod_eq_of_lt secondNonnegative secondBelow] at congruent
  have phaseEq : firstPhase = secondPhase := by
    unfold ReservedDigit at firstReserved secondReserved
    unfold phaseResidue phaseShift at congruent
    omega
  subst secondPhase
  constructor
  · rfl
  · unfold phaseResidue phaseShift at congruent
    omega

end Mortality.Compiler
