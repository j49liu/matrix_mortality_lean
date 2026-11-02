import Mortality.Prime
import Mortality.SourceMachine.KorecPrimeSystem

/-!
# A literal normalized Korec prime system

This file checks the finite conclusions of Korec's Lemma 6.1 on one positive
state.  The lower factors are

`17, 19, 23, 29, 31, 37, 41`,

and the candidate is `43`.  Their quotient ranks at `41` and `43` are nine
and ten.  Thus the single endpoint equation forces candidate rank
`offset + state = 9 + 1`.  The two envelopes are

`3 * 10 + 3 < 41` and `43 < 3 * 9 + 17`.

The example passes through the general `System.toRankFrame` conversion and
then checks the automatically assigned gateway residue.
-/

namespace Mortality.SourceMachine.KorecNormalizedShellExample

open Mortality.SourceMachine
open Mortality.SourceMachine.KorecR2
open Mortality.SourceMachine.KorecNormalizedShell
open Mortality.SourceMachine.KorecPrimeSystem

/-- The halt gateway used by the positive-target normalization. -/
def gatewayProgram : KorecR2.Program := fun state =>
  if state = 1 then some (.incrementBoth 0) else none

def selectedPrimes : List Nat := [17, 19, 23, 29, 31, 37, 41, 43]

/-- A literal instance of conditions (6.1.1)--(6.1.5), specialized to
`c = 3`. -/
def gatewayPrimeSystem : System 2 where
  least := 17
  base := 41
  bound := 43
  lowerFactors := [17, 19, 23, 29, 31, 37, 41]
  candidates := [43]
  candidateLength := by decide
  lowerLength := by decide
  selectedOrdered := by decide
  leastMem := by simp
  selectedAtLeastLeast := by
    intro factor factorMem
    simp at factorMem
    omega
  selectedAtMostBound := by
    intro factor factorMem
    simp at factorMem
    omega
  primeLike := by
    intro factor factorMem
    simp at factorMem
    rcases factorMem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals
      refine ⟨by decide, ?_⟩
      intro divisor divisorDivides
      exact (Mortality.primeCheck_sound (by decide)).eq_one_or_self_of_dvd
        divisorDivides
  lowerAtMostBase := by
    intro factor factorMem
    simp at factorMem
    omega
  baseBelowCandidates := by simp
  leastSquareAboveBound := by decide
  endpointRank := by decide
  lowerEnvelope := by decide
  upperEnvelope := by decide

/-- A completely kernel-checked rank frame obtained through the general
Korec-system conversion. -/
def gatewayFrame : RankFrame 9 2 17 43 :=
  gatewayPrimeSystem.toRankFrame

def candidate : Nat → Nat := gatewayPrimeSystem.candidate

theorem gateway_quotient_rank :
    (selectedPrimes.map fun factor => candidate 1 / factor).sum = 10 := by
  decide

/-- The canonical residue assignment gives the gateway candidate operation
code two. -/
theorem gateway_assignedResidue :
    gatewayFrame.assignedResidue gatewayProgram 43 = 2 := by
  simpa [candidate, gatewayProgram, R2Relocation.shiftInstruction,
    R2Relocation.shiftState, KorecR2.Instruction.code] using
    (gatewayFrame.assignedResidue_candidate
      (program := gatewayProgram) (state := 1)
      (operation := .incrementBoth 0) (by decide) (by decide)
      (by simp [gatewayProgram]))

end Mortality.SourceMachine.KorecNormalizedShellExample
