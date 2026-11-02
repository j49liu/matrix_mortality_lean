import Mortality.Compiler.PhysicalWord

/-!
# Boundary-aware parsers for forced finite scans

This file packages the induction shared by the compiler's automatic scans.
The scan state has zero residue before a fixed limit and a reserved marker
residue at the limit.  A completed path to a distinct guarded endpoint
cannot stop inside the scan, so locality forces every loop and the unique
exit.  The theorem returns both a certificate produced by the exit and the
unconsumed suffix at its canonical next state.
-/

namespace Mortality.Compiler

theorem forcedScanPrefixToEndpoint
    {Certificate : Prop} {prime phaseCount currentPhase endpointPhase : Nat}
    {markerDigit endpointDigit : Int} {endpoint next : Vec2}
    {alphabet : List PhysicalTemplate} {loopLetter exitLetter : PhysicalTemplate}
    {limit deleted remaining : Nat} {state : Nat → Vec2}
    (primeProperty : IsPrime prime) (primeBound : 6 * phaseCount < prime)
    (currentBound : currentPhase < phaseCount)
    (endpointBound : endpointPhase < phaseCount)
    (phaseDistinct : currentPhase ≠ endpointPhase)
    (endpointMembership : InPhaseAt prime endpointPhase endpointDigit endpoint)
    (beforeMembership : ∀ position, position < limit →
      InPhaseAt prime currentPhase 0 (state position))
    (markerMembership :
      InPhaseAt prime currentPhase markerDigit (state limit))
    (stateLocal : ∀ position, position ≤ limit → LocalAt prime (state position))
    (nextLocal : LocalAt prime next)
    (forceLoop : ∀ position, position < limit →
      ∀ {letter : PhysicalTemplate}, letter ∈ alphabet →
        LocalAt prime (letter.act prime (state position)) →
        letter = loopLetter)
    (forceExit : ∀ {letter : PhysicalTemplate}, letter ∈ alphabet →
      LocalAt prime (letter.act prime (state limit)) →
      Certificate ∧ letter = exitLetter)
    (loopStep : ∀ position, position < limit →
      SameLine (loopLetter.act prime (state position)) (state (position + 1)))
    (exitStep : Certificate →
      SameLine (exitLetter.act prime (state limit)) next)
    (sumEq : deleted + remaining = limit)
    {word : List PhysicalTemplate} (wordOver : WordOver alphabet word)
    (allLocal : AllStatesLocal prime word (state deleted))
    (completeRun :
      SameLine (physicalWordAction prime word (state deleted)) endpoint) :
    ∃ suffix,
      Certificate ∧
      word = List.replicate remaining loopLetter ++ [exitLetter] ++ suffix ∧
      WordOver alphabet suffix ∧
      AllStatesLocal prime suffix next ∧
      SameLine (physicalWordAction prime suffix next) endpoint := by
  induction remaining generalizing deleted word with
  | zero =>
      have deletedEq : deleted = limit := by omega
      have wordNonempty : word ≠ [] := by
        intro wordEmpty
        subst word
        have phasesEq := (markerMembership.unique primeProperty primeBound
          currentBound endpointBound endpointMembership (by
            simpa only [physicalWordAction, deletedEq] using completeRun)).1
        exact phaseDistinct phasesEq
      cases word with
      | nil => exact False.elim (wordNonempty rfl)
      | cons letter tail =>
          have letterMem := wordOver letter (by simp)
          have tailOver : WordOver alphabet tail := by
            intro candidate candidateMem
            exact wordOver candidate (by simp [candidateMem])
          obtain ⟨certificate, letterEq⟩ := forceExit letterMem (by
            simpa only [deletedEq] using allLocal.2.start)
          subst letter
          have firstStep := exitStep certificate
          have tailLocal : AllStatesLocal prime tail next := by
            apply AllStatesLocal.of_sameLine
              (primePositive := by have := primeProperty.1; omega)
              allLocal.2 nextLocal.1
            simpa only [deletedEq] using firstStep.symm
          have tailRun : SameLine
              (physicalWordAction prime tail next) endpoint := by
            apply physicalWordAction_tail_sameLine prime exitLetter tail
              (completeRun := by simpa only [deletedEq] using completeRun)
            simpa only [deletedEq] using firstStep
          exact ⟨tail, certificate, by simp, tailOver, tailLocal, tailRun⟩
  | succ remaining inductionHypothesis =>
      have deletedBelow : deleted < limit := by omega
      have currentMembership := beforeMembership deleted deletedBelow
      have wordNonempty : word ≠ [] := by
        intro wordEmpty
        subst word
        have phasesEq := (currentMembership.unique primeProperty primeBound
          currentBound endpointBound endpointMembership (by
            simpa only [physicalWordAction] using completeRun)).1
        exact phaseDistinct phasesEq
      cases word with
      | nil => exact False.elim (wordNonempty rfl)
      | cons letter tail =>
          have letterMem := wordOver letter (by simp)
          have tailOver : WordOver alphabet tail := by
            intro candidate candidateMem
            exact wordOver candidate (by simp [candidateMem])
          have letterEq := forceLoop deleted deletedBelow letterMem
            allLocal.2.start
          subst letter
          have firstStep := loopStep deleted deletedBelow
          have nextStateLocal := stateLocal (deleted + 1) (by omega)
          have tailLocal : AllStatesLocal prime tail (state (deleted + 1)) := by
            apply AllStatesLocal.of_sameLine
              (primePositive := by have := primeProperty.1; omega)
              allLocal.2 nextStateLocal.1 firstStep.symm
          have tailRun : SameLine
              (physicalWordAction prime tail (state (deleted + 1))) endpoint :=
            physicalWordAction_tail_sameLine prime loopLetter tail firstStep
              completeRun
          obtain ⟨suffix, certificate, tailEq, suffixOver, suffixLocal,
              suffixRun⟩ :=
            inductionHypothesis (deleted := deleted + 1) (by omega) tailOver
              tailLocal tailRun
          refine ⟨suffix, certificate, ?_, suffixOver, suffixLocal,
            suffixRun⟩
          rw [tailEq]
          simp [List.replicate_succ]

/-- A forced zero loop whose terminal marker has no surviving alphabet
letter cannot occur on any completed local path to a different guarded
endpoint. -/
theorem forcedScanRejectsAtMarker
    {prime phaseCount currentPhase endpointPhase : Nat}
    {markerDigit endpointDigit : Int} {endpoint : Vec2}
    {alphabet : List PhysicalTemplate} {loopLetter : PhysicalTemplate}
    {limit deleted remaining : Nat} {state : Nat → Vec2}
    (primeProperty : IsPrime prime) (primeBound : 6 * phaseCount < prime)
    (currentBound : currentPhase < phaseCount)
    (endpointBound : endpointPhase < phaseCount)
    (phaseDistinct : currentPhase ≠ endpointPhase)
    (endpointMembership : InPhaseAt prime endpointPhase endpointDigit endpoint)
    (beforeMembership : ∀ position, position < limit →
      InPhaseAt prime currentPhase 0 (state position))
    (markerMembership :
      InPhaseAt prime currentPhase markerDigit (state limit))
    (stateLocal : ∀ position, position ≤ limit → LocalAt prime (state position))
    (forceLoop : ∀ position, position < limit →
      ∀ {letter : PhysicalTemplate}, letter ∈ alphabet →
        LocalAt prime (letter.act prime (state position)) →
        letter = loopLetter)
    (rejectMarker : ∀ {letter : PhysicalTemplate}, letter ∈ alphabet →
      ¬LocalAt prime (letter.act prime (state limit)))
    (loopStep : ∀ position, position < limit →
      SameLine (loopLetter.act prime (state position)) (state (position + 1)))
    (sumEq : deleted + remaining = limit)
    {word : List PhysicalTemplate} (wordOver : WordOver alphabet word)
    (allLocal : AllStatesLocal prime word (state deleted))
    (completeRun :
      SameLine (physicalWordAction prime word (state deleted)) endpoint) :
    False := by
  induction remaining generalizing deleted word with
  | zero =>
      have deletedEq : deleted = limit := by omega
      have wordNonempty : word ≠ [] := by
        intro wordEmpty
        subst word
        have phasesEq := (markerMembership.unique primeProperty primeBound
          currentBound endpointBound endpointMembership (by
            simpa only [physicalWordAction, deletedEq] using completeRun)).1
        exact phaseDistinct phasesEq
      cases word with
      | nil => exact wordNonempty rfl
      | cons letter tail =>
          have letterMem := wordOver letter (by simp)
          exact rejectMarker letterMem (by
            simpa only [deletedEq] using allLocal.2.start)
  | succ remaining inductionHypothesis =>
      have deletedBelow : deleted < limit := by omega
      have currentMembership := beforeMembership deleted deletedBelow
      have wordNonempty : word ≠ [] := by
        intro wordEmpty
        subst word
        have phasesEq := (currentMembership.unique primeProperty primeBound
          currentBound endpointBound endpointMembership (by
            simpa only [physicalWordAction] using completeRun)).1
        exact phaseDistinct phasesEq
      cases word with
      | nil => exact wordNonempty rfl
      | cons letter tail =>
          have letterMem := wordOver letter (by simp)
          have tailOver : WordOver alphabet tail := by
            intro candidate candidateMem
            exact wordOver candidate (by simp [candidateMem])
          have letterEq := forceLoop deleted deletedBelow letterMem
            allLocal.2.start
          subst letter
          have firstStep := loopStep deleted deletedBelow
          have nextStateLocal := stateLocal (deleted + 1) (by omega)
          have tailLocal : AllStatesLocal prime tail (state (deleted + 1)) := by
            apply AllStatesLocal.of_sameLine
              (primePositive := by have := primeProperty.1; omega)
              allLocal.2 nextStateLocal.1 firstStep.symm
          have tailRun : SameLine
              (physicalWordAction prime tail (state (deleted + 1))) endpoint :=
            physicalWordAction_tail_sameLine prime loopLetter tail firstStep
              completeRun
          exact inductionHypothesis (deleted := deleted + 1) (by omega)
            tailOver tailLocal tailRun

end Mortality.Compiler
