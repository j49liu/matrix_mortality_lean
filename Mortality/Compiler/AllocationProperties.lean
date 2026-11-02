import Mortality.Compiler.DistinctCertificate

/-!
# Structural properties of the concrete phase allocation

These lemmas turn the finite checks in `FixedAllocation` into the ownership
facts used by the unrestricted-word converse.  Boundary phases are injective
on quotient states.  Every physical letter is sourced either at its edge's
program boundary or inside that occurrence's private interval, and private
intervals belonging to distinct indexed occurrences are disjoint.
-/

namespace Mortality.Compiler.AllocationProperties

open Mortality
open Mortality.OneCounter
open Mortality.Compiler
open Mortality.Compiler.FixedAllocation
open Mortality.PeriodicCode

set_option maxRecDepth 1000000
set_option maxHeartbeats 8000000

theorem fixedEdge_endpoints_mem {edge : Edge Nat}
    (edgeMem : edge ∈ fixedProgram.edges) :
    edge.source ∈ SourceMachine.quotientStates ∧
      edge.target ∈ SourceMachine.quotientStates := by
  have checked :=
    (List.all_eq_true.mp fixedEndpoints_are_quotientStates) edge edgeMem
  simpa using checked

theorem boundaryPhase_bound {state : Nat}
    (stateMem : state ∈ SourceMachine.quotientStates) :
    boundaryPhase state < SourceMachine.quotientStates.length := by
  exact List.idxOf_lt_length_of_mem stateMem

private theorem map_injective_on_of_nodup
    {α β : Type} (function : α → β) {values : List α}
    (mappedNodup : (values.map function).Nodup)
    {first second : α} (firstMem : first ∈ values)
    (secondMem : second ∈ values)
    (imagesEqual : function first = function second) :
    first = second := by
  induction values generalizing first second with
  | nil => simp at firstMem
  | cons head tail inductionHypothesis =>
      rw [List.map_cons, List.nodup_cons] at mappedNodup
      simp only [List.mem_cons] at firstMem secondMem
      rcases firstMem with rfl | firstMem <;>
        rcases secondMem with rfl | secondMem
      · rfl
      · exact False.elim
          (mappedNodup.1 (List.mem_map.mpr
            ⟨second, secondMem, imagesEqual.symm⟩))
      · exact False.elim
          (mappedNodup.1 (List.mem_map.mpr
            ⟨first, firstMem, imagesEqual⟩))
      · exact inductionHypothesis mappedNodup.2 firstMem secondMem imagesEqual

/-- Dense boundary phases retain the quotient-state label. -/
theorem boundaryPhase_injective_on_quotientStates
    {first second : Nat}
    (firstMem : first ∈ SourceMachine.quotientStates)
    (secondMem : second ∈ SourceMachine.quotientStates)
    (phaseEq : boundaryPhase first = boundaryPhase second) :
    first = second := by
  apply map_injective_on_of_nodup boundaryPhase
  · rw [boundaryPhases_eq_range]
    exact List.nodup_range
  · exact firstMem
  · exact secondMem
  · exact phaseEq

def InPrivateBlock (index : Nat) (edge : Edge Nat) (phase : Nat) : Prop :=
  privateBase index ≤ phase ∧
    phase < privateBase index + instructionPrivateCost edge.instruction

theorem privateBase_after_boundaries {index : Nat} {edge : Edge Nat}
    (indexedMem : (edge, index) ∈ fixedProgram.edges.zipIdx) :
    SourceMachine.quotientStates.length ≤ privateBase index := by
  have checked := (List.all_eq_true.mp
    fixedPrivateBlocks_after_boundaries) (edge, index) indexedMem
  simpa using checked

theorem privateBlock_bounded {index : Nat} {edge : Edge Nat}
    (indexedMem : (edge, index) ∈ fixedProgram.edges.zipIdx)
    {phase : Nat} (phasePrivate : InPrivateBlock index edge phase) :
    phase < genuinePhaseBound := by
  have blockFits := (List.all_eq_true.mp fixedPrivateBlocks_fit)
    (edge, index) indexedMem
  have blockFits' : privateBase index +
      instructionPrivateCost edge.instruction ≤ genuinePhaseBound := by
    simpa using blockFits
  unfold InPrivateBlock at phasePrivate
  omega

/-- Checked source-phase ownership for every letter of every occurrence. -/
private theorem edgeLetter_sources_owned_check :
    fixedProgram.edges.zipIdx.all (fun indexed =>
      (edgeAlphabet indexed.2 indexed.1).all (fun letter =>
        letter.sourcePhase = boundaryPhase indexed.1.source ||
          (privateBase indexed.2 ≤ letter.sourcePhase &&
            letter.sourcePhase < privateBase indexed.2 +
              instructionPrivateCost indexed.1.instruction))) = true := by
  decide

theorem edgeLetter_source_owned
    {index : Nat} {edge : Edge Nat} {letter : PhysicalTemplate}
    (indexedMem : (edge, index) ∈ fixedProgram.edges.zipIdx)
    (letterMem : letter ∈ edgeAlphabet index edge) :
    letter.sourcePhase = boundaryPhase edge.source ∨
      InPrivateBlock index edge letter.sourcePhase := by
  have occurrenceChecked :=
    (List.all_eq_true.mp edgeLetter_sources_owned_check)
      (edge, index) indexedMem
  have letterChecked :=
    (List.all_eq_true.mp occurrenceChecked) letter letterMem
  simpa [InPrivateBlock] using letterChecked

/-- Checked target-phase ownership: a module letter stays in its occurrence's
private block or returns to that edge's target boundary. -/
private theorem edgeLetter_targets_owned_check :
    fixedProgram.edges.zipIdx.all (fun indexed =>
      (edgeAlphabet indexed.2 indexed.1).all (fun letter =>
        letter.targetPhase = boundaryPhase indexed.1.target ||
          (privateBase indexed.2 ≤ letter.targetPhase &&
            letter.targetPhase < privateBase indexed.2 +
              instructionPrivateCost indexed.1.instruction))) = true := by
  decide

theorem edgeLetter_target_owned
    {index : Nat} {edge : Edge Nat} {letter : PhysicalTemplate}
    (indexedMem : (edge, index) ∈ fixedProgram.edges.zipIdx)
    (letterMem : letter ∈ edgeAlphabet index edge) :
    letter.targetPhase = boundaryPhase edge.target ∨
      InPrivateBlock index edge letter.targetPhase := by
  have occurrenceChecked :=
    (List.all_eq_true.mp edgeLetter_targets_owned_check)
      (edge, index) indexedMem
  have letterChecked :=
    (List.all_eq_true.mp occurrenceChecked) letter letterMem
  simpa [InPrivateBlock] using letterChecked

/-- Earlier occurrence blocks end before later occurrence blocks begin. -/
private theorem privateBlocks_ordered_check :
    fixedProgram.edges.zipIdx.all (fun first =>
      fixedProgram.edges.zipIdx.all (fun second =>
        if first.2 < second.2 then
          privateBase first.2 + instructionPrivateCost first.1.instruction ≤
            privateBase second.2
        else true)) = true := by
  decide

theorem privateBlock_before
    {firstIndex secondIndex : Nat} {firstEdge secondEdge : Edge Nat}
    (firstMem : (firstEdge, firstIndex) ∈ fixedProgram.edges.zipIdx)
    (secondMem : (secondEdge, secondIndex) ∈ fixedProgram.edges.zipIdx)
    (indexLt : firstIndex < secondIndex) :
    privateBase firstIndex +
        instructionPrivateCost firstEdge.instruction ≤
      privateBase secondIndex := by
  have firstChecked :=
    (List.all_eq_true.mp privateBlocks_ordered_check)
      (firstEdge, firstIndex) firstMem
  have secondChecked :=
    (List.all_eq_true.mp firstChecked) (secondEdge, secondIndex) secondMem
  simpa [indexLt] using secondChecked

/-- A phase cannot belong to the private blocks of two different indexed
edge occurrences. -/
theorem privateBlock_owner_unique
    {firstIndex secondIndex phase : Nat} {firstEdge secondEdge : Edge Nat}
    (firstMem : (firstEdge, firstIndex) ∈ fixedProgram.edges.zipIdx)
    (secondMem : (secondEdge, secondIndex) ∈ fixedProgram.edges.zipIdx)
    (firstPrivate : InPrivateBlock firstIndex firstEdge phase)
    (secondPrivate : InPrivateBlock secondIndex secondEdge phase) :
    firstIndex = secondIndex := by
  by_cases indicesEqual : firstIndex = secondIndex
  · exact indicesEqual
  have order : firstIndex < secondIndex ∨ secondIndex < firstIndex := by omega
  rcases order with indexLt | indexGt
  · have separated := privateBlock_before firstMem secondMem indexLt
    unfold InPrivateBlock at firstPrivate secondPrivate
    omega
  · have separated := privateBlock_before secondMem firstMem indexGt
    unfold InPrivateBlock at firstPrivate secondPrivate
    omega

/-- Program boundaries and occurrence-private phases are disjoint. -/
theorem boundary_ne_private
    {state index phase : Nat} {edge : Edge Nat}
    (stateMem : state ∈ SourceMachine.quotientStates)
    (indexedMem : (edge, index) ∈ fixedProgram.edges.zipIdx)
    (phasePrivate : InPrivateBlock index edge phase) :
    boundaryPhase state ≠ phase := by
  have boundaryBound := boundaryPhase_bound stateMem
  have privateLower := privateBase_after_boundaries indexedMem
  unfold InPrivateBlock at phasePrivate
  omega

def reservedDigitCheck (digit : Int) : Bool :=
  decide (-1 ≤ digit) && decide (digit ≤ 4)

theorem reservedDigitCheck_iff (digit : Int) :
    reservedDigitCheck digit = true ↔ ReservedDigit digit := by
  simp [reservedDigitCheck, ReservedDigit]

/-- Every letter in the flattened genuine alphabet satisfies the common
phase and digit bounds needed by phase enforcement. -/
private theorem listedTemplate_guard_check :
    listedTemplates.all (fun letter =>
      letter.sourcePhase < genuinePhaseBound &&
        letter.targetPhase < genuinePhaseBound &&
          reservedDigitCheck letter.digit) = true := by
  decide

theorem listedLetter_guard {letter : PhysicalTemplate}
    (letterMem : letter ∈ listedTemplates) :
    letter.sourcePhase < genuinePhaseBound ∧
      letter.targetPhase < genuinePhaseBound ∧
        ReservedDigit letter.digit := by
  have checked :=
    (List.all_eq_true.mp listedTemplate_guard_check) letter letterMem
  simp only [Bool.and_eq_true] at checked
  have sourceBound : letter.sourcePhase < genuinePhaseBound := by
    simpa using checked.1.1
  have targetBound : letter.targetPhase < genuinePhaseBound := by
    simpa using checked.1.2
  have reserved := (reservedDigitCheck_iff letter.digit).mp checked.2
  exact ⟨sourceBound, targetBound, reserved⟩

/-- Membership in the flattened list exposes the indexed edge occurrence
that contributed the letter. -/
theorem listedLetter_has_owner {letter : PhysicalTemplate}
    (letterMem : letter ∈ listedTemplates) :
    ∃ edge index,
      (edge, index) ∈ fixedProgram.edges.zipIdx ∧
        letter ∈ edgeAlphabet index edge := by
  unfold listedTemplates at letterMem
  obtain ⟨indexed, indexedMem, localMem⟩ := List.mem_flatMap.mp letterMem
  exact ⟨indexed.1, indexed.2, indexedMem, localMem⟩

theorem indexedEdge_mem {edge : Edge Nat} {index : Nat}
    (indexedMem : (edge, index) ∈ fixedProgram.edges.zipIdx) :
    edge ∈ fixedProgram.edges := by
  have indexedFacts := List.mem_zipIdx indexedMem
  exact indexedFacts.2.2 ▸ List.getElem_mem indexedFacts.2.1

/-- Every local occurrence alphabet embeds in the flattened genuine list. -/
theorem edgeLetter_listed {edge : Edge Nat} {index : Nat}
    (indexedMem : (edge, index) ∈ fixedProgram.edges.zipIdx)
    {letter : PhysicalTemplate}
    (letterMem : letter ∈ edgeAlphabet index edge) :
    letter ∈ listedTemplates := by
  unfold listedTemplates
  exact List.mem_flatMap.mpr ⟨(edge, index), indexedMem, letterMem⟩

/-- The cleanup increment is the only self-loop occurrence in the concrete
fixed program. -/
private theorem fixedNonincrement_not_selfloop_check :
    fixedProgram.edges.all (fun edge =>
      if edge.instruction == Instruction.increment then true
      else edge.source != edge.target) = true := by
  decide

theorem fixedEdge_source_ne_target_of_not_increment
    {edge : Edge Nat} {index : Nat}
    (indexedMem : (edge, index) ∈ fixedProgram.edges.zipIdx)
    (notIncrement : edge.instruction ≠ .increment) :
    edge.source ≠ edge.target := by
  have checked := (List.all_eq_true.mp
    fixedNonincrement_not_selfloop_check) edge (indexedEdge_mem indexedMem)
  simp [notIncrement] at checked
  exact checked

theorem indexedEdge_eq_of_index_eq
    {firstEdge secondEdge : Edge Nat} {firstIndex secondIndex : Nat}
    (firstMem : (firstEdge, firstIndex) ∈ fixedProgram.edges.zipIdx)
    (secondMem : (secondEdge, secondIndex) ∈ fixedProgram.edges.zipIdx)
    (indexEq : firstIndex = secondIndex) : firstEdge = secondEdge := by
  subst secondIndex
  have firstFacts := List.mem_zipIdx firstMem
  have secondFacts := List.mem_zipIdx secondMem
  exact firstFacts.2.2.trans secondFacts.2.2.symm

/-- A globally available letter that preserves locality on a unary boundary
code must advertise that boundary as its source phase. -/
theorem survivingListedLetter_source_phase
    {state counter : Nat} {letter : PhysicalTemplate}
    (stateMem : state ∈ SourceMachine.quotientStates)
    (letterMem : letter ∈ listedTemplates)
    (outputLocal : LocalAt codingPrime
      (letter.act codingPrime
        (phaseAffine (boundaryPhase state)
          (unaryCode codingPrime counter)))) :
    letter.sourcePhase = boundaryPhase state := by
  have guard := listedLetter_guard letterMem
  have inputLocal := IncrementModule.phaseUnaryCode_local codingPrime
    (boundaryPhase state) counter codingPrime_isPrime.1
  have letterMembership : InPhaseAt codingPrime letter.sourcePhase
      letter.digit
      (phaseAffine (boundaryPhase state) (unaryCode codingPrime counter)) := by
    apply physicalLetter_input_inPhaseAt codingPrime_isPrime guard.2.2
      inputLocal
    simpa [PhysicalTemplate.act, PhysicalTemplate.matrix] using outputLocal
  obtain ⟨actualDigit, actualMembership⟩ :=
    unaryCode_inPhaseAt (base := codingPrime)
      (phase := boundaryPhase state) (counter := counter)
      codingPrime_isPrime.1
  have phaseDigit := InPhaseAt.unique codingPrime_isPrime
    codingPrime_phase_bound
    (by
      have boundaryBound := boundaryPhase_bound stateMem
      have boundariesFit : SourceMachine.quotientStates.length ≤
          genuinePhaseBound := by decide
      unfold totalPhaseCount
      omega)
    (by
      have sourceBound := guard.1
      unfold totalPhaseCount
      omega)
    actualMembership letterMembership (SameLine.refl _)
  exact phaseDigit.1.symm

/-- The first surviving global letter chooses an actual outgoing edge of the
current program state; no occurrence-private source can masquerade as a
program boundary. -/
theorem survivingListedLetter_selects_edge
    {state counter : Nat} {letter : PhysicalTemplate}
    (stateMem : state ∈ SourceMachine.quotientStates)
    (letterMem : letter ∈ listedTemplates)
    (outputLocal : LocalAt codingPrime
      (letter.act codingPrime
        (phaseAffine (boundaryPhase state)
          (unaryCode codingPrime counter)))) :
    ∃ edge index,
      (edge, index) ∈ fixedProgram.edges.zipIdx ∧
        letter ∈ edgeAlphabet index edge ∧ edge.source = state := by
  obtain ⟨edge, index, indexedMem, localMem⟩ :=
    listedLetter_has_owner letterMem
  have sourcePhaseEq := survivingListedLetter_source_phase stateMem letterMem
    outputLocal
  rcases edgeLetter_source_owned indexedMem localMem with
    boundarySource | privateSource
  · have edgeMem := indexedEdge_mem indexedMem
    have edgeSourceMem := (fixedEdge_endpoints_mem edgeMem).1
    have stateEq := boundaryPhase_injective_on_quotientStates edgeSourceMem
      stateMem (boundarySource.symm.trans sourcePhaseEq)
    exact ⟨edge, index, indexedMem, localMem, stateEq⟩
  · exact False.elim
      (boundary_ne_private stateMem indexedMem privateSource
        sourcePhaseEq.symm)

/-- Once a run is inside one occurrence's private block, every globally
available letter that preserves locality belongs to that same indexed
occurrence.  This is the key no-interleaving fact for the global parser. -/
theorem survivingListedLetter_at_private
    {chosenEdge : Edge Nat} {chosenIndex phase : Nat}
    {actualDigit : Int} {vector : Vec2} {letter : PhysicalTemplate}
    (chosenMem :
      (chosenEdge, chosenIndex) ∈ fixedProgram.edges.zipIdx)
    (phasePrivate : InPrivateBlock chosenIndex chosenEdge phase)
    (actualMembership : InPhaseAt codingPrime phase actualDigit vector)
    (letterMem : letter ∈ listedTemplates)
    (outputLocal : LocalAt codingPrime (letter.act codingPrime vector)) :
    letter ∈ edgeAlphabet chosenIndex chosenEdge := by
  have guard := listedLetter_guard letterMem
  have letterMembership : InPhaseAt codingPrime letter.sourcePhase
      letter.digit vector := by
    apply physicalLetter_input_inPhaseAt codingPrime_isPrime guard.2.2
      actualMembership.local
    simpa [PhysicalTemplate.act, PhysicalTemplate.matrix] using outputLocal
  have actualPhaseBound : phase < totalPhaseCount := by
    have genuineBound := privateBlock_bounded chosenMem phasePrivate
    unfold totalPhaseCount
    omega
  have letterPhaseBound : letter.sourcePhase < totalPhaseCount := by
    have genuineBound := guard.1
    unfold totalPhaseCount
    omega
  have sourceEq := (InPhaseAt.unique codingPrime_isPrime
    codingPrime_phase_bound actualPhaseBound letterPhaseBound
    actualMembership letterMembership (SameLine.refl _)).1.symm
  obtain ⟨ownerEdge, ownerIndex, ownerMem, localMem⟩ :=
    listedLetter_has_owner letterMem
  rcases edgeLetter_source_owned ownerMem localMem with
    boundarySource | ownerPrivate
  · have ownerSourceMem :=
      (fixedEdge_endpoints_mem (indexedEdge_mem ownerMem)).1
    exact False.elim
      (boundary_ne_private ownerSourceMem chosenMem phasePrivate
        (boundarySource.symm.trans sourceEq))
  · have ownerPrivateAtPhase :
        InPrivateBlock ownerIndex ownerEdge phase := by
      simpa [sourceEq] using ownerPrivate
    have indexEq := privateBlock_owner_unique chosenMem ownerMem phasePrivate
      ownerPrivateAtPhase
    have edgeEq := indexedEdge_eq_of_index_eq chosenMem ownerMem indexEq
    subst ownerIndex
    subst ownerEdge
    exact localMem

end Mortality.Compiler.AllocationProperties
