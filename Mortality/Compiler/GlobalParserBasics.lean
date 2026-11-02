import Mortality.Compiler.AllocationProperties

/-!
# Finite-alphabet splitting for the global converse

For one indexed instruction occurrence, the full genuine alphabet is split
into its local alphabet and the filtered list of all remaining templates.
The first-foreign-letter decomposition is purely finite-list bookkeeping and
is reused by the boundary parser.
-/

namespace Mortality.Compiler.GlobalParserBasics

open Mortality
open Mortality.OneCounter
open Mortality.PeriodicCode
open Mortality.Compiler
open Mortality.Compiler.FixedAllocation
open Mortality.Compiler.AllocationProperties

def outsideAlphabet (alphabet : List PhysicalTemplate) : List PhysicalTemplate :=
  listedTemplates.filter fun letter => decide (letter ∉ alphabet)

theorem mem_outsideAlphabet_iff
    {alphabet : List PhysicalTemplate} {letter : PhysicalTemplate} :
    letter ∈ outsideAlphabet alphabet ↔
      letter ∈ listedTemplates ∧ letter ∉ alphabet := by
  simp [outsideAlphabet]

theorem listed_mem_local_or_outside
    (alphabet : List PhysicalTemplate) {letter : PhysicalTemplate}
    (letterMem : letter ∈ listedTemplates) :
    letter ∈ alphabet ∨ letter ∈ outsideAlphabet alphabet := by
  by_cases localMem : letter ∈ alphabet
  · exact .inl localMem
  · exact .inr ((mem_outsideAlphabet_iff).mpr ⟨letterMem, localMem⟩)

theorem wordOver_local_append_outside
    {alphabet word : List PhysicalTemplate}
    (globalOver : WordOver listedTemplates word) :
    WordOver (alphabet ++ outsideAlphabet alphabet) word := by
  intro letter letterMem
  exact List.mem_append.mpr
    (listed_mem_local_or_outside alphabet (globalOver letter letterMem))

/-- Split a global word at its first template outside a chosen local
alphabet.  In the second branch the residual suffix remains a global word. -/
theorem split_first_outside
    {alphabet word : List PhysicalTemplate}
    (localListed : ∀ {letter}, letter ∈ alphabet → letter ∈ listedTemplates)
    (globalOver : WordOver listedTemplates word) :
    WordOver alphabet word ∨
      ∃ initial letter suffix,
        word = initial ++ letter :: suffix ∧
        WordOver alphabet initial ∧
        letter ∈ listedTemplates ∧ letter ∉ alphabet ∧
        WordOver listedTemplates suffix := by
  rcases wordOver_append_first_right
      (wordOver_local_append_outside (alphabet := alphabet) globalOver) with
    localOnly | ⟨initial, letter, suffix, wordEq, initialOver,
      letterOutside, suffixPartitioned⟩
  · exact .inl localOnly
  · have outsideFacts := mem_outsideAlphabet_iff.mp letterOutside
    have suffixGlobal : WordOver listedTemplates suffix := by
      intro candidate candidateMem
      have partitioned := suffixPartitioned candidate candidateMem
      rcases List.mem_append.mp partitioned with localMem | outsideMem
      · exact localListed localMem
      · exact (mem_outsideAlphabet_iff.mp outsideMem).1
    exact .inr ⟨initial, letter, suffix, wordEq, initialOver,
      outsideFacts.1, outsideFacts.2, suffixGlobal⟩

/-- A non-self-loop occurrence has no surviving nonempty local word once its
canonical target boundary has been reached. -/
theorem localWord_from_target_empty
    {edge : Edge Nat} {index counter : Nat}
    (indexedMem : (edge, index) ∈ fixedProgram.edges.zipIdx)
    (notIncrement : edge.instruction ≠ .increment)
    {word : List PhysicalTemplate}
    (wordOver : WordOver (edgeAlphabet index edge) word)
    (allLocal : AllStatesLocal codingPrime word
      (phaseAffine (boundaryPhase edge.target)
        (unaryCode codingPrime counter))) :
    word = [] := by
  cases word with
  | nil => rfl
  | cons letter tail =>
      have letterLocal := wordOver letter (by simp)
      have letterListed := edgeLetter_listed indexedMem letterLocal
      have targetMem := (fixedEdge_endpoints_mem (indexedEdge_mem indexedMem)).2
      have sourcePhaseEq := survivingListedLetter_source_phase targetMem
        letterListed allLocal.2.start
      rcases edgeLetter_source_owned indexedMem letterLocal with
        sourceBoundary | sourcePrivate
      · have sourceMem :=
          (fixedEdge_endpoints_mem (indexedEdge_mem indexedMem)).1
        have statesEq := boundaryPhase_injective_on_quotientStates sourceMem
          targetMem (sourceBoundary.symm.trans sourcePhaseEq)
        exact False.elim
          ((fixedEdge_source_ne_target_of_not_increment indexedMem
            notIncrement) statesEq)
      · exact False.elim
          (boundary_ne_private targetMem indexedMem sourcePrivate
            sourcePhaseEq.symm)

end Mortality.Compiler.GlobalParserBasics
