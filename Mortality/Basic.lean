import Std

/-!
# Finite words over a fixed alphabet

Words are lists in application order: the head acts first.  Matrix
products therefore multiply the head on the right.
-/

namespace Mortality

/-- Every letter of a word belongs to the supplied finite alphabet. -/
def WordOver {α : Type} (alphabet word : List α) : Prop :=
  ∀ letter ∈ word, letter ∈ alphabet

@[simp] theorem wordOver_nil {α : Type} (alphabet : List α) :
    WordOver alphabet [] := by
  simp [WordOver]

theorem wordOver_cons {α : Type} {alphabet : List α} {letter : α}
    {word : List α} (letterMem : letter ∈ alphabet)
    (wordOver : WordOver alphabet word) :
    WordOver alphabet (letter :: word) := by
  intro candidate candidateMem
  simp only [List.mem_cons] at candidateMem
  rcases candidateMem with rfl | candidateMem
  · exact letterMem
  · exact wordOver candidate candidateMem

theorem wordOver_append {α : Type} {alphabet first second : List α}
    (firstOver : WordOver alphabet first)
    (secondOver : WordOver alphabet second) :
    WordOver alphabet (first ++ second) := by
  intro letter letterMem
  simp only [List.mem_append] at letterMem
  rcases letterMem with inFirst | inSecond
  · exact firstOver letter inFirst
  · exact secondOver letter inSecond

/-- Adding a letter to an alphabet preserves every old word. -/
theorem WordOver.mono {α : Type} {small large word : List α}
    (wordOver : WordOver small word)
    (included : ∀ letter ∈ small, letter ∈ large) :
    WordOver large word := by
  intro letter letterMem
  exact included letter (wordOver letter letterMem)

theorem WordOver.take {α : Type} {alphabet word : List α}
    (wordOver : WordOver alphabet word) (length : Nat) :
    WordOver alphabet (word.take length) := by
  induction length generalizing word with
  | zero => simp [WordOver]
  | succ length inductionHypothesis =>
      cases word with
      | nil => simp [WordOver]
      | cons letter word =>
          apply wordOver_cons
          · exact wordOver letter (by simp)
          · apply inductionHypothesis
            intro candidate candidateMem
            exact wordOver candidate (by simp [candidateMem])

theorem WordOver.drop {α : Type} {alphabet word : List α}
    (wordOver : WordOver alphabet word) (length : Nat) :
    WordOver alphabet (word.drop length) := by
  induction length generalizing word with
  | zero => simpa using wordOver
  | succ length inductionHypothesis =>
      cases word with
      | nil => simp [WordOver]
      | cons letter word =>
          apply inductionHypothesis
          intro candidate candidateMem
          exact wordOver candidate (by simp [candidateMem])

theorem nodup_map_of_injective {α β : Type} (function : α → β)
    (injective : Function.Injective function) {values : List α}
    (nodup : values.Nodup) : (values.map function).Nodup := by
  induction values with
  | nil => simp
  | cons value values inductionHypothesis =>
      have split := List.nodup_cons.mp nodup
      rw [List.map_cons, List.nodup_cons]
      constructor
      · intro member
        obtain ⟨other, otherMem, equality⟩ := List.mem_map.mp member
        exact split.1 (injective equality ▸ otherMem)
      · exact inductionHypothesis split.2

/-- Lift a word over a mapped alphabet to a word over the source
alphabet.  No injectivity assumption is needed. -/
theorem wordOver_map_lift {α β : Type} (function : α → β)
    {alphabet : List α} {word : List β}
    (wordOver : WordOver (alphabet.map function) word) :
    ∃ sourceWord : List α,
      WordOver alphabet sourceWord ∧ sourceWord.map function = word := by
  induction word with
  | nil => exact ⟨[], wordOver_nil alphabet, rfl⟩
  | cons letter word inductionHypothesis =>
      have letterMem := wordOver letter (by simp)
      obtain ⟨sourceLetter, sourceLetterMem, sourceLetterEq⟩ :=
        List.mem_map.mp letterMem
      have tailOver : WordOver (alphabet.map function) word := by
        intro candidate candidateMem
        exact wordOver candidate (by simp [candidateMem])
      obtain ⟨sourceWord, sourceWordOver, sourceWordEq⟩ :=
        inductionHypothesis tailOver
      refine ⟨sourceLetter :: sourceWord,
        wordOver_cons sourceLetterMem sourceWordOver, ?_⟩
      simp only [List.map_cons, sourceWordEq, sourceLetterEq]

end Mortality
