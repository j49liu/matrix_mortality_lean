import Mortality.Compiler.Enforcement

/-!
# Arbitrary words of physical letters

The matrix semigroup does not restrict the order in which generators
are used.  This file packages physical-letter metadata and proves that
an error remains an error through an arbitrary word.  Equivalently, if
the final point is local, every prefix state of the word was local.
-/

namespace Mortality.Compiler

structure PhysicalTemplate where
  sourcePhase : Nat
  targetPhase : Nat
  digit : Int
  preCoefficient : Int
  postSign : Sign
  postCoefficient : Int
  deriving DecidableEq, Repr

namespace PhysicalTemplate

def matrix (prime : Nat) (letter : PhysicalTemplate) : IntMatrix2 :=
  physicalLetter prime letter.sourcePhase letter.targetPhase letter.digit
    letter.preCoefficient letter.postSign letter.postCoefficient

def act (prime : Nat) (letter : PhysicalTemplate) (vector : Vec2) : Vec2 :=
  Matrix2.apply (IntMatrix2.cast (letter.matrix prime)) vector

theorem matrix_nonsingular {prime : Nat} (letter : PhysicalTemplate)
    (primePositive : 0 < prime) :
    (IntMatrix2.cast (letter.matrix prime)).Nonsingular :=
  IntMatrix2.cast_nonsingular
    (physicalLetter_nonsingular primePositive)

theorem act_nonzero {prime : Nat} (letter : PhysicalTemplate)
    (primePositive : 0 < prime) {vector : Vec2}
    (vectorNonzero : vector.Nonzero) :
    (letter.act prime vector).Nonzero :=
  Matrix2.apply_nonzero (letter.matrix_nonsingular primePositive)
    vectorNonzero

theorem preserves_error {prime : Nat} (letter : PhysicalTemplate)
    (primePositive : 0 < prime) {vector : Vec2}
    (inputError : ErrorAt prime vector) :
    ErrorAt prime (letter.act prime vector) := by
  exact physicalLetter_preserves_error letter.sourcePhase letter.targetPhase
    letter.digit letter.preCoefficient letter.postSign letter.postCoefficient
    primePositive inputError

/-- The contrapositive form needed when an unrestricted word is read
backwards from its local endpoint. -/
theorem local_of_output_local {prime : Nat} (letter : PhysicalTemplate)
    (primePositive : 0 < prime) {vector : Vec2}
    (inputNonzero : vector.Nonzero)
    (outputLocal : LocalAt prime (letter.act prime vector)) :
    LocalAt prime vector := by
  apply Classical.byContradiction
  intro inputNotLocal
  have outputError := letter.preserves_error primePositive
    ⟨inputNonzero, inputNotLocal⟩
  exact outputError.2 outputLocal

end PhysicalTemplate

/-- Apply a list in chronological order. -/
def physicalWordAction (prime : Nat) : List PhysicalTemplate → Vec2 → Vec2
  | [], vector => vector
  | letter :: word, vector =>
      physicalWordAction prime word (letter.act prime vector)

theorem physicalWordAction_append (prime : Nat)
    (first second : List PhysicalTemplate) (vector : Vec2) :
    physicalWordAction prime (first ++ second) vector =
      physicalWordAction prime second
        (physicalWordAction prime first vector) := by
  induction first generalizing vector with
  | nil => rfl
  | cons letter first inductionHypothesis =>
      exact inductionHypothesis (letter.act prime vector)

theorem physicalWordAction_eq_product (prime : Nat)
    (word : List PhysicalTemplate) (vector : Vec2) :
    physicalWordAction prime word vector =
      Matrix2.apply
        (matrixWordProduct (word.map fun letter =>
          IntMatrix2.cast (letter.matrix prime))) vector := by
  induction word generalizing vector with
  | nil => simp [physicalWordAction]
  | cons letter word inductionHypothesis =>
      simp only [physicalWordAction, List.map_cons, matrixWordProduct_cons,
        Matrix2.apply_mul]
      exact inductionHypothesis (letter.act prime vector)

theorem physicalWordAction_preserves_sameLine (prime : Nat)
    (word : List PhysicalTemplate) {first second : Vec2}
    (same : SameLine first second) :
    SameLine (physicalWordAction prime word first)
      (physicalWordAction prime word second) := by
  induction word generalizing first second with
  | nil => exact same
  | cons letter word inductionHypothesis =>
      exact inductionHypothesis
        (same.apply (IntMatrix2.cast (letter.matrix prime)))

theorem physicalWordAction_nonzero {prime : Nat}
    (primePositive : 0 < prime) (word : List PhysicalTemplate)
    {vector : Vec2} (inputNonzero : vector.Nonzero) :
    (physicalWordAction prime word vector).Nonzero := by
  induction word generalizing vector with
  | nil => exact inputNonzero
  | cons letter word inductionHypothesis =>
      exact inductionHypothesis
        (letter.act_nonzero primePositive inputNonzero)

theorem physicalWordAction_cons_sameLine (prime : Nat)
    (letter : PhysicalTemplate) (word : List PhysicalTemplate)
    {start middle finish : Vec2}
    (firstStep : SameLine (letter.act prime start) middle)
    (remainingRun : SameLine (physicalWordAction prime word middle) finish) :
    SameLine (physicalWordAction prime (letter :: word) start) finish := by
  exact (physicalWordAction_preserves_sameLine prime word firstStep).trans
    remainingRun

/-- Transport an endpoint equation across a canonicalized first step.
This is the converse-facing companion of `physicalWordAction_cons_sameLine`.
-/
theorem physicalWordAction_tail_sameLine (prime : Nat)
    (letter : PhysicalTemplate) (word : List PhysicalTemplate)
    {start next endpoint : Vec2}
    (firstStep : SameLine (letter.act prime start) next)
    (completeRun : SameLine
      (physicalWordAction prime (letter :: word) start) endpoint) :
    SameLine (physicalWordAction prime word next) endpoint := by
  have transported := physicalWordAction_preserves_sameLine prime word
    firstStep
  exact transported.symm.trans completeRun

theorem physicalWordAction_append_sameLine (prime : Nat)
    (first second : List PhysicalTemplate) {start middle finish : Vec2}
    (firstRun : SameLine (physicalWordAction prime first start) middle)
    (secondRun : SameLine (physicalWordAction prime second middle) finish) :
    SameLine (physicalWordAction prime (first ++ second) start) finish := by
  rw [physicalWordAction_append]
  exact (physicalWordAction_preserves_sameLine prime second firstRun).trans
    secondRun

/-- Locality of the start and every successive prefix state. -/
def AllStatesLocal (prime : Nat) : List PhysicalTemplate → Vec2 → Prop
  | [], vector => LocalAt prime vector
  | letter :: word, vector =>
      LocalAt prime vector ∧
        AllStatesLocal prime word (letter.act prime vector)

theorem AllStatesLocal.start {prime : Nat} {word : List PhysicalTemplate}
    {vector : Vec2} (allLocal : AllStatesLocal prime word vector) :
    LocalAt prime vector := by
  cases word with
  | nil => exact allLocal
  | cons => exact allLocal.1

/-- Locality of every prefix depends only on the initial projective
line.  The explicit nonzero hypothesis rules out the zero column as an
alternative representative. -/
theorem AllStatesLocal.of_sameLine {prime : Nat}
    (primePositive : 0 < prime) {word : List PhysicalTemplate}
    {source target : Vec2} (allLocal : AllStatesLocal prime word source)
    (targetNonzero : target.Nonzero) (same : SameLine target source) :
    AllStatesLocal prime word target := by
  induction word generalizing source target with
  | nil =>
      exact LocalAt.of_sameLine allLocal targetNonzero same
  | cons letter word inductionHypothesis =>
      have targetLocal := LocalAt.of_sameLine allLocal.1 targetNonzero same
      have nextSame := same.apply (IntMatrix2.cast (letter.matrix prime))
      have nextNonzero := letter.act_nonzero primePositive targetNonzero
      exact ⟨targetLocal,
        inductionHypothesis allLocal.2 nextNonzero nextSame⟩

theorem AllStatesLocal.take {prime : Nat} {word : List PhysicalTemplate}
    {vector : Vec2} (allLocal : AllStatesLocal prime word vector)
    (length : Nat) :
    AllStatesLocal prime (word.take length) vector := by
  induction length generalizing word vector with
  | zero => exact allLocal.start
  | succ length inductionHypothesis =>
      cases word with
      | nil => simpa [AllStatesLocal] using allLocal
      | cons letter word =>
          exact ⟨allLocal.1, inductionHypothesis allLocal.2⟩

/-- The suffix after any number of surviving letters is itself
surviving from the state reached by that prefix. -/
theorem AllStatesLocal.drop {prime : Nat} {word : List PhysicalTemplate}
    {vector : Vec2} (allLocal : AllStatesLocal prime word vector)
    (length : Nat) :
    AllStatesLocal prime (word.drop length)
      (physicalWordAction prime (word.take length) vector) := by
  induction length generalizing word vector with
  | zero => simpa [physicalWordAction] using allLocal
  | succ length inductionHypothesis =>
      cases word with
      | nil => simpa [physicalWordAction] using allLocal
      | cons letter word =>
          exact inductionHypothesis allLocal.2

/-- Concatenate two prefix-local runs at their common intermediate state. -/
theorem AllStatesLocal.append {prime : Nat}
    {first second : List PhysicalTemplate} {start : Vec2}
    (firstLocal : AllStatesLocal prime first start)
    (secondLocal : AllStatesLocal prime second
      (physicalWordAction prime first start)) :
    AllStatesLocal prime (first ++ second) start := by
  induction first generalizing start with
  | nil => simpa [physicalWordAction] using secondLocal
  | cons letter first inductionHypothesis =>
      exact ⟨firstLocal.1, inductionHypothesis firstLocal.2 secondLocal⟩

/-- If an unrestricted physical word has a local endpoint, no prefix
could have entered the error region. -/
theorem allStatesLocal_of_final_local {prime : Nat}
    (primePositive : 0 < prime) (word : List PhysicalTemplate)
    {vector : Vec2} (inputNonzero : vector.Nonzero)
    (finalLocal : LocalAt prime (physicalWordAction prime word vector)) :
    AllStatesLocal prime word vector := by
  induction word generalizing vector with
  | nil => exact finalLocal
  | cons letter word inductionHypothesis =>
      have nextNonzero := letter.act_nonzero primePositive inputNonzero
      have tailLocal := inductionHypothesis nextNonzero finalLocal
      have nextLocal := tailLocal.start
      exact ⟨letter.local_of_output_local primePositive inputNonzero nextLocal,
        tailLocal⟩

/-- An error remains an error through every arbitrary physical word. -/
theorem physicalWord_preserves_error {prime : Nat}
    (primePositive : 0 < prime) (word : List PhysicalTemplate)
    {vector : Vec2} (inputError : ErrorAt prime vector) :
    ErrorAt prime (physicalWordAction prime word vector) := by
  induction word generalizing vector with
  | nil => exact inputError
  | cons letter word inductionHypothesis =>
      exact inductionHypothesis (letter.preserves_error primePositive inputError)

/-- Lift an arbitrary matrix word over a physical alphabet back to
metadata-bearing physical templates. -/
theorem lift_matrix_word {prime : Nat} {alphabet : List PhysicalTemplate}
    {word : List IntMatrix2}
    (wordOver : WordOver (alphabet.map (PhysicalTemplate.matrix prime)) word) :
    ∃ templateWord : List PhysicalTemplate,
      WordOver alphabet templateWord ∧
      templateWord.map (PhysicalTemplate.matrix prime) = word :=
  wordOver_map_lift (PhysicalTemplate.matrix prime) wordOver

/-- Split a word over an appended alphabet at its first letter from the
right-hand alphabet.  If no such letter occurs, the entire word is over the
left-hand alphabet. -/
theorem wordOver_append_first_right
    {first second word : List PhysicalTemplate}
    (wordOver : WordOver (first ++ second) word) :
    WordOver first word ∨
      ∃ initial letter suffix,
        word = initial ++ letter :: suffix ∧
        WordOver first initial ∧
        letter ∈ second ∧
        WordOver (first ++ second) suffix := by
  induction word with
  | nil =>
      exact .inl (by intro letter letterMem; simp at letterMem)
  | cons head tail inductionHypothesis =>
      have headMem : head ∈ first ∨ head ∈ second := by
        simpa using wordOver head (by simp)
      have tailOver : WordOver (first ++ second) tail := by
        intro letter letterMem
        exact wordOver letter (by simp [letterMem])
      rcases headMem with headFirst | headSecond
      · rcases inductionHypothesis tailOver with tailFirst |
          ⟨initial, letter, suffix, tailEq, initialOver, letterSecond,
            suffixOver⟩
        · exact .inl (by
            intro letter letterMem
            simp at letterMem
            rcases letterMem with rfl | letterMem
            · exact headFirst
            · exact tailFirst letter letterMem)
        · exact .inr ⟨head :: initial, letter, suffix, by simp [tailEq],
            by
              intro candidate candidateMem
              simp at candidateMem
              rcases candidateMem with rfl | candidateMem
              · exact headFirst
              · exact initialOver candidate candidateMem,
            letterSecond, suffixOver⟩
      · exact .inr ⟨[], head, tail, by simp,
          by intro letter letterMem; simp at letterMem,
          headSecond, tailOver⟩

/-- Membership in a union alphabet is independent of the order in which its
two component lists are appended. -/
theorem WordOver.append_swap
    {first second word : List PhysicalTemplate}
    (wordOver : WordOver (first ++ second) word) :
    WordOver (second ++ first) word := by
  intro letter letterMem
  have membership := wordOver letter letterMem
  simp only [List.mem_append] at membership ⊢
  exact membership.symm

/-- Locality splits at an explicit prefix decomposition. -/
theorem AllStatesLocal.split_append_cons
    {prime : Nat} {word initial : List PhysicalTemplate}
    {letter : PhysicalTemplate} {suffix : List PhysicalTemplate}
    {start : Vec2}
    (wordEq : word = initial ++ letter :: suffix)
    (allLocal : AllStatesLocal prime word start) :
    AllStatesLocal prime initial start ∧
      AllStatesLocal prime (letter :: suffix)
        (physicalWordAction prime initial start) := by
  have initialLocal := allLocal.take initial.length
  have suffixLocal := allLocal.drop initial.length
  constructor
  · simpa [wordEq] using initialLocal
  · simpa [wordEq] using suffixLocal

end Mortality.Compiler
