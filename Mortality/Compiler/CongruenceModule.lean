import Mortality.Compiler.IncrementModule

/-!
# Read-only congruence-test modules

This file formalizes the phase cycle in Lemma 5.3.  The private phase
used after `deleted` zero digits is supplied by a function and indexed
modulo the positive test modulus.  Every physical letter has identity
mutations, so a successful execution rotates one full unary period and
returns the input code unchanged.
-/

namespace Mortality.Compiler.CongruenceModule

open Mortality.PeriodicCode
open Mortality.Compiler.IncrementModule

def identityLetter (source target : Nat) (digit : Int) : PhysicalTemplate :=
  { sourcePhase := source
    targetPhase := target
    digit := digit
    preCoefficient := 0
    postSign := .positive
    postCoefficient := 0 }

def entryZero (source modulus : Nat) (phase : Nat → Nat) :
    PhysicalTemplate :=
  identityLetter source (phase (1 % modulus)) 0

def loopZero (modulus index : Nat) (phase : Nat → Nat) :
    PhysicalTemplate :=
  identityLetter (phase index) (phase ((index + 1) % modulus)) 0

def exitMarker (target index : Nat) (phase : Nat → Nat) :
    PhysicalTemplate :=
  identityLetter (phase index) target 1

def directMarker (source target : Nat) : PhysicalTemplate :=
  identityLetter source target 1

/-- The displayed finite table: one entry, one zero edge per residue,
one marker exit per allowed residue, and the optional zero-input exit. -/
def congruenceAlphabet (source target modulus : Nat)
    (phase : Nat → Nat) (allowed : List Nat) : List PhysicalTemplate :=
  entryZero source modulus phase ::
    (List.range modulus).map (fun index => loopZero modulus index phase) ++
    allowed.map (fun index => exitMarker target index phase) ++
    if 0 ∈ allowed then [directMarker source target] else []

@[simp] theorem congruenceAlphabet_length (source target modulus : Nat)
    (phase : Nat → Nat) (allowed : List Nat) :
    (congruenceAlphabet source target modulus phase allowed).length =
      1 + modulus + allowed.length + if 0 ∈ allowed then 1 else 0 := by
  by_cases zeroAllowed : 0 ∈ allowed <;>
    simp [congruenceAlphabet, zeroAllowed] <;> omega

theorem modTwoAlphabet_length (source target : Nat) (phase : Nat → Nat) :
    (congruenceAlphabet source target 2 phase [0]).length = 5 := by
  rw [congruenceAlphabet_length]
  decide

theorem modThreeAlphabet_length (source target : Nat) (phase : Nat → Nat) :
    (congruenceAlphabet source target 3 phase [0, 1]).length = 7 := by
  rw [congruenceAlphabet_length]
  decide

/-- The periodic digit word after `deleted` of the `counter` leading
zeros have been rotated to the rear. -/
def scanStateDigits (counter deleted : Nat) : List Int :=
  List.replicate (counter - deleted) 0 ++ [1] ++
    List.replicate deleted 0

theorem scanStateDigits_zero (counter : Nat) :
    scanStateDigits counter 0 = unaryDigits counter := by
  simp [scanStateDigits, unaryDigits]

theorem scanStateDigits_before_marker {counter deleted : Nat}
    (deletedBelow : deleted < counter) :
    scanStateDigits counter deleted =
      0 :: (List.replicate (counter - (deleted + 1)) 0 ++ [1] ++
        List.replicate deleted 0) := by
  rw [scanStateDigits]
  have exponentEq : counter - deleted =
      (counter - (deleted + 1)) + 1 := by omega
  rw [exponentEq, List.replicate_succ]
  simp

@[simp] theorem replicate_zero_snoc (length : Nat) :
    List.replicate length (0 : Int) ++ [0] =
      List.replicate (length + 1) 0 := by
  induction length with
  | zero => simp
  | succ length inductionHypothesis =>
      simp [List.replicate_succ, inductionHypothesis]

theorem scanStateDigits_rotate_zero {counter deleted : Nat} :
    let remaining :=
      List.replicate (counter - (deleted + 1)) 0 ++ [1] ++
        List.replicate deleted 0
    remaining ++ [0] = scanStateDigits counter (deleted + 1) := by
  dsimp
  simp [scanStateDigits, List.append_assoc]

theorem scanStateDigits_at_marker (counter : Nat) :
    scanStateDigits counter counter = 1 :: List.replicate counter 0 := by
  simp [scanStateDigits]

theorem scanStateDigits_rotate_marker (counter : Nat) :
    List.replicate counter 0 ++ [1] = unaryDigits counter := by
  rfl

theorem phaseScanState_local (base phase counter deleted : Nat)
    (baseAtLeastTwo : 2 ≤ base) :
    LocalAt base
      (phaseAffine phase
        (periodicCode (base : Rat) (scanStateDigits counter deleted))) := by
  rw [show phaseAffine phase
        (periodicCode (base : Rat) (scanStateDigits counter deleted)) =
      Matrix2.apply (IntMatrix2.cast (chart phase))
        (Vec2.affine
          (periodicCode (base : Rat) (scanStateDigits counter deleted))) by
    simpa [phaseAffine] using
      (chart_apply phase
        (periodicCode (base : Rat) (scanStateDigits counter deleted))).symm]
  apply (local_chart_iff base phase _).mpr
  apply periodicCode_local_affine base _ baseAtLeastTwo
  simp [scanStateDigits]

/-- Before the unary marker, a congruence scan occupies digit zero in its
current residue-cycle phase.  This guarded form lets the fixed compiler
exclude letters owned by other instruction occurrences. -/
theorem scanState_inPhaseAt_before
    {base phase counter deleted : Nat} (baseAtLeastTwo : 2 ≤ base)
    (deletedBelow : deleted < counter) :
    InPhaseAt base phase 0
      (phaseAffine phase
        (periodicCode (base : Rat) (scanStateDigits counter deleted))) := by
  rw [scanStateDigits_before_marker deletedBelow]
  exact periodicCode_inPhaseAt base phase 0 _ baseAtLeastTwo
    (by simp [ReservedDigit])

/-- At the unary marker, a congruence scan occupies digit one in its current
residue-cycle phase. -/
theorem scanState_inPhaseAt_marker
    {base phase counter : Nat} (baseAtLeastTwo : 2 ≤ base) :
    InPhaseAt base phase 1
      (phaseAffine phase
        (periodicCode (base : Rat) (scanStateDigits counter counter))) := by
  rw [scanStateDigits_at_marker]
  exact periodicCode_inPhaseAt base phase 1 _ baseAtLeastTwo
    (by simp [ReservedDigit])

def scanTail (target modulus deleted remaining : Nat)
    (phase : Nat → Nat) : List PhysicalTemplate :=
  match remaining with
  | 0 => [exitMarker target (deleted % modulus) phase]
  | remaining + 1 =>
      loopZero modulus (deleted % modulus) phase ::
        scanTail target modulus (deleted + 1) remaining phase

def congruenceWord (source target modulus counter : Nat)
    (phase : Nat → Nat) : List PhysicalTemplate :=
  if counter = 0 then [directMarker source target]
  else entryZero source modulus phase ::
    scanTail target modulus 1 (counter - 1) phase

@[simp] theorem scanTail_length (target modulus deleted remaining : Nat)
    (phase : Nat → Nat) :
    (scanTail target modulus deleted remaining phase).length =
      remaining + 1 := by
  induction remaining generalizing deleted with
  | zero => simp [scanTail]
  | succ remaining inductionHypothesis =>
      simp [scanTail, inductionHypothesis]

@[simp] theorem congruenceWord_length (source target modulus counter : Nat)
    (phase : Nat → Nat) :
    (congruenceWord source target modulus counter phase).length =
      counter + 1 := by
  by_cases counterZero : counter = 0
  · subst counter
    simp [congruenceWord]
  · simp [congruenceWord, counterZero]
    omega

theorem entryZero_mem (source target modulus : Nat) (phase : Nat → Nat)
    (allowed : List Nat) :
    entryZero source modulus phase ∈
      congruenceAlphabet source target modulus phase allowed := by
  simp [congruenceAlphabet]

theorem loopZero_mem {source target modulus index : Nat}
    (phase : Nat → Nat) (allowed : List Nat) (indexBound : index < modulus) :
    loopZero modulus index phase ∈
      congruenceAlphabet source target modulus phase allowed := by
  simp [congruenceAlphabet]
  exact Or.inr (Or.inl ⟨index, indexBound, rfl⟩)

theorem exitMarker_mem {source target modulus index : Nat}
    (phase : Nat → Nat) {allowed : List Nat}
    (allowedMem : index ∈ allowed) :
    exitMarker target index phase ∈
      congruenceAlphabet source target modulus phase allowed := by
  simp [congruenceAlphabet]
  exact Or.inr (Or.inr (Or.inl ⟨index, allowedMem, rfl⟩))

theorem directMarker_mem {source target modulus : Nat} (phase : Nat → Nat)
    {allowed : List Nat} (zeroAllowed : 0 ∈ allowed) :
    directMarker source target ∈
      congruenceAlphabet source target modulus phase allowed := by
  simp [congruenceAlphabet, zeroAllowed]

theorem scanTail_wordOver
    {source target modulus deleted remaining : Nat} (phase : Nat → Nat)
    {allowed : List Nat} (modulusPositive : 0 < modulus)
    (allowedResidue : (deleted + remaining) % modulus ∈ allowed) :
    WordOver (congruenceAlphabet source target modulus phase allowed)
      (scanTail target modulus deleted remaining phase) := by
  induction remaining generalizing deleted with
  | zero =>
      apply wordOver_cons
      · apply exitMarker_mem
        simpa using allowedResidue
      · exact wordOver_nil _
  | succ remaining inductionHypothesis =>
      apply wordOver_cons
      · apply loopZero_mem
        exact Nat.mod_lt _ modulusPositive
      · apply inductionHypothesis
        simpa only [show deleted + (remaining + 1) =
          deleted + 1 + remaining by omega] using allowedResidue

/-- The intended complete word belongs to the finite module alphabet
whenever the tested residue is allowed. -/
theorem congruenceWord_wordOver
    {source target modulus counter : Nat} (phase : Nat → Nat)
    {allowed : List Nat} (modulusPositive : 0 < modulus)
    (allowedResidue : counter % modulus ∈ allowed) :
    WordOver (congruenceAlphabet source target modulus phase allowed)
      (congruenceWord source target modulus counter phase) := by
  by_cases counterZero : counter = 0
  · subst counter
    apply wordOver_cons
    · apply directMarker_mem
      simpa using allowedResidue
    · exact wordOver_nil _
  · simp only [congruenceWord, counterZero, ite_false]
    apply wordOver_cons
    · exact entryZero_mem source target modulus phase allowed
    · apply scanTail_wordOver phase modulusPositive
      simpa only [show 1 + (counter - 1) = counter by omega] using
        allowedResidue

theorem zeroRotationStep
    (base modulus counter deleted : Nat) (phase : Nat → Nat)
    (baseAtLeastTwo : 2 ≤ base)
    (deletedBelow : deleted < counter) :
    SameLine
      ((loopZero modulus (deleted % modulus) phase).act base
        (phaseAffine (phase (deleted % modulus))
          (periodicCode (base : Rat) (scanStateDigits counter deleted))))
      (phaseAffine (phase ((deleted + 1) % modulus))
        (periodicCode (base : Rat)
          (scanStateDigits counter (deleted + 1)))) := by
  have sourceDigits := scanStateDigits_before_marker deletedBelow
  rw [sourceDigits]
  have rotation := physicalLetter_rotates_periodicCode base
    (phase (deleted % modulus)) (phase ((deleted + 1) % modulus)) 0
    (List.replicate (counter - (deleted + 1)) 0 ++ [1] ++
      List.replicate deleted 0) baseAtLeastTwo
  have phaseIndex : ((deleted % modulus + 1) % modulus) =
      (deleted + 1) % modulus := by
    exact Nat.mod_add_mod deleted modulus 1
  have rotatedDigits := scanStateDigits_rotate_zero
    (counter := counter) (deleted := deleted)
  rw [← rotatedDigits]
  simpa [loopZero, identityLetter, PhysicalTemplate.act,
    PhysicalTemplate.matrix, phaseAffine, phaseIndex] using rotation

theorem markerExitStep
    (base target modulus counter : Nat) (phase : Nat → Nat)
    (baseAtLeastTwo : 2 ≤ base) :
    SameLine
      ((exitMarker target (counter % modulus) phase).act base
        (phaseAffine (phase (counter % modulus))
          (periodicCode (base : Rat) (scanStateDigits counter counter))))
      (phaseAffine target (unaryCode base counter)) := by
  rw [scanStateDigits_at_marker]
  have rotation := physicalLetter_rotates_periodicCode base
    (phase (counter % modulus)) target 1 (List.replicate counter 0)
    baseAtLeastTwo
  simpa [exitMarker, identityLetter, PhysicalTemplate.act,
    PhysicalTemplate.matrix, phaseAffine, unaryCode, unaryDigits] using rotation

theorem directMarkerStep (base source target : Nat)
    (baseAtLeastTwo : 2 ≤ base) :
    SameLine
      ((directMarker source target).act base
        (phaseAffine source (unaryCode base 0)))
      (phaseAffine target (unaryCode base 0)) := by
  have rotation := physicalLetter_rotates_periodicCode base source target
    1 [] baseAtLeastTwo
  simpa [directMarker, identityLetter, PhysicalTemplate.act,
    PhysicalTemplate.matrix, phaseAffine, unaryCode, unaryDigits] using rotation

theorem entryZeroStep
    (base source modulus counter : Nat) (phase : Nat → Nat)
    (baseAtLeastTwo : 2 ≤ base)
    (counterPositive : 0 < counter) :
    SameLine
      ((entryZero source modulus phase).act base
        (phaseAffine source (unaryCode base counter)))
      (phaseAffine (phase (1 % modulus))
        (periodicCode (base : Rat) (scanStateDigits counter 1))) := by
  have sourceDigits := scanStateDigits_before_marker
    (counter := counter) (deleted := 0) counterPositive
  unfold unaryCode
  rw [← scanStateDigits_zero counter, sourceDigits]
  have rotation := physicalLetter_rotates_periodicCode base source
    (phase (1 % modulus)) 0
    (List.replicate (counter - 1) 0 ++ [1]) baseAtLeastTwo
  have rotatedDigits :
      (List.replicate (counter - 1) 0 ++ [1]) ++ [0] =
        scanStateDigits counter 1 := by
    simpa using scanStateDigits_rotate_zero
      (counter := counter) (deleted := 0)
  simpa [entryZero, identityLetter, PhysicalTemplate.act,
    PhysicalTemplate.matrix, phaseAffine, unaryCode, rotatedDigits] using rotation

theorem scanTail_correct
    (base target modulus deleted remaining : Nat) (phase : Nat → Nat)
    (baseAtLeastTwo : 2 ≤ base) :
    SameLine
      (physicalWordAction base
        (scanTail target modulus deleted remaining phase)
        (phaseAffine (phase (deleted % modulus))
          (periodicCode (base : Rat)
            (scanStateDigits (deleted + remaining) deleted))))
      (phaseAffine target (unaryCode base (deleted + remaining))) := by
  induction remaining generalizing deleted with
  | zero =>
      simpa [scanTail, physicalWordAction] using
        markerExitStep base target modulus deleted phase baseAtLeastTwo
  | succ remaining inductionHypothesis =>
      have firstStep := zeroRotationStep base modulus
        (deleted + (remaining + 1)) deleted phase baseAtLeastTwo
        (by omega)
      have tailRun := inductionHypothesis (deleted := deleted + 1)
      have tailRun' :
          SameLine
            (physicalWordAction base
              (scanTail target modulus (deleted + 1) remaining phase)
              (phaseAffine (phase ((deleted + 1) % modulus))
                (periodicCode (base : Rat)
                  (scanStateDigits (deleted + (remaining + 1))
                    (deleted + 1)))))
            (phaseAffine target
              (unaryCode base (deleted + (remaining + 1)))) := by
        simpa only [show deleted + 1 + remaining =
          deleted + (remaining + 1) by omega] using tailRun
      exact physicalWordAction_cons_sameLine base
        (loopZero modulus (deleted % modulus) phase)
        (scanTail target modulus (deleted + 1) remaining phase)
        firstStep tailRun'

/-- A complete congruence scan preserves the unary code.  The membership
hypothesis is exactly the condition under which the final marker edge is
present in the finite module alphabet. -/
theorem congruenceWord_correct
    (base source target modulus counter : Nat) (phase : Nat → Nat)
    (baseAtLeastTwo : 2 ≤ base) :
    SameLine
      (physicalWordAction base
        (congruenceWord source target modulus counter phase)
        (phaseAffine source (unaryCode base counter)))
      (phaseAffine target (unaryCode base counter)) := by
  by_cases counterZero : counter = 0
  · subst counter
    simpa [congruenceWord, physicalWordAction] using
      directMarkerStep base source target baseAtLeastTwo
  · have counterPositive : 0 < counter := by omega
    have firstStep := entryZeroStep base source modulus counter phase
      baseAtLeastTwo counterPositive
    have tailRun := scanTail_correct base target modulus 1
      (counter - 1) phase baseAtLeastTwo
    have tailRun' :
        SameLine
          (physicalWordAction base
            (scanTail target modulus 1 (counter - 1) phase)
            (phaseAffine (phase (1 % modulus))
              (periodicCode (base : Rat) (scanStateDigits counter 1))))
          (phaseAffine target (unaryCode base counter)) := by
      simpa only [show 1 + (counter - 1) = counter by omega] using tailRun
    have combined := physicalWordAction_cons_sameLine base
      (entryZero source modulus phase)
      (scanTail target modulus 1 (counter - 1) phase)
      firstStep tailRun'
    simpa [congruenceWord, counterZero] using combined

/-- Forward local module obligation, including word membership, exact
length, exact output, and locality of every intermediate state. -/
theorem congruence_execution
    {base source target modulus counter : Nat} (phase : Nat → Nat)
    {allowed : List Nat} (baseAtLeastTwo : 2 ≤ base)
    (modulusPositive : 0 < modulus)
    (allowedResidue : counter % modulus ∈ allowed) :
    let word := congruenceWord source target modulus counter phase
    WordOver (congruenceAlphabet source target modulus phase allowed) word ∧
      word.length = counter + 1 ∧
      SameLine
        (physicalWordAction base word
          (phaseAffine source (unaryCode base counter)))
        (phaseAffine target (unaryCode base counter)) ∧
      AllStatesLocal base word
        (phaseAffine source (unaryCode base counter)) := by
  dsimp
  have wordOver := congruenceWord_wordOver
    (source := source) (target := target) phase modulusPositive allowedResidue
  have action := congruenceWord_correct base source target modulus counter
    phase baseAtLeastTwo
  have inputNonzero :
      (phaseAffine source (unaryCode base counter)).Nonzero :=
    Vec2.affine_nonzero _
  have outputNonzero := physicalWordAction_nonzero (prime := base) (by omega)
    (congruenceWord source target modulus counter phase) inputNonzero
  have finalLocal := LocalAt.of_sameLine
    (phaseUnaryCode_local base target counter baseAtLeastTwo)
    outputNonzero action
  exact ⟨wordOver, congruenceWord_length source target modulus counter phase,
    action, allStatesLocal_of_final_local (by omega) _ inputNonzero finalLocal⟩

private theorem congruenceLetter_source_bound
    {phaseCount source target modulus : Nat} {phase : Nat → Nat}
    {allowed : List Nat} {letter : PhysicalTemplate}
    (sourceBound : source < phaseCount)
    (phaseBound : ∀ index, index < modulus → phase index < phaseCount)
    (allowedBound : ∀ index ∈ allowed, index < modulus)
    (letterMem : letter ∈
      congruenceAlphabet source target modulus phase allowed) :
    letter.sourcePhase < phaseCount := by
  simp [congruenceAlphabet] at letterMem
  rcases letterMem with rfl | ⟨index, indexBound, rfl⟩ |
      ⟨index, indexMem, rfl⟩ | ⟨_, rfl⟩
  · simpa [entryZero, identityLetter] using sourceBound
  · simpa [loopZero, identityLetter] using phaseBound index indexBound
  · simpa [exitMarker, identityLetter] using
      phaseBound index (allowedBound index indexMem)
  · simpa [directMarker, identityLetter] using sourceBound

private theorem congruenceLetter_reserved
    {source target modulus : Nat} {phase : Nat → Nat}
    {allowed : List Nat} {letter : PhysicalTemplate}
    (letterMem : letter ∈
      congruenceAlphabet source target modulus phase allowed) :
    ReservedDigit letter.digit := by
  simp [congruenceAlphabet] at letterMem
  rcases letterMem with rfl | ⟨index, _, rfl⟩ |
      ⟨index, _, rfl⟩ | ⟨_, rfl⟩ <;>
    simp [entryZero, loopZero, exitMarker, directMarker, identityLetter,
      ReservedDigit]

/-- At a positive input, the unique surviving entry is the zero edge
into the private residue cycle. -/
theorem source_letter_positive
    {prime phaseCount source target modulus counter : Nat}
    {phase : Nat → Nat} {allowed : List Nat}
    (primeProperty : IsPrime prime)
    (primeBound : 6 * phaseCount < prime)
    (sourceBound : source < phaseCount)
    (phaseBound : ∀ index, index < modulus → phase index < phaseCount)
    (allowedBound : ∀ index ∈ allowed, index < modulus)
    (sourcePrivateDistinct :
      ∀ index, index < modulus → source ≠ phase index)
    {letter : PhysicalTemplate}
    (letterMem : letter ∈
      congruenceAlphabet source target modulus phase allowed)
    (outputLocal : LocalAt prime
      (letter.act prime
        (phaseAffine source (unaryCode prime (counter + 1))))) :
    letter = entryZero source modulus phase := by
  have digitsEq : unaryDigits (counter + 1) = 0 :: unaryDigits counter := by
    simp [unaryDigits, List.replicate_succ]
  have forced := physicalLetter_periodic_affine_source_digit_unique
    (prime := prime) (phaseCount := phaseCount)
    (actualPhase := source) (sourcePhase := letter.sourcePhase)
    (targetPhase := letter.targetPhase) (actualDigit := 0)
    (letterDigit := letter.digit)
    (preCoefficient := letter.preCoefficient)
    (postCoefficient := letter.postCoefficient)
    (postSign := letter.postSign) (unaryDigits counter) primeProperty
    primeBound sourceBound
    (congruenceLetter_source_bound sourceBound phaseBound allowedBound letterMem)
    (by simp [ReservedDigit]) (congruenceLetter_reserved letterMem)
    (by simpa [PhysicalTemplate.act, PhysicalTemplate.matrix, phaseAffine,
      unaryCode, digitsEq] using outputLocal)
  simp [congruenceAlphabet] at letterMem
  rcases letterMem with rfl | ⟨index, indexBound, rfl⟩ |
      ⟨index, indexMem, rfl⟩ | ⟨_, rfl⟩
  · rfl
  · exact False.elim
      (sourcePrivateDistinct index indexBound forced.1)
  · exact False.elim
      (sourcePrivateDistinct index (allowedBound index indexMem) forced.1)
  · simp [directMarker, identityLetter] at forced

/-- At `z_0`, the only surviving entry is the optional direct marker
edge.  Its membership therefore also certifies that residue zero is
allowed. -/
theorem source_letter_zero
    {prime phaseCount source target modulus : Nat}
    {phase : Nat → Nat} {allowed : List Nat}
    (primeProperty : IsPrime prime)
    (primeBound : 6 * phaseCount < prime)
    (sourceBound : source < phaseCount)
    (phaseBound : ∀ index, index < modulus → phase index < phaseCount)
    (allowedBound : ∀ index ∈ allowed, index < modulus)
    (sourcePrivateDistinct :
      ∀ index, index < modulus → source ≠ phase index)
    {letter : PhysicalTemplate}
    (letterMem : letter ∈
      congruenceAlphabet source target modulus phase allowed)
    (outputLocal : LocalAt prime
      (letter.act prime (phaseAffine source (unaryCode prime 0)))) :
    0 ∈ allowed ∧ letter = directMarker source target := by
  have forced := physicalLetter_periodic_affine_source_digit_unique
    (prime := prime) (phaseCount := phaseCount)
    (actualPhase := source) (sourcePhase := letter.sourcePhase)
    (targetPhase := letter.targetPhase) (actualDigit := 1)
    (letterDigit := letter.digit)
    (preCoefficient := letter.preCoefficient)
    (postCoefficient := letter.postCoefficient)
    (postSign := letter.postSign) [] primeProperty primeBound sourceBound
    (congruenceLetter_source_bound sourceBound phaseBound allowedBound letterMem)
    (by simp [ReservedDigit]) (congruenceLetter_reserved letterMem)
    (by simpa [PhysicalTemplate.act, PhysicalTemplate.matrix, phaseAffine,
      unaryCode, unaryDigits] using outputLocal)
  simp [congruenceAlphabet] at letterMem
  rcases letterMem with rfl | ⟨index, indexBound, rfl⟩ |
      ⟨index, indexMem, rfl⟩ | ⟨zeroAllowed, rfl⟩
  · simp [entryZero, identityLetter] at forced
  · exact False.elim
      (sourcePrivateDistinct index indexBound forced.1)
  · exact False.elim
      (sourcePrivateDistinct index (allowedBound index indexMem) forced.1)
  · exact ⟨zeroAllowed, rfl⟩

/-- Before the marker, a surviving private-phase letter is the unique
zero edge of the residue cycle. -/
theorem private_letter_before_marker
    {prime phaseCount source target modulus counter deleted : Nat}
    {phase : Nat → Nat} {allowed : List Nat}
    (primeProperty : IsPrime prime)
    (primeBound : 6 * phaseCount < prime)
    (modulusPositive : 0 < modulus)
    (sourceBound : source < phaseCount)
    (phaseBound : ∀ index, index < modulus → phase index < phaseCount)
    (allowedBound : ∀ index ∈ allowed, index < modulus)
    (sourcePrivateDistinct :
      ∀ index, index < modulus → source ≠ phase index)
    (phaseInjective : ∀ {first second}, first < modulus → second < modulus →
      phase first = phase second → first = second)
    (deletedBelow : deleted < counter)
    {letter : PhysicalTemplate}
    (letterMem : letter ∈
      congruenceAlphabet source target modulus phase allowed)
    (outputLocal : LocalAt prime
      (letter.act prime
        (phaseAffine (phase (deleted % modulus))
          (periodicCode (prime : Rat)
            (scanStateDigits counter deleted))))) :
    letter = loopZero modulus (deleted % modulus) phase := by
  rw [scanStateDigits_before_marker deletedBelow] at outputLocal
  have actualBound := Nat.mod_lt deleted modulusPositive
  have forced := physicalLetter_periodic_affine_source_digit_unique
    (prime := prime) (phaseCount := phaseCount)
    (actualPhase := phase (deleted % modulus))
    (sourcePhase := letter.sourcePhase) (targetPhase := letter.targetPhase)
    (actualDigit := 0) (letterDigit := letter.digit)
    (preCoefficient := letter.preCoefficient)
    (postCoefficient := letter.postCoefficient)
    (postSign := letter.postSign)
    (List.replicate (counter - (deleted + 1)) 0 ++ [1] ++
      List.replicate deleted 0) primeProperty primeBound
    (phaseBound _ actualBound)
    (congruenceLetter_source_bound sourceBound phaseBound allowedBound letterMem)
    (by simp [ReservedDigit]) (congruenceLetter_reserved letterMem)
    (by simpa [PhysicalTemplate.act, PhysicalTemplate.matrix, phaseAffine]
      using outputLocal)
  simp [congruenceAlphabet] at letterMem
  rcases letterMem with rfl | ⟨index, indexBound, rfl⟩ |
      ⟨index, indexMem, rfl⟩ | ⟨_, rfl⟩
  · exact False.elim
      (sourcePrivateDistinct _ actualBound forced.1.symm)
  · have indexEq := phaseInjective actualBound indexBound forced.1
    subst index
    rfl
  · simp [exitMarker, identityLetter] at forced
  · exact False.elim
      (sourcePrivateDistinct _ actualBound forced.1.symm)

/-- At the marker, a surviving private-phase letter exists exactly when
the current residue is allowed, and it is that residue's unique exit. -/
theorem private_letter_at_marker
    {prime phaseCount source target modulus counter : Nat}
    {phase : Nat → Nat} {allowed : List Nat}
    (primeProperty : IsPrime prime)
    (primeBound : 6 * phaseCount < prime)
    (modulusPositive : 0 < modulus)
    (sourceBound : source < phaseCount)
    (phaseBound : ∀ index, index < modulus → phase index < phaseCount)
    (allowedBound : ∀ index ∈ allowed, index < modulus)
    (sourcePrivateDistinct :
      ∀ index, index < modulus → source ≠ phase index)
    (phaseInjective : ∀ {first second}, first < modulus → second < modulus →
      phase first = phase second → first = second)
    {letter : PhysicalTemplate}
    (letterMem : letter ∈
      congruenceAlphabet source target modulus phase allowed)
    (outputLocal : LocalAt prime
      (letter.act prime
        (phaseAffine (phase (counter % modulus))
          (periodicCode (prime : Rat)
            (scanStateDigits counter counter))))) :
    counter % modulus ∈ allowed ∧
      letter = exitMarker target (counter % modulus) phase := by
  rw [scanStateDigits_at_marker] at outputLocal
  have actualBound := Nat.mod_lt counter modulusPositive
  have forced := physicalLetter_periodic_affine_source_digit_unique
    (prime := prime) (phaseCount := phaseCount)
    (actualPhase := phase (counter % modulus))
    (sourcePhase := letter.sourcePhase) (targetPhase := letter.targetPhase)
    (actualDigit := 1) (letterDigit := letter.digit)
    (preCoefficient := letter.preCoefficient)
    (postCoefficient := letter.postCoefficient)
    (postSign := letter.postSign) (List.replicate counter 0)
    primeProperty primeBound (phaseBound _ actualBound)
    (congruenceLetter_source_bound sourceBound phaseBound allowedBound letterMem)
    (by simp [ReservedDigit]) (congruenceLetter_reserved letterMem)
    (by simpa [PhysicalTemplate.act, PhysicalTemplate.matrix, phaseAffine]
      using outputLocal)
  simp [congruenceAlphabet] at letterMem
  rcases letterMem with rfl | ⟨index, indexBound, rfl⟩ |
      ⟨index, indexMem, rfl⟩ | ⟨_, rfl⟩
  · simp [entryZero, identityLetter] at forced
  · simp [loopZero, identityLetter] at forced
  · have indexEq := phaseInjective actualBound
      (allowedBound index indexMem) forced.1
    subst index
    exact ⟨indexMem, rfl⟩
  · exact False.elim
      (sourcePrivateDistinct _ actualBound forced.1.symm)

/-- A surviving private-phase word of the remaining scan length is
unique.  Its existence also proves that the final counter residue is in
the allowed set. -/
theorem scanTail_surviving_unique
    {prime phaseCount source target modulus deleted remaining : Nat}
    {phase : Nat → Nat} {allowed : List Nat}
    (primeProperty : IsPrime prime)
    (primeBound : 6 * phaseCount < prime)
    (modulusPositive : 0 < modulus)
    (sourceBound : source < phaseCount)
    (phaseBound : ∀ index, index < modulus → phase index < phaseCount)
    (allowedBound : ∀ index ∈ allowed, index < modulus)
    (sourcePrivateDistinct :
      ∀ index, index < modulus → source ≠ phase index)
    (phaseInjective : ∀ {first second}, first < modulus → second < modulus →
      phase first = phase second → first = second)
    {word : List PhysicalTemplate}
    (wordOver : WordOver
      (congruenceAlphabet source target modulus phase allowed) word)
    (allLocal : AllStatesLocal prime word
      (phaseAffine (phase (deleted % modulus))
        (periodicCode (prime : Rat)
          (scanStateDigits (deleted + remaining) deleted))))
    (lengthEq : word.length = remaining + 1) :
    (deleted + remaining) % modulus ∈ allowed ∧
      word = scanTail target modulus deleted remaining phase := by
  induction remaining generalizing deleted word with
  | zero =>
      cases word with
      | nil => simp at lengthEq
      | cons letter tail =>
          have tailEmpty : tail = [] := by
            apply List.eq_nil_of_length_eq_zero
            simpa using lengthEq
          subst tail
          have letterMem := wordOver letter (by simp)
          have classified := private_letter_at_marker
            (counter := deleted) primeProperty primeBound modulusPositive
            sourceBound phaseBound allowedBound sourcePrivateDistinct
            phaseInjective letterMem (by exact allLocal.2)
          rcases classified with ⟨residueAllowed, letterEq⟩
          subst letter
          exact ⟨by simpa using residueAllowed, by simp [scanTail]⟩
  | succ remaining inductionHypothesis =>
      cases word with
      | nil => simp at lengthEq
      | cons letter tail =>
          have letterMem := wordOver letter (by simp)
          have tailOver : WordOver
              (congruenceAlphabet source target modulus phase allowed) tail := by
            intro candidate candidateMem
            exact wordOver candidate (by simp [candidateMem])
          have tailLength : tail.length = remaining + 1 := by
            simpa using lengthEq
          have letterEq := private_letter_before_marker
            (counter := deleted + (remaining + 1)) (deleted := deleted)
            primeProperty primeBound modulusPositive sourceBound phaseBound
            allowedBound sourcePrivateDistinct phaseInjective (by omega)
            letterMem allLocal.2.start
          subst letter
          have firstStep := zeroRotationStep prime modulus
            (deleted + (remaining + 1)) deleted phase primeProperty.1
            (by omega)
          have canonicalLocal := phaseScanState_local prime
            (phase ((deleted + 1) % modulus))
            ((deleted + 1) + remaining) (deleted + 1) primeProperty.1
          have canonicalAll : AllStatesLocal prime tail
              (phaseAffine (phase ((deleted + 1) % modulus))
                (periodicCode (prime : Rat)
                  (scanStateDigits ((deleted + 1) + remaining)
                    (deleted + 1)))) := by
            apply AllStatesLocal.of_sameLine
              (primePositive := by have := primeProperty.1; omega)
              allLocal.2 canonicalLocal.1
            simpa only [show deleted + (remaining + 1) =
              (deleted + 1) + remaining by omega] using firstStep.symm
          have tailClassified := inductionHypothesis tailOver canonicalAll
            tailLength
          rcases tailClassified with ⟨residueAllowed, tailEq⟩
          rw [tailEq]
          exact ⟨by simpa only [show deleted + (remaining + 1) =
              deleted + 1 + remaining by omega] using residueAllowed,
            by simp [scanTail]⟩

/-- Exact-length converse for the full congruence module.  A surviving
word exists only on an allowed residue and is literally the prescribed
full-period scan. -/
theorem congruenceWord_surviving_unique
    {prime phaseCount source target modulus counter : Nat}
    {phase : Nat → Nat} {allowed : List Nat}
    (primeProperty : IsPrime prime)
    (primeBound : 6 * phaseCount < prime)
    (modulusPositive : 0 < modulus)
    (sourceBound : source < phaseCount)
    (phaseBound : ∀ index, index < modulus → phase index < phaseCount)
    (allowedBound : ∀ index ∈ allowed, index < modulus)
    (sourcePrivateDistinct :
      ∀ index, index < modulus → source ≠ phase index)
    (phaseInjective : ∀ {first second}, first < modulus → second < modulus →
      phase first = phase second → first = second)
    {word : List PhysicalTemplate}
    (wordOver : WordOver
      (congruenceAlphabet source target modulus phase allowed) word)
    (allLocal : AllStatesLocal prime word
      (phaseAffine source (unaryCode prime counter)))
    (lengthEq : word.length = counter + 1) :
    counter % modulus ∈ allowed ∧
      word = congruenceWord source target modulus counter phase := by
  cases counter with
  | zero =>
      cases word with
      | nil => simp at lengthEq
      | cons letter tail =>
          have tailEmpty : tail = [] := by
            apply List.eq_nil_of_length_eq_zero
            simpa using lengthEq
          subst tail
          have letterMem := wordOver letter (by simp)
          have classified := source_letter_zero primeProperty primeBound
            sourceBound phaseBound allowedBound sourcePrivateDistinct
            letterMem (by exact allLocal.2)
          rcases classified with ⟨zeroAllowed, letterEq⟩
          subst letter
          exact ⟨by simpa using zeroAllowed, by simp [congruenceWord]⟩
  | succ previous =>
      cases word with
      | nil => simp at lengthEq
      | cons letter tail =>
          have letterMem := wordOver letter (by simp)
          have tailOver : WordOver
              (congruenceAlphabet source target modulus phase allowed) tail := by
            intro candidate candidateMem
            exact wordOver candidate (by simp [candidateMem])
          have tailLength : tail.length = previous + 1 := by
            simpa using lengthEq
          have letterEq := source_letter_positive
            (counter := previous) primeProperty primeBound sourceBound
            phaseBound allowedBound sourcePrivateDistinct letterMem
            allLocal.2.start
          subst letter
          have firstStep := entryZeroStep prime source modulus
            (previous + 1) phase primeProperty.1 (by omega)
          have canonicalLocal := phaseScanState_local prime
            (phase (1 % modulus)) (1 + previous) 1 primeProperty.1
          have canonicalAll : AllStatesLocal prime tail
              (phaseAffine (phase (1 % modulus))
                (periodicCode (prime : Rat)
                  (scanStateDigits (1 + previous) 1))) := by
            apply AllStatesLocal.of_sameLine
              (primePositive := by have := primeProperty.1; omega)
              allLocal.2 canonicalLocal.1
            simpa only [show previous + 1 = 1 + previous by omega]
              using firstStep.symm
          have tailClassified := scanTail_surviving_unique
            (deleted := 1) (remaining := previous) primeProperty primeBound
            modulusPositive sourceBound phaseBound allowedBound
            sourcePrivateDistinct phaseInjective tailOver canonicalAll
            tailLength
          rcases tailClassified with ⟨residueAllowed, tailEq⟩
          rw [tailEq]
          exact ⟨by simpa only [show previous + 1 = 1 + previous by omega]
              using residueAllowed,
            by simp [congruenceWord]⟩

/-- Prefix form of the congruence-test converse for an arbitrary
final-local word over the module alphabet. -/
theorem congruenceWord_forced_prefix_of_final_local
    {prime phaseCount source target modulus counter : Nat}
    {phase : Nat → Nat} {allowed : List Nat}
    (primeProperty : IsPrime prime)
    (primeBound : 6 * phaseCount < prime)
    (modulusPositive : 0 < modulus)
    (sourceBound : source < phaseCount)
    (phaseBound : ∀ index, index < modulus → phase index < phaseCount)
    (allowedBound : ∀ index ∈ allowed, index < modulus)
    (sourcePrivateDistinct :
      ∀ index, index < modulus → source ≠ phase index)
    (phaseInjective : ∀ {first second}, first < modulus → second < modulus →
      phase first = phase second → first = second)
    {word : List PhysicalTemplate}
    (wordOver : WordOver
      (congruenceAlphabet source target modulus phase allowed) word)
    (finalLocal : LocalAt prime
      (physicalWordAction prime word
        (phaseAffine source (unaryCode prime counter))))
    (longEnough : counter + 1 ≤ word.length) :
    counter % modulus ∈ allowed ∧
      word.take (counter + 1) =
        congruenceWord source target modulus counter phase := by
  have inputNonzero :
      (phaseAffine source (unaryCode prime counter)).Nonzero :=
    Vec2.affine_nonzero _
  have allLocal := allStatesLocal_of_final_local
    (by have := primeProperty.1; omega) word inputNonzero finalLocal
  have classified := congruenceWord_surviving_unique primeProperty
    primeBound modulusPositive sourceBound phaseBound allowedBound
    sourcePrivateDistinct phaseInjective (wordOver.take (counter + 1))
    (allLocal.take (counter + 1)) (by
      rw [List.length_take, Nat.min_eq_left longEnough])
  exact classified

end Mortality.Compiler.CongruenceModule
