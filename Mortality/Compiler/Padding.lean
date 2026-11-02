import Mortality.Compiler.Enforcement

/-!
# Exact-cardinality dummy matrices

The semantic exclusion of dummy letters uses the error region and is
proved later.  This file checks their exact integer formula,
determinants, pairwise distinctness, and list-cardinality bookkeeping.
-/

namespace Mortality.Compiler

def dummyMatrix (prime phase : Nat) : IntMatrix2 :=
  { a := 1
    b := ((prime : Int) - 1) * phaseShift phase
    c := 0
    d := prime }

theorem dummyMatrix_factorization (prime phase : Nat) :
    dummyMatrix prime phase =
      IntMatrix2.mul (chart phase)
        (IntMatrix2.mul (deletion prime 0) (chartInverse phase)) := by
  simp only [dummyMatrix, chart, deletion, chartInverse, phaseShift,
    IntMatrix2.mul]
  grind

/-- A dummy is itself the zero-deletion physical letter at its reserved
phase.  This identity lets the common phase guard exclude dummy letters
semantically, not merely count them. -/
theorem dummyMatrix_eq_physicalLetter (prime phase : Nat) :
    dummyMatrix prime phase =
      physicalLetter prime phase phase 0 0 .positive 0 := by
  simp [dummyMatrix, physicalLetter, chart, chartInverse, deletion,
    mutation, phaseShift, IntMatrix2.mul, Sign.value]
  congr 1 <;> grind

/-- A dummy letter at one phase cannot preserve locality when applied to
a reserved-residue point in another phase. -/
theorem dummyMatrix_rejects_other_phase
    {prime phaseCount actualPhase dummyPhase : Nat}
    {actualDigit : Int} {numerator denominator : Int}
    (primeProperty : IsPrime prime)
    (primeBound : 6 * phaseCount < prime)
    (actualPhaseBound : actualPhase < phaseCount)
    (dummyPhaseBound : dummyPhase < phaseCount)
    (actualReserved : ReservedDigit actualDigit)
    (denominatorNotDivisible : ¬(prime : Int) ∣ denominator)
    (actualResidue :
      (prime : Int) ∣ numerator - actualDigit * denominator)
    (phaseDistinct : actualPhase ≠ dummyPhase) :
    ¬LocalAt prime
      (Matrix2.apply (IntMatrix2.cast (dummyMatrix prime dummyPhase))
        (phasePoint actualPhase numerator denominator)) := by
  intro outputLocal
  rw [dummyMatrix_eq_physicalLetter] at outputLocal
  have forced := physicalLetter_source_digit_unique primeProperty primeBound
    actualPhaseBound dummyPhaseBound actualReserved
    (by simp [ReservedDigit]) denominatorNotDivisible actualResidue outputLocal
  exact phaseDistinct forced.1

@[simp] theorem dummyMatrix_det (prime phase : Nat) :
    (dummyMatrix prime phase).det = prime := by
  simp [dummyMatrix, IntMatrix2.det]

theorem dummyMatrix_nonsingular {prime phase : Nat} (primePositive : 0 < prime) :
    (dummyMatrix prime phase).Nonsingular := by
  rw [IntMatrix2.Nonsingular, dummyMatrix_det]
  intro castZero
  have naturalZero := Int.ofNat_eq_zero.mp castZero
  omega

theorem dummyMatrix_injective {prime : Nat} (primeAtLeastTwo : 2 ≤ prime) :
    Function.Injective (dummyMatrix prime) := by
  intro first second matrixEq
  have entryEq := congrArg IntMatrix2.b matrixEq
  simp only [dummyMatrix] at entryEq
  have factorNonzero : (prime : Int) - 1 ≠ 0 := by omega
  have shiftEq := Int.eq_of_mul_eq_mul_left factorNonzero entryEq
  unfold phaseShift at shiftEq
  omega

def dummyMatrices (prime : Nat) (phases : List Nat) : List IntMatrix2 :=
  phases.map (dummyMatrix prime)

theorem dummyMatrices_length (prime : Nat) (phases : List Nat) :
    (dummyMatrices prime phases).length = phases.length := by
  simp [dummyMatrices]

theorem dummyMatrices_nodup {prime : Nat} {phases : List Nat}
    (primeAtLeastTwo : 2 ≤ prime) (phasesNodup : phases.Nodup) :
    (dummyMatrices prime phases).Nodup := by
  induction phases with
  | nil => simp [dummyMatrices]
  | cons phase phases inductionHypothesis =>
      have split := List.nodup_cons.mp phasesNodup
      rw [dummyMatrices, List.map_cons, List.nodup_cons]
      constructor
      · intro matrixMem
        obtain ⟨otherPhase, otherPhaseMem, matrixEq⟩ :=
          List.mem_map.mp matrixMem
        have phaseEq := dummyMatrix_injective primeAtLeastTwo matrixEq
        exact split.1 (phaseEq ▸ otherPhaseMem)
      · exact inductionHypothesis split.2

/-- Appending a disjoint dummy list preserves distinctness and gives the
sum of the two exact cardinalities. -/
theorem append_dummy_exact {prime : Nat} {genuine : List IntMatrix2}
    {phases : List Nat} (primeAtLeastTwo : 2 ≤ prime)
    (genuineNodup : genuine.Nodup) (phasesNodup : phases.Nodup)
    (disjoint : ∀ matrix ∈ dummyMatrices prime phases, matrix ∉ genuine) :
    (genuine ++ dummyMatrices prime phases).Nodup ∧
      (genuine ++ dummyMatrices prime phases).length =
        genuine.length + phases.length := by
  constructor
  · apply List.nodup_append.mpr
    refine ⟨genuineNodup, dummyMatrices_nodup primeAtLeastTwo phasesNodup, ?_⟩
    intro genuineMatrix genuineMem dummy dummyMem equality
    subst dummy
    exact disjoint genuineMatrix dummyMem genuineMem
  · simp [dummyMatrices_length]

end Mortality.Compiler
