import Mortality.RankOne

/-!
# Integer representatives

The reduction ultimately outputs integer matrices.  This file defines
their exact embedding into the rational matrix model and the integer
outer product used by the rank-one conversion.
-/

namespace Mortality

structure IntVec2 where
  x : Int
  y : Int
  deriving DecidableEq, Repr

namespace IntVec2

def cast (vector : IntVec2) : Vec2 :=
  { x := (vector.x : Rat), y := (vector.y : Rat) }

def Nonzero (vector : IntVec2) : Prop := vector.x ≠ 0 ∨ vector.y ≠ 0

theorem cast_nonzero {vector : IntVec2} (nonzero : vector.Nonzero) :
    vector.cast.Nonzero := by
  cases vector with
  | mk x y =>
      simp only [Nonzero] at nonzero
      simp only [cast, Vec2.Nonzero]
      rcases nonzero with xNonzero | yNonzero
      · left
        simpa using xNonzero
      · right
        simpa using yNonzero

end IntVec2

structure IntMatrix2 where
  a : Int
  b : Int
  c : Int
  d : Int
  deriving DecidableEq, Repr

namespace IntMatrix2

def zero : IntMatrix2 := { a := 0, b := 0, c := 0, d := 0 }

def identity : IntMatrix2 := { a := 1, b := 0, c := 0, d := 1 }

def mul (left right : IntMatrix2) : IntMatrix2 :=
  { a := left.a * right.a + left.b * right.c
    b := left.a * right.b + left.b * right.d
    c := left.c * right.a + left.d * right.c
    d := left.c * right.b + left.d * right.d }

def det (matrix : IntMatrix2) : Int :=
  matrix.a * matrix.d - matrix.b * matrix.c

def Nonsingular (matrix : IntMatrix2) : Prop := matrix.det ≠ 0

def cast (matrix : IntMatrix2) : Matrix2 :=
  { a := (matrix.a : Rat), b := (matrix.b : Rat)
    c := (matrix.c : Rat), d := (matrix.d : Rat) }

def RankOne (matrix : IntMatrix2) : Prop := matrix.cast.RankOne

@[simp] theorem cast_zero : cast zero = Matrix2.zero := by
  rfl

@[simp] theorem cast_identity : cast identity = Matrix2.identity := by
  rfl

theorem cast_mul (left right : IntMatrix2) :
    cast (mul left right) = Matrix2.mul (cast left) (cast right) := by
  cases left
  cases right
  simp only [cast, mul, Matrix2.mul, Rat.intCast_add, Rat.intCast_mul]

theorem det_mul (left right : IntMatrix2) :
    det (mul left right) = det left * det right := by
  cases left
  cases right
  simp only [det, mul]
  grind

theorem cast_det (matrix : IntMatrix2) :
    (matrix.det : Rat) = matrix.cast.det := by
  cases matrix
  simp [det, cast, Matrix2.det]

theorem cast_nonsingular {matrix : IntMatrix2}
    (nonsingular : matrix.Nonsingular) : matrix.cast.Nonsingular := by
  rw [Matrix2.Nonsingular, ← cast_det]
  simpa [Nonsingular] using nonsingular

end IntMatrix2

/-- An integer matrix word, in application order. -/
def intMatrixWordProduct : List IntMatrix2 → IntMatrix2
  | [] => IntMatrix2.identity
  | matrix :: word => IntMatrix2.mul (intMatrixWordProduct word) matrix

theorem cast_intMatrixWordProduct (word : List IntMatrix2) :
    (intMatrixWordProduct word).cast =
      matrixWordProduct (word.map IntMatrix2.cast) := by
  induction word with
  | nil => rfl
  | cons matrix word inductionHypothesis =>
      simp only [intMatrixWordProduct, List.map_cons, matrixWordProduct_cons,
        IntMatrix2.cast_mul, inductionHypothesis]

/-- Mortality of an integer alphabet, interpreted through its faithful
entrywise embedding into rational matrices. -/
def IntegerMortal (alphabet : List IntMatrix2) : Prop :=
  Mortal (alphabet.map IntMatrix2.cast)

def IntegerProjectivelyReachable (alphabet : List IntMatrix2)
    (source target : IntVec2) : Prop :=
  ProjectivelyReachable (alphabet.map IntMatrix2.cast)
    source.cast target.cast

/-- The integer outer product in the paper. -/
def integerRankOneMatrix (source target : IntVec2) : IntMatrix2 :=
  { a := source.x * target.y
    b := -(source.x * target.x)
    c := source.y * target.y
    d := -(source.y * target.x) }

@[simp] theorem integerRankOneMatrix_det (source target : IntVec2) :
    (integerRankOneMatrix source target).det = 0 := by
  cases source
  cases target
  simp only [integerRankOneMatrix, IntMatrix2.det]
  grind

theorem cast_integerRankOneMatrix (source target : IntVec2) :
    (integerRankOneMatrix source target).cast =
      rankOneMatrix source.cast target.cast := by
  cases source
  cases target
  simp [integerRankOneMatrix, IntMatrix2.cast, rankOneMatrix, targetRow,
    IntVec2.cast, Matrix2.outer, Vec2.perp]
  grind

theorem integerRankOneMatrix_nonzero {source target : IntVec2}
    (sourceNonzero : source.Nonzero) (targetNonzero : target.Nonzero) :
    integerRankOneMatrix source target ≠ IntMatrix2.zero := by
  intro matrixZero
  have castZero := congrArg IntMatrix2.cast matrixZero
  rw [cast_integerRankOneMatrix, IntMatrix2.cast_zero] at castZero
  exact rankOneMatrix_nonzero (IntVec2.cast_nonzero sourceNonzero)
    (IntVec2.cast_nonzero targetNonzero) castZero

theorem integerRankOneMatrix_rankOne {source target : IntVec2}
    (sourceNonzero : source.Nonzero) (targetNonzero : target.Nonzero) :
    (integerRankOneMatrix source target).RankOne := by
  rw [IntMatrix2.RankOne, cast_integerRankOneMatrix]
  exact rankOneMatrix_rankOne (IntVec2.cast_nonzero sourceNonzero)
    (IntVec2.cast_nonzero targetNonzero)

theorem integerRankOneMatrix_not_mem_nonsingular
    (alphabet : List IntMatrix2) (source target : IntVec2)
    (alphabetNonsingular : ∀ matrix ∈ alphabet, matrix.Nonsingular) :
    integerRankOneMatrix source target ∉ alphabet := by
  intro member
  have nonsingular := alphabetNonsingular _ member
  exact nonsingular (integerRankOneMatrix_det source target)

theorem integer_rankOne_cons_nodup {alphabet : List IntMatrix2}
    {source target : IntVec2} (alphabetNodup : alphabet.Nodup)
    (alphabetNonsingular : ∀ matrix ∈ alphabet, matrix.Nonsingular) :
    (integerRankOneMatrix source target :: alphabet).Nodup := by
  exact List.nodup_cons.mpr
    ⟨integerRankOneMatrix_not_mem_nonsingular alphabet source target
      alphabetNonsingular, alphabetNodup⟩

theorem integer_rankOne_family_count {alphabet : List IntMatrix2}
    {source target : IntVec2} (fixedCount : alphabet.length = 5798) :
    (integerRankOneMatrix source target :: alphabet).length = 5799 := by
  simp [fixedCount]

/-- Integer specialization of the arbitrary-factor rank-one theorem. -/
theorem one_integer_rankOne_mortality_iff (alphabet : List IntMatrix2)
    (source target : IntVec2)
    (alphabetNonsingular :
      ∀ matrix ∈ alphabet, matrix.Nonsingular)
    (sourceNonzero : source.Nonzero) (targetNonzero : target.Nonzero) :
    IntegerMortal (integerRankOneMatrix source target :: alphabet) ↔
      IntegerProjectivelyReachable alphabet source target := by
  unfold IntegerMortal IntegerProjectivelyReachable
  simp only [List.map_cons, cast_integerRankOneMatrix]
  apply one_rankOne_mortality_iff
  · intro matrix matrixMem
    obtain ⟨integerMatrix, integerMatrixMem, rfl⟩ :=
      List.mem_map.mp matrixMem
    exact IntMatrix2.cast_nonsingular
      (alphabetNonsingular integerMatrix integerMatrixMem)
  · exact IntVec2.cast_nonzero sourceNonzero
  · exact IntVec2.cast_nonzero targetNonzero

end Mortality
