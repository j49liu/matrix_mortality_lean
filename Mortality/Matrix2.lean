import Mortality.Basic

/-!
# Explicit two-dimensional rational linear algebra

The formalization uses an explicit four-entry matrix type so the product
convention and every rank-one calculation remain visible.  No result in
this file depends on Mathlib.
-/

namespace Mortality

structure Vec2 where
  x : Rat
  y : Rat
  deriving DecidableEq, Repr

namespace Vec2

def zero : Vec2 := { x := 0, y := 0 }

/-- The standard column representing a finite rational projective point. -/
def affine (value : Rat) : Vec2 := { x := value, y := 1 }

def scale (scalar : Rat) (vector : Vec2) : Vec2 :=
  { x := scalar * vector.x, y := scalar * vector.y }

@[simp] theorem scale_one (vector : Vec2) : scale 1 vector = vector := by
  cases vector
  simp only [scale]
  congr 1 <;> grind

theorem scale_assoc (first second : Rat) (vector : Vec2) :
    scale first (scale second vector) = scale (first * second) vector := by
  cases vector
  simp only [scale]
  congr 1 <;> grind

@[simp] theorem scale_zero (vector : Vec2) : scale 0 vector = zero := by
  cases vector
  simp only [scale, zero]
  congr 1 <;> grind

def Nonzero (vector : Vec2) : Prop := vector.x ≠ 0 ∨ vector.y ≠ 0

theorem affine_nonzero (value : Rat) : (affine value).Nonzero := by
  right
  simp only [affine]
  decide

def dot (row column : Vec2) : Rat :=
  row.x * column.x + row.y * column.y

/-- A row annihilating the line through `vector`. -/
def perp (vector : Vec2) : Vec2 :=
  { x := vector.y, y := -vector.x }

@[simp] theorem dot_perp_self (vector : Vec2) :
    dot (perp vector) vector = 0 := by
  cases vector
  simp only [dot, perp]
  grind

theorem scale_nonzero {scalar : Rat} {vector : Vec2}
    (scalarNonzero : scalar ≠ 0) (vectorNonzero : vector.Nonzero) :
    (scale scalar vector).Nonzero := by
  rcases vectorNonzero with xNonzero | yNonzero
  · left
    simp only [scale]
    exact fun productZero => xNonzero
      ((Rat.mul_eq_zero.mp productZero).resolve_left scalarNonzero)
  · right
    simp only [scale]
    exact fun productZero => yNonzero
      ((Rat.mul_eq_zero.mp productZero).resolve_left scalarNonzero)

theorem perp_nonzero {vector : Vec2} (nonzero : vector.Nonzero) :
    (perp vector).Nonzero := by
  simp only [Nonzero, perp] at nonzero ⊢
  grind

end Vec2

structure Matrix2 where
  a : Rat
  b : Rat
  c : Rat
  d : Rat
  deriving DecidableEq, Repr

namespace Matrix2

def zero : Matrix2 := { a := 0, b := 0, c := 0, d := 0 }

def identity : Matrix2 := { a := 1, b := 0, c := 0, d := 1 }

def mul (left right : Matrix2) : Matrix2 :=
  { a := left.a * right.a + left.b * right.c
    b := left.a * right.b + left.b * right.d
    c := left.c * right.a + left.d * right.c
    d := left.c * right.b + left.d * right.d }

def apply (matrix : Matrix2) (vector : Vec2) : Vec2 :=
  { x := matrix.a * vector.x + matrix.b * vector.y
    y := matrix.c * vector.x + matrix.d * vector.y }

def rowMul (row : Vec2) (matrix : Matrix2) : Vec2 :=
  { x := row.x * matrix.a + row.y * matrix.c
    y := row.x * matrix.b + row.y * matrix.d }

def outer (column row : Vec2) : Matrix2 :=
  { a := column.x * row.x, b := column.x * row.y
    c := column.y * row.x, d := column.y * row.y }

def det (matrix : Matrix2) : Rat :=
  matrix.a * matrix.d - matrix.b * matrix.c

def Nonsingular (matrix : Matrix2) : Prop := matrix.det ≠ 0

/-- A nonzero outer product; over the rationals this is equivalent to
having matrix rank exactly one. -/
def RankOne (matrix : Matrix2) : Prop :=
  ∃ column row, column.Nonzero ∧ row.Nonzero ∧
    matrix = outer column row

@[simp] theorem mul_identity (matrix : Matrix2) :
    mul matrix identity = matrix := by
  cases matrix
  simp only [mul, identity]
  congr 1 <;> grind

@[simp] theorem identity_mul (matrix : Matrix2) :
    mul identity matrix = matrix := by
  cases matrix
  simp only [mul, identity]
  congr 1 <;> grind

theorem mul_assoc (first second third : Matrix2) :
    mul (mul first second) third = mul first (mul second third) := by
  cases first
  cases second
  cases third
  simp only [mul]
  congr 1 <;> grind

@[simp] theorem mul_zero (matrix : Matrix2) : mul matrix zero = zero := by
  cases matrix
  simp only [mul, zero]
  congr 1 <;> grind

@[simp] theorem zero_mul (matrix : Matrix2) : mul zero matrix = zero := by
  cases matrix
  simp only [mul, zero]
  congr 1 <;> grind

@[simp] theorem apply_identity (vector : Vec2) :
    apply identity vector = vector := by
  cases vector
  simp only [apply, identity]
  congr 1 <;> grind

@[simp] theorem apply_zero (vector : Vec2) : apply zero vector = Vec2.zero := by
  cases vector
  simp only [apply, zero, Vec2.zero]
  congr 1 <;> grind

theorem apply_mul (left right : Matrix2) (vector : Vec2) :
    apply (mul left right) vector = apply left (apply right vector) := by
  cases left
  cases right
  cases vector
  simp only [mul, apply]
  congr 1 <;> grind

theorem apply_scale (matrix : Matrix2) (scalar : Rat) (vector : Vec2) :
    apply matrix (Vec2.scale scalar vector) =
      Vec2.scale scalar (apply matrix vector) := by
  cases matrix
  cases vector
  simp only [apply, Vec2.scale]
  congr 1 <;> grind

theorem apply_outer (column row vector : Vec2) :
    apply (outer column row) vector =
      Vec2.scale (Vec2.dot row vector) column := by
  cases column
  cases row
  cases vector
  simp only [apply, outer, Vec2.scale, Vec2.dot]
  congr 1 <;> grind

@[simp] theorem rowMul_identity (row : Vec2) :
    rowMul row identity = row := by
  cases row
  simp only [rowMul, identity]
  congr 1 <;> grind

theorem rowMul_mul (row : Vec2) (left right : Matrix2) :
    rowMul row (mul left right) = rowMul (rowMul row left) right := by
  cases row
  cases left
  cases right
  simp only [rowMul, mul]
  congr 1 <;> grind

theorem mul_outer (matrix : Matrix2) (column row : Vec2) :
    mul matrix (outer column row) = outer (apply matrix column) row := by
  cases matrix
  cases column
  cases row
  simp only [mul, outer, apply]
  congr 1 <;> grind

theorem outer_mul (column row : Vec2) (matrix : Matrix2) :
    mul (outer column row) matrix = outer column (rowMul row matrix) := by
  cases matrix
  cases column
  cases row
  simp only [mul, outer, rowMul]
  congr 1 <;> grind

theorem outer_outer (u row column lambda : Vec2) :
    mul (outer u row) (outer column lambda) =
      outer (Vec2.scale (Vec2.dot row column) u) lambda := by
  cases u
  cases row
  cases column
  cases lambda
  simp only [mul, outer, Vec2.scale, Vec2.dot]
  congr 1 <;> grind

theorem outer_scale_left (scalar : Rat) (column row : Vec2) :
    outer (Vec2.scale scalar column) row =
      outer column (Vec2.scale scalar row) := by
  cases column
  cases row
  simp only [outer, Vec2.scale]
  congr 1 <;> grind

@[simp] theorem outer_zero_column (row : Vec2) :
    outer Vec2.zero row = zero := by
  cases row
  simp only [outer, Vec2.zero, zero]
  congr 1 <;> grind

@[simp] theorem det_identity : det identity = 1 := by
  simp only [det, identity]
  grind

@[simp] theorem det_zero : det zero = 0 := by
  simp only [det, zero]
  grind

theorem det_mul (left right : Matrix2) :
    det (mul left right) = det left * det right := by
  cases left
  cases right
  simp only [det, mul]
  grind

theorem Nonsingular.identity : identity.Nonsingular := by
  rw [Nonsingular, det_identity]
  decide

theorem not_nonsingular_zero : ¬zero.Nonsingular := by
  simp [Nonsingular]

theorem Nonsingular.mul {left right : Matrix2}
    (leftNonsingular : left.Nonsingular)
    (rightNonsingular : right.Nonsingular) :
    (mul left right).Nonsingular := by
  rw [Nonsingular, det_mul]
  intro productZero
  rcases Rat.mul_eq_zero.mp productZero with leftZero | rightZero
  · exact leftNonsingular leftZero
  · exact rightNonsingular rightZero

theorem apply_nonzero {matrix : Matrix2} {vector : Vec2}
    (matrixNonsingular : matrix.Nonsingular)
    (vectorNonzero : vector.Nonzero) :
    (apply matrix vector).Nonzero := by
  apply Classical.byContradiction
  intro outputZero
  simp only [Vec2.Nonzero, not_or, Classical.not_not] at outputZero
  rcases outputZero with ⟨firstEq, secondEq⟩
  cases matrix with
  | mk a b c d =>
    cases vector with
    | mk x y =>
      simp only [apply] at firstEq secondEq
      simp only [Nonsingular, det] at matrixNonsingular
      simp only [Vec2.Nonzero] at vectorNonzero
      have detX : (a * d - b * c) * x = 0 := by grind
      have detY : (a * d - b * c) * y = 0 := by grind
      rcases vectorNonzero with xNonzero | yNonzero
      · exact matrixNonsingular
          ((Rat.mul_eq_zero.mp detX).resolve_right xNonzero)
      · exact matrixNonsingular
          ((Rat.mul_eq_zero.mp detY).resolve_right yNonzero)

theorem rowMul_nonzero {row : Vec2} {matrix : Matrix2}
    (rowNonzero : row.Nonzero) (matrixNonsingular : matrix.Nonsingular) :
    (rowMul row matrix).Nonzero := by
  apply Classical.byContradiction
  intro outputZero
  simp only [Vec2.Nonzero, not_or, Classical.not_not] at outputZero
  rcases outputZero with ⟨firstEq, secondEq⟩
  cases row with
  | mk x y =>
    cases matrix with
    | mk a b c d =>
      simp only [rowMul] at firstEq secondEq
      simp only [Nonsingular, det] at matrixNonsingular
      simp only [Vec2.Nonzero] at rowNonzero
      have detX : x * (a * d - b * c) = 0 := by grind
      have detY : y * (a * d - b * c) = 0 := by grind
      rcases rowNonzero with xNonzero | yNonzero
      · exact matrixNonsingular
          ((Rat.mul_eq_zero.mp detX).resolve_left xNonzero)
      · exact matrixNonsingular
          ((Rat.mul_eq_zero.mp detY).resolve_left yNonzero)

theorem outer_nonzero {column row : Vec2}
    (columnNonzero : column.Nonzero) (rowNonzero : row.Nonzero) :
    outer column row ≠ zero := by
  intro matrixEq
  have aEq := congrArg Matrix2.a matrixEq
  have bEq := congrArg Matrix2.b matrixEq
  have cEq := congrArg Matrix2.c matrixEq
  have dEq := congrArg Matrix2.d matrixEq
  simp only [outer, zero] at aEq bEq cEq dEq
  rcases columnNonzero with columnX | columnY <;>
    rcases rowNonzero with rowX | rowY
  · exact columnX ((Rat.mul_eq_zero.mp aEq).resolve_right rowX)
  · exact columnX ((Rat.mul_eq_zero.mp bEq).resolve_right rowY)
  · exact columnY ((Rat.mul_eq_zero.mp cEq).resolve_right rowX)
  · exact columnY ((Rat.mul_eq_zero.mp dEq).resolve_right rowY)

end Matrix2

/-- Evaluate a word listed in application order.  Thus `[A, B]`
evaluates to `B A`. -/
def matrixWordProduct : List Matrix2 → Matrix2
  | [] => Matrix2.identity
  | matrix :: word => Matrix2.mul (matrixWordProduct word) matrix

@[simp] theorem matrixWordProduct_nil : matrixWordProduct [] = Matrix2.identity := rfl

@[simp] theorem matrixWordProduct_cons (matrix : Matrix2) (word : List Matrix2) :
    matrixWordProduct (matrix :: word) =
      Matrix2.mul (matrixWordProduct word) matrix := rfl

theorem matrixWordProduct_append (first second : List Matrix2) :
    matrixWordProduct (first ++ second) =
      Matrix2.mul (matrixWordProduct second) (matrixWordProduct first) := by
  induction first with
  | nil => simp
  | cons matrix word inductionHypothesis =>
      simp [inductionHypothesis, Matrix2.mul_assoc]

theorem matrixWordProduct_nonsingular {alphabet word : List Matrix2}
    (alphabetNonsingular : ∀ matrix ∈ alphabet, matrix.Nonsingular)
    (wordOver : WordOver alphabet word) :
    (matrixWordProduct word).Nonsingular := by
  induction word with
  | nil => exact Matrix2.Nonsingular.identity
  | cons matrix word inductionHypothesis =>
      apply Matrix2.Nonsingular.mul
      · exact inductionHypothesis (fun letter letterMem =>
          wordOver letter (by simp [letterMem]))
      · exact alphabetNonsingular matrix (wordOver matrix (by simp))

/-- A finite matrix alphabet is mortal when a positive-length word
evaluates to the zero matrix. -/
def Mortal (alphabet : List Matrix2) : Prop :=
  ∃ word, word ≠ [] ∧ WordOver alphabet word ∧
    matrixWordProduct word = Matrix2.zero

/-- Equality of rational lines represented by nonzero columns. -/
def SameLine (source target : Vec2) : Prop :=
  ∃ scalar : Rat, scalar ≠ 0 ∧ source = Vec2.scale scalar target

theorem SameLine.refl (vector : Vec2) : SameLine vector vector := by
  exact ⟨1, by decide, (Vec2.scale_one vector).symm⟩

theorem SameLine.symm {source target : Vec2}
    (same : SameLine source target) : SameLine target source := by
  rcases same with ⟨scalar, scalarNonzero, rfl⟩
  have inverseCancel := Rat.inv_mul_cancel scalar scalarNonzero
  have inverseNonzero : scalar⁻¹ ≠ 0 := by
    intro inverseZero
    rw [inverseZero, Rat.zero_mul] at inverseCancel
    contradiction
  refine ⟨scalar⁻¹, inverseNonzero, ?_⟩
  rw [Vec2.scale_assoc, inverseCancel, Vec2.scale_one]

theorem SameLine.trans {first second third : Vec2}
    (firstSecond : SameLine first second)
    (secondThird : SameLine second third) : SameLine first third := by
  rcases firstSecond with ⟨firstScalar, firstNonzero, firstEq⟩
  rcases secondThird with ⟨secondScalar, secondNonzero, secondEq⟩
  refine ⟨firstScalar * secondScalar, ?_, ?_⟩
  · intro productZero
    rcases Rat.mul_eq_zero.mp productZero with firstZero | secondZero
    · exact firstNonzero firstZero
    · exact secondNonzero secondZero
  · rw [firstEq, secondEq, Vec2.scale_assoc]

theorem SameLine.apply (matrix : Matrix2) {source target : Vec2}
    (same : SameLine source target) :
    SameLine (Matrix2.apply matrix source) (Matrix2.apply matrix target) := by
  rcases same with ⟨scalar, scalarNonzero, rfl⟩
  exact ⟨scalar, scalarNonzero, Matrix2.apply_scale matrix scalar target⟩

/-- In dimension two, a nonzero column lies on the target line exactly
when the perpendicular target row annihilates it. -/
theorem sameLine_iff_dot_perp_eq_zero {source target : Vec2}
    (sourceNonzero : source.Nonzero) (targetNonzero : target.Nonzero) :
    SameLine source target ↔
      Vec2.dot (Vec2.perp target) source = 0 := by
  constructor
  · rintro ⟨scalar, scalarNonzero, rfl⟩
    cases target
    simp only [Vec2.dot, Vec2.perp, Vec2.scale]
    grind
  · intro annihilated
    cases source with
    | mk sourceX sourceY =>
      cases target with
      | mk targetX targetY =>
        simp only [Vec2.Nonzero] at sourceNonzero targetNonzero
        simp only [Vec2.dot, Vec2.perp] at annihilated
        rcases targetNonzero with targetXNonzero | targetYNonzero
        · have sourceXNonzero : sourceX ≠ 0 := by
            intro sourceXZero
            have productZero : targetX * sourceY = 0 := by
              grind
            have sourceYZero :=
              (Rat.mul_eq_zero.mp productZero).resolve_left targetXNonzero
            exact (sourceNonzero.resolve_left (fun h => h sourceXZero)) sourceYZero
          have inverseCancel := Rat.inv_mul_cancel targetX targetXNonzero
          have inverseNonzero : targetX⁻¹ ≠ 0 := by
            intro inverseZero
            rw [inverseZero, Rat.zero_mul] at inverseCancel
            contradiction
          refine ⟨sourceX * targetX⁻¹, ?_, ?_⟩
          · intro productZero
            rcases Rat.mul_eq_zero.mp productZero with sourceXZero | inverseZero
            · exact sourceXNonzero sourceXZero
            · exact inverseNonzero inverseZero
          · simp only [Vec2.scale]
            congr 1 <;> grind
        · have sourceYNonzero : sourceY ≠ 0 := by
            intro sourceYZero
            have productZero : targetY * sourceX = 0 := by
              grind
            have sourceXZero :=
              (Rat.mul_eq_zero.mp productZero).resolve_left targetYNonzero
            exact (sourceNonzero.resolve_right (fun h => h sourceYZero)) sourceXZero
          have inverseCancel := Rat.inv_mul_cancel targetY targetYNonzero
          have inverseNonzero : targetY⁻¹ ≠ 0 := by
            intro inverseZero
            rw [inverseZero, Rat.zero_mul] at inverseCancel
            contradiction
          refine ⟨sourceY * targetY⁻¹, ?_, ?_⟩
          · intro productZero
            rcases Rat.mul_eq_zero.mp productZero with sourceYZero | inverseZero
            · exact sourceYNonzero sourceYZero
            · exact inverseNonzero inverseZero
          · simp only [Vec2.scale]
            congr 1 <;> grind

/-- Exact projective reachability, with the empty word allowed. -/
def ProjectivelyReachable (alphabet : List Matrix2)
    (source target : Vec2) : Prop :=
  ∃ word, WordOver alphabet word ∧
    SameLine (Matrix2.apply (matrixWordProduct word) source) target

end Mortality
