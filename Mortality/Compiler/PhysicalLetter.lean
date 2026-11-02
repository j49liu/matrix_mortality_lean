import Mortality.IntegerMatrix2

/-!
# Integral phase charts and physical letters

Each compiler letter is one matrix, obtained by multiplying the five
integral factors in the manuscript.  This file fixes that multiplication
order and proves the determinant restriction symbolically.
-/

namespace Mortality.Compiler

inductive Sign where
  | positive
  | negative
  deriving DecidableEq, Repr

namespace Sign

def value : Sign → Int
  | .positive => 1
  | .negative => -1

@[simp] theorem value_eq (sign : Sign) :
    sign.value = 1 ∨ sign.value = -1 := by
  cases sign <;> simp [value]

end Sign

def phaseShift (phase : Nat) : Int := 6 * (phase : Int) + 1

/-- Matrix of `C_q(z)=z+6q+1`. -/
def chart (phase : Nat) : IntMatrix2 :=
  { a := 1, b := phaseShift phase, c := 0, d := 1 }

def chartInverse (phase : Nat) : IntMatrix2 :=
  { a := 1, b := -phaseShift phase, c := 0, d := 1 }

/-- Matrix of `D_e(z)=(z-e)/p`. -/
def deletion (prime : Nat) (digit : Int) : IntMatrix2 :=
  { a := 1, b := -digit, c := 0, d := prime }

/-- Matrix of `M_{δ,h}(z)=δz/(1+phz)`. -/
def mutation (prime : Nat) (sign : Sign) (coefficient : Int) : IntMatrix2 :=
  { a := sign.value, b := 0
    c := (prime : Int) * coefficient, d := 1 }

/-- One guarded matrix letter.  The factors are written in their matrix
multiplication order and therefore act from right to left. -/
def physicalLetter (prime sourcePhase targetPhase : Nat) (digit : Int)
    (preCoefficient : Int) (postSign : Sign) (postCoefficient : Int) :
    IntMatrix2 :=
  IntMatrix2.mul (chart targetPhase)
    (IntMatrix2.mul (mutation prime postSign postCoefficient)
      (IntMatrix2.mul (deletion prime digit)
        (IntMatrix2.mul (mutation prime .positive preCoefficient)
          (chartInverse sourcePhase))))

@[simp] theorem chart_mul_inverse (phase : Nat) :
    IntMatrix2.mul (chart phase) (chartInverse phase) =
      IntMatrix2.identity := by
  simp only [chart, chartInverse, phaseShift, IntMatrix2.mul,
    IntMatrix2.identity]
  grind

@[simp] theorem chartInverse_mul_chart (phase : Nat) :
    IntMatrix2.mul (chartInverse phase) (chart phase) =
      IntMatrix2.identity := by
  simp only [chart, chartInverse, phaseShift, IntMatrix2.mul,
    IntMatrix2.identity]
  grind

theorem chart_apply (phase : Nat) (value : Rat) :
    Matrix2.apply (IntMatrix2.cast (chart phase)) (Vec2.affine value) =
      Vec2.affine (value + (phaseShift phase : Rat)) := by
  simp only [chart, IntMatrix2.cast, Matrix2.apply, Vec2.affine]
  congr 1 <;> grind

theorem chartInverse_apply (phase : Nat) (value : Rat) :
    Matrix2.apply (IntMatrix2.cast (chartInverse phase))
        (Vec2.affine value) =
      Vec2.affine (value - (phaseShift phase : Rat)) := by
  simp only [chartInverse, IntMatrix2.cast, Matrix2.apply, Vec2.affine,
    Rat.intCast_neg]
  congr 1 <;> grind

/-- The deletion matrix represents `(z-e)/p` on finite points. -/
theorem deletion_apply_scaled {prime : Nat} (digit : Int) (value : Rat)
    (primePositive : 0 < prime) :
    Matrix2.apply (IntMatrix2.cast (deletion prime digit))
        (Vec2.affine value) =
      Vec2.scale (prime : Rat)
        (Vec2.affine ((value - (digit : Rat)) / (prime : Rat))) := by
  have primeNonzero : (prime : Rat) ≠ 0 := by
    simpa using (show prime ≠ 0 by omega)
  have primeCancel := Rat.mul_inv_cancel (prime : Rat) primeNonzero
  simp only [deletion, IntMatrix2.cast, Matrix2.apply, Vec2.affine,
    Vec2.scale, Rat.intCast_neg, Rat.intCast_natCast, Rat.div_def]
  congr 1 <;> grind

def mutationDenominator (prime : Nat) (coefficient : Int)
    (value : Rat) : Rat :=
  1 + (prime : Rat) * (coefficient : Rat) * value

def mutationMap (prime : Nat) (sign : Sign) (coefficient : Int)
    (value : Rat) : Rat :=
  (sign.value : Rat) * value /
    mutationDenominator prime coefficient value

@[simp] theorem mutationMap_positive_zero (prime : Nat) (value : Rat) :
    mutationMap prime .positive 0 value = value := by
  simp [mutationMap, mutationDenominator, Sign.value, Rat.div_def]
  grind

/-- Away from its pole, the mutation matrix represents
`δz/(1+phz)`. -/
theorem mutation_apply_scaled (prime : Nat) (sign : Sign)
    (coefficient : Int) (value : Rat)
    (denominatorNonzero : mutationDenominator prime coefficient value ≠ 0) :
    Matrix2.apply (IntMatrix2.cast (mutation prime sign coefficient))
        (Vec2.affine value) =
      Vec2.scale (mutationDenominator prime coefficient value)
        (Vec2.affine (mutationMap prime sign coefficient value)) := by
  change 1 + (prime : Rat) * (coefficient : Rat) * value ≠ 0 at denominatorNonzero
  have denominatorCancel := Rat.mul_inv_cancel
    (1 + (prime : Rat) * (coefficient : Rat) * value)
    denominatorNonzero
  simp only [mutation, IntMatrix2.cast, Matrix2.apply, Vec2.affine,
    Vec2.scale, mutationDenominator, mutationMap, Rat.div_def,
    Rat.intCast_mul, Rat.intCast_natCast]
  congr 1 <;> grind

/-- The cast physical matrix acts by its five factors in the displayed
right-to-left order. -/
theorem physicalLetter_apply (prime sourcePhase targetPhase : Nat)
    (digit preCoefficient postCoefficient : Int) (postSign : Sign)
    (vector : Vec2) :
    Matrix2.apply
        (IntMatrix2.cast
          (physicalLetter prime sourcePhase targetPhase digit
            preCoefficient postSign postCoefficient)) vector =
      Matrix2.apply (IntMatrix2.cast (chart targetPhase))
        (Matrix2.apply
          (IntMatrix2.cast (mutation prime postSign postCoefficient))
          (Matrix2.apply (IntMatrix2.cast (deletion prime digit))
            (Matrix2.apply
              (IntMatrix2.cast
                (mutation prime .positive preCoefficient))
              (Matrix2.apply (IntMatrix2.cast (chartInverse sourcePhase))
                vector)))) := by
  simp only [physicalLetter, IntMatrix2.cast_mul, Matrix2.apply_mul]

def localLetterMap (prime : Nat) (digit preCoefficient : Int)
    (postSign : Sign) (postCoefficient : Int) (value : Rat) : Rat :=
  mutationMap prime postSign postCoefficient
    ((mutationMap prime .positive preCoefficient value - (digit : Rat)) /
      (prime : Rat))

/-- Exact affine action of one physical letter, including its nonzero
homogeneous scale. -/
theorem physicalLetter_affine_action
    (prime sourcePhase targetPhase : Nat)
    (digit preCoefficient postCoefficient : Int) (postSign : Sign)
    (value : Rat) (primePositive : 0 < prime)
    (preDenominatorNonzero :
      mutationDenominator prime preCoefficient value ≠ 0)
    (postDenominatorNonzero :
      mutationDenominator prime postCoefficient
        ((mutationMap prime .positive preCoefficient value - (digit : Rat)) /
          (prime : Rat)) ≠ 0) :
    Matrix2.apply
        (IntMatrix2.cast
          (physicalLetter prime sourcePhase targetPhase digit
            preCoefficient postSign postCoefficient))
        (Vec2.affine (value + (phaseShift sourcePhase : Rat))) =
      Vec2.scale
        (mutationDenominator prime preCoefficient value * (prime : Rat) *
          mutationDenominator prime postCoefficient
            ((mutationMap prime .positive preCoefficient value -
              (digit : Rat)) / (prime : Rat)))
        (Vec2.affine
          (localLetterMap prime digit preCoefficient postSign
            postCoefficient value + (phaseShift targetPhase : Rat))) := by
  rw [physicalLetter_apply, chartInverse_apply]
  have unchart :
      value + (phaseShift sourcePhase : Rat) -
        (phaseShift sourcePhase : Rat) = value := by grind
  rw [unchart,
    mutation_apply_scaled prime .positive preCoefficient value
      preDenominatorNonzero,
    Matrix2.apply_scale,
    deletion_apply_scaled digit
      (mutationMap prime .positive preCoefficient value) primePositive,
    Vec2.scale_assoc,
    Matrix2.apply_scale,
    mutation_apply_scaled prime postSign postCoefficient _
      postDenominatorNonzero,
    Vec2.scale_assoc,
    Matrix2.apply_scale,
    chart_apply]
  rfl

/-- Projective form of `physicalLetter_affine_action`. -/
theorem physicalLetter_affine_sameLine
    (prime sourcePhase targetPhase : Nat)
    (digit preCoefficient postCoefficient : Int) (postSign : Sign)
    (value : Rat) (primePositive : 0 < prime)
    (preDenominatorNonzero :
      mutationDenominator prime preCoefficient value ≠ 0)
    (postDenominatorNonzero :
      mutationDenominator prime postCoefficient
        ((mutationMap prime .positive preCoefficient value - (digit : Rat)) /
          (prime : Rat)) ≠ 0) :
    SameLine
      (Matrix2.apply
        (IntMatrix2.cast
          (physicalLetter prime sourcePhase targetPhase digit
            preCoefficient postSign postCoefficient))
        (Vec2.affine (value + (phaseShift sourcePhase : Rat))))
      (Vec2.affine
        (localLetterMap prime digit preCoefficient postSign
          postCoefficient value + (phaseShift targetPhase : Rat))) := by
  rw [physicalLetter_affine_action prime sourcePhase targetPhase digit
    preCoefficient postCoefficient postSign value primePositive
    preDenominatorNonzero postDenominatorNonzero]
  refine ⟨mutationDenominator prime preCoefficient value * (prime : Rat) *
      mutationDenominator prime postCoefficient
        ((mutationMap prime .positive preCoefficient value - (digit : Rat)) /
          (prime : Rat)), ?_, rfl⟩
  intro productZero
  rcases Rat.mul_eq_zero.mp productZero with firstProductZero | postZero
  · rcases Rat.mul_eq_zero.mp firstProductZero with preZero | primeZero
    · exact preDenominatorNonzero preZero
    · have naturalZero : prime = 0 := by
        exact_mod_cast primeZero
      omega
  · exact postDenominatorNonzero postZero

@[simp] theorem chart_det (phase : Nat) : (chart phase).det = 1 := by
  simp [chart, IntMatrix2.det]

@[simp] theorem chartInverse_det (phase : Nat) :
    (chartInverse phase).det = 1 := by
  simp [chartInverse, IntMatrix2.det]

@[simp] theorem deletion_det (prime : Nat) (digit : Int) :
    (deletion prime digit).det = prime := by
  simp [deletion, IntMatrix2.det]

@[simp] theorem mutation_det (prime : Nat) (sign : Sign)
    (coefficient : Int) :
    (mutation prime sign coefficient).det = sign.value := by
  simp [mutation, IntMatrix2.det]

/-- Every physical letter has determinant `p` or `-p`. -/
theorem physicalLetter_det (prime sourcePhase targetPhase : Nat)
    (digit : Int) (preCoefficient : Int) (postSign : Sign)
    (postCoefficient : Int) :
    (physicalLetter prime sourcePhase targetPhase digit preCoefficient
      postSign postCoefficient).det = postSign.value * prime := by
  simp [physicalLetter, IntMatrix2.det_mul, Sign.value]

theorem physicalLetter_det_cases (prime sourcePhase targetPhase : Nat)
    (digit : Int) (preCoefficient : Int) (postSign : Sign)
    (postCoefficient : Int) :
    (physicalLetter prime sourcePhase targetPhase digit preCoefficient
      postSign postCoefficient).det = prime ∨
    (physicalLetter prime sourcePhase targetPhase digit preCoefficient
      postSign postCoefficient).det = -(prime : Int) := by
  rw [physicalLetter_det]
  cases postSign <;> simp [Sign.value]

theorem physicalLetter_nonsingular {prime sourcePhase targetPhase : Nat}
    {digit preCoefficient postCoefficient : Int} {postSign : Sign}
    (primePositive : 0 < prime) :
    (physicalLetter prime sourcePhase targetPhase digit preCoefficient
      postSign postCoefficient).Nonsingular := by
  rw [IntMatrix2.Nonsingular, physicalLetter_det]
  cases postSign with
  | positive =>
    simp only [Sign.value, Int.one_mul]
    intro castZero
    have naturalZero := Int.ofNat_eq_zero.mp castZero
    omega
  | negative =>
    simp only [Sign.value, Int.neg_mul, Int.one_mul]
    intro negativeZero
    have castZero : (prime : Int) = 0 := by omega
    have naturalZero := Int.ofNat_eq_zero.mp castZero
    omega

end Mortality.Compiler
