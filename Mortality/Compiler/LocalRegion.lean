import Mortality.Compiler.PhysicalLetter
import Mortality.Prime

/-!
# The projective local region and irreversible deletion errors

Instead of introducing a numerical `p`-adic valuation, we characterize
`Z_(p)` projectively.  A nonzero column is local at `p` when its line has
an integer representative whose second coordinate is not divisible by
`p`.  This definition includes finite rational points and excludes the
point at infinity.  It is particularly convenient for the integral
matrices used by the compiler.
-/

namespace Mortality.Compiler

def integerVector (numerator denominator : Int) : Vec2 :=
  { x := (numerator : Rat), y := (denominator : Rat) }

/-- Projective membership in the localization `Z_(p)`. -/
def LocalAt (prime : Nat) (vector : Vec2) : Prop :=
  vector.Nonzero ∧
    ∃ numerator denominator : Int,
      ¬(prime : Int) ∣ denominator ∧
      SameLine vector (integerVector numerator denominator)

def ErrorAt (prime : Nat) (vector : Vec2) : Prop :=
  vector.Nonzero ∧ ¬LocalAt prime vector

theorem LocalAt.of_sameLine {prime : Nat} {source target : Vec2}
    (sourceLocal : LocalAt prime source) (targetNonzero : target.Nonzero)
    (targetSame : SameLine target source) : LocalAt prime target := by
  rcases sourceLocal with ⟨_, numerator, denominator,
    denominatorNotDivisible, sourceSame⟩
  exact ⟨targetNonzero, numerator, denominator, denominatorNotDivisible,
    targetSame.trans sourceSame⟩

theorem LocalAt.y_ne_zero {prime : Nat} {vector : Vec2}
    (membership : LocalAt prime vector) : vector.y ≠ 0 := by
  rcases membership with ⟨_, numerator, denominator,
    denominatorNotDivisible, same⟩
  rcases same with ⟨scalar, scalarNonzero, vectorEq⟩
  rw [vectorEq]
  simp only [Vec2.scale, integerVector]
  intro productZero
  rcases Rat.mul_eq_zero.mp productZero with scalarZero | denominatorZero
  · exact scalarNonzero scalarZero
  · have integerZero : denominator = 0 := Rat.intCast_inj.mp denominatorZero
    subst denominator
    exact denominatorNotDivisible (Int.dvd_zero _)

theorem integerVector_nonzero_of_denominator {prime : Nat}
    {numerator denominator : Int}
    (denominatorNotDivisible : ¬(prime : Int) ∣ denominator) :
    (integerVector numerator denominator).Nonzero := by
  right
  simp only [integerVector]
  intro castZero
  have denominatorZero : denominator = 0 := Rat.intCast_inj.mp castZero
  subst denominator
  exact denominatorNotDivisible (Int.dvd_zero _)

theorem local_integerVector {prime : Nat} {numerator denominator : Int}
    (denominatorNotDivisible : ¬(prime : Int) ∣ denominator) :
    LocalAt prime (integerVector numerator denominator) := by
  constructor
  · exact integerVector_nonzero_of_denominator denominatorNotDivisible
  · exact ⟨numerator, denominator, denominatorNotDivisible,
      SameLine.refl _⟩

theorem sameLine_integerVector_cross_iff
    {firstNumerator firstDenominator secondNumerator secondDenominator : Int}
    (firstNonzero :
      (integerVector firstNumerator firstDenominator).Nonzero)
    (secondNonzero :
      (integerVector secondNumerator secondDenominator).Nonzero) :
    SameLine (integerVector firstNumerator firstDenominator)
        (integerVector secondNumerator secondDenominator) ↔
      firstNumerator * secondDenominator =
        firstDenominator * secondNumerator := by
  rw [sameLine_iff_dot_perp_eq_zero firstNonzero secondNonzero]
  simp only [Vec2.dot, Vec2.perp, integerVector]
  constructor
  · intro equality
    apply Rat.intCast_inj.mp
    grind
  · intro equality
    have castEquality := congrArg (fun value : Int => (value : Rat)) equality
    simp only [Rat.intCast_mul] at castEquality
    grind

theorem chart_apply_integerVector (phase : Nat)
    (numerator denominator : Int) :
    Matrix2.apply (IntMatrix2.cast (chart phase))
        (integerVector numerator denominator) =
      integerVector (numerator + phaseShift phase * denominator) denominator := by
  simp [chart, IntMatrix2.cast, Matrix2.apply, integerVector,
    Rat.intCast_add, Rat.intCast_mul]
  congr 1 <;> grind

theorem chartInverse_apply_integerVector (phase : Nat)
    (numerator denominator : Int) :
    Matrix2.apply (IntMatrix2.cast (chartInverse phase))
        (integerVector numerator denominator) =
      integerVector (numerator - phaseShift phase * denominator) denominator := by
  simp only [chartInverse, IntMatrix2.cast, Matrix2.apply, integerVector,
    Rat.intCast_sub, Rat.intCast_mul, Rat.intCast_neg]
  congr 1 <;> grind

theorem mutation_apply_integerVector (prime : Nat) (sign : Sign)
    (coefficient numerator denominator : Int) :
    Matrix2.apply (IntMatrix2.cast (mutation prime sign coefficient))
        (integerVector numerator denominator) =
      integerVector (sign.value * numerator)
        ((prime : Int) * coefficient * numerator + denominator) := by
  simp [mutation, IntMatrix2.cast, Matrix2.apply, integerVector,
    Rat.intCast_mul, Rat.intCast_add, Rat.intCast_natCast]
  congr 1 <;> grind

theorem deletion_apply_integerVector (prime : Nat) (digit : Int)
    (numerator denominator : Int) :
    Matrix2.apply (IntMatrix2.cast (deletion prime digit))
        (integerVector numerator denominator) =
      integerVector (numerator - digit * denominator)
        ((prime : Int) * denominator) := by
  simp only [deletion, IntMatrix2.cast, Matrix2.apply, integerVector,
    Rat.intCast_neg, Rat.intCast_natCast, Rat.intCast_sub, Rat.intCast_mul]
  congr 1 <;> grind

private theorem chart_cast_nonsingular (phase : Nat) :
    (IntMatrix2.cast (chart phase)).Nonsingular := by
  apply IntMatrix2.cast_nonsingular
  rw [IntMatrix2.Nonsingular, chart_det]
  decide

private theorem chartInverse_cast_nonsingular (phase : Nat) :
    (IntMatrix2.cast (chartInverse phase)).Nonsingular := by
  apply IntMatrix2.cast_nonsingular
  rw [IntMatrix2.Nonsingular, chartInverse_det]
  decide

private theorem mutation_cast_nonsingular (prime : Nat) (sign : Sign)
    (coefficient : Int) :
    (IntMatrix2.cast (mutation prime sign coefficient)).Nonsingular := by
  apply IntMatrix2.cast_nonsingular
  rw [IntMatrix2.Nonsingular, mutation_det]
  cases sign <;> decide

private theorem deletion_cast_nonsingular {prime : Nat} (digit : Int)
    (primePositive : 0 < prime) :
    (IntMatrix2.cast (deletion prime digit)).Nonsingular := by
  apply IntMatrix2.cast_nonsingular
  rw [IntMatrix2.Nonsingular, deletion_det]
  intro primeZero
  have naturalZero := Int.ofNat_eq_zero.mp primeZero
  omega

theorem local_chart_iff (prime phase : Nat) (vector : Vec2) :
    LocalAt prime
        (Matrix2.apply (IntMatrix2.cast (chart phase)) vector) ↔
      LocalAt prime vector := by
  constructor
  · intro outputLocal
    rcases outputLocal with ⟨outputNonzero, numerator, denominator,
      denominatorNotDivisible, outputSame⟩
    have pulledSame := outputSame.apply
      (IntMatrix2.cast (chartInverse phase))
    rw [← Matrix2.apply_mul, ← IntMatrix2.cast_mul,
      chartInverse_mul_chart, IntMatrix2.cast_identity,
      Matrix2.apply_identity] at pulledSame
    rw [chartInverse_apply_integerVector] at pulledSame
    constructor
    · have pulledNonzero := Matrix2.apply_nonzero
        (chartInverse_cast_nonsingular phase) outputNonzero
      rw [← Matrix2.apply_mul, ← IntMatrix2.cast_mul,
        chartInverse_mul_chart, IntMatrix2.cast_identity,
        Matrix2.apply_identity] at pulledNonzero
      exact pulledNonzero
    · exact ⟨numerator - phaseShift phase * denominator, denominator,
        denominatorNotDivisible, pulledSame⟩
  · intro inputLocal
    rcases inputLocal with ⟨inputNonzero, numerator, denominator,
      denominatorNotDivisible, inputSame⟩
    have pushedSame := inputSame.apply (IntMatrix2.cast (chart phase))
    rw [chart_apply_integerVector] at pushedSame
    constructor
    · exact Matrix2.apply_nonzero (chart_cast_nonsingular phase) inputNonzero
    · exact ⟨numerator + phaseShift phase * denominator, denominator,
        denominatorNotDivisible, pushedSame⟩

theorem local_chartInverse_iff (prime phase : Nat) (vector : Vec2) :
    LocalAt prime
        (Matrix2.apply (IntMatrix2.cast (chartInverse phase)) vector) ↔
      LocalAt prime vector := by
  constructor
  · intro outputLocal
    rcases outputLocal with ⟨outputNonzero, numerator, denominator,
      denominatorNotDivisible, outputSame⟩
    have pulledSame := outputSame.apply (IntMatrix2.cast (chart phase))
    rw [← Matrix2.apply_mul, ← IntMatrix2.cast_mul,
      chart_mul_inverse, IntMatrix2.cast_identity,
      Matrix2.apply_identity] at pulledSame
    rw [chart_apply_integerVector] at pulledSame
    constructor
    · have pulledNonzero := Matrix2.apply_nonzero
        (chart_cast_nonsingular phase) outputNonzero
      rw [← Matrix2.apply_mul, ← IntMatrix2.cast_mul,
        chart_mul_inverse, IntMatrix2.cast_identity,
        Matrix2.apply_identity] at pulledNonzero
      exact pulledNonzero
    · exact ⟨numerator + phaseShift phase * denominator, denominator,
        denominatorNotDivisible, pulledSame⟩
  · intro inputLocal
    rcases inputLocal with ⟨inputNonzero, numerator, denominator,
      denominatorNotDivisible, inputSame⟩
    have pushedSame := inputSame.apply
      (IntMatrix2.cast (chartInverse phase))
    rw [chartInverse_apply_integerVector] at pushedSame
    constructor
    · exact Matrix2.apply_nonzero (chartInverse_cast_nonsingular phase)
        inputNonzero
    · exact ⟨numerator - phaseShift phase * denominator, denominator,
        denominatorNotDivisible, pushedSame⟩

theorem local_mutation_forward {prime : Nat} (sign : Sign)
    (coefficient : Int) {vector : Vec2} (inputLocal : LocalAt prime vector) :
    LocalAt prime
      (Matrix2.apply (IntMatrix2.cast (mutation prime sign coefficient))
        vector) := by
  rcases inputLocal with ⟨inputNonzero, numerator, denominator,
    denominatorNotDivisible, inputSame⟩
  have outputSame := inputSame.apply
    (IntMatrix2.cast (mutation prime sign coefficient))
  rw [mutation_apply_integerVector] at outputSame
  have newDenominatorNotDivisible :
      ¬(prime : Int) ∣
        (prime : Int) * coefficient * numerator + denominator := by
    intro dividesNew
    apply denominatorNotDivisible
    have dividesFirst : (prime : Int) ∣
        (prime : Int) * coefficient * numerator := by
      exact ⟨coefficient * numerator, by grind⟩
    have dividesDifference := Int.dvd_sub dividesNew dividesFirst
    have differenceEq :
        (prime : Int) * coefficient * numerator + denominator -
          (prime : Int) * coefficient * numerator = denominator := by
      grind
    rw [differenceEq] at dividesDifference
    exact dividesDifference
  constructor
  · exact Matrix2.apply_nonzero
      (mutation_cast_nonsingular prime sign coefficient) inputNonzero
  · exact ⟨sign.value * numerator,
      (prime : Int) * coefficient * numerator + denominator,
      newDenominatorNotDivisible, outputSame⟩

/-- A safe mutation has no pole on the local region. -/
theorem mutationDenominator_ne_zero_of_local {prime : Nat}
    (coefficient : Int) {value : Rat}
    (inputLocal : LocalAt prime (Vec2.affine value)) :
    mutationDenominator prime coefficient value ≠ 0 := by
  have outputLocal := local_mutation_forward (.positive) coefficient inputLocal
  have outputYNonzero := outputLocal.y_ne_zero
  intro denominatorZero
  apply outputYNonzero
  simp only [mutation, IntMatrix2.cast, Matrix2.apply, Vec2.affine,
    Rat.intCast_mul, Rat.intCast_natCast]
  unfold mutationDenominator at denominatorZero
  grind

/-- A safe mutation sends a finite local affine point to the finite local
point described by its rational map. -/
theorem mutationMap_local_of_local {prime : Nat} (sign : Sign)
    (coefficient : Int) {value : Rat}
    (inputLocal : LocalAt prime (Vec2.affine value)) :
    LocalAt prime
      (Vec2.affine (mutationMap prime sign coefficient value)) := by
  have denominatorNonzero := mutationDenominator_ne_zero_of_local
    coefficient inputLocal
  have matrixLocal := local_mutation_forward sign coefficient inputLocal
  have matrixSame : SameLine
      (Matrix2.apply (IntMatrix2.cast (mutation prime sign coefficient))
        (Vec2.affine value))
      (Vec2.affine (mutationMap prime sign coefficient value)) := by
    rw [mutation_apply_scaled prime sign coefficient value denominatorNonzero]
    exact ⟨mutationDenominator prime coefficient value,
      denominatorNonzero, rfl⟩
  exact LocalAt.of_sameLine matrixLocal (Vec2.affine_nonzero _)
    matrixSame.symm

/-- A physical letter realizes its advertised local rational map whenever
the values before and after deletion are local. -/
theorem physicalLetter_affine_sameLine_of_local
    {prime sourcePhase targetPhase : Nat}
    {digit preCoefficient postCoefficient : Int} {postSign : Sign}
    {value : Rat} (primePositive : 0 < prime)
    (inputLocal : LocalAt prime (Vec2.affine value))
    (deletedLocal :
      LocalAt prime
        (Vec2.affine
          ((mutationMap prime .positive preCoefficient value -
            (digit : Rat)) / (prime : Rat)))) :
    SameLine
      (Matrix2.apply
        (IntMatrix2.cast
          (physicalLetter prime sourcePhase targetPhase digit
            preCoefficient postSign postCoefficient))
        (Vec2.affine (value + (phaseShift sourcePhase : Rat))))
      (Vec2.affine
        (localLetterMap prime digit preCoefficient postSign
          postCoefficient value + (phaseShift targetPhase : Rat))) := by
  apply physicalLetter_affine_sameLine prime sourcePhase targetPhase digit
    preCoefficient postCoefficient postSign value primePositive
  · exact mutationDenominator_ne_zero_of_local preCoefficient inputLocal
  · exact mutationDenominator_ne_zero_of_local postCoefficient deletedLocal

def inverseMutationCoefficient (sign : Sign) (coefficient : Int) : Int :=
  match sign with
  | .positive => -coefficient
  | .negative => coefficient

@[simp] theorem inverseMutation_mul_mutation (prime : Nat) (sign : Sign)
    (coefficient : Int) :
    IntMatrix2.mul
        (mutation prime sign (inverseMutationCoefficient sign coefficient))
        (mutation prime sign coefficient) = IntMatrix2.identity := by
  cases sign <;>
    simp [inverseMutationCoefficient, mutation, Sign.value,
      IntMatrix2.mul, IntMatrix2.identity] <;>
    congr 1 <;> grind

/-- Mutations preserve the local region in both directions. -/
theorem local_mutation_iff (prime : Nat) (sign : Sign)
    (coefficient : Int) (vector : Vec2) :
    LocalAt prime
        (Matrix2.apply (IntMatrix2.cast (mutation prime sign coefficient))
          vector) ↔
      LocalAt prime vector := by
  constructor
  · intro outputLocal
    have pulledLocal := local_mutation_forward sign
      (inverseMutationCoefficient sign coefficient) outputLocal
    rw [← Matrix2.apply_mul, ← IntMatrix2.cast_mul,
      inverseMutation_mul_mutation, IntMatrix2.cast_identity,
      Matrix2.apply_identity] at pulledLocal
    exact pulledLocal
  · exact local_mutation_forward sign coefficient

theorem chart_preserves_error (prime phase : Nat) {vector : Vec2}
    (inputError : ErrorAt prime vector) :
    ErrorAt prime
      (Matrix2.apply (IntMatrix2.cast (chart phase)) vector) := by
  constructor
  · exact Matrix2.apply_nonzero (chart_cast_nonsingular phase)
      inputError.1
  · intro outputLocal
    exact inputError.2 ((local_chart_iff prime phase vector).mp outputLocal)

theorem chartInverse_preserves_error (prime phase : Nat) {vector : Vec2}
    (inputError : ErrorAt prime vector) :
    ErrorAt prime
      (Matrix2.apply (IntMatrix2.cast (chartInverse phase)) vector) := by
  constructor
  · exact Matrix2.apply_nonzero (chartInverse_cast_nonsingular phase)
      inputError.1
  · intro outputLocal
    exact inputError.2
      ((local_chartInverse_iff prime phase vector).mp outputLocal)

theorem mutation_preserves_error (prime : Nat) (sign : Sign)
    (coefficient : Int) {vector : Vec2} (inputError : ErrorAt prime vector) :
    ErrorAt prime
      (Matrix2.apply (IntMatrix2.cast (mutation prime sign coefficient))
        vector) := by
  constructor
  · exact Matrix2.apply_nonzero
      (mutation_cast_nonsingular prime sign coefficient) inputError.1
  · intro outputLocal
    exact inputError.2
      ((local_mutation_iff prime sign coefficient vector).mp outputLocal)

/-- The integral projective inverse of a digit deletion. -/
def deletionRecovery (prime : Nat) (digit : Int) : IntMatrix2 :=
  { a := prime, b := digit, c := 0, d := 1 }

theorem deletionRecovery_apply_integerVector (prime : Nat) (digit : Int)
    (numerator denominator : Int) :
    Matrix2.apply (IntMatrix2.cast (deletionRecovery prime digit))
        (integerVector numerator denominator) =
      integerVector
        ((prime : Int) * numerator + digit * denominator) denominator := by
  simp only [deletionRecovery, IntMatrix2.cast, Matrix2.apply, integerVector,
    Rat.intCast_natCast, Rat.intCast_add, Rat.intCast_mul]
  congr 1 <;> grind

private theorem deletionRecovery_cast_nonsingular {prime : Nat}
    (digit : Int) (primePositive : 0 < prime) :
    (IntMatrix2.cast (deletionRecovery prime digit)).Nonsingular := by
  apply IntMatrix2.cast_nonsingular
  rw [IntMatrix2.Nonsingular]
  simp only [deletionRecovery, IntMatrix2.det]
  intro primeZero
  have primeZero' : (prime : Int) = 0 := by grind
  have naturalZero := Int.ofNat_eq_zero.mp primeZero'
  omega

theorem local_deletionRecovery_forward {prime : Nat} (digit : Int)
    (primePositive : 0 < prime) {vector : Vec2}
    (inputLocal : LocalAt prime vector) :
    LocalAt prime
      (Matrix2.apply (IntMatrix2.cast (deletionRecovery prime digit))
        vector) := by
  rcases inputLocal with ⟨inputNonzero, numerator, denominator,
    denominatorNotDivisible, inputSame⟩
  have outputSame := inputSame.apply
    (IntMatrix2.cast (deletionRecovery prime digit))
  rw [deletionRecovery_apply_integerVector] at outputSame
  constructor
  · exact Matrix2.apply_nonzero
      (deletionRecovery_cast_nonsingular digit primePositive) inputNonzero
  · exact ⟨(prime : Int) * numerator + digit * denominator,
      denominator, denominatorNotDivisible, outputSame⟩

theorem deletionRecovery_after_deletion (prime : Nat) (digit : Int)
    (vector : Vec2) :
    Matrix2.apply (IntMatrix2.cast (deletionRecovery prime digit))
        (Matrix2.apply (IntMatrix2.cast (deletion prime digit)) vector) =
      Vec2.scale (prime : Rat) vector := by
  cases vector
  simp only [deletionRecovery, deletion, IntMatrix2.cast, Matrix2.apply,
    Vec2.scale, Rat.intCast_natCast, Rat.intCast_neg]
  congr 1 <;> grind

/-- If a deletion output is local, then its input was already local. -/
theorem local_of_deletion_local {prime : Nat} (digit : Int)
    (primePositive : 0 < prime) {vector : Vec2}
    (inputNonzero : vector.Nonzero)
    (outputLocal : LocalAt prime
      (Matrix2.apply (IntMatrix2.cast (deletion prime digit)) vector)) :
    LocalAt prime vector := by
  have recoveredLocal := local_deletionRecovery_forward digit primePositive
    outputLocal
  rw [deletionRecovery_after_deletion] at recoveredLocal
  have primeNonzero : (prime : Rat) ≠ 0 := by
    simpa using (show prime ≠ 0 by omega)
  apply LocalAt.of_sameLine recoveredLocal inputNonzero
  refine ⟨(prime : Rat)⁻¹, ?_, ?_⟩
  · intro inverseZero
    have inverseCancel := Rat.inv_mul_cancel (prime : Rat) primeNonzero
    rw [inverseZero, Rat.zero_mul] at inverseCancel
    contradiction
  · rw [Vec2.scale_assoc, Rat.inv_mul_cancel _ primeNonzero,
      Vec2.scale_one]

/-- A digit deletion cannot repair a projective point outside the local
region. -/
theorem deletion_preserves_error {prime : Nat} (digit : Int)
    (primePositive : 0 < prime) {vector : Vec2}
    (inputError : ErrorAt prime vector) :
    ErrorAt prime
      (Matrix2.apply (IntMatrix2.cast (deletion prime digit)) vector) := by
  constructor
  · exact Matrix2.apply_nonzero
      (deletion_cast_nonsingular digit primePositive) inputError.1
  · intro outputLocal
    exact inputError.2
      (local_of_deletion_local digit primePositive inputError.1 outputLocal)

/-- Every complete physical letter preserves the error region. -/
theorem physicalLetter_preserves_error {prime : Nat}
    (sourcePhase targetPhase : Nat) (digit preCoefficient : Int)
    (postSign : Sign) (postCoefficient : Int)
    (primePositive : 0 < prime) {vector : Vec2}
    (inputError : ErrorAt prime vector) :
    ErrorAt prime
      (Matrix2.apply
        (IntMatrix2.cast
          (physicalLetter prime sourcePhase targetPhase digit
            preCoefficient postSign postCoefficient)) vector) := by
  rw [physicalLetter_apply]
  exact chart_preserves_error prime targetPhase
    (mutation_preserves_error prime postSign postCoefficient
      (deletion_preserves_error digit primePositive
        (mutation_preserves_error prime .positive preCoefficient
          (chartInverse_preserves_error prime sourcePhase inputError))))

/-- Exact digit check: on a local integer representative, deletion stays
local exactly when the represented residue equals the requested digit. -/
theorem deletion_local_iff_dvd {prime : Nat}
    (primeProperty : IsPrime prime) (digit : Int) {vector : Vec2}
    (inputNonzero : vector.Nonzero) {numerator denominator : Int}
    (denominatorNotDivisible : ¬(prime : Int) ∣ denominator)
    (inputSame : SameLine vector (integerVector numerator denominator)) :
    LocalAt prime
        (Matrix2.apply (IntMatrix2.cast (deletion prime digit)) vector) ↔
      (prime : Int) ∣ numerator - digit * denominator := by
  have primePositive : 0 < prime := by
    unfold IsPrime at primeProperty
    omega
  have primeRatNonzero : (prime : Rat) ≠ 0 := by
    simpa using (show prime ≠ 0 by omega)
  constructor
  · intro outputLocal
    rcases outputLocal with ⟨_, otherNumerator, otherDenominator,
      otherDenominatorNotDivisible, outputSame⟩
    have representedOutput := inputSame.apply
      (IntMatrix2.cast (deletion prime digit))
    rw [deletion_apply_integerVector] at representedOutput
    have canonicalSame :
        SameLine
          (integerVector (numerator - digit * denominator)
            ((prime : Int) * denominator))
          (integerVector otherNumerator otherDenominator) :=
      representedOutput.symm.trans outputSame
    have inputIntegerNonzero :=
      integerVector_nonzero_of_denominator (numerator := numerator)
        denominatorNotDivisible
    have canonicalNonzero :
        (integerVector (numerator - digit * denominator)
          ((prime : Int) * denominator)).Nonzero := by
      rw [← deletion_apply_integerVector]
      exact Matrix2.apply_nonzero
        (deletion_cast_nonsingular digit primePositive) inputIntegerNonzero
    have otherNonzero := integerVector_nonzero_of_denominator
      (numerator := otherNumerator) otherDenominatorNotDivisible
    have cross := (sameLine_integerVector_cross_iff canonicalNonzero
      otherNonzero).mp canonicalSame
    have dividesProduct : (prime : Int) ∣
        (numerator - digit * denominator) * otherDenominator := by
      refine ⟨denominator * otherNumerator, ?_⟩
      grind
    rcases primeProperty.int_dvd_mul dividesProduct with
      dividesNumerator | dividesOtherDenominator
    · exact dividesNumerator
    · exact False.elim
        (otherDenominatorNotDivisible dividesOtherDenominator)
  · intro dividesNumerator
    rcases dividesNumerator with ⟨quotient, quotientEq⟩
    have representedOutput := inputSame.apply
      (IntMatrix2.cast (deletion prime digit))
    rw [deletion_apply_integerVector] at representedOutput
    have canonicalSame :
        SameLine
          (integerVector (numerator - digit * denominator)
            ((prime : Int) * denominator))
          (integerVector quotient denominator) := by
      refine ⟨(prime : Rat), primeRatNonzero, ?_⟩
      rw [quotientEq]
      simp [integerVector, Vec2.scale, Rat.intCast_mul,
        Rat.intCast_natCast]
    constructor
    · exact Matrix2.apply_nonzero
        (deletion_cast_nonsingular digit primePositive) inputNonzero
    · exact ⟨quotient, denominator, denominatorNotDivisible,
        representedOutput.trans canonicalSame⟩

end Mortality.Compiler
