import LeanWang.Kari.SignedPrimrec
import Mortality.SourceMachine.LeanWangMortality

/-!
# Paper-facing endpoint

This file collects the formal statements that correspond directly to the
main theorem and fixed-cardinality corollary in the companion paper.  The
construction itself remains factored into the source-machine, compiler, and
matrix modules.
-/

namespace Mortality.PaperTheorem

open Mortality
open Mortality.Compiler.FixedAllocation
open Mortality.OneCounter
open Mortality.PeriodicCode

/-- Integer vectors use their two entries as a primitive-recursive code. -/
def intVecEquiv : IntVec2 ≃ Int × Int where
  toFun vector := (vector.x, vector.y)
  invFun pair := ⟨pair.1, pair.2⟩
  left_inv := by intro vector; cases vector; rfl
  right_inv := by intro pair; cases pair; rfl

instance : Primcodable IntVec2 :=
  Primcodable.ofEquiv (Int × Int) intVecEquiv

/-- Integer matrices use their four entries as a primitive-recursive code. -/
def intMatrixEquiv : IntMatrix2 ≃ Int × Int × Int × Int where
  toFun matrix := (matrix.a, matrix.b, matrix.c, matrix.d)
  invFun tuple := ⟨tuple.1, tuple.2.1, tuple.2.2.1, tuple.2.2.2⟩
  left_inv := by intro matrix; cases matrix; rfl
  right_inv := by rintro ⟨a, b, c, d⟩; rfl

instance : Primcodable IntMatrix2 :=
  Primcodable.ofEquiv (Int × Int × Int × Int) intMatrixEquiv

private theorem intVecEquiv_primrec : Primrec intVecEquiv := by
  simpa [intVecEquiv] using
    (Primrec.of_equiv (e := intVecEquiv) : Primrec intVecEquiv)

private theorem intVecX_primrec : Primrec IntVec2.x :=
  Primrec.fst.comp intVecEquiv_primrec

private theorem intVecY_primrec : Primrec IntVec2.y :=
  Primrec.snd.comp intVecEquiv_primrec

private theorem natPow_primrec :
    Primrec₂ ((· ^ ·) : Nat → Nat → Nat) :=
  Primrec₂.unpaired'.1 Nat.Primrec.pow

/-- The fixed source vector whose rational line is the image of every
input-dependent rank-one matrix. -/
def fixedSource : IntVec2 :=
  Main.integerEncodedConfiguration zeroHaltConfiguration

/-- The input-dependent target vector whose rational line is the kernel of
the rank-one matrix. -/
def variableTarget (input : Nat) : IntVec2 :=
  Main.integerEncodedConfiguration (inputConfiguration input)

/-- The concrete rank-one matrix used for one input. -/
def variableMatrix (input : Nat) : IntMatrix2 :=
  integerRankOneMatrix fixedSource (variableTarget input)

private theorem integerDigitPolynomial_unaryDigits (base counter : Nat) :
    Compiler.integerDigitPolynomial base (unaryDigits counter) =
      (base : Int) ^ counter := by
  induction counter with
  | zero => simp [unaryDigits, Compiler.integerDigitPolynomial]
  | succ counter inductionHypothesis =>
      rw [show unaryDigits (counter + 1) = 0 :: unaryDigits counter by
        simp [unaryDigits, List.replicate_succ]]
      simp only [Compiler.integerDigitPolynomial, Int.zero_add]
      rw [inductionHypothesis, Int.pow_succ]
      exact Int.mul_comm _ _

private theorem boundaryPhase_one : boundaryPhase 1 = 0 := by decide

/-- The power that appears in the homogeneous target vector. -/
def targetPower (input : Nat) : Nat := 2 ^ input

private def targetNumerator (input : Nat) : Nat :=
  codingPrime ^ (targetPower input - 1)

private def targetDenominatorMagnitude (input : Nat) : Nat :=
  codingPrime ^ targetPower input

/-- A closed, primitive-recursive form of `variableTarget`. -/
private def effectiveVariableTarget (input : Nat) : IntVec2 :=
  let denominator : Int :=
    1 - (targetDenominatorMagnitude input : Int)
  { x := Int.ofNat (targetNumerator input) + denominator
    y := denominator }

private theorem variableTarget_eq_effective (input : Nat) :
    variableTarget input = effectiveVariableTarget input := by
  have targetPowerPositive : 0 < 2 ^ input := by simp
  have exponentEq : 2 ^ input - 1 + 1 = 2 ^ input := by omega
  simp [variableTarget, Main.integerEncodedConfiguration,
    inputConfiguration, effectiveVariableTarget, targetNumerator,
    targetDenominatorMagnitude, targetPower,
    integerDigitPolynomial_unaryDigits,
    Compiler.periodicIntegerDenominator, unaryDigits_length,
    boundaryPhase_one, Compiler.phaseShift, exponentEq]

private theorem effectiveVariableTarget_primrec :
    Primrec effectiveVariableTarget := by
  have hpower : Primrec targetPower :=
    natPow_primrec.comp (Primrec.const 2) Primrec.id
  have hnumeratorNat : Primrec targetNumerator :=
    natPow_primrec.comp (Primrec.const codingPrime)
      (Primrec.pred.comp hpower)
  have hdenominatorNat : Primrec targetDenominatorMagnitude :=
    natPow_primrec.comp (Primrec.const codingPrime) hpower
  have hnumerator : Primrec fun input =>
      Int.ofNat (targetNumerator input) :=
    LeanWang.Kari.SignedPrimrec.intOfNat.comp hnumeratorNat
  have hdenominator : Primrec fun input =>
      (1 : Int) - (targetDenominatorMagnitude input : Int) :=
    LeanWang.Kari.SignedPrimrec.intAdd.comp (Primrec.const 1)
      (LeanWang.Kari.SignedPrimrec.intNeg.comp
        (LeanWang.Kari.SignedPrimrec.intOfNat.comp hdenominatorNat))
  apply Primrec.of_equiv_iff intVecEquiv |>.mp
  exact Primrec.pair
    (LeanWang.Kari.SignedPrimrec.intAdd.comp hnumerator hdenominator)
    hdenominator

/-- The target vector is primitive recursive in the paper's natural-number
input. -/
theorem variableTarget_primrec : Primrec variableTarget := by
  exact effectiveVariableTarget_primrec.of_eq fun input =>
    (variableTarget_eq_effective input).symm

private theorem integerRankOneMatrix_primrec :
    Primrec₂ integerRankOneMatrix := by
  have hsx : Primrec fun pair : IntVec2 × IntVec2 => pair.1.x :=
    intVecX_primrec.comp Primrec.fst
  have hsy : Primrec fun pair : IntVec2 × IntVec2 => pair.1.y :=
    intVecY_primrec.comp Primrec.fst
  have htx : Primrec fun pair : IntVec2 × IntVec2 => pair.2.x :=
    intVecX_primrec.comp Primrec.snd
  have hty : Primrec fun pair : IntVec2 × IntVec2 => pair.2.y :=
    intVecY_primrec.comp Primrec.snd
  have ha := LeanWang.Kari.SignedPrimrec.intMul.comp hsx hty
  have hb := LeanWang.Kari.SignedPrimrec.intNeg.comp
    (LeanWang.Kari.SignedPrimrec.intMul.comp hsx htx)
  have hc := LeanWang.Kari.SignedPrimrec.intMul.comp hsy hty
  have hd := LeanWang.Kari.SignedPrimrec.intNeg.comp
    (LeanWang.Kari.SignedPrimrec.intMul.comp hsy htx)
  apply Primrec.of_equiv_iff intMatrixEquiv |>.mp
  exact Primrec.pair ha (Primrec.pair hb (Primrec.pair hc hd))

/-- The paper's input-to-matrix map is primitive recursive. -/
theorem variableMatrix_primrec : Primrec variableMatrix := by
  exact integerRankOneMatrix_primrec.comp
    (Primrec.const fixedSource) variableTarget_primrec

@[simp] theorem variableMatrix_eq_inputRankOneMatrix (input : Nat) :
    variableMatrix input = Main.inputRankOneMatrix input := by
  rfl

/-- Every output of the variable matrix lies on one fixed rational line.
Together with `variableMatrix_rankOne` and `fixedSource_nonzero`, this says
that its image is exactly that line. -/
theorem variableMatrix_fixed_image (input : Nat) (vector : Vec2) :
    Matrix2.apply (variableMatrix input).cast vector =
      Vec2.scale
        (Vec2.dot (targetRow (variableTarget input).cast) vector)
        fixedSource.cast := by
  exact Main.inputRankOneMatrix_fixed_image input vector

theorem fixedSource_nonzero : fixedSource.Nonzero := by
  exact Main.integerEncodedConfiguration_nonzero zeroHaltConfiguration

theorem variableTarget_nonzero (input : Nat) :
    (variableTarget input).Nonzero := by
  exact Main.integerEncodedConfiguration_nonzero (inputConfiguration input)

theorem variableMatrix_rankOne (input : Nat) :
    (variableMatrix input).RankOne := by
  exact Main.inputRankOneMatrix_rankOne input

theorem family_mortal_iff_u2Halts (input : Nat) :
    IntegerMortal (variableMatrix input :: listedMatrices) ↔
      SourceMachine.U2Halts input := by
  exact Main.mortalityFamily_iff_u2Halts input

/-- A matrix has the fixed image line used in the paper when it has rank one
and every output is a scalar multiple of `fixedSource`.  Since
`fixedSource` is nonzero, this is equality of image lines, not merely
containment. -/
def HasFixedImageLine (matrix : IntMatrix2) : Prop :=
  matrix.RankOne ∧
    ∀ vector, ∃ scalar,
      Matrix2.apply matrix.cast vector =
        Vec2.scale scalar fixedSource.cast

theorem variableMatrix_hasFixedImageLine (input : Nat) :
    HasFixedImageLine (variableMatrix input) := by
  constructor
  · exact variableMatrix_rankOne input
  · intro vector
    refine ⟨Vec2.dot (targetRow (variableTarget input).cast) vector, ?_⟩
    exact variableMatrix_fixed_image input vector

/-- There is no computable matrix-input predicate that decides mortality on
all rank-one matrices with the fixed image line.  This is the formal version
of the paper's main undecidability statement, rather than only a theorem
about an abstract natural-number parameter. -/
theorem no_computable_matrix_decider :
    ¬ ∃ accepts : IntMatrix2 → Prop,
      ComputablePred accepts ∧
      ∀ matrix, HasFixedImageLine matrix →
        (accepts matrix ↔
          IntegerMortal (matrix :: listedMatrices)) := by
  rintro ⟨accepts, acceptsComputable, acceptsCorrect⟩
  apply SourceMachine.LeanWangMortality.mortalityFamily_not_computable_unconditional
  apply ComputablePred.computable_of_manyOneReducible
    (q := accepts) (h₂ := acceptsComputable)
  exact ⟨variableMatrix, variableMatrix_primrec.to_comp, fun input =>
    (acceptsCorrect (variableMatrix input)
      (variableMatrix_hasFixedImageLine input)).symm⟩

/-- A single statement collecting the exact structural and undecidability
claims formalized for the paper: the coding prime is prime; the fixed family
contains 5,798 distinct nonsingular integer matrices of determinant `p` or
`-p`; the variable matrix has rank one and one fixed image line; every
instance contains exactly 5,799 distinct matrices; and mortality of this
parameterized family is not computable. -/
theorem paper_result :
    IsPrime codingPrime ∧
    listedMatrices.length = 5798 ∧
    listedMatrices.Nodup ∧
    (∀ matrix ∈ listedMatrices,
      matrix.Nonsingular ∧
        (matrix.det = codingPrime ∨
          matrix.det = -(codingPrime : Int))) ∧
    fixedSource.Nonzero ∧
    (∀ input, (variableTarget input).Nonzero) ∧
    (∀ input, (variableMatrix input).RankOne) ∧
    (∀ input vector,
      Matrix2.apply (variableMatrix input).cast vector =
        Vec2.scale
          (Vec2.dot (targetRow (variableTarget input).cast) vector)
          fixedSource.cast) ∧
    (∀ input,
      (variableMatrix input :: listedMatrices).length = 5799 ∧
      (variableMatrix input :: listedMatrices).Nodup) ∧
    Primrec variableMatrix ∧
    (∀ input,
      IntegerMortal (variableMatrix input :: listedMatrices) ↔
        SourceMachine.U2Halts input) ∧
    (¬ComputablePred fun input : Nat =>
      IntegerMortal (variableMatrix input :: listedMatrices)) ∧
    (¬ ∃ accepts : IntMatrix2 → Prop,
      ComputablePred accepts ∧
      ∀ matrix, HasFixedImageLine matrix →
        (accepts matrix ↔
          IntegerMortal (matrix :: listedMatrices))) := by
  refine ⟨codingPrime_isPrime, listedMatrices_length,
    Compiler.DistinctCertificate.listedMatrices_nodup, ?_,
    fixedSource_nonzero, variableTarget_nonzero, variableMatrix_rankOne,
    variableMatrix_fixed_image, ?_, variableMatrix_primrec,
    family_mortal_iff_u2Halts, ?_, no_computable_matrix_decider⟩
  · intro matrix matrixMem
    exact ⟨listedMatrices_nonsingular matrix matrixMem,
      listedMatrices_det_cases matrix matrixMem⟩
  · intro input
    exact ⟨Main.mortalityFamily_length input,
      Main.mortalityFamily_nodup input⟩
  · simpa [variableMatrix, fixedSource, variableTarget,
      Main.mortalityFamily, Main.inputRankOneMatrix] using
      SourceMachine.LeanWangMortality.mortalityFamily_not_computable_unconditional

end Mortality.PaperTheorem
