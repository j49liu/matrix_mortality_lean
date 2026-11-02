import Mortality.Compiler.LocalRegion
import Mortality.Compiler.PhaseGuard

/-!
# Kernel-checked phase and digit enforcement

This file proves the semantic half of the phase-guard lemma.  The input
is an explicitly represented local projective point in an actual phase.
If an arbitrary physical letter has local output, its advertised source
phase and deletion digit must be the actual ones.
-/

namespace Mortality.Compiler

def phaseAffine (phase : Nat) (value : Rat) : Vec2 :=
  Vec2.affine (value + (phaseShift phase : Rat))

def phasePoint (phase : Nat) (numerator denominator : Int) : Vec2 :=
  Matrix2.apply (IntMatrix2.cast (chart phase))
    (integerVector numerator denominator)

theorem phasePoint_eq_integerVector (phase : Nat)
    (numerator denominator : Int) :
    phasePoint phase numerator denominator =
      integerVector (numerator + phaseShift phase * denominator)
        denominator :=
  chart_apply_integerVector phase numerator denominator

/-- Two local integer points in reserved phase blocks can represent the
same projective line only when both their phases and their local residues
agree.  This is the endpoint form of phase enforcement, independent of
any next physical letter. -/
theorem phasePoint_sameLine_phase_digit_unique
    {prime phaseCount firstPhase secondPhase : Nat}
    {firstDigit secondDigit firstNumerator firstDenominator
      secondNumerator secondDenominator : Int}
    (primeProperty : IsPrime prime)
    (primeBound : 6 * phaseCount < prime)
    (firstPhaseBound : firstPhase < phaseCount)
    (secondPhaseBound : secondPhase < phaseCount)
    (firstReserved : ReservedDigit firstDigit)
    (secondReserved : ReservedDigit secondDigit)
    (firstDenominatorNotDivisible :
      ¬(prime : Int) ∣ firstDenominator)
    (secondDenominatorNotDivisible :
      ¬(prime : Int) ∣ secondDenominator)
    (firstResidue :
      (prime : Int) ∣ firstNumerator - firstDigit * firstDenominator)
    (secondResidue :
      (prime : Int) ∣ secondNumerator - secondDigit * secondDenominator)
    (same : SameLine
      (phasePoint firstPhase firstNumerator firstDenominator)
      (phasePoint secondPhase secondNumerator secondDenominator)) :
    firstPhase = secondPhase ∧ firstDigit = secondDigit := by
  rw [phasePoint_eq_integerVector, phasePoint_eq_integerVector] at same
  have firstNonzero := integerVector_nonzero_of_denominator
    (numerator := firstNumerator +
      phaseShift firstPhase * firstDenominator)
    firstDenominatorNotDivisible
  have secondNonzero := integerVector_nonzero_of_denominator
    (numerator := secondNumerator +
      phaseShift secondPhase * secondDenominator)
    secondDenominatorNotDivisible
  have cross := (sameLine_integerVector_cross_iff firstNonzero
    secondNonzero).mp same
  rcases firstResidue with ⟨firstFactor, firstEq⟩
  rcases secondResidue with ⟨secondFactor, secondEq⟩
  have productDivisible : (prime : Int) ∣
      (phaseResidue firstPhase firstDigit -
        phaseResidue secondPhase secondDigit) *
        firstDenominator * secondDenominator := by
    refine ⟨secondFactor * firstDenominator -
      firstFactor * secondDenominator, ?_⟩
    unfold phaseResidue
    grind
  have firstProductDivisible : (prime : Int) ∣
      (phaseResidue firstPhase firstDigit -
        phaseResidue secondPhase secondDigit) * firstDenominator := by
    rcases primeProperty.int_dvd_mul productDivisible with
      firstProductDivides | secondDenominatorDivides
    · exact firstProductDivides
    · exact False.elim
        (secondDenominatorNotDivisible secondDenominatorDivides)
  have residueDifferenceDivisible : (prime : Int) ∣
      phaseResidue firstPhase firstDigit -
        phaseResidue secondPhase secondDigit := by
    rcases primeProperty.int_dvd_mul firstProductDivisible with
      differenceDivides | firstDenominatorDivides
    · exact differenceDivides
    · exact False.elim
        (firstDenominatorNotDivisible firstDenominatorDivides)
  have congruent :
      phaseResidue firstPhase firstDigit % (prime : Int) =
        phaseResidue secondPhase secondDigit % (prime : Int) := by
    rw [Int.emod_eq_emod_iff_emod_sub_eq_zero]
    exact Int.emod_eq_zero_of_dvd residueDifferenceDivisible
  exact phase_digit_unique primeBound firstPhaseBound secondPhaseBound
    firstReserved secondReserved congruent

/-- Affine-coordinate wrapper for endpoint phase-and-digit uniqueness. -/
theorem phaseAffine_sameLine_phase_digit_unique
    {prime phaseCount firstPhase secondPhase : Nat}
    {firstDigit secondDigit firstNumerator firstDenominator
      secondNumerator secondDenominator : Int}
    {firstValue secondValue : Rat}
    (primeProperty : IsPrime prime)
    (primeBound : 6 * phaseCount < prime)
    (firstPhaseBound : firstPhase < phaseCount)
    (secondPhaseBound : secondPhase < phaseCount)
    (firstReserved : ReservedDigit firstDigit)
    (secondReserved : ReservedDigit secondDigit)
    (firstDenominatorNotDivisible :
      ¬(prime : Int) ∣ firstDenominator)
    (secondDenominatorNotDivisible :
      ¬(prime : Int) ∣ secondDenominator)
    (firstResidue :
      (prime : Int) ∣ firstNumerator - firstDigit * firstDenominator)
    (secondResidue :
      (prime : Int) ∣ secondNumerator - secondDigit * secondDenominator)
    (firstValueSame : SameLine (Vec2.affine firstValue)
      (integerVector firstNumerator firstDenominator))
    (secondValueSame : SameLine (Vec2.affine secondValue)
      (integerVector secondNumerator secondDenominator))
    (same : SameLine (phaseAffine firstPhase firstValue)
      (phaseAffine secondPhase secondValue)) :
    firstPhase = secondPhase ∧ firstDigit = secondDigit := by
  have firstChart := firstValueSame.apply (IntMatrix2.cast (chart firstPhase))
  have secondChart := secondValueSame.apply
    (IntMatrix2.cast (chart secondPhase))
  rw [chart_apply] at firstChart secondChart
  change SameLine (phaseAffine firstPhase firstValue)
    (phasePoint firstPhase firstNumerator firstDenominator) at firstChart
  change SameLine (phaseAffine secondPhase secondValue)
    (phasePoint secondPhase secondNumerator secondDenominator) at secondChart
  apply phasePoint_sameLine_phase_digit_unique primeProperty primeBound
    firstPhaseBound secondPhaseBound firstReserved secondReserved
    firstDenominatorNotDivisible secondDenominatorNotDivisible firstResidue
    secondResidue
  exact firstChart.symm.trans (same.trans secondChart)

/-- A projective vector lies in one guarded phase block with the stated
reserved local residue. -/
def InPhaseAt (prime phase : Nat) (digit : Int) (vector : Vec2) : Prop :=
  ReservedDigit digit ∧
    ∃ numerator denominator : Int,
      ¬(prime : Int) ∣ denominator ∧
      (prime : Int) ∣ numerator - digit * denominator ∧
      SameLine vector (phasePoint phase numerator denominator)

/-- Membership in a guarded phase block supplies the ordinary locality
needed by the error-irreversibility argument. -/
theorem InPhaseAt.local {prime phase : Nat} {digit : Int} {vector : Vec2}
    (membership : InPhaseAt prime phase digit vector) :
    LocalAt prime vector := by
  rcases membership with
    ⟨_, numerator, denominator, denominatorNotDivisible, _, same⟩
  have pointLocal : LocalAt prime (phasePoint phase numerator denominator) := by
    rw [phasePoint_eq_integerVector]
    exact local_integerVector denominatorNotDivisible
  have vectorNonzero : vector.Nonzero := by
    rcases same with ⟨scalar, scalarNonzero, vectorEq⟩
    rw [vectorEq]
    exact Vec2.scale_nonzero scalarNonzero pointLocal.1
  exact LocalAt.of_sameLine pointLocal vectorNonzero same

theorem inPhaseAt_phaseAffine_integer
    {prime phase : Nat} {digit numerator denominator : Int} {value : Rat}
    (reserved : ReservedDigit digit)
    (denominatorNotDivisible : ¬(prime : Int) ∣ denominator)
    (residue : (prime : Int) ∣ numerator - digit * denominator)
    (valueSame : SameLine (Vec2.affine value)
      (integerVector numerator denominator)) :
    InPhaseAt prime phase digit (phaseAffine phase value) := by
  refine ⟨reserved, numerator, denominator, denominatorNotDivisible,
    residue, ?_⟩
  have charted := valueSame.apply (IntMatrix2.cast (chart phase))
  rw [chart_apply] at charted
  change SameLine (phaseAffine phase value)
    (phasePoint phase numerator denominator) at charted
  exact charted

theorem InPhaseAt.unique
    {prime phaseCount firstPhase secondPhase : Nat}
    {firstDigit secondDigit : Int} {firstVector secondVector : Vec2}
    (primeProperty : IsPrime prime)
    (primeBound : 6 * phaseCount < prime)
    (firstPhaseBound : firstPhase < phaseCount)
    (secondPhaseBound : secondPhase < phaseCount)
    (firstMembership : InPhaseAt prime firstPhase firstDigit firstVector)
    (secondMembership : InPhaseAt prime secondPhase secondDigit secondVector)
    (same : SameLine firstVector secondVector) :
    firstPhase = secondPhase ∧ firstDigit = secondDigit := by
  rcases firstMembership with
    ⟨firstReserved, firstNumerator, firstDenominator,
      firstDenominatorNotDivisible, firstResidue, firstSame⟩
  rcases secondMembership with
    ⟨secondReserved, secondNumerator, secondDenominator,
      secondDenominatorNotDivisible, secondResidue, secondSame⟩
  apply phasePoint_sameLine_phase_digit_unique primeProperty primeBound
    firstPhaseBound secondPhaseBound firstReserved secondReserved
    firstDenominatorNotDivisible secondDenominatorNotDivisible firstResidue
    secondResidue
  exact firstSame.symm.trans (same.trans secondSame)

/-- The full phase-guard conclusion for one arbitrary physical letter. -/
theorem physicalLetter_source_digit_unique
    {prime phaseCount actualPhase sourcePhase targetPhase : Nat}
    {actualDigit letterDigit preCoefficient postCoefficient : Int}
    {postSign : Sign} {numerator denominator : Int}
    (primeProperty : IsPrime prime)
    (primeBound : 6 * phaseCount < prime)
    (actualPhaseBound : actualPhase < phaseCount)
    (sourcePhaseBound : sourcePhase < phaseCount)
    (actualReserved : ReservedDigit actualDigit)
    (letterReserved : ReservedDigit letterDigit)
    (denominatorNotDivisible : ¬(prime : Int) ∣ denominator)
    (actualResidue :
      (prime : Int) ∣ numerator - actualDigit * denominator)
    (outputLocal :
      LocalAt prime
        (Matrix2.apply
          (IntMatrix2.cast
            (physicalLetter prime sourcePhase targetPhase letterDigit
              preCoefficient postSign postCoefficient))
          (phasePoint actualPhase numerator denominator))) :
    actualPhase = sourcePhase ∧ actualDigit = letterDigit := by
  let preNumerator : Int :=
    numerator + (phaseShift actualPhase - phaseShift sourcePhase) * denominator
  let preDenominator : Int :=
    (prime : Int) * preCoefficient * preNumerator + denominator
  have unchartEq :
      Matrix2.apply (IntMatrix2.cast (chartInverse sourcePhase))
          (phasePoint actualPhase numerator denominator) =
        integerVector preNumerator denominator := by
    rw [phasePoint_eq_integerVector, chartInverse_apply_integerVector]
    unfold preNumerator
    congr 1 <;> grind
  have preMutationEq :
      Matrix2.apply
          (IntMatrix2.cast (mutation prime .positive preCoefficient))
          (Matrix2.apply (IntMatrix2.cast (chartInverse sourcePhase))
            (phasePoint actualPhase numerator denominator)) =
        integerVector preNumerator preDenominator := by
    rw [unchartEq, mutation_apply_integerVector]
    simp only [Sign.value, Int.one_mul]
    rfl
  rw [physicalLetter_apply] at outputLocal
  have afterPostLocal :=
    (local_chart_iff prime targetPhase _).mp outputLocal
  have afterDeletionLocal :=
    (local_mutation_iff prime postSign postCoefficient _).mp afterPostLocal
  rw [preMutationEq] at afterDeletionLocal
  have primePositive : 0 < prime := by
    unfold IsPrime at primeProperty
    omega
  have preDenominatorNotDivisible :
      ¬(prime : Int) ∣ preDenominator := by
    intro dividesPre
    apply denominatorNotDivisible
    have dividesFirst : (prime : Int) ∣
        (prime : Int) * preCoefficient * preNumerator := by
      exact ⟨preCoefficient * preNumerator, by grind⟩
    have dividesDifference := Int.dvd_sub dividesPre dividesFirst
    have differenceEq :
        preDenominator -
          (prime : Int) * preCoefficient * preNumerator = denominator := by
      unfold preDenominator
      grind
    rw [differenceEq] at dividesDifference
    exact dividesDifference
  have preNonzero := integerVector_nonzero_of_denominator
    (numerator := preNumerator) preDenominatorNotDivisible
  have checkedResidue :
      (prime : Int) ∣ preNumerator - letterDigit * preDenominator :=
    (deletion_local_iff_dvd primeProperty letterDigit preNonzero
      preDenominatorNotDivisible (SameLine.refl _)).mp afterDeletionLocal
  have residueDifferenceProduct :
      (prime : Int) ∣
        (phaseResidue actualPhase actualDigit -
          phaseResidue sourcePhase letterDigit) * denominator := by
    rcases actualResidue with ⟨actualFactor, actualEq⟩
    rcases checkedResidue with ⟨checkedFactor, checkedEq⟩
    refine ⟨checkedFactor - actualFactor +
      letterDigit * preCoefficient * preNumerator, ?_⟩
    simp only [preNumerator, preDenominator, phaseResidue, phaseShift]
      at checkedEq ⊢
    grind
  have residueDifferenceDivisible :
      (prime : Int) ∣
        phaseResidue actualPhase actualDigit -
          phaseResidue sourcePhase letterDigit := by
    rcases primeProperty.int_dvd_mul residueDifferenceProduct with
      differenceDivides | denominatorDivides
    · exact differenceDivides
    · exact False.elim (denominatorNotDivisible denominatorDivides)
  have congruent :
      phaseResidue actualPhase actualDigit % (prime : Int) =
        phaseResidue sourcePhase letterDigit % (prime : Int) := by
    rw [Int.emod_eq_emod_iff_emod_sub_eq_zero]
    exact Int.emod_eq_zero_of_dvd residueDifferenceDivisible
  exact phase_digit_unique primeBound actualPhaseBound sourcePhaseBound
    actualReserved letterReserved congruent

/-- A physical letter whose input and output are both local certifies its
own advertised source phase and digit on the input.  Unlike phase uniqueness,
this direction does not require a previously known phase for the input.  It
is the bridge used to cut a word over a union of module alphabets at its
first foreign letter. -/
theorem physicalLetter_input_inPhaseAt
    {prime sourcePhase targetPhase : Nat}
    {letterDigit preCoefficient postCoefficient : Int} {postSign : Sign}
    {vector : Vec2}
    (primeProperty : IsPrime prime)
    (letterReserved : ReservedDigit letterDigit)
    (inputLocal : LocalAt prime vector)
    (outputLocal : LocalAt prime
      (Matrix2.apply
        (IntMatrix2.cast
          (physicalLetter prime sourcePhase targetPhase letterDigit
            preCoefficient postSign postCoefficient)) vector)) :
    InPhaseAt prime sourcePhase letterDigit vector := by
  rcases inputLocal with
    ⟨inputNonzero, numerator, denominator, denominatorNotDivisible,
      inputSame⟩
  let localNumerator : Int :=
    numerator - phaseShift sourcePhase * denominator
  let preDenominator : Int :=
    (prime : Int) * preCoefficient * localNumerator + denominator
  have phasePointEq :
      phasePoint sourcePhase localNumerator denominator =
        integerVector numerator denominator := by
    rw [phasePoint_eq_integerVector]
    unfold localNumerator
    congr 1 <;> grind
  have unchartEq :
      Matrix2.apply (IntMatrix2.cast (chartInverse sourcePhase))
          (integerVector numerator denominator) =
        integerVector localNumerator denominator := by
    rw [chartInverse_apply_integerVector]
  have preMutationEq :
      Matrix2.apply
          (IntMatrix2.cast (mutation prime .positive preCoefficient))
          (Matrix2.apply (IntMatrix2.cast (chartInverse sourcePhase))
            (integerVector numerator denominator)) =
        integerVector localNumerator preDenominator := by
    rw [unchartEq, mutation_apply_integerVector]
    simp only [Sign.value, Int.one_mul]
    rfl
  have canonicalInputLocal : LocalAt prime
      (integerVector numerator denominator) :=
    local_integerVector denominatorNotDivisible
  have letterNonsingular :
      (physicalLetter prime sourcePhase targetPhase letterDigit
        preCoefficient postSign postCoefficient).Nonsingular :=
    physicalLetter_nonsingular (by have := primeProperty.1; omega)
  have canonicalOutputNonzero := Matrix2.apply_nonzero
    (IntMatrix2.cast_nonsingular letterNonsingular) canonicalInputLocal.1
  have outputSame := inputSame.apply
    (IntMatrix2.cast
      (physicalLetter prime sourcePhase targetPhase letterDigit
        preCoefficient postSign postCoefficient))
  have canonicalOutputLocal := LocalAt.of_sameLine outputLocal
    canonicalOutputNonzero outputSame.symm
  rw [physicalLetter_apply] at canonicalOutputLocal
  have afterPostLocal :=
    (local_chart_iff prime targetPhase _).mp canonicalOutputLocal
  have afterDeletionLocal :=
    (local_mutation_iff prime postSign postCoefficient _).mp afterPostLocal
  rw [preMutationEq] at afterDeletionLocal
  have preDenominatorNotDivisible :
      ¬(prime : Int) ∣ preDenominator := by
    intro dividesPre
    apply denominatorNotDivisible
    have dividesFirst : (prime : Int) ∣
        (prime : Int) * preCoefficient * localNumerator :=
      ⟨preCoefficient * localNumerator, by grind⟩
    have dividesDifference := Int.dvd_sub dividesPre dividesFirst
    have differenceEq :
        preDenominator -
          (prime : Int) * preCoefficient * localNumerator = denominator := by
      unfold preDenominator
      grind
    rw [differenceEq] at dividesDifference
    exact dividesDifference
  have preNonzero := integerVector_nonzero_of_denominator
    (numerator := localNumerator) preDenominatorNotDivisible
  have checkedResidue : (prime : Int) ∣
      localNumerator - letterDigit * preDenominator :=
    (deletion_local_iff_dvd primeProperty letterDigit preNonzero
      preDenominatorNotDivisible (SameLine.refl _)).mp afterDeletionLocal
  have localResidue : (prime : Int) ∣
      localNumerator - letterDigit * denominator := by
    rcases checkedResidue with ⟨factor, factorEq⟩
    refine ⟨factor + letterDigit * preCoefficient * localNumerator, ?_⟩
    unfold preDenominator at factorEq
    grind
  exact ⟨letterReserved, localNumerator, denominator,
    denominatorNotDivisible, localResidue, by simpa [phasePointEq] using
      inputSame⟩

/-- Phase enforcement stated directly from guarded endpoint membership.
This wrapper is convenient for module and global-alphabet parsers because
it hides the particular integer representative of the current state. -/
theorem InPhaseAt.physicalLetter_source_digit_unique
    {prime phaseCount actualPhase sourcePhase targetPhase : Nat}
    {actualDigit letterDigit preCoefficient postCoefficient : Int}
    {postSign : Sign} {vector : Vec2}
    (primeProperty : IsPrime prime)
    (primeBound : 6 * phaseCount < prime)
    (actualPhaseBound : actualPhase < phaseCount)
    (sourcePhaseBound : sourcePhase < phaseCount)
    (membership : InPhaseAt prime actualPhase actualDigit vector)
    (letterReserved : ReservedDigit letterDigit)
    (outputLocal : LocalAt prime
      (Matrix2.apply
        (IntMatrix2.cast
          (physicalLetter prime sourcePhase targetPhase letterDigit
            preCoefficient postSign postCoefficient)) vector)) :
    actualPhase = sourcePhase ∧ actualDigit = letterDigit := by
  rcases membership with
    ⟨actualReserved, numerator, denominator, denominatorNotDivisible,
      actualResidue, same⟩
  have outputSame := same.apply
    (IntMatrix2.cast
      (physicalLetter prime sourcePhase targetPhase letterDigit
        preCoefficient postSign postCoefficient))
  have pointLocal : LocalAt prime
      (phasePoint actualPhase numerator denominator) := by
    rw [phasePoint_eq_integerVector]
    exact local_integerVector denominatorNotDivisible
  have letterNonsingular :
      (physicalLetter prime sourcePhase targetPhase letterDigit
        preCoefficient postSign postCoefficient).Nonsingular :=
    physicalLetter_nonsingular
      (sourcePhase := sourcePhase) (targetPhase := targetPhase)
      (digit := letterDigit) (preCoefficient := preCoefficient)
      (postSign := postSign) (postCoefficient := postCoefficient)
      (by have := primeProperty.1; omega)
  have canonicalOutputNonzero := Matrix2.apply_nonzero
    (IntMatrix2.cast_nonsingular letterNonsingular) pointLocal.1
  have canonicalOutputLocal := LocalAt.of_sameLine outputLocal
    canonicalOutputNonzero outputSame.symm
  exact Mortality.Compiler.physicalLetter_source_digit_unique
    primeProperty primeBound
    actualPhaseBound sourcePhaseBound actualReserved letterReserved
    denominatorNotDivisible actualResidue canonicalOutputLocal

/-- Affine-coordinate enforcement from any explicit local integer
representative. -/
theorem physicalLetter_affine_integer_source_digit_unique
    {prime phaseCount actualPhase sourcePhase targetPhase : Nat}
    {actualDigit letterDigit preCoefficient postCoefficient : Int}
    {postSign : Sign} {value : Rat} {numerator denominator : Int}
    (primeProperty : IsPrime prime)
    (primeBound : 6 * phaseCount < prime)
    (actualPhaseBound : actualPhase < phaseCount)
    (sourcePhaseBound : sourcePhase < phaseCount)
    (actualReserved : ReservedDigit actualDigit)
    (letterReserved : ReservedDigit letterDigit)
    (denominatorNotDivisible : ¬(prime : Int) ∣ denominator)
    (actualResidue :
      (prime : Int) ∣ numerator - actualDigit * denominator)
    (valueSame : SameLine (Vec2.affine value)
      (integerVector numerator denominator))
    (outputLocal :
      LocalAt prime
        (Matrix2.apply
          (IntMatrix2.cast
            (physicalLetter prime sourcePhase targetPhase letterDigit
              preCoefficient postSign postCoefficient))
          (Vec2.affine
            (value + (phaseShift actualPhase : Rat))))) :
    actualPhase = sourcePhase ∧ actualDigit = letterDigit := by
  have chartedSame := valueSame.apply (IntMatrix2.cast (chart actualPhase))
  rw [chart_apply] at chartedSame
  change SameLine
      (Vec2.affine (value + (phaseShift actualPhase : Rat)))
      (phasePoint actualPhase numerator denominator) at chartedSame
  have outputSame := chartedSame.apply
    (IntMatrix2.cast
      (physicalLetter prime sourcePhase targetPhase letterDigit
        preCoefficient postSign postCoefficient))
  have phasePointLocal :
      LocalAt prime (phasePoint actualPhase numerator denominator) := by
    apply (local_chart_iff prime actualPhase _).mpr
    exact local_integerVector denominatorNotDivisible
  have letterNonsingular :
      (physicalLetter prime sourcePhase targetPhase letterDigit
        preCoefficient postSign postCoefficient).Nonsingular :=
    physicalLetter_nonsingular
      (sourcePhase := sourcePhase) (targetPhase := targetPhase)
      (digit := letterDigit) (preCoefficient := preCoefficient)
      (postSign := postSign) (postCoefficient := postCoefficient)
      (by have := primeProperty.1; omega)
  have canonicalOutputNonzero := Matrix2.apply_nonzero
    (IntMatrix2.cast_nonsingular letterNonsingular) phasePointLocal.1
  have canonicalOutputLocal := LocalAt.of_sameLine outputLocal
    canonicalOutputNonzero outputSame.symm
  exact physicalLetter_source_digit_unique primeProperty primeBound
    actualPhaseBound sourcePhaseBound actualReserved letterReserved
    denominatorNotDivisible actualResidue canonicalOutputLocal

end Mortality.Compiler
