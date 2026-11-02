import Mortality.Basic

/-!
# A finite Chinese remainder theorem for Korec's program code

Korec's construction ends with a finite system of congruences whose moduli
are positive and pairwise coprime.  The Lean standard library contains the
elementary theory of gcd and coprimality, but no Chinese remainder theorem.
This file supplies the exact finite existence result needed by the program
code construction without adding an external dependency.

Residues are indexed by their moduli.  This is sufficient for the intended
application because pairwise coprimality excludes repeated nonunit moduli.
The theorem nevertheless remains valid for every list satisfying its stated
hypotheses.
-/

namespace Mortality.SourceMachine.KorecCRT

/-- Bézout's identity for natural inputs, with integer coefficients. -/
theorem exists_bezout : ∀ first second : Nat, ∃ left right : Int,
    left * (first : Int) + right * (second : Int) =
      (Nat.gcd first second : Int) := by
  intro first second
  induction first using Nat.strongRecOn generalizing second with
  | ind first inductionHypothesis =>
      by_cases firstZero : first = 0
      · subst first
        exact ⟨0, 1, by simp⟩
      · have firstPositive : 0 < first := Nat.pos_of_ne_zero firstZero
        have remainderSmall : second % first < first :=
          Nat.mod_lt second firstPositive
        obtain ⟨left, right, remainderIdentity⟩ :=
          inductionHypothesis (second % first) remainderSmall first
        refine ⟨right - left * (second / first : Nat), left, ?_⟩
        have divisionIdentity :
            (second % first : Int) +
                (first : Int) * (second / first : Nat) = (second : Int) := by
          rw [Int.natCast_ediv]
          exact Int.emod_add_mul_ediv (second : Int) (first : Int)
        have rearranged :
            (right - left * (second / first : Nat)) * (first : Int) +
                left * (second : Int) =
              left * (second % first : Int) + right * (first : Int) := by
          calc
            (right - left * (second / first : Nat)) * (first : Int) +
                  left * (second : Int) =
                right * (first : Int) + left * ((second : Int) -
                  (first : Int) * (second / first : Nat)) := by
                    simp only [Int.sub_eq_add_neg, Int.add_mul, Int.mul_add,
                      Int.neg_mul, Int.mul_neg]
                    ac_rfl
            _ = right * (first : Int) +
                left * (second % first : Int) := by
                  have remainderEquality :
                      (second : Int) -
                          (first : Int) * (second / first : Nat) =
                        (second % first : Int) := by
                    omega
                  rw [remainderEquality]
            _ = left * (second % first : Int) +
                right * (first : Int) := by ac_rfl
        rw [rearranged, ← Int.natCast_emod, remainderIdentity]
        exact_mod_cast (Nat.gcd_rec first second).symm

/-- The two-modulus Chinese remainder theorem.  Residues are normalized in
the conclusion, so no upper-bound hypotheses on them are needed. -/
theorem exists_pair_solution
    {firstModulus secondModulus firstResidue secondResidue : Nat}
    (firstPositive : 0 < firstModulus)
    (secondPositive : 0 < secondModulus)
    (coprime : Nat.Coprime firstModulus secondModulus) :
    ∃ solution : Nat,
      solution % firstModulus = firstResidue % firstModulus ∧
      solution % secondModulus = secondResidue % secondModulus := by
  obtain ⟨left, right, bezoutIdentity⟩ :=
    exists_bezout firstModulus secondModulus
  have gcdOne : Nat.gcd firstModulus secondModulus = 1 := coprime
  rw [gcdOne] at bezoutIdentity
  let integerSolution : Int :=
    (firstResidue : Int) + (firstModulus : Int) * left *
      ((secondResidue : Int) - (firstResidue : Int))
  have atFirst :
      integerSolution % (firstModulus : Int) =
        (firstResidue : Int) % (firstModulus : Int) := by
    rw [Int.emod_eq_emod_iff_emod_sub_eq_zero]
    apply Int.emod_eq_zero_of_dvd
    refine ⟨left * ((secondResidue : Int) - (firstResidue : Int)), ?_⟩
    change integerSolution - (firstResidue : Int) =
      (firstModulus : Int) *
        (left * ((secondResidue : Int) - (firstResidue : Int)))
    simp only [integerSolution]
    rw [show (firstResidue : Int) + (firstModulus : Int) * left *
          ((secondResidue : Int) - (firstResidue : Int)) =
        ((firstModulus : Int) * left *
          ((secondResidue : Int) - (firstResidue : Int))) +
            (firstResidue : Int) by ac_rfl,
      Int.add_sub_cancel]
    ac_rfl
  have atSecond :
      integerSolution % (secondModulus : Int) =
        (secondResidue : Int) % (secondModulus : Int) := by
    rw [Int.emod_eq_emod_iff_emod_sub_eq_zero]
    apply Int.emod_eq_zero_of_dvd
    refine ⟨-right * ((secondResidue : Int) - (firstResidue : Int)), ?_⟩
    simp only [integerSolution]
    have bezoutCommuted :
        (firstModulus : Int) * left +
          right * (secondModulus : Int) = 1 := by
      rw [Int.mul_comm (firstModulus : Int) left]
      simpa using bezoutIdentity
    have linearIdentity :
        (firstModulus : Int) * left - 1 =
          -right * (secondModulus : Int) := by
      rw [← bezoutCommuted]
      simp only [Int.sub_eq_add_neg, Int.neg_add, Int.neg_mul,
        Int.add_neg_cancel_left]
    let difference : Int :=
      (secondResidue : Int) - (firstResidue : Int)
    have differenceIdentity :
        (firstResidue : Int) + difference = (secondResidue : Int) := by
      simp only [difference]
      omega
    calc
      (firstResidue : Int) + (firstModulus : Int) * left *
            ((secondResidue : Int) - (firstResidue : Int)) -
          (secondResidue : Int) =
        ((firstModulus : Int) * left - 1) * difference := by
          change (firstResidue : Int) +
              (firstModulus : Int) * left * difference -
                (secondResidue : Int) =
            ((firstModulus : Int) * left - 1) * difference
          rw [Int.sub_mul, Int.one_mul]
          omega
      _ = (secondModulus : Int) *
          (-right * ((secondResidue : Int) - (firstResidue : Int))) := by
            rw [linearIdentity]
            change (-right * (secondModulus : Int)) * difference =
              (secondModulus : Int) * (-right * difference)
            ac_rfl
  let product := firstModulus * secondModulus
  have productPositive : 0 < product :=
    Nat.mul_pos firstPositive secondPositive
  let reduced : Int := integerSolution % (product : Int)
  have reducedNonnegative : 0 ≤ reduced := by
    apply Int.emod_nonneg
    exact_mod_cast (Nat.ne_of_gt productPositive)
  refine ⟨reduced.toNat, ?_, ?_⟩
  · apply Int.natCast_inj.mp
    rw [Int.natCast_emod, Int.toNat_of_nonneg reducedNonnegative,
      Int.natCast_emod]
    change reduced % (firstModulus : Int) =
      (firstResidue : Int) % (firstModulus : Int)
    rw [show reduced = integerSolution % (product : Int) by rfl]
    rw [Int.emod_emod_of_dvd]
    · exact atFirst
    · exact_mod_cast Nat.dvd_mul_right firstModulus secondModulus
  · apply Int.natCast_inj.mp
    rw [Int.natCast_emod, Int.toNat_of_nonneg reducedNonnegative,
      Int.natCast_emod]
    change reduced % (secondModulus : Int) =
      (secondResidue : Int) % (secondModulus : Int)
    rw [show reduced = integerSolution % (product : Int) by rfl]
    rw [Int.emod_emod_of_dvd]
    · exact atSecond
    · exact_mod_cast Nat.dvd_mul_left secondModulus firstModulus

/-- The product of a finite list of moduli. -/
def modulusProduct : List Nat → Nat
  | [] => 1
  | modulus :: moduli => modulus * modulusProduct moduli

/-- Every listed modulus divides their product. -/
theorem modulus_dvd_product {moduli : List Nat} {modulus : Nat}
    (member : modulus ∈ moduli) : modulus ∣ modulusProduct moduli := by
  induction moduli with
  | nil => simp at member
  | cons head tail inductionHypothesis =>
      simp only [List.mem_cons] at member
      simp only [modulusProduct]
      rcases member with rfl | member
      · exact Nat.dvd_mul_right _ _
      · exact Nat.dvd_trans (inductionHypothesis member)
          (Nat.dvd_mul_left (modulusProduct tail) head)

/-- A product of positive moduli is positive. -/
theorem modulusProduct_positive {moduli : List Nat}
    (positive : ∀ modulus, modulus ∈ moduli → 0 < modulus) :
    0 < modulusProduct moduli := by
  induction moduli with
  | nil => decide
  | cons head tail inductionHypothesis =>
      simp only [modulusProduct]
      apply Nat.mul_pos
      · exact positive head (by simp)
      · apply inductionHypothesis
        intro modulus member
        exact positive modulus (by simp [member])

/-- Coprimality with every listed modulus implies coprimality with their
product. -/
theorem coprime_modulusProduct {modulus : Nat} {moduli : List Nat}
    (coprime : ∀ other, other ∈ moduli → Nat.Coprime modulus other) :
    Nat.Coprime modulus (modulusProduct moduli) := by
  induction moduli with
  | nil => exact Nat.coprime_one_right modulus
  | cons head tail inductionHypothesis =>
      simp only [modulusProduct]
      apply Nat.Coprime.mul_right
      · exact coprime head (by simp)
      · apply inductionHypothesis
        intro other member
        exact coprime other (by simp [member])

/-- If pairwise-coprime moduli all divide one number, their product divides
that number.  This is the form needed for Korec's collection of maximal prime
powers: a bounded integer may use several omitted primes and therefore divide
the product without dividing any single prime power. -/
theorem modulusProduct_dvd
    {moduli : List Nat} {value : Nat}
    (pairwise : moduli.Pairwise Nat.Coprime)
    (eachDivides : ∀ modulus, modulus ∈ moduli → modulus ∣ value) :
    modulusProduct moduli ∣ value := by
  induction moduli with
  | nil => exact Nat.one_dvd value
  | cons modulus moduli inductionHypothesis =>
      rw [List.pairwise_cons] at pairwise
      simp only [modulusProduct]
      have modulusDivides := eachDivides modulus (by simp)
      have productDivides := inductionHypothesis pairwise.2
        (fun other member => eachDivides other (by simp [member]))
      have modulusCoprimeProduct := coprime_modulusProduct pairwise.1
      exact modulusCoprimeProduct.mul_dvd_of_dvd_of_dvd
        modulusDivides productDivides

/-- A natural number satisfies the residue assigned to every listed
modulus. -/
def SatisfiesCongruences (solution : Nat) (moduli : List Nat)
    (residue : Nat → Nat) : Prop :=
  ∀ modulus, modulus ∈ moduli →
    solution % modulus = residue modulus % modulus

/-- A bounded prescribed residue is recovered without normalization. -/
theorem SatisfiesCongruences.exact
    {solution modulus : Nat} {moduli : List Nat} {residue : Nat → Nat}
    (satisfies : SatisfiesCongruences solution moduli residue)
    (member : modulus ∈ moduli) (residueBelow : residue modulus < modulus) :
    solution % modulus = residue modulus := by
  rw [satisfies modulus member, Nat.mod_eq_of_lt residueBelow]

/-- A prescribed zero residue turns into the corresponding divisibility
fact. -/
theorem SatisfiesCongruences.dvd_of_residue_zero
    {solution modulus : Nat} {moduli : List Nat} {residue : Nat → Nat}
    (satisfies : SatisfiesCongruences solution moduli residue)
    (member : modulus ∈ moduli) (residueZero : residue modulus = 0) :
    modulus ∣ solution := by
  apply Nat.dvd_of_mod_eq_zero
  rw [satisfies modulus member, residueZero]
  simp

/-- Finite Chinese remainder theorem in the form used by Korec: every
positive pairwise-coprime list of moduli admits a simultaneous solution. -/
theorem exists_solution {moduli : List Nat} {residue : Nat → Nat}
    (positive : ∀ modulus, modulus ∈ moduli → 0 < modulus)
    (pairwise : moduli.Pairwise Nat.Coprime) :
    ∃ solution, SatisfiesCongruences solution moduli residue := by
  induction moduli with
  | nil => exact ⟨0, by simp [SatisfiesCongruences]⟩
  | cons modulus moduli inductionHypothesis =>
      rw [List.pairwise_cons] at pairwise
      have tailPositive : ∀ other, other ∈ moduli → 0 < other := by
        intro other member
        exact positive other (by simp [member])
      obtain ⟨tailSolution, tailSatisfies⟩ :=
        inductionHypothesis tailPositive pairwise.2
      have productPositive := modulusProduct_positive tailPositive
      have modulusPositive := positive modulus (by simp)
      have productCoprime := coprime_modulusProduct pairwise.1
      obtain ⟨solution, atModulus, atProduct⟩ := exists_pair_solution
        modulusPositive productPositive productCoprime
        (firstResidue := residue modulus) (secondResidue := tailSolution)
      refine ⟨solution, ?_⟩
      intro other member
      simp only [List.mem_cons] at member
      rcases member with rfl | member
      · exact atModulus
      · have otherDivides : other ∣ modulusProduct moduli :=
          modulus_dvd_product member
        have reducedEquality :=
          congrArg (fun value => value % other) atProduct
        change (solution % modulusProduct moduli) % other =
          (tailSolution % modulusProduct moduli) % other at reducedEquality
        rw [Nat.mod_mod_of_dvd solution otherDivides,
          Nat.mod_mod_of_dvd tailSolution otherDivides] at reducedEquality
        exact reducedEquality.trans (tailSatisfies other member)

/-- Adding the product of all moduli preserves every listed congruence. -/
theorem SatisfiesCongruences.add_modulusProduct
    {solution : Nat} {moduli : List Nat} {residue : Nat → Nat}
    (satisfies : SatisfiesCongruences solution moduli residue) :
    SatisfiesCongruences (solution + modulusProduct moduli) moduli residue := by
  intro modulus member
  rw [Nat.add_mod,
    Nat.mod_eq_zero_of_dvd (modulus_dvd_product member)]
  simpa using satisfies modulus member

/-- Reducing a solution modulo the product preserves every listed
congruence. -/
theorem SatisfiesCongruences.mod_modulusProduct
    {solution : Nat} {moduli : List Nat} {residue : Nat → Nat}
    (satisfies : SatisfiesCongruences solution moduli residue) :
    SatisfiesCongruences (solution % modulusProduct moduli) moduli residue := by
  intro modulus member
  rw [Nat.mod_mod_of_dvd solution (modulus_dvd_product member)]
  exact satisfies modulus member

/-- The simultaneous congruences are decidable by a finite Boolean scan. -/
def congruencesHold (candidate : Nat) (moduli : List Nat)
    (residue : Nat → Nat) : Bool :=
  moduli.all fun modulus => candidate % modulus == residue modulus % modulus

theorem congruencesHold_eq_true_iff
    (candidate : Nat) (moduli : List Nat) (residue : Nat → Nat) :
    congruencesHold candidate moduli residue = true ↔
      SatisfiesCongruences candidate moduli residue := by
  simp [congruencesHold, SatisfiesCongruences, List.all_eq_true]

/-- Search the candidates below `limit`, testing the largest candidate
first.  The order is immaterial; this definition is used only to obtain an
explicit executable CRT solver. -/
def searchSolution (moduli : List Nat) (residue : Nat → Nat) :
    Nat → Option Nat
  | 0 => none
  | limit + 1 =>
      if congruencesHold limit moduli residue then some limit
      else searchSolution moduli residue limit

theorem searchSolution_sound
    {moduli : List Nat} {residue : Nat → Nat} {limit solution : Nat}
    (found : searchSolution moduli residue limit = some solution) :
    SatisfiesCongruences solution moduli residue := by
  induction limit generalizing solution with
  | zero => simp [searchSolution] at found
  | succ limit inductionHypothesis =>
      by_cases holds : congruencesHold limit moduli residue = true
      · simp [searchSolution, holds] at found
        subst solution
        exact (congruencesHold_eq_true_iff limit moduli residue).mp holds
      · simp [searchSolution, holds] at found
        exact inductionHypothesis found

theorem searchSolution_complete
    {moduli : List Nat} {residue : Nat → Nat} {limit witness : Nat}
    (witnessBelow : witness < limit)
    (witnessSatisfies : SatisfiesCongruences witness moduli residue) :
    ∃ solution, searchSolution moduli residue limit = some solution := by
  induction limit generalizing witness with
  | zero => omega
  | succ limit inductionHypothesis =>
      by_cases holds : congruencesHold limit moduli residue = true
      · exact ⟨limit, by simp [searchSolution, holds]⟩
      · have witnessStrict : witness < limit := by
          have witnessNotEqual : witness ≠ limit := by
            intro equality
            subst witness
            exact holds
              ((congruencesHold_eq_true_iff limit moduli residue).mpr
                witnessSatisfies)
          omega
        obtain ⟨solution, found⟩ :=
          inductionHypothesis witnessStrict witnessSatisfies
        exact ⟨solution, by simp [searchSolution, holds, found]⟩

/-- Executable finite CRT solver.  Correctness is conditional on the usual
positive, pairwise-coprime hypotheses; the definition itself is total. -/
def solveCongruences (moduli : List Nat) (residue : Nat → Nat) : Nat :=
  (searchSolution moduli residue (modulusProduct moduli)).getD 0

theorem solveCongruences_spec
    {moduli : List Nat} {residue : Nat → Nat}
    (positive : ∀ modulus, modulus ∈ moduli → 0 < modulus)
    (pairwise : moduli.Pairwise Nat.Coprime) :
    SatisfiesCongruences (solveCongruences moduli residue) moduli residue := by
  obtain ⟨solution, satisfies⟩ :=
    exists_solution (residue := residue) positive pairwise
  have productPositive := modulusProduct_positive positive
  have reducedBelow : solution % modulusProduct moduli <
      modulusProduct moduli := Nat.mod_lt solution productPositive
  have reducedSatisfies :=
    SatisfiesCongruences.mod_modulusProduct
      (residue := residue) satisfies
  obtain ⟨found, searchFound⟩ :=
    searchSolution_complete reducedBelow reducedSatisfies
  have foundSatisfies := searchSolution_sound searchFound
  have solverEquality : solveCongruences moduli residue = found := by
    simp [solveCongruences, searchFound]
  rw [solverEquality]
  exact foundSatisfies

/-- An executable program code obtained from the CRT solution.  Adding the
modulus product makes the coded number positive before subtracting one. -/
def programCode (moduli : List Nat) (residue : Nat → Nat) : Nat :=
  solveCongruences moduli residue + modulusProduct moduli - 1

theorem programCode_spec
    {moduli : List Nat} {residue : Nat → Nat}
    (positive : ∀ modulus, modulus ∈ moduli → 0 < modulus)
    (pairwise : moduli.Pairwise Nat.Coprime) :
    SatisfiesCongruences (programCode moduli residue + 1) moduli residue := by
  have solved := solveCongruences_spec
    (residue := residue) positive pairwise
  have shifted := solved.add_modulusProduct
  have productPositive := modulusProduct_positive positive
  have successorEquality :
      programCode moduli residue + 1 =
        solveCongruences moduli residue + modulusProduct moduli := by
    unfold programCode
    omega
  simpa [successorEquality] using shifted

/-- A finite CRT solution can always be chosen positive.  This matters for
Korec because the coded integer is `programCode + 1`. -/
theorem exists_positive_solution
    {moduli : List Nat} {residue : Nat → Nat}
    (positive : ∀ modulus, modulus ∈ moduli → 0 < modulus)
    (pairwise : moduli.Pairwise Nat.Coprime) :
    ∃ solution, 0 < solution ∧
      SatisfiesCongruences solution moduli residue := by
  obtain ⟨solution, satisfies⟩ := exists_solution positive pairwise
  refine ⟨solution + modulusProduct moduli, ?_,
    satisfies.add_modulusProduct⟩
  have productPositive := modulusProduct_positive positive
  omega

/-- Program-code form of the finite CRT: there is a natural `programCode`
whose successor satisfies all prescribed congruences. -/
theorem exists_programCode
    {moduli : List Nat} {residue : Nat → Nat}
    (positive : ∀ modulus, modulus ∈ moduli → 0 < modulus)
    (pairwise : moduli.Pairwise Nat.Coprime) :
    ∃ programCode,
      SatisfiesCongruences (programCode + 1) moduli residue := by
  obtain ⟨codedNumber, codedNumberPositive, satisfies⟩ :=
    exists_positive_solution positive pairwise
  refine ⟨codedNumber - 1, ?_⟩
  have successorEquality : codedNumber - 1 + 1 = codedNumber := by omega
  simpa [successorEquality] using satisfies

end Mortality.SourceMachine.KorecCRT
