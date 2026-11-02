import Mortality.Counts

/-!
# The concrete coding prime

The manuscript only needs one fixed prime above the phase bound.  We use
the elementary trial-divisor definition below so the concrete certificate
can be checked by the Lean kernel before Mathlib is added.
-/

namespace Mortality

set_option maxRecDepth 1000000

/-- Elementary primality: no divisor strictly between one and the number. -/
def IsPrime (number : Nat) : Prop :=
  2 ≤ number ∧
    ∀ divisor, 2 ≤ divisor → divisor < number → number % divisor ≠ 0

/-- Executable exhaustive divisor check corresponding to `IsPrime`. -/
def primeCheck (number : Nat) : Bool :=
  decide (2 ≤ number) &&
    (List.range number).all fun divisor =>
      decide (divisor < 2 ∨ number % divisor ≠ 0)

/-- The elementary definition has the usual divisor classification. -/
theorem IsPrime.eq_one_or_self_of_dvd {prime divisor : Nat}
    (primeProperty : IsPrime prime) (divides : divisor ∣ prime) :
    divisor = 1 ∨ divisor = prime := by
  by_cases divisorOne : divisor = 1
  · exact Or.inl divisorOne
  right
  have primePositive : 0 < prime := by
    unfold IsPrime at primeProperty
    omega
  have divisorPositive : 0 < divisor := by
    apply Nat.pos_of_ne_zero
    intro divisorZero
    subst divisor
    simp at divides
    omega
  have divisorAtLeastTwo : 2 ≤ divisor := by omega
  have divisorAtMostPrime := Nat.le_of_dvd primePositive divides
  rcases Nat.eq_or_lt_of_le divisorAtMostPrime with divisorEq | divisorBelow
  · exact divisorEq
  · exact False.elim (primeProperty.2 divisor divisorAtLeastTwo divisorBelow
      (Nat.mod_eq_zero_of_dvd divides))

/-- A prime is coprime to every number that it does not divide. -/
theorem IsPrime.coprime_of_not_dvd {prime number : Nat}
    (primeProperty : IsPrime prime) (notDivides : ¬prime ∣ number) :
    Nat.Coprime prime number := by
  rw [Nat.coprime_iff_gcd_eq_one]
  rcases primeProperty.eq_one_or_self_of_dvd
      (Nat.gcd_dvd_left prime number) with gcdOne | gcdPrime
  · exact gcdOne
  · exfalso
    apply notDivides
    rw [← gcdPrime]
    exact Nat.gcd_dvd_right prime number

/-- Euclid's lemma derived from the elementary definition. -/
theorem IsPrime.dvd_mul {prime first second : Nat}
    (primeProperty : IsPrime prime) (divides : prime ∣ first * second) :
    prime ∣ first ∨ prime ∣ second := by
  by_cases dividesFirst : prime ∣ first
  · exact Or.inl dividesFirst
  · exact Or.inr
      ((primeProperty.coprime_of_not_dvd dividesFirst).dvd_of_dvd_mul_left
        divides)

/-- Euclid's lemma for integer factors. -/
theorem IsPrime.int_dvd_mul {prime : Nat} {first second : Int}
    (primeProperty : IsPrime prime)
    (divides : (prime : Int) ∣ first * second) :
    (prime : Int) ∣ first ∨ (prime : Int) ∣ second := by
  have naturalDivides : prime ∣ (first * second).natAbs :=
    Int.ofNat_dvd_left.mp divides
  rw [Int.natAbs_mul] at naturalDivides
  rcases primeProperty.dvd_mul naturalDivides with firstDivides | secondDivides
  · exact Or.inl (Int.ofNat_dvd_left.mpr firstDivides)
  · exact Or.inr (Int.ofNat_dvd_left.mpr secondDivides)

theorem primeCheck_sound {number : Nat}
    (checked : primeCheck number = true) : IsPrime number := by
  unfold primeCheck at checked
  simp only [Bool.and_eq_true] at checked
  constructor
  · exact of_decide_eq_true checked.1
  · intro divisor divisorAtLeastTwo divisorBelow
    have divisorMem : divisor ∈ List.range number := by
      simp
      exact divisorBelow
    have divisorChecked :=
      (List.all_eq_true.mp checked.2) divisor divisorMem
    have alternative : divisor < 2 ∨ number % divisor ≠ 0 :=
      of_decide_eq_true divisorChecked
    exact alternative.resolve_left (by omega)

/-- The fixed number used by the matrix compiler is prime. -/
theorem codingPrime_isPrime : IsPrime codingPrime := by
  apply primeCheck_sound
  decide

end Mortality
