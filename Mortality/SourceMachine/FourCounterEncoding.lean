import Mortality.SourceMachine.FourCounterSemantics

/-!
# Prime-exponent encoding of four counter registers

The four logical registers are stored in the exponents of `2,3,5,7`.
This file proves the arithmetic identities needed by the later Minsky-block
compiler.  Counter-machine control is not encoded here.
-/

namespace Mortality.SourceMachine.FourCounterEncoding

open Mortality.SourceMachine.FourCounter

def registerPrime : Register → Nat
  | .left => 2
  | .right => 3
  | .temp => 5
  | .clock => 7

theorem registerPrime_large (register : Register) :
    1 < registerPrime register := by
  cases register <;> decide

def encode (registers : Registers) : Nat :=
  2 ^ registers.left * 3 ^ registers.right *
    5 ^ registers.temp * 7 ^ registers.clock

theorem encode_positive (registers : Registers) : 0 < encode registers := by
  unfold encode
  repeat apply Nat.mul_pos
  all_goals exact Nat.pow_pos (by decide)

/-- Incrementing one logical register multiplies its prime-exponent code by
the assigned prime. -/
theorem encode_increment (registers : Registers) (register : Register) :
    encode (registers.increment register) =
      registerPrime register * encode registers := by
  cases register <;>
    simp [encode, registerPrime, Registers.increment, Registers.set,
      Registers.get, Nat.pow_succ] <;> ac_rfl

/-- A successful logical decrement divides the code by the assigned prime. -/
theorem encode_decrement_mul_prime (registers : Registers)
    (register : Register) (positive : 0 < registers.get register) :
    registerPrime register * encode (registers.decrement register) =
      encode registers := by
  cases register with
  | left =>
      obtain ⟨value, valueEq⟩ := Nat.exists_eq_succ_of_ne_zero
        (Nat.ne_of_gt positive)
      change registers.left = value + 1 at valueEq
      simp [encode, registerPrime, Registers.decrement, Registers.set,
        Registers.get, valueEq, Nat.pow_succ]
      ac_rfl
  | right =>
      obtain ⟨value, valueEq⟩ := Nat.exists_eq_succ_of_ne_zero
        (Nat.ne_of_gt positive)
      change registers.right = value + 1 at valueEq
      simp [encode, registerPrime, Registers.decrement, Registers.set,
        Registers.get, valueEq, Nat.pow_succ]
      ac_rfl
  | temp =>
      obtain ⟨value, valueEq⟩ := Nat.exists_eq_succ_of_ne_zero
        (Nat.ne_of_gt positive)
      change registers.temp = value + 1 at valueEq
      simp [encode, registerPrime, Registers.decrement, Registers.set,
        Registers.get, valueEq, Nat.pow_succ]
      ac_rfl
  | clock =>
      obtain ⟨value, valueEq⟩ := Nat.exists_eq_succ_of_ne_zero
        (Nat.ne_of_gt positive)
      change registers.clock = value + 1 at valueEq
      simp [encode, registerPrime, Registers.decrement, Registers.set,
        Registers.get, valueEq, Nat.pow_succ]
      ac_rfl

private theorem coprime_encode_of_factors (prime : Nat)
    (registers : Registers)
    (left : Nat.Coprime prime (2 ^ registers.left))
    (right : Nat.Coprime prime (3 ^ registers.right))
    (temp : Nat.Coprime prime (5 ^ registers.temp))
    (clock : Nat.Coprime prime (7 ^ registers.clock)) :
    Nat.Coprime prime (encode registers) := by
  simpa [encode] using
    ((left.mul_right right).mul_right temp).mul_right clock

/-- If one logical register is zero, its prime does not divide the complete
code.  Pairwise coprimality of `2,3,5,7` is discharged by kernel reduction. -/
theorem coprime_encode_of_get_zero (registers : Registers)
    (register : Register) (zero : registers.get register = 0) :
    Nat.Coprime (registerPrime register) (encode registers) := by
  cases register with
  | left =>
      exact coprime_encode_of_factors 2 registers
        (by simp [Registers.get] at zero; simp [zero])
        ((by decide : Nat.Coprime 2 3).pow_right _)
        ((by decide : Nat.Coprime 2 5).pow_right _)
        ((by decide : Nat.Coprime 2 7).pow_right _)
  | right =>
      exact coprime_encode_of_factors 3 registers
        ((by decide : Nat.Coprime 3 2).pow_right _)
        (by simp [Registers.get] at zero; simp [zero])
        ((by decide : Nat.Coprime 3 5).pow_right _)
        ((by decide : Nat.Coprime 3 7).pow_right _)
  | temp =>
      exact coprime_encode_of_factors 5 registers
        ((by decide : Nat.Coprime 5 2).pow_right _)
        ((by decide : Nat.Coprime 5 3).pow_right _)
        (by simp [Registers.get] at zero; simp [zero])
        ((by decide : Nat.Coprime 5 7).pow_right _)
  | clock =>
      exact coprime_encode_of_factors 7 registers
        ((by decide : Nat.Coprime 7 2).pow_right _)
        ((by decide : Nat.Coprime 7 3).pow_right _)
        ((by decide : Nat.Coprime 7 5).pow_right _)
        (by simp [Registers.get] at zero; simp [zero])

theorem not_dvd_encode_of_get_zero (registers : Registers)
    (register : Register) (zero : registers.get register = 0) :
    ¬registerPrime register ∣ encode registers := by
  intro divides
  have primeOne :=
    (coprime_encode_of_get_zero registers register zero).eq_one_of_dvd divides
  have primeLarge := registerPrime_large register
  omega

theorem encode_mod_prime_positive_of_get_zero (registers : Registers)
    (register : Register) (zero : registers.get register = 0) :
    0 < encode registers % registerPrime register := by
  have modulusPositive : 0 < registerPrime register := by
    exact Nat.zero_lt_of_lt (registerPrime_large register)
  have remainderNonzero : encode registers % registerPrime register ≠ 0 := by
    intro remainderZero
    exact not_dvd_encode_of_get_zero registers register zero
      (Nat.dvd_of_mod_eq_zero remainderZero)
  exact Nat.pos_of_ne_zero remainderNonzero

theorem encode_mod_prime_bound (registers : Registers) (register : Register) :
    encode registers % registerPrime register < registerPrime register :=
  Nat.mod_lt _ (Nat.zero_lt_of_lt (registerPrime_large register))

end Mortality.SourceMachine.FourCounterEncoding
