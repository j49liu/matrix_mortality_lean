import Mortality.SourceMachine.ConcreteBlocks

/-!
# Exponential encoding of Korec's eight registers

Ivanov's two-counter construction stores the simulated register tuple in the
prime exponents of counter zero.  Counter one is scratch space.  This file
proves the multiplication, division, and nondivisibility facts needed by the
two generic compiler blocks.
-/

namespace Mortality.SourceMachine.U20Compilation

open Mortality.SourceMachine.KorecU20

def encodeRegisters (registers : Registers) : Nat :=
  7 ^ registers 0 * 11 ^ registers 1 * 13 ^ registers 2 *
  19 ^ registers 3 * 5 ^ registers 4 * 2 ^ registers 5 *
  3 ^ registers 6 * 17 ^ registers 7

theorem encodeRegisters_positive (registers : Registers) :
    0 < encodeRegisters registers := by
  unfold encodeRegisters
  repeat apply Nat.mul_pos
  all_goals exact Nat.pow_pos (by decide)

theorem encodeRegisters_initial (input : Nat) :
    encodeRegisters (initialRegisters input) = 13 ^ input := by
  simp [encodeRegisters, initialRegisters]

theorem encodeRegisters_initialTwo (programInput dataInput : Nat) :
    encodeRegisters (initialRegistersTwo programInput dataInput) =
      11 ^ programInput * 13 ^ dataInput := by
  simp [encodeRegisters, initialRegistersTwo]

private theorem coprime_encode_of_factors (p : Nat) (registers : Registers)
    (h0 : Nat.Coprime p (7 ^ registers 0))
    (h1 : Nat.Coprime p (11 ^ registers 1))
    (h2 : Nat.Coprime p (13 ^ registers 2))
    (h3 : Nat.Coprime p (19 ^ registers 3))
    (h4 : Nat.Coprime p (5 ^ registers 4))
    (h5 : Nat.Coprime p (2 ^ registers 5))
    (h6 : Nat.Coprime p (3 ^ registers 6))
    (h7 : Nat.Coprime p (17 ^ registers 7)) :
    Nat.Coprime p (encodeRegisters registers) := by
  simpa [encodeRegisters] using
    (((((((h0.mul_right h1).mul_right h2).mul_right h3).mul_right h4).mul_right h5).mul_right h6).mul_right h7)

theorem coprime_seven_encode_of_r0_zero (registers : Registers)
    (zero : registers 0 = 0) : Nat.Coprime 7 (encodeRegisters registers) :=
  coprime_encode_of_factors 7 registers
    (by simp [zero])
    ((by decide : Nat.Coprime 7 11).pow_right _)
    ((by decide : Nat.Coprime 7 13).pow_right _)
    ((by decide : Nat.Coprime 7 19).pow_right _)
    ((by decide : Nat.Coprime 7 5).pow_right _)
    ((by decide : Nat.Coprime 7 2).pow_right _)
    ((by decide : Nat.Coprime 7 3).pow_right _)
    ((by decide : Nat.Coprime 7 17).pow_right _)

theorem coprime_eleven_encode_of_r1_zero (registers : Registers)
    (zero : registers 1 = 0) : Nat.Coprime 11 (encodeRegisters registers) :=
  coprime_encode_of_factors 11 registers
    ((by decide : Nat.Coprime 11 7).pow_right _)
    (by simp [zero])
    ((by decide : Nat.Coprime 11 13).pow_right _)
    ((by decide : Nat.Coprime 11 19).pow_right _)
    ((by decide : Nat.Coprime 11 5).pow_right _)
    ((by decide : Nat.Coprime 11 2).pow_right _)
    ((by decide : Nat.Coprime 11 3).pow_right _)
    ((by decide : Nat.Coprime 11 17).pow_right _)

theorem coprime_thirteen_encode_of_r2_zero (registers : Registers)
    (zero : registers 2 = 0) : Nat.Coprime 13 (encodeRegisters registers) :=
  coprime_encode_of_factors 13 registers
    ((by decide : Nat.Coprime 13 7).pow_right _)
    ((by decide : Nat.Coprime 13 11).pow_right _)
    (by simp [zero])
    ((by decide : Nat.Coprime 13 19).pow_right _)
    ((by decide : Nat.Coprime 13 5).pow_right _)
    ((by decide : Nat.Coprime 13 2).pow_right _)
    ((by decide : Nat.Coprime 13 3).pow_right _)
    ((by decide : Nat.Coprime 13 17).pow_right _)

theorem coprime_five_encode_of_r4_zero (registers : Registers)
    (zero : registers 4 = 0) : Nat.Coprime 5 (encodeRegisters registers) :=
  coprime_encode_of_factors 5 registers
    ((by decide : Nat.Coprime 5 7).pow_right _)
    ((by decide : Nat.Coprime 5 11).pow_right _)
    ((by decide : Nat.Coprime 5 13).pow_right _)
    ((by decide : Nat.Coprime 5 19).pow_right _)
    (by simp [zero])
    ((by decide : Nat.Coprime 5 2).pow_right _)
    ((by decide : Nat.Coprime 5 3).pow_right _)
    ((by decide : Nat.Coprime 5 17).pow_right _)

theorem coprime_two_encode_of_r5_zero (registers : Registers)
    (zero : registers 5 = 0) : Nat.Coprime 2 (encodeRegisters registers) :=
  coprime_encode_of_factors 2 registers
    ((by decide : Nat.Coprime 2 7).pow_right _)
    ((by decide : Nat.Coprime 2 11).pow_right _)
    ((by decide : Nat.Coprime 2 13).pow_right _)
    ((by decide : Nat.Coprime 2 19).pow_right _)
    ((by decide : Nat.Coprime 2 5).pow_right _)
    (by simp [zero])
    ((by decide : Nat.Coprime 2 3).pow_right _)
    ((by decide : Nat.Coprime 2 17).pow_right _)

theorem coprime_three_encode_of_r6_zero (registers : Registers)
    (zero : registers 6 = 0) : Nat.Coprime 3 (encodeRegisters registers) :=
  coprime_encode_of_factors 3 registers
    ((by decide : Nat.Coprime 3 7).pow_right _)
    ((by decide : Nat.Coprime 3 11).pow_right _)
    ((by decide : Nat.Coprime 3 13).pow_right _)
    ((by decide : Nat.Coprime 3 19).pow_right _)
    ((by decide : Nat.Coprime 3 5).pow_right _)
    ((by decide : Nat.Coprime 3 2).pow_right _)
    (by simp [zero])
    ((by decide : Nat.Coprime 3 17).pow_right _)

theorem coprime_seventeen_encode_of_r7_zero (registers : Registers)
    (zero : registers 7 = 0) : Nat.Coprime 17 (encodeRegisters registers) :=
  coprime_encode_of_factors 17 registers
    ((by decide : Nat.Coprime 17 7).pow_right _)
    ((by decide : Nat.Coprime 17 11).pow_right _)
    ((by decide : Nat.Coprime 17 13).pow_right _)
    ((by decide : Nat.Coprime 17 19).pow_right _)
    ((by decide : Nat.Coprime 17 5).pow_right _)
    ((by decide : Nat.Coprime 17 2).pow_right _)
    ((by decide : Nat.Coprime 17 3).pow_right _)
    (by simp [zero])

theorem mod_positive_of_coprime {prime value : Nat} (primeLarge : 1 < prime)
    (coprime : Nat.Coprime prime value) : 0 < value % prime := by
  have nonzero : value % prime ≠ 0 := by
    intro moduloZero
    have divides : prime ∣ value := Nat.dvd_of_mod_eq_zero moduloZero
    have primeOne := coprime.eq_one_of_dvd divides
    omega
  exact Nat.pos_of_ne_zero nonzero

theorem encode_update_r0_increment (registers : Registers) :
    encodeRegisters (registers.update 0 (registers 0 + 1)) =
      7 * encodeRegisters registers := by
  simp [encodeRegisters, Registers.update, Nat.pow_succ]
  ac_rfl

theorem encode_update_r1_increment (registers : Registers) :
    encodeRegisters (registers.update 1 (registers 1 + 1)) =
      11 * encodeRegisters registers := by
  simp [encodeRegisters, Registers.update, Nat.pow_succ]
  ac_rfl

theorem encode_update_r2_increment (registers : Registers) :
    encodeRegisters (registers.update 2 (registers 2 + 1)) =
      13 * encodeRegisters registers := by
  simp [encodeRegisters, Registers.update, Nat.pow_succ]
  ac_rfl

theorem encode_update_r4_increment (registers : Registers) :
    encodeRegisters (registers.update 4 (registers 4 + 1)) =
      5 * encodeRegisters registers := by
  simp [encodeRegisters, Registers.update, Nat.pow_succ]
  ac_rfl

theorem encode_update_r5_increment (registers : Registers) :
    encodeRegisters (registers.update 5 (registers 5 + 1)) =
      2 * encodeRegisters registers := by
  simp [encodeRegisters, Registers.update, Nat.pow_succ]
  ac_rfl

theorem encode_update_r6_increment (registers : Registers) :
    encodeRegisters (registers.update 6 (registers 6 + 1)) =
      3 * encodeRegisters registers := by
  simp [encodeRegisters, Registers.update, Nat.pow_succ]
  ac_rfl

theorem encode_update_r7_increment (registers : Registers) :
    encodeRegisters (registers.update 7 (registers 7 + 1)) =
      17 * encodeRegisters registers := by
  simp [encodeRegisters, Registers.update, Nat.pow_succ]
  ac_rfl

private theorem predecessor_form {value : Nat} (positive : value ≠ 0) :
    value = value - 1 + 1 := by omega

theorem encode_update_r0_decrement (registers : Registers)
    (positive : registers 0 ≠ 0) :
    encodeRegisters registers =
      7 * encodeRegisters (registers.update 0 (registers 0 - 1)) := by
  simp [encodeRegisters, Registers.update]
  rw [predecessor_form positive]
  simp only [Nat.pow_succ]
  have normalize : (registers 0 - 1) + 1 - 1 = registers 0 - 1 := by omega
  rw [normalize]
  ac_rfl

theorem encode_update_r1_decrement (registers : Registers)
    (positive : registers 1 ≠ 0) :
    encodeRegisters registers =
      11 * encodeRegisters (registers.update 1 (registers 1 - 1)) := by
  simp [encodeRegisters, Registers.update]
  rw [predecessor_form positive]
  simp only [Nat.pow_succ]
  have normalize : (registers 1 - 1) + 1 - 1 = registers 1 - 1 := by omega
  rw [normalize]
  ac_rfl

theorem encode_update_r2_decrement (registers : Registers)
    (positive : registers 2 ≠ 0) :
    encodeRegisters registers =
      13 * encodeRegisters (registers.update 2 (registers 2 - 1)) := by
  simp [encodeRegisters, Registers.update]
  rw [predecessor_form positive]
  simp only [Nat.pow_succ]
  have normalize : (registers 2 - 1) + 1 - 1 = registers 2 - 1 := by omega
  rw [normalize]
  ac_rfl

theorem encode_update_r4_decrement (registers : Registers)
    (positive : registers 4 ≠ 0) :
    encodeRegisters registers =
      5 * encodeRegisters (registers.update 4 (registers 4 - 1)) := by
  simp [encodeRegisters, Registers.update]
  rw [predecessor_form positive]
  simp only [Nat.pow_succ]
  have normalize : (registers 4 - 1) + 1 - 1 = registers 4 - 1 := by omega
  rw [normalize]
  ac_rfl

theorem encode_update_r5_decrement (registers : Registers)
    (positive : registers 5 ≠ 0) :
    encodeRegisters registers =
      2 * encodeRegisters (registers.update 5 (registers 5 - 1)) := by
  simp [encodeRegisters, Registers.update]
  rw [predecessor_form positive]
  simp only [Nat.pow_succ]
  have normalize : (registers 5 - 1) + 1 - 1 = registers 5 - 1 := by omega
  rw [normalize]
  ac_rfl

theorem encode_update_r6_decrement (registers : Registers)
    (positive : registers 6 ≠ 0) :
    encodeRegisters registers =
      3 * encodeRegisters (registers.update 6 (registers 6 - 1)) := by
  simp [encodeRegisters, Registers.update]
  rw [predecessor_form positive]
  simp only [Nat.pow_succ]
  have normalize : (registers 6 - 1) + 1 - 1 = registers 6 - 1 := by omega
  rw [normalize]
  ac_rfl

theorem encode_update_r7_decrement (registers : Registers)
    (positive : registers 7 ≠ 0) :
    encodeRegisters registers =
      17 * encodeRegisters (registers.update 7 (registers 7 - 1)) := by
  simp [encodeRegisters, Registers.update]
  rw [predecessor_form positive]
  simp only [Nat.pow_succ]
  have normalize : (registers 7 - 1) + 1 - 1 = registers 7 - 1 := by omega
  rw [normalize]
  ac_rfl

end Mortality.SourceMachine.U20Compilation
