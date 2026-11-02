import Mortality.OneCounter.Program

/-!
# Prime-factor counter encoding

The source counters `u` and `v`, together with the successful-decrement
clock `t`, are encoded by

`code u v t + 1 = 2^u * 3^v * 5^t`.

The three successor identities below are the arithmetic core of the
four simulated source updates.  They are proved over natural numbers,
including all boundary cases; no divisibility side condition is hidden
in truncated subtraction.
-/

namespace Mortality.OneCounter

/-- The positive number whose predecessor is stored by the one-counter program. -/
def primeClock (u v t : Nat) : Nat :=
  2 ^ u * 3 ^ v * 5 ^ t

/-- Encode two source counters and a successful-decrement clock. -/
def primeCode (u v t : Nat) : Nat :=
  primeClock u v t - 1

theorem primeClock_pos (u v t : Nat) : 0 < primeClock u v t := by
  have twoPositive : 0 < 2 ^ u :=
    Nat.pow_pos_iff.mpr (.inl (by decide))
  have threePositive : 0 < 3 ^ v :=
    Nat.pow_pos_iff.mpr (.inl (by decide))
  have fivePositive : 0 < 5 ^ t :=
    Nat.pow_pos_iff.mpr (.inl (by decide))
  exact Nat.mul_pos (Nat.mul_pos twoPositive threePositive) fivePositive

theorem primeCode_add_one (u v t : Nat) :
    primeCode u v t + 1 = primeClock u v t := by
  have positive := primeClock_pos u v t
  unfold primeCode
  omega

theorem primeClock_succ_zero (u v t : Nat) :
    primeClock (u + 1) v t = 2 * primeClock u v t := by
  simp [primeClock, Nat.pow_succ, Nat.mul_assoc, Nat.mul_comm]

theorem primeClock_succ_one (u v t : Nat) :
    primeClock u (v + 1) t = 3 * primeClock u v t := by
  simp [primeClock, Nat.pow_succ, Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]

theorem primeClock_succ_time (u v t : Nat) :
    primeClock u v (t + 1) = 5 * primeClock u v t := by
  simp [primeClock, Nat.pow_succ, Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]

/-- Incrementing the first exponent gives the odd binary progression. -/
theorem primeCode_succ_zero (u v t : Nat) :
    primeCode (u + 1) v t = 2 * primeCode u v t + 1 := by
  have currentPositive := primeClock_pos u v t
  rw [primeCode, primeClock_succ_zero, primeCode]
  omega

/-- Incrementing the second exponent gives the ternary-two progression. -/
theorem primeCode_succ_one (u v t : Nat) :
    primeCode u (v + 1) t = 3 * primeCode u v t + 2 := by
  have currentPositive := primeClock_pos u v t
  rw [primeCode, primeClock_succ_one, primeCode]
  omega

/-- Incrementing the clock gives the fivefold-four progression. -/
theorem primeCode_succ_time (u v t : Nat) :
    primeCode u v (t + 1) = 5 * primeCode u v t + 4 := by
  have currentPositive := primeClock_pos u v t
  rw [primeCode, primeClock_succ_time, primeCode]
  omega

/-- Binary division removes one unit from the first exponent. -/
theorem divideTwo_primeCode (u v t : Nat) :
    Instruction.evaluate .divideTwoOdd (primeCode (u + 1) v t) =
      some (primeCode u v t) := by
  rw [primeCode_succ_zero]
  exact Instruction.evaluate_divideTwoOdd _

/-- Ternary division removes one unit from the second exponent. -/
theorem divideThree_primeCode (u v t : Nat) :
    Instruction.evaluate .divideThreeTwo (primeCode u (v + 1) t) =
      some (primeCode u v t) := by
  rw [primeCode_succ_one]
  exact Instruction.evaluate_divideThreeTwo _

/-- The first contraction exchanges one unit of the clock for exponent two. -/
theorem contractTwo_primeCode (u v t : Nat) :
    Instruction.evaluate .contractTwo (primeCode u v (t + 1)) =
      some (primeCode (u + 1) v t) := by
  rw [primeCode_succ_time, primeCode_succ_zero]
  exact Instruction.evaluate_contractTwo _

/-- The second contraction exchanges one unit of the clock for exponent three. -/
theorem contractThree_primeCode (u v t : Nat) :
    Instruction.evaluate .contractThree (primeCode u v (t + 1)) =
      some (primeCode u (v + 1) t) := by
  rw [primeCode_succ_time, primeCode_succ_one]
  exact Instruction.evaluate_contractThree _

/-- When the first exponent is zero, its code has residue zero modulo two. -/
theorem primeCode_zero_mod_two (v t : Nat) :
    primeCode 0 v t % 2 = 0 := by
  have clockResidue : primeClock 0 v t % 2 = 1 := by
    simp [primeClock, Nat.mul_mod, Nat.pow_mod]
  have successorResidue : (primeCode 0 v t + 1) % 2 = 1 := by
    rw [primeCode_add_one]
    exact clockResidue
  cases Nat.mod_two_eq_zero_or_one (primeCode 0 v t) with
  | inl isZero => exact isZero
  | inr isOne => simp [Nat.add_mod, isOne] at successorResidue

/-- A positive first exponent gives residue one modulo two. -/
theorem primeCode_succ_mod_two (u v t : Nat) :
    primeCode (u + 1) v t % 2 = 1 := by
  rw [primeCode_succ_zero]
  simp [Nat.add_mod]

/-- The modulo-two test is enabled exactly when the first exponent is zero. -/
theorem testTwo_primeCode_iff (u v t : Nat) :
    Instruction.evaluate (.congruenceTest 2 [0]) (primeCode u v t) =
        some (primeCode u v t) ↔
      u = 0 := by
  cases u with
  | zero => simp [Instruction.evaluate, primeCode_zero_mod_two]
  | succ u => simp [Instruction.evaluate, primeCode_succ_mod_two]

/-- Powers of two have residue one or two modulo three. -/
theorem pow_two_mod_three (exponent : Nat) :
    2 ^ exponent % 3 = 1 ∨ 2 ^ exponent % 3 = 2 := by
  induction exponent with
  | zero => simp
  | succ exponent inductionHypothesis =>
      rw [Nat.pow_succ, Nat.mul_mod]
      rcases inductionHypothesis with residue | residue <;> simp [residue]

/-- Powers of five have residue one or two modulo three. -/
theorem pow_five_mod_three (exponent : Nat) :
    5 ^ exponent % 3 = 1 ∨ 5 ^ exponent % 3 = 2 := by
  induction exponent with
  | zero => simp
  | succ exponent inductionHypothesis =>
      rw [Nat.pow_succ, Nat.mul_mod]
      rcases inductionHypothesis with residue | residue <;> simp [residue]

/-- With second exponent zero, the positive clock is nonzero modulo three. -/
theorem primeClock_zero_one_mod_three (u t : Nat) :
    primeClock u 0 t % 3 = 1 ∨ primeClock u 0 t % 3 = 2 := by
  have twoResidue := pow_two_mod_three u
  have fiveResidue := pow_five_mod_three t
  simp only [primeClock, Nat.pow_zero, Nat.mul_one]
  rw [Nat.mul_mod]
  rcases twoResidue with twoResidue | twoResidue <;>
    rcases fiveResidue with fiveResidue | fiveResidue <;>
      simp [twoResidue, fiveResidue]

/-- With second exponent zero, the stored predecessor has residue zero or one. -/
theorem primeCode_zero_one_mod_three (u t : Nat) :
    primeCode u 0 t % 3 = 0 ∨ primeCode u 0 t % 3 = 1 := by
  have clockResidue := primeClock_zero_one_mod_three u t
  have codeBound := Nat.mod_lt (primeCode u 0 t) (by decide : 0 < 3)
  have residueCases : primeCode u 0 t % 3 = 0 ∨
      primeCode u 0 t % 3 = 1 ∨ primeCode u 0 t % 3 = 2 := by
    omega
  rcases residueCases with isZero | isOne | isTwo
  · exact .inl isZero
  · exact .inr isOne
  · have clockZero : primeClock u 0 t % 3 = 0 := by
      rw [← primeCode_add_one]
      simp [Nat.add_mod, isTwo]
    rcases clockResidue with clockOne | clockTwo <;> omega

/-- A positive second exponent gives residue two modulo three. -/
theorem primeCode_succ_mod_three (u v t : Nat) :
    primeCode u (v + 1) t % 3 = 2 := by
  rw [primeCode_succ_one]
  simp [Nat.add_mod]

/-- The modulo-three test is enabled exactly when the second exponent is zero. -/
theorem testThree_primeCode_iff (u v t : Nat) :
    Instruction.evaluate (.congruenceTest 3 [0, 1]) (primeCode u v t) =
        some (primeCode u v t) ↔
      v = 0 := by
  cases v with
  | zero =>
      rcases primeCode_zero_one_mod_three u t with residue | residue <;>
        simp [Instruction.evaluate, residue]
  | succ v => simp [Instruction.evaluate, primeCode_succ_mod_three]

/-- The initial source pair `(input, 0)` has the manuscript's code `2^input - 1`. -/
theorem primeCode_initial (input : Nat) :
    primeCode input 0 0 = 2 ^ input - 1 := by
  simp [primeCode, primeClock]

end Mortality.OneCounter
