import Mortality.SourceMachine.U20Decoder

/-!
# Arithmetic of Korec U20's instruction reader

States `q1` through `q15` scan consecutive candidate divisors of the fixed
program number plus one.  This file proves the unbounded counter loops used
by one candidate test.  The proof is expressed through `rotationPair`: after
`t` probes around a positive candidate `d`, its two components are exactly
the contents of `R5` and `R6`.
-/

namespace Mortality.SourceMachine.KorecU20Interpreter

open Mortality.SourceMachine
open Mortality.SourceMachine.KorecU20

/-- Move the program number from `R1` to `R7`.  State `q1` takes its zero
branch only after the whole value has been transferred. -/
theorem reader_transfer_program
    (r0 r2 r3 r4 r5 r6 program accumulator : Nat) :
    Reaches KorecU20.step
      (configuration 1 r0 program r2 r3 r4 r5 r6 accumulator)
      (configuration 6 r0 0 r2 r3 r4 r5 r6 (accumulator + program)) := by
  induction program generalizing accumulator with
  | zero =>
      exact Reaches.single (by
        simp [KorecU20.step, KorecU20.instruction, configuration])
  | succ program inductionHypothesis =>
      have firstStep :
          KorecU20.step
              (configuration 1 r0 (program + 1) r2 r3 r4 r5 r6 accumulator) =
            some (configuration 3 r0 program r2 r3 r4 r5 r6 accumulator) := by
        simp [KorecU20.step, KorecU20.instruction, configuration]
      have secondStep :
          KorecU20.step
              (configuration 3 r0 program r2 r3 r4 r5 r6 accumulator) =
            some (configuration 1 r0 program r2 r3 r4 r5 r6 (accumulator + 1)) := by
        simp [KorecU20.step, KorecU20.instruction, configuration]
      have suffix := inductionHypothesis (accumulator := accumulator + 1)
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        (Reaches.single firstStep).trans <|
          (Reaches.single secondStep).trans suffix

/-- State `q4`, with the intervening `q6` increment, transfers all of `R5`
to `R6`. -/
theorem reader_reload_loop
    (r0 r1 r2 r3 r4 amount r6 r7 : Nat) :
    Reaches KorecU20.step
      (configuration 4 r0 r1 r2 r3 r4 amount r6 r7)
      (configuration 7 r0 r1 r2 r3 r4 0 (r6 + amount) r7) := by
  induction amount generalizing r6 with
  | zero =>
      have fiveVal : (5 : Fin 8).val = 5 := by decide
      exact Reaches.single (by
        simp [KorecU20.step, KorecU20.instruction, configuration,
          registers, fiveVal])
  | succ amount inductionHypothesis =>
      have firstStep :
          KorecU20.step
              (configuration 4 r0 r1 r2 r3 r4 (amount + 1) r6 r7) =
            some (configuration 6 r0 r1 r2 r3 r4 amount r6 r7) := by
        simp [KorecU20.step, KorecU20.instruction, configuration]
      have secondStep :
          KorecU20.step
              (configuration 6 r0 r1 r2 r3 r4 amount r6 r7) =
            some (configuration 4 r0 r1 r2 r3 r4 amount (r6 + 1) r7) := by
        simp [KorecU20.step, KorecU20.instruction, configuration]
      have suffix := inductionHypothesis (r6 := r6 + 1)
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        (Reaches.single firstStep).trans <|
          (Reaches.single secondStep).trans suffix

/-- Entering at `q6` increases the candidate divisor by one before the
reload. -/
theorem reader_prepare_candidate
    (r0 r1 r2 r3 r4 r5 r6 r7 : Nat) :
    Reaches KorecU20.step
      (configuration 6 r0 r1 r2 r3 r4 r5 r6 r7)
      (configuration 7 r0 r1 r2 r3 r4 0 (r5 + r6 + 1) r7) := by
  have firstStep :
      KorecU20.step (configuration 6 r0 r1 r2 r3 r4 r5 r6 r7) =
        some (configuration 4 r0 r1 r2 r3 r4 r5 (r6 + 1) r7) := by
    simp [KorecU20.step, KorecU20.instruction, configuration]
  have suffix := reader_reload_loop r0 r1 r2 r3 r4 r5 (r6 + 1) r7
  simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
    (Reaches.single firstStep).trans suffix

/-- Pure rotation of the two reader registers after a sequence of probes.
When the right component is empty, the next probe first reloads the left
component into the right one. -/
def rotationPair (candidate : Nat) : Nat → Nat × Nat
  | 0 => (0, candidate)
  | probes + 1 =>
      let previous := rotationPair candidate probes
      if previous.2 = 0 then (1, previous.1 - 1)
      else (previous.1 + 1, previous.2 - 1)

theorem rotationPair_sum (candidate : Nat) (candidatePositive : 0 < candidate) :
    ∀ probes, (rotationPair candidate probes).1 +
      (rotationPair candidate probes).2 = candidate := by
  intro probes
  induction probes with
  | zero => simp [rotationPair]
  | succ probes inductionHypothesis =>
      simp only [rotationPair]
      split
      · rename_i rightZero
        have leftPositive : 0 < (rotationPair candidate probes).1 := by omega
        omega
      · rename_i rightNonzero
        omega

theorem succ_mod_eq_succ_of_lt
    {value modulus remainder : Nat}
    (modulusPositive : 0 < modulus)
    (remainderEq : value % modulus = remainder)
    (bound : remainder + 1 < modulus) :
    (value + 1) % modulus = remainder + 1 := by
  rw [Nat.add_mod, remainderEq]
  have oneMod : 1 % modulus = 1 := Nat.mod_eq_of_lt (by omega)
  rw [oneMod, Nat.mod_eq_of_lt bound]

theorem succ_mod_eq_zero_of_eq
    {value modulus remainder : Nat}
    (modulusPositive : 0 < modulus)
    (remainderEq : value % modulus = remainder)
    (last : remainder + 1 = modulus) :
    (value + 1) % modulus = 0 := by
  by_cases remainderZero : remainder = 0
  · subst remainder
    have modulusOne : modulus = 1 := by omega
    subst modulus
    have bound := Nat.mod_lt value (by decide : 0 < 1)
    omega
  · rw [Nat.add_mod, remainderEq]
    have oneMod : 1 % modulus = 1 := Nat.mod_eq_of_lt (by omega)
    rw [oneMod, last]
    simp

theorem rotationPair_one (probes : Nat) :
    rotationPair 1 (probes + 1) = (1, 0) := by
  induction probes with
  | zero => simp [rotationPair]
  | succ probes inductionHypothesis =>
      change
        (if (rotationPair 1 (probes + 1)).2 = 0 then
          (1, (rotationPair 1 (probes + 1)).1 - 1)
        else
          ((rotationPair 1 (probes + 1)).1 + 1,
            (rotationPair 1 (probes + 1)).2 - 1)) = (1, 0)
      rw [inductionHypothesis]
      rfl

/-- Closed form for the reader rotation after a positive number of probes.
At a multiple of the candidate, the completed cycle is represented by
`(candidate,0)` rather than `(0,candidate)`. -/
theorem rotationPair_formula (candidate : Nat) (candidatePositive : 0 < candidate) :
    ∀ probes,
      rotationPair candidate (probes + 1) =
        if (probes + 1) % candidate = 0 then (candidate, 0)
        else
          ((probes + 1) % candidate,
            candidate - (probes + 1) % candidate) := by
  by_cases candidateOne : candidate = 1
  · subst candidate
    intro probes
    rw [rotationPair_one]
    have modOne : (probes + 1) % 1 = 0 := by
      have bound := Nat.mod_lt (probes + 1) (by decide : 0 < 1)
      omega
    rw [modOne]
    rfl
  · have candidateLarge : 1 < candidate := by omega
    intro probes
    induction probes with
    | zero =>
        simp [rotationPair, Nat.mod_eq_of_lt candidateLarge,
          Nat.ne_of_gt candidatePositive]
    | succ probes inductionHypothesis =>
        generalize remainderEq : (probes + 1) % candidate = remainder
        have remainderBound : remainder < candidate := by
          rw [← remainderEq]
          exact Nat.mod_lt _ candidatePositive
        have remainderEqSaved := remainderEq
        rw [rotationPair, inductionHypothesis, remainderEq]
        by_cases remainderZero : remainder = 0
        · rw [if_pos remainderZero]
          simp only [if_pos]
          have nextRemainder' :
              (probes + 1 + 1) % candidate = remainder + 1 :=
            succ_mod_eq_succ_of_lt candidatePositive remainderEqSaved (by omega)
          have nextRemainder : (probes + 1 + 1) % candidate = 1 := by omega
          rw [nextRemainder]
          simp
        · rw [if_neg remainderZero]
          have remainderPositive : 0 < remainder := by omega
          by_cases last : remainder + 1 = candidate
          · have nextRemainder : (probes + 1 + 1) % candidate = 0 :=
              succ_mod_eq_zero_of_eq candidatePositive remainderEqSaved last
            have rightOne : candidate - remainder = 1 := by omega
            rw [rightOne]
            simp [nextRemainder]
            omega
          · have nextBound : remainder + 1 < candidate := by omega
            have nextRemainder : (probes + 1 + 1) % candidate = remainder + 1 :=
              succ_mod_eq_succ_of_lt candidatePositive remainderEqSaved nextBound
            have rightPositive : candidate - remainder ≠ 0 := by omega
            rw [if_neg rightPositive, nextRemainder]
            simp
            omega

theorem rotationPair_right_eq_zero_iff_dvd
    (candidate probes : Nat) (candidatePositive : 0 < candidate)
    (probesPositive : 0 < probes) :
    (rotationPair candidate probes).2 = 0 ↔ candidate ∣ probes := by
  obtain ⟨predecessor, rfl⟩ := Nat.exists_eq_succ_of_ne_zero
    (Nat.ne_of_gt probesPositive)
  rw [rotationPair_formula candidate candidatePositive predecessor]
  by_cases remainderZero : (predecessor + 1) % candidate = 0
  · constructor
    · intro _
      exact Nat.dvd_of_mod_eq_zero remainderZero
    · intro _
      simp [remainderZero]
  · have remainderBound := Nat.mod_lt (predecessor + 1) candidatePositive
    have differenceNonzero :
        candidate - (predecessor + 1) % candidate ≠ 0 := by omega
    constructor
    · intro rightZero
      simp [remainderZero] at rightZero
      exact (differenceNonzero rightZero).elim
    · intro divides
      exact (remainderZero (Nat.mod_eq_zero_of_dvd divides)).elim

theorem rotationPair_left_eq_mod_of_not_dvd
    (candidate probes : Nat) (candidatePositive : 0 < candidate)
    (probesPositive : 0 < probes) (notDivides : ¬candidate ∣ probes) :
    (rotationPair candidate probes).1 = probes % candidate := by
  obtain ⟨predecessor, rfl⟩ := Nat.exists_eq_succ_of_ne_zero
    (Nat.ne_of_gt probesPositive)
  rw [rotationPair_formula candidate candidatePositive predecessor]
  have remainderNonzero : (predecessor + 1) % candidate ≠ 0 := by
    intro remainderZero
    exact notDivides (Nat.dvd_of_mod_eq_zero remainderZero)
  simp [remainderNonzero]

theorem rotationPair_eq_of_dvd
    (candidate program : Nat) (candidatePositive : 0 < candidate)
    (divides : candidate ∣ program + 1) :
    rotationPair candidate (program + 1) = (candidate, 0) := by
  rw [rotationPair_formula candidate candidatePositive program]
  have remainderZero := Nat.mod_eq_zero_of_dvd divides
  simp [remainderZero]

theorem rotationPair_eq_of_not_dvd
    (candidate program : Nat) (candidatePositive : 0 < candidate)
    (notDivides : ¬candidate ∣ program + 1) :
    rotationPair candidate (program + 1) =
      ((program + 1) % candidate,
        candidate - (program + 1) % candidate) := by
  rw [rotationPair_formula candidate candidatePositive program]
  have remainderNonzero : (program + 1) % candidate ≠ 0 := by
    intro remainderZero
    exact notDivides (Nat.dvd_of_mod_eq_zero remainderZero)
  simp [remainderNonzero]

theorem mod_complement_positive
    (candidate program : Nat) (candidatePositive : 0 < candidate) :
    0 < candidate - (program + 1) % candidate := by
  have remainderBound := Nat.mod_lt (program + 1) candidatePositive
  omega

/-- One ordinary data probe, when `R6` is already positive. -/
theorem reader_data_probe_positive
    (r0 r2 r3 r4 r5 r6 r1 r7 : Nat) :
    Reaches KorecU20.step
      (configuration 7 r0 r1 r2 r3 r4 r5 (r6 + 1) (r7 + 1))
      (configuration 7 r0 (r1 + 1) r2 r3 r4 (r5 + 1) r6 r7) := by
  have firstStep :
      KorecU20.step
          (configuration 7 r0 r1 r2 r3 r4 r5 (r6 + 1) (r7 + 1)) =
        some (configuration 9 r0 r1 r2 r3 r4 r5 r6 (r7 + 1)) := by
    simp [KorecU20.step, KorecU20.instruction, configuration]
  have secondStep :
      KorecU20.step
          (configuration 9 r0 r1 r2 r3 r4 r5 r6 (r7 + 1)) =
        some (configuration 10 r0 r1 r2 r3 r4 (r5 + 1) r6 (r7 + 1)) := by
    simp [KorecU20.step, KorecU20.instruction, configuration]
  have thirdStep :
      KorecU20.step
          (configuration 10 r0 r1 r2 r3 r4 (r5 + 1) r6 (r7 + 1)) =
        some (configuration 12 r0 r1 r2 r3 r4 (r5 + 1) r6 r7) := by
    simp [KorecU20.step, KorecU20.instruction, configuration]
  have fourthStep :
      KorecU20.step
          (configuration 12 r0 r1 r2 r3 r4 (r5 + 1) r6 r7) =
        some (configuration 7 r0 (r1 + 1) r2 r3 r4 (r5 + 1) r6 r7) := by
    simp [KorecU20.step, KorecU20.instruction, configuration]
  exact (Reaches.single firstStep).trans <|
    (Reaches.single secondStep).trans <|
      (Reaches.single thirdStep).trans (Reaches.single fourthStep)

/-- The final probe differs only at `q10`: with `R7=0`, it enters `q13`
without increasing `R1`. -/
theorem reader_final_probe_positive
    (r0 r1 r2 r3 r4 r5 r6 : Nat) :
    Reaches KorecU20.step
      (configuration 7 r0 r1 r2 r3 r4 r5 (r6 + 1) 0)
      (configuration 13 r0 r1 r2 r3 r4 (r5 + 1) r6 0) := by
  have firstStep :
      KorecU20.step
          (configuration 7 r0 r1 r2 r3 r4 r5 (r6 + 1) 0) =
        some (configuration 9 r0 r1 r2 r3 r4 r5 r6 0) := by
    simp [KorecU20.step, KorecU20.instruction, configuration]
  have secondStep :
      KorecU20.step
          (configuration 9 r0 r1 r2 r3 r4 r5 r6 0) =
        some (configuration 10 r0 r1 r2 r3 r4 (r5 + 1) r6 0) := by
    simp [KorecU20.step, KorecU20.instruction, configuration]
  have thirdStep :
      KorecU20.step
          (configuration 10 r0 r1 r2 r3 r4 (r5 + 1) r6 0) =
        some (configuration 13 r0 r1 r2 r3 r4 (r5 + 1) r6 0) := by
    simp [KorecU20.step, KorecU20.instruction, configuration]
  exact (Reaches.single firstStep).trans <|
    (Reaches.single secondStep).trans (Reaches.single thirdStep)

/-- Reload an exhausted positive candidate and perform one ordinary data
probe. -/
theorem reader_data_probe_zero
    (r0 r2 r3 r4 r1 r7 candidate : Nat) (candidatePositive : 0 < candidate) :
    Reaches KorecU20.step
      (configuration 7 r0 r1 r2 r3 r4 candidate 0 (r7 + 1))
      (configuration 7 r0 (r1 + 1) r2 r3 r4 1 (candidate - 1) r7) := by
  have enterReload :
      KorecU20.step
          (configuration 7 r0 r1 r2 r3 r4 candidate 0 (r7 + 1)) =
        some (configuration 4 r0 r1 r2 r3 r4 candidate 0 (r7 + 1)) := by
    simp [KorecU20.step, KorecU20.instruction, configuration]
  have reload := reader_reload_loop r0 r1 r2 r3 r4 candidate 0 (r7 + 1)
  have probe := reader_data_probe_positive r0 r2 r3 r4 0 (candidate - 1) r1 r7
  have candidateEq : candidate - 1 + 1 = candidate := by omega
  rw [candidateEq] at probe
  have reload' :
      Reaches KorecU20.step
        (configuration 4 r0 r1 r2 r3 r4 candidate 0 (r7 + 1))
        (configuration 7 r0 r1 r2 r3 r4 0 candidate (r7 + 1)) := by
    simpa using reload
  have probe' :
      Reaches KorecU20.step
        (configuration 7 r0 r1 r2 r3 r4 0 candidate (r7 + 1))
        (configuration 7 r0 (r1 + 1) r2 r3 r4 1 (candidate - 1) r7) := by
    simpa using probe
  exact (Reaches.single enterReload).trans <| reload'.trans probe'

/-- Reload an exhausted positive candidate and perform the final probe. -/
theorem reader_final_probe_zero
    (r0 r1 r2 r3 r4 candidate : Nat) (candidatePositive : 0 < candidate) :
    Reaches KorecU20.step
      (configuration 7 r0 r1 r2 r3 r4 candidate 0 0)
      (configuration 13 r0 r1 r2 r3 r4 1 (candidate - 1) 0) := by
  have enterReload :
      KorecU20.step (configuration 7 r0 r1 r2 r3 r4 candidate 0 0) =
        some (configuration 4 r0 r1 r2 r3 r4 candidate 0 0) := by
    have sixVal : (6 : Fin 8).val = 6 := by decide
    simp [KorecU20.step, KorecU20.instruction, configuration,
      registers, sixVal]
  have reload := reader_reload_loop r0 r1 r2 r3 r4 candidate 0 0
  have probe := reader_final_probe_positive r0 r1 r2 r3 r4 0 (candidate - 1)
  have candidateEq : candidate - 1 + 1 = candidate := by omega
  rw [candidateEq] at probe
  have reload' :
      Reaches KorecU20.step
        (configuration 4 r0 r1 r2 r3 r4 candidate 0 0)
        (configuration 7 r0 r1 r2 r3 r4 0 candidate 0) := by
    simpa using reload
  have probe' :
      Reaches KorecU20.step
        (configuration 7 r0 r1 r2 r3 r4 0 candidate 0)
        (configuration 13 r0 r1 r2 r3 r4 1 (candidate - 1) 0) := by
    simpa using probe
  exact (Reaches.single enterReload).trans <| reload'.trans probe'

/-- One data probe advances the pure rotation model. -/
theorem reader_data_probe_rotation
    (candidate probes r0 r2 r3 r4 r1 r7 : Nat)
    (candidatePositive : 0 < candidate) :
    Reaches KorecU20.step
      (configuration 7 r0 r1 r2 r3 r4
        (rotationPair candidate probes).1
        (rotationPair candidate probes).2 (r7 + 1))
      (configuration 7 r0 (r1 + 1) r2 r3 r4
        (rotationPair candidate (probes + 1)).1
        (rotationPair candidate (probes + 1)).2 r7) := by
  simp only [rotationPair]
  by_cases rightZero : (rotationPair candidate probes).2 = 0
  · rw [if_pos rightZero]
    have sum := rotationPair_sum candidate candidatePositive probes
    have leftEq : (rotationPair candidate probes).1 = candidate := by omega
    rw [rightZero, leftEq]
    exact reader_data_probe_zero r0 r2 r3 r4 r1 r7 candidate candidatePositive
  · rw [if_neg rightZero]
    obtain ⟨right, rightEq⟩ := Nat.exists_eq_succ_of_ne_zero rightZero
    rw [rightEq]
    exact reader_data_probe_positive r0 r2 r3 r4
      (rotationPair candidate probes).1 right r1 r7

/-- Consume an arbitrary number of genuine program-data units. -/
theorem reader_consume_data
    (candidate offset amount r0 r2 r3 r4 r1 r7 : Nat)
    (candidatePositive : 0 < candidate) :
    Reaches KorecU20.step
      (configuration 7 r0 r1 r2 r3 r4
        (rotationPair candidate offset).1
        (rotationPair candidate offset).2 (r7 + amount))
      (configuration 7 r0 (r1 + amount) r2 r3 r4
        (rotationPair candidate (offset + amount)).1
        (rotationPair candidate (offset + amount)).2 r7) := by
  induction amount generalizing offset r1 r7 with
  | zero => simp; exact Reaches.refl _
  | succ amount inductionHypothesis =>
      have first := reader_data_probe_rotation candidate offset r0 r2 r3 r4 r1
        (r7 + amount) candidatePositive
      have suffix := inductionHypothesis (offset := offset + 1)
        (r1 := r1 + 1) (r7 := r7)
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using first.trans suffix

/-- After all `program` data units have returned to `R1`, one extra probe
produces the remainder pair for `program+1` and enters the pure-zero-test
replacement at `q13`. -/
theorem reader_divide_candidate
    (candidate program r0 r2 r3 r4 : Nat)
    (candidatePositive : 0 < candidate) :
    Reaches KorecU20.step
      (configuration 7 r0 0 r2 r3 r4 0 candidate program)
      (configuration 13 r0 program r2 r3 r4
        (rotationPair candidate (program + 1)).1
        (rotationPair candidate (program + 1)).2 0) := by
  have consumed := reader_consume_data candidate 0 program r0 r2 r3 r4 0 0
    candidatePositive
  simp only [rotationPair, Nat.zero_add] at consumed
  by_cases rightZero : (rotationPair candidate program).2 = 0
  · have sum := rotationPair_sum candidate candidatePositive program
    have leftEq : (rotationPair candidate program).1 = candidate := by omega
    have final := reader_final_probe_zero r0 program r2 r3 r4 candidate
      candidatePositive
    have consumed' :
        Reaches KorecU20.step
          (configuration 7 r0 0 r2 r3 r4 0 candidate program)
          (configuration 7 r0 program r2 r3 r4 candidate 0 0) := by
      simpa [rightZero, leftEq] using consumed
    simp only [rotationPair]
    rw [if_pos rightZero, leftEq]
    exact consumed'.trans final
  · obtain ⟨rightPredecessor, rightEq⟩ :=
      Nat.exists_eq_succ_of_ne_zero rightZero
    have final := reader_final_probe_positive r0 program r2 r3 r4
      (rotationPair candidate program).1 rightPredecessor
    have consumed' :
        Reaches KorecU20.step
          (configuration 7 r0 0 r2 r3 r4 0 candidate program)
          (configuration 7 r0 program r2 r3 r4
            (rotationPair candidate program).1 (rightPredecessor + 1) 0) := by
      simpa [rightEq] using consumed
    simp only [rotationPair]
    rw [if_neg rightZero, rightEq]
    simpa using consumed'.trans final

/-- One complete candidate test, starting at the instruction-reader entry.
The incoming sum `R5+R6` is the previous candidate, so `q6` prepares the
next one. -/
theorem reader_test_candidate
    (program previous r0 r2 r3 remaining r5 r6 : Nat)
    (sum : r5 + r6 = previous) :
    Reaches KorecU20.step
      (configuration 1 r0 program r2 r3 remaining r5 r6 0)
      (configuration 13 r0 program r2 r3 remaining
        (rotationPair (previous + 1) (program + 1)).1
        (rotationPair (previous + 1) (program + 1)).2 0) := by
  have transfer := reader_transfer_program r0 r2 r3 remaining r5 r6 program 0
  have prepare := reader_prepare_candidate r0 0 r2 r3 remaining r5 r6 program
  have candidatePositive : 0 < previous + 1 := by omega
  have divide := reader_divide_candidate (previous + 1) program r0 r2 r3
    remaining candidatePositive
  have prepare' :
      Reaches KorecU20.step
        (configuration 6 r0 0 r2 r3 remaining r5 r6 program)
        (configuration 7 r0 0 r2 r3 remaining 0 (previous + 1) program) := by
    simpa [sum, Nat.add_assoc] using prepare
  have transfer' :
      Reaches KorecU20.step
        (configuration 1 r0 program r2 r3 remaining r5 r6 0)
        (configuration 6 r0 0 r2 r3 remaining r5 r6 program) := by
    simpa using transfer
  exact transfer'.trans <| prepare'.trans divide

/-- A zero right component means the candidate divided `program+1`; the
pure zero test at `q13` returns directly to the reader. -/
theorem reader_divisor_continue
    (program r0 r2 r3 remaining left : Nat) :
    Reaches KorecU20.step
      (configuration 13 r0 program r2 r3 remaining left 0 0)
      (configuration 1 r0 program r2 r3 remaining left 0 0) := by
  exact Reaches.single (by
    simp [KorecU20.step, KorecU20.instruction, configuration])

/-- A nonzero right component restores `R6` through `q15`; when the
nondivisor counter is zero, `q14` enters the decoder. -/
theorem reader_nondivisor_found
    (program r0 r2 r3 left right : Nat) :
    Reaches KorecU20.step
      (configuration 13 r0 program r2 r3 0 left (right + 1) 0)
      (configuration 16 r0 program r2 r3 0 left (right + 1) 0) := by
  have firstStep :
      KorecU20.step
          (configuration 13 r0 program r2 r3 0 left (right + 1) 0) =
        some (configuration 15 r0 program r2 r3 0 left right 0) := by
    simp [KorecU20.step, KorecU20.instruction, configuration]
  have secondStep :
      KorecU20.step
          (configuration 15 r0 program r2 r3 0 left right 0) =
        some (configuration 14 r0 program r2 r3 0 left (right + 1) 0) := by
    simp [KorecU20.step, KorecU20.instruction, configuration]
  have thirdStep :
      KorecU20.step
          (configuration 14 r0 program r2 r3 0 left (right + 1) 0) =
        some (configuration 16 r0 program r2 r3 0 left (right + 1) 0) := by
    simp [KorecU20.step, KorecU20.instruction, configuration]
  exact (Reaches.single firstStep).trans <|
    (Reaches.single secondStep).trans (Reaches.single thirdStep)

/-- With a positive remaining-nondivisor count, `q14` consumes one unit and
continues the scan. -/
theorem reader_nondivisor_skip
    (program r0 r2 r3 remaining left right : Nat) :
    Reaches KorecU20.step
      (configuration 13 r0 program r2 r3 (remaining + 1) left (right + 1) 0)
      (configuration 1 r0 program r2 r3 remaining left (right + 1) 0) := by
  have firstStep :
      KorecU20.step
          (configuration 13 r0 program r2 r3 (remaining + 1)
            left (right + 1) 0) =
        some (configuration 15 r0 program r2 r3 (remaining + 1)
          left right 0) := by
    simp [KorecU20.step, KorecU20.instruction, configuration]
  have secondStep :
      KorecU20.step
          (configuration 15 r0 program r2 r3 (remaining + 1) left right 0) =
        some (configuration 14 r0 program r2 r3 (remaining + 1)
          left (right + 1) 0) := by
    simp [KorecU20.step, KorecU20.instruction, configuration]
  have thirdStep :
      KorecU20.step
          (configuration 14 r0 program r2 r3 (remaining + 1)
            left (right + 1) 0) =
        some (configuration 1 r0 program r2 r3 remaining
          left (right + 1) 0) := by
    simp [KorecU20.step, KorecU20.instruction, configuration]
  exact (Reaches.single firstStep).trans <|
    (Reaches.single secondStep).trans (Reaches.single thirdStep)

/-- A finite certificate for the consecutive candidate tests made by the
reader.  `previous` is the candidate immediately before the scan,
`remaining` is the zero-based nondivisor index, and the last two indices are
the code and carry delivered to `q16`. -/
inductive ReaderPlan (program : Nat) : Nat → Nat → Nat → Nat → Prop where
  | found (previous : Nat)
      (rightPositive : 0 < (rotationPair (previous + 1) (program + 1)).2) :
      ReaderPlan program previous 0
        (rotationPair (previous + 1) (program + 1)).1
        (rotationPair (previous + 1) (program + 1)).2
  | divisor {previous remaining code carry : Nat}
      (rightZero : (rotationPair (previous + 1) (program + 1)).2 = 0)
      (suffix : ReaderPlan program (previous + 1) remaining code carry) :
      ReaderPlan program previous remaining code carry
  | skip {previous remaining code carry : Nat}
      (rightPositive : 0 < (rotationPair (previous + 1) (program + 1)).2)
      (suffix : ReaderPlan program (previous + 1) remaining code carry) :
      ReaderPlan program previous (remaining + 1) code carry

/-- Number-theoretic description of a scan to one selected nondivisor.
Unlike `ReaderPlan`, this certificate mentions only ordinary divisibility. -/
inductive NondivisorScan (program : Nat) : Nat → Nat → Nat → Prop where
  | found (previous : Nat) (notDivides : ¬(previous + 1) ∣ program + 1) :
      NondivisorScan program previous 0 (previous + 1)
  | divisor {previous remaining candidate : Nat}
      (divides : previous + 1 ∣ program + 1)
      (suffix : NondivisorScan program (previous + 1) remaining candidate) :
      NondivisorScan program previous remaining candidate
  | skip {previous remaining candidate : Nat}
      (notDivides : ¬(previous + 1) ∣ program + 1)
      (suffix : NondivisorScan program (previous + 1) remaining candidate) :
      NondivisorScan program previous (remaining + 1) candidate

/-- Divisibility certificates compile to concrete reader plans. -/
theorem nondivisorScan_to_readerPlan
    {program previous remaining candidate : Nat}
    (scan : NondivisorScan program previous remaining candidate) :
    ReaderPlan program previous remaining
      ((program + 1) % candidate)
      (candidate - (program + 1) % candidate) := by
  induction scan with
  | found previous notDivides =>
      have candidatePositive : 0 < previous + 1 := by omega
      have pairEq := rotationPair_eq_of_not_dvd (previous + 1) program
        candidatePositive notDivides
      have carryPositive := mod_complement_positive
        (previous + 1) program candidatePositive
      simpa [pairEq] using ReaderPlan.found (program := program) previous
        (by simpa [pairEq] using carryPositive)
  | divisor divides suffix inductionHypothesis =>
      rename_i sourcePrevious sourceRemaining sourceCandidate
      have pairEq := rotationPair_eq_of_dvd (sourcePrevious + 1) program
        (by omega) divides
      exact ReaderPlan.divisor (by simp [pairEq]) inductionHypothesis
  | skip notDivides suffix inductionHypothesis =>
      rename_i sourcePrevious sourceRemaining sourceCandidate
      have candidatePositive : 0 < sourcePrevious + 1 := by omega
      have pairEq := rotationPair_eq_of_not_dvd (sourcePrevious + 1) program
        candidatePositive notDivides
      have carryPositive := mod_complement_positive
        (sourcePrevious + 1) program candidatePositive
      exact ReaderPlan.skip (by simpa [pairEq] using carryPositive)
        inductionHypothesis

/-- Executable bounded search for the selected nondivisor.  It begins with
`previous+1`; divisors do not change the remaining index, while each
nondivisor before the selected one consumes one unit. -/
def scanNondivisor (program : Nat) : Nat → Nat → Nat → Option Nat
  | _, _, 0 => none
  | previous, remaining, fuel + 1 =>
      let candidate := previous + 1
      if candidate ∣ program + 1 then
        scanNondivisor program candidate remaining fuel
      else
        match remaining with
        | 0 => some candidate
        | remaining + 1 => scanNondivisor program candidate remaining fuel

theorem scanNondivisor_sound
    {program previous remaining fuel candidate : Nat}
    (result : scanNondivisor program previous remaining fuel = some candidate) :
    NondivisorScan program previous remaining candidate := by
  induction fuel generalizing previous remaining with
  | zero => simp [scanNondivisor] at result
  | succ fuel inductionHypothesis =>
      by_cases divides : previous + 1 ∣ program + 1
      · have suffixResult :
            scanNondivisor program (previous + 1) remaining fuel = some candidate := by
          simpa [scanNondivisor, divides] using result
        exact NondivisorScan.divisor divides
          (inductionHypothesis suffixResult)
      · cases remaining with
        | zero =>
            simp [scanNondivisor, divides] at result
            subst candidate
            exact NondivisorScan.found previous divides
        | succ remaining =>
            have suffixResult :
                scanNondivisor program (previous + 1) remaining fuel =
                  some candidate := by
              simpa [scanNondivisor, divides] using result
            exact NondivisorScan.skip divides
              (inductionHypothesis suffixResult)

/-- A successful bounded search produces the exact operational reader
certificate and its arithmetic output. -/
theorem readerPlan_of_scanNondivisor
    {program previous remaining fuel candidate : Nat}
    (result : scanNondivisor program previous remaining fuel = some candidate) :
    ReaderPlan program previous remaining
      ((program + 1) % candidate)
      (candidate - (program + 1) % candidate) :=
  nondivisorScan_to_readerPlan (scanNondivisor_sound result)

/-- Every finite reader certificate is realized by the concrete U20 table. -/
theorem reader_plan_correct
    {program previous remaining code carry : Nat}
    (plan : ReaderPlan program previous remaining code carry)
    (r0 r2 r3 r5 r6 : Nat) (sum : r5 + r6 = previous) :
    Reaches KorecU20.step
      (configuration 1 r0 program r2 r3 remaining r5 r6 0)
      (configuration 16 r0 program r2 r3 0 code carry 0) := by
  induction plan generalizing r5 r6 with
  | found previous rightPositive =>
      have tested := reader_test_candidate program previous r0 r2 r3 0 r5 r6 sum
      obtain ⟨right, rightEq⟩ :=
        Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt rightPositive)
      have found := reader_nondivisor_found program r0 r2 r3
        (rotationPair (previous + 1) (program + 1)).1 right
      rw [rightEq] at tested ⊢
      simpa using tested.trans found
  | divisor rightZero suffix inductionHypothesis =>
      rename_i sourcePrevious sourceRemaining sourceCode sourceCarry
      have tested := reader_test_candidate program sourcePrevious r0 r2 r3 sourceRemaining
        r5 r6 sum
      have continued := reader_divisor_continue program r0 r2 r3 sourceRemaining
        (rotationPair (sourcePrevious + 1) (program + 1)).1
      rw [rightZero] at tested
      have pairSum := rotationPair_sum (sourcePrevious + 1) (by omega) (program + 1)
      exact tested.trans <| continued.trans <|
        inductionHypothesis _ _ (by omega)
  | skip rightPositive suffix inductionHypothesis =>
      rename_i sourcePrevious sourceRemaining sourceCode sourceCarry
      have tested := reader_test_candidate program sourcePrevious r0 r2 r3
        (sourceRemaining + 1)
        r5 r6 sum
      obtain ⟨right, rightEq⟩ :=
        Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt rightPositive)
      have skipped := reader_nondivisor_skip program r0 r2 r3 sourceRemaining
        (rotationPair (sourcePrevious + 1) (program + 1)).1 right
      rw [rightEq] at tested
      have pairSum := rotationPair_sum (sourcePrevious + 1) (by omega) (program + 1)
      have prefixRun := tested.trans (by simpa using skipped)
      exact prefixRun.trans <| inductionHypothesis _ _ (by omega)

/-- A reader certificate whose final left component is an instruction code
feeds directly into the already verified decoder and simulation block. -/
theorem reader_plan_decode_and_execute
    {program previous remaining carry : Nat}
    (instruction : KorecR2.Instruction)
    (plan : ReaderPlan program previous remaining instruction.code carry)
    (registerZero registerTwo r5 r6 : Nat) (sum : r5 + r6 = previous) :
    Reaches KorecU20.step
      (configuration 1 registerZero program registerTwo 0 remaining r5 r6 0)
      (decodedResult program carry registerZero registerTwo instruction) := by
  exact (reader_plan_correct plan registerZero registerTwo 0 r5 r6 sum).trans
    (decode_and_execute program carry registerZero registerTwo instruction)

end Mortality.SourceMachine.KorecU20Interpreter
