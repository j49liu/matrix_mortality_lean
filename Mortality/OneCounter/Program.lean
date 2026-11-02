import Std

/-!
# One-counter programs

This file formalizes the abstract instruction set in Table 3.1 of the
paper.  Programs are finite lists of labelled edges and their step
relation is nondeterministic.  The generic path-reversal theorem is
stated for relations, so it does not assume that a reversed instruction
is itself a function.
-/

namespace Mortality.OneCounter

/-- The six instruction forms used by the fixed one-counter program. -/
inductive Instruction where
  | increment
  | congruenceTest (modulus : Nat) (allowed : List Nat)
  | divideTwoOdd
  | divideThreeTwo
  | contractTwo
  | contractThree
  deriving DecidableEq, Repr

namespace Instruction

/-- Execute an abstract instruction when its domain condition holds. -/
def evaluate : Instruction → Nat → Option Nat
  | .increment, n => some (n + 1)
  | .congruenceTest modulus allowed, n =>
      if modulus = 0 then none
      else if allowed.contains (n % modulus) then some n else none
  | .divideTwoOdd, n =>
      if n % 2 = 1 then some (n / 2) else none
  | .divideThreeTwo, n =>
      if n % 3 = 2 then some (n / 3) else none
  | .contractTwo, n =>
      if n % 5 = 4 then some (2 * (n / 5) + 1) else none
  | .contractThree, n =>
      if n % 5 = 4 then some (3 * (n / 5) + 2) else none

/-- The relational semantics induced by `evaluate`. -/
def Relates (instruction : Instruction) (input output : Nat) : Prop :=
  instruction.evaluate input = some output

@[simp] theorem evaluate_increment (n : Nat) :
    evaluate .increment n = some (n + 1) := rfl

@[simp] theorem evaluate_divideTwoOdd (a : Nat) :
    evaluate .divideTwoOdd (2 * a + 1) = some a := by
  simp [evaluate]
  rw [Nat.mul_add_div Nat.two_pos]
  rfl

@[simp] theorem evaluate_divideThreeTwo (a : Nat) :
    evaluate .divideThreeTwo (3 * a + 2) = some a := by
  simp [evaluate]
  rw [Nat.mul_add_div (by decide : 0 < 3)]
  rfl

@[simp] theorem evaluate_contractTwo (a : Nat) :
    evaluate .contractTwo (5 * a + 4) = some (2 * a + 1) := by
  simp [evaluate]
  rw [Nat.mul_add_div (by decide : 0 < 5)]
  rfl

@[simp] theorem evaluate_contractThree (a : Nat) :
    evaluate .contractThree (5 * a + 4) = some (3 * a + 2) := by
  simp [evaluate]
  rw [Nat.mul_add_div (by decide : 0 < 5)]
  rfl

/-- Exact converse for binary division. -/
theorem evaluate_divideTwoOdd_iff {input output : Nat} :
    evaluate .divideTwoOdd input = some output ↔
      input = 2 * output + 1 := by
  constructor
  · intro evaluation
    change (if input % 2 = 1 then some (input / 2) else none) =
      some output at evaluation
    split at evaluation
    · rename_i residue
      simp only [Option.some.injEq] at evaluation
      subst output
      have reconstruction := Nat.mod_add_div input 2
      omega
    · contradiction
  · intro inputEq
    subst input
    exact evaluate_divideTwoOdd output

/-- Exact converse for ternary division. -/
theorem evaluate_divideThreeTwo_iff {input output : Nat} :
    evaluate .divideThreeTwo input = some output ↔
      input = 3 * output + 2 := by
  constructor
  · intro evaluation
    change (if input % 3 = 2 then some (input / 3) else none) =
      some output at evaluation
    split at evaluation
    · rename_i residue
      simp only [Option.some.injEq] at evaluation
      subst output
      have reconstruction := Nat.mod_add_div input 3
      omega
    · contradiction
  · intro inputEq
    subst input
    exact evaluate_divideThreeTwo output

/-- Exact converse for the twofold contraction. -/
theorem evaluate_contractTwo_iff {input output : Nat} :
    evaluate .contractTwo input = some output ↔
      ∃ a, input = 5 * a + 4 ∧ output = 2 * a + 1 := by
  constructor
  · intro evaluation
    change (if input % 5 = 4 then some (2 * (input / 5) + 1) else none) =
      some output at evaluation
    split at evaluation
    · rename_i residue
      simp only [Option.some.injEq] at evaluation
      refine ⟨input / 5, ?_, evaluation.symm⟩
      have reconstruction := Nat.mod_add_div input 5
      omega
    · contradiction
  · rintro ⟨a, rfl, rfl⟩
    exact evaluate_contractTwo a

/-- Exact converse for the threefold contraction. -/
theorem evaluate_contractThree_iff {input output : Nat} :
    evaluate .contractThree input = some output ↔
      ∃ a, input = 5 * a + 4 ∧ output = 3 * a + 2 := by
  constructor
  · intro evaluation
    change (if input % 5 = 4 then some (3 * (input / 5) + 2) else none) =
      some output at evaluation
    split at evaluation
    · rename_i residue
      simp only [Option.some.injEq] at evaluation
      refine ⟨input / 5, ?_, evaluation.symm⟩
      have reconstruction := Nat.mod_add_div input 5
      omega
    · contradiction
  · rintro ⟨a, rfl, rfl⟩
    exact evaluate_contractThree a

/-- A successful congruence test leaves its input unchanged. -/
theorem evaluate_congruenceTest_eq {modulus : Nat} {allowed : List Nat}
    {input output : Nat}
    (evaluation : evaluate (.congruenceTest modulus allowed) input = some output) :
    output = input := by
  change (if modulus = 0 then none
    else if allowed.contains (input % modulus) then some input else none) =
      some output at evaluation
  split at evaluation
  · contradiction
  · split at evaluation
    · simpa using evaluation.symm
    · contradiction

end Instruction

/-- One labelled edge of a finite-control one-counter program. -/
structure Edge (State : Type) where
  source : State
  target : State
  instruction : Instruction
  deriving Repr

/-- A finite-control one-counter program. -/
structure Program (State : Type) where
  edges : List (Edge State)

/-- A control state paired with its natural counter value. -/
structure Configuration (State : Type) where
  state : State
  counter : Nat
  deriving DecidableEq, Repr

/-- One program step along any matching enabled edge. -/
def Step {State : Type} (program : Program State) :
    Configuration State → Configuration State → Prop :=
  fun before after =>
    ∃ edge ∈ program.edges,
      edge.source = before.state ∧
      edge.target = after.state ∧
      edge.instruction.evaluate before.counter = some after.counter

/-- Reflexive transitive closure, with the last step exposed. -/
inductive Reaches {α : Type} (step : α → α → Prop) : α → α → Prop
  | refl (start : α) : Reaches step start start
  | tail {start middle finish : α} :
      Reaches step start middle →
      step middle finish →
      Reaches step start finish

namespace Reaches

/-- A single edge is a finite path. -/
theorem single {α : Type} {step : α → α → Prop} {start finish : α}
    (h : step start finish) : Reaches step start finish :=
  .tail (.refl start) h

/-- Concatenate two finite paths. -/
theorem trans {α : Type} {step : α → α → Prop} {start middle finish : α}
    (first : Reaches step start middle) (second : Reaches step middle finish) :
    Reaches step start finish := by
  induction second with
  | refl => exact first
  | tail hRun hStep inductionHypothesis =>
      exact .tail inductionHypothesis hStep

/-- Enlarge the step relation of a finite path. -/
theorem mono {α : Type} {step larger : α → α → Prop}
    (includes : ∀ {before after}, step before after → larger before after)
    {start finish : α} (run : Reaches step start finish) :
    Reaches larger start finish := by
  induction run with
  | refl => exact .refl _
  | tail hRun hStep inductionHypothesis =>
      exact .tail inductionHypothesis (includes hStep)

/-- A relation with every edge reversed. -/
def converse {α : Type} (step : α → α → Prop) : α → α → Prop :=
  fun after before => step before after

/-- Reverse a finite path, including the empty path. -/
theorem reverse {α : Type} {step : α → α → Prop} {start finish : α}
    (run : Reaches step start finish) :
    Reaches (converse step) finish start := by
  induction run with
  | refl => exact .refl _
  | tail hRun hStep inductionHypothesis =>
      have reversedLast : Reaches (converse step) _ _ :=
        single (show converse step _ _ from hStep)
      exact reversedLast.trans inductionHypothesis

/-- Reversing twice restores the original step relation. -/
theorem reverse_iff {α : Type} {step : α → α → Prop} {start finish : α} :
    Reaches (converse step) finish start ↔ Reaches step start finish := by
  constructor
  · intro run
    have reversed := reverse run
    change Reaches (fun before after => step before after) start finish at reversed
    exact reversed
  · exact reverse

end Reaches

end Mortality.OneCounter
