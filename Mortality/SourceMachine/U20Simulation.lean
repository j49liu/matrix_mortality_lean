import Mortality.SourceMachine.RegisterEncoding

/-!
# Semantic simulation of Korec U20 by Ivanov U2

This file combines the certified table intervals, generic Minsky-block
semantics, and exponential register arithmetic.  Its principal one-step
theorem covers every occupied U20 instruction address and both branches of
every conditional decrement.
-/

namespace Mortality.SourceMachine.U20Compilation

open Mortality.SourceMachine
open Mortality.SourceMachine.KorecU20

def encodedConfiguration
    (configuration : KorecU20.Configuration) : SourceMachine.Configuration :=
  blockConfiguration (compiledState configuration.state)
    (encodeRegisters configuration.registers) 0

theorem decrementBlock_failure_of_coprime
    {start prime positiveTarget zeroTarget value : Nat}
    (primeLarge : 1 < prime)
    (coprime : Nat.Coprime prime value)
    (realizes : RealizesBlock start
      (decrementBlock start prime positiveTarget zeroTarget)) :
    Reaches u2Step
      (blockConfiguration start value 0)
      (blockConfiguration zeroTarget value 0) := by
  have remainderPositive : 0 < value % prime :=
    mod_positive_of_coprime primeLarge coprime
  have remainderBound : value % prime < prime :=
    Nat.mod_lt _ (by omega)
  have run := decrementBlock_failure (by omega) remainderPositive
    remainderBound realizes (quotient := value / prime)
    (remainder := value % prime)
  simpa [Nat.mod_add_div] using run

/-- Every successful step from an occupied U20 address is simulated by a
nonempty finite U2 run between the corresponding macro configurations. -/
theorem u20Step_compiles_of_state_mem
    {before after : KorecU20.Configuration}
    (stateMem : before.state ∈ KorecU20.states)
    (stepEq : KorecU20.step before = some after) :
    Reaches u2Step (encodedConfiguration before) (encodedConfiguration after) := by
  rcases before with ⟨state, registers⟩
  simp [KorecU20.states] at stateMem
  rcases stateMem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl
  · by_cases zero : registers 1 = 0
    · simp [KorecU20.step, KorecU20.instruction, zero] at stepEq
      subst after
      have coprime := coprime_eleven_encode_of_r1_zero registers zero
      simpa [encodedConfiguration, compiledState] using
        decrementBlock_failure_of_coprime (by decide) coprime realizes_q1
    · simp [KorecU20.step, KorecU20.instruction, zero] at stepEq
      subst after
      have run := decrementBlock_success (by decide) realizes_q1
        (quotient := encodeRegisters
          (registers.update 1 (registers 1 - 1)))
      simpa [encodedConfiguration, compiledState,
        encode_update_r1_decrement registers zero] using run
  · simp [KorecU20.step, KorecU20.instruction] at stepEq
    subst after
    simpa [encodedConfiguration, compiledState,
      encode_update_r7_increment] using
      incrementBlock_correct (by decide) realizes_q3
        (input := encodeRegisters registers)
  · by_cases zero : registers 5 = 0
    · simp [KorecU20.step, KorecU20.instruction, zero] at stepEq
      subst after
      have coprime := coprime_two_encode_of_r5_zero registers zero
      simpa [encodedConfiguration, compiledState] using
        decrementBlock_failure_of_coprime (by decide) coprime realizes_q4
    · simp [KorecU20.step, KorecU20.instruction, zero] at stepEq
      subst after
      have run := decrementBlock_success (by decide) realizes_q4
        (quotient := encodeRegisters
          (registers.update 5 (registers 5 - 1)))
      simpa [encodedConfiguration, compiledState,
        encode_update_r5_decrement registers zero] using run
  · simp [KorecU20.step, KorecU20.instruction] at stepEq
    subst after
    simpa [encodedConfiguration, compiledState,
      encode_update_r6_increment] using
      incrementBlock_correct (by decide) realizes_q6
        (input := encodeRegisters registers)
  · by_cases zero : registers 6 = 0
    · simp [KorecU20.step, KorecU20.instruction, zero] at stepEq
      subst after
      have coprime := coprime_three_encode_of_r6_zero registers zero
      simpa [encodedConfiguration, compiledState] using
        decrementBlock_failure_of_coprime (by decide) coprime realizes_q7
    · simp [KorecU20.step, KorecU20.instruction, zero] at stepEq
      subst after
      have run := decrementBlock_success (by decide) realizes_q7
        (quotient := encodeRegisters
          (registers.update 6 (registers 6 - 1)))
      simpa [encodedConfiguration, compiledState,
        encode_update_r6_decrement registers zero] using run
  · simp [KorecU20.step, KorecU20.instruction] at stepEq
    subst after
    simpa [encodedConfiguration, compiledState,
      encode_update_r5_increment] using
      incrementBlock_correct (by decide) realizes_q9
        (input := encodeRegisters registers)
  · by_cases zero : registers 7 = 0
    · simp [KorecU20.step, KorecU20.instruction, zero] at stepEq
      subst after
      have coprime := coprime_seventeen_encode_of_r7_zero registers zero
      simpa [encodedConfiguration, compiledState] using
        decrementBlock_failure_of_coprime (by decide) coprime realizes_q10
    · simp [KorecU20.step, KorecU20.instruction, zero] at stepEq
      subst after
      have run := decrementBlock_success (by decide) realizes_q10
        (quotient := encodeRegisters
          (registers.update 7 (registers 7 - 1)))
      simpa [encodedConfiguration, compiledState,
        encode_update_r7_decrement registers zero] using run
  · simp [KorecU20.step, KorecU20.instruction] at stepEq
    subst after
    simpa [encodedConfiguration, compiledState,
      encode_update_r1_increment] using
      incrementBlock_correct (by decide) realizes_q12
        (input := encodeRegisters registers)
  · by_cases zero : registers 6 = 0
    · simp [KorecU20.step, KorecU20.instruction, zero] at stepEq
      subst after
      have coprime := coprime_three_encode_of_r6_zero registers zero
      simpa [encodedConfiguration, compiledState] using
        decrementBlock_failure_of_coprime (by decide) coprime realizes_q13
    · simp [KorecU20.step, KorecU20.instruction, zero] at stepEq
      subst after
      have run := decrementBlock_success (by decide) realizes_q13
        (quotient := encodeRegisters
          (registers.update 6 (registers 6 - 1)))
      simpa [encodedConfiguration, compiledState,
        encode_update_r6_decrement registers zero] using run
  · simp [KorecU20.step, KorecU20.instruction] at stepEq
    subst after
    simpa [encodedConfiguration, compiledState,
      encode_update_r6_increment] using
      incrementBlock_correct (by decide) realizes_q15
        (input := encodeRegisters registers)
  · by_cases zero : registers 4 = 0
    · simp [KorecU20.step, KorecU20.instruction, zero] at stepEq
      subst after
      have coprime := coprime_five_encode_of_r4_zero registers zero
      simpa [encodedConfiguration, compiledState] using
        decrementBlock_failure_of_coprime (by decide) coprime realizes_q14
    · simp [KorecU20.step, KorecU20.instruction, zero] at stepEq
      subst after
      have run := decrementBlock_success (by decide) realizes_q14
        (quotient := encodeRegisters
          (registers.update 4 (registers 4 - 1)))
      simpa [encodedConfiguration, compiledState,
        encode_update_r4_decrement registers zero] using run
  · by_cases zero : registers 5 = 0
    · simp [KorecU20.step, KorecU20.instruction, zero] at stepEq
      subst after
      have coprime := coprime_two_encode_of_r5_zero registers zero
      simpa [encodedConfiguration, compiledState] using
        decrementBlock_failure_of_coprime (by decide) coprime realizes_q16
    · simp [KorecU20.step, KorecU20.instruction, zero] at stepEq
      subst after
      have run := decrementBlock_success (by decide) realizes_q16
        (quotient := encodeRegisters
          (registers.update 5 (registers 5 - 1)))
      simpa [encodedConfiguration, compiledState,
        encode_update_r5_decrement registers zero] using run
  · by_cases zero : registers 5 = 0
    · simp [KorecU20.step, KorecU20.instruction, zero] at stepEq
      subst after
      have coprime := coprime_two_encode_of_r5_zero registers zero
      simpa [encodedConfiguration, compiledState] using
        decrementBlock_failure_of_coprime (by decide) coprime realizes_q18
    · simp [KorecU20.step, KorecU20.instruction, zero] at stepEq
      subst after
      have run := decrementBlock_success (by decide) realizes_q18
        (quotient := encodeRegisters
          (registers.update 5 (registers 5 - 1)))
      simpa [encodedConfiguration, compiledState,
        encode_update_r5_decrement registers zero] using run
  · by_cases zero : registers 5 = 0
    · simp [KorecU20.step, KorecU20.instruction, zero] at stepEq
      subst after
      have coprime := coprime_two_encode_of_r5_zero registers zero
      simpa [encodedConfiguration, compiledState] using
        decrementBlock_failure_of_coprime (by decide) coprime realizes_q20
    · simp [KorecU20.step, KorecU20.instruction, zero] at stepEq
      subst after
      have run := decrementBlock_success (by decide) realizes_q20
        (quotient := encodeRegisters
          (registers.update 5 (registers 5 - 1)))
      simpa [encodedConfiguration, compiledState,
        encode_update_r5_decrement registers zero] using run
  · simp [KorecU20.step, KorecU20.instruction] at stepEq
    subst after
    simpa [encodedConfiguration, compiledState,
      encode_update_r4_increment] using
      incrementBlock_correct (by decide) realizes_q22
        (input := encodeRegisters registers)
  · by_cases zero : registers 0 = 0
    · simp [KorecU20.step, KorecU20.instruction, zero] at stepEq
      subst after
      have coprime := coprime_seven_encode_of_r0_zero registers zero
      simpa [encodedConfiguration, compiledState] using
        decrementBlock_failure_of_coprime (by decide) coprime realizes_q23
    · simp [KorecU20.step, KorecU20.instruction, zero] at stepEq
      subst after
      have run := decrementBlock_success (by decide) realizes_q23
        (quotient := encodeRegisters
          (registers.update 0 (registers 0 - 1)))
      simpa [encodedConfiguration, compiledState,
        encode_update_r0_decrement registers zero] using run
  · by_cases zero : registers 2 = 0
    · simp [KorecU20.step, KorecU20.instruction, zero] at stepEq
      subst after
      have coprime := coprime_thirteen_encode_of_r2_zero registers zero
      simpa [encodedConfiguration, compiledState] using
        decrementBlock_failure_of_coprime (by decide) coprime realizes_q27
    · simp [KorecU20.step, KorecU20.instruction, zero] at stepEq
      subst after
      have run := decrementBlock_success (by decide) realizes_q27
        (quotient := encodeRegisters
          (registers.update 2 (registers 2 - 1)))
      simpa [encodedConfiguration, compiledState,
        encode_update_r2_decrement registers zero] using run
  · simp [KorecU20.step, KorecU20.instruction] at stepEq
    subst after
    simpa [encodedConfiguration, compiledState,
      encode_update_r0_increment] using
      incrementBlock_correct (by decide) realizes_q30
        (input := encodeRegisters registers)
  · simp [KorecU20.step, KorecU20.instruction] at stepEq
    subst after
    simpa [encodedConfiguration, compiledState,
      encode_update_r2_increment] using
      incrementBlock_correct (by decide) realizes_q31
        (input := encodeRegisters registers)
  · by_cases zero : registers 4 = 0
    · simp [KorecU20.step, KorecU20.instruction, zero] at stepEq
      subst after
      have coprime := coprime_five_encode_of_r4_zero registers zero
      simpa [encodedConfiguration, compiledState] using
        decrementBlock_failure_of_coprime (by decide) coprime realizes_q32
    · simp [KorecU20.step, KorecU20.instruction, zero] at stepEq
      subst after
      have run := decrementBlock_success (by decide) realizes_q32
        (quotient := encodeRegisters
          (registers.update 4 (registers 4 - 1)))
      simpa [encodedConfiguration, compiledState,
        encode_update_r4_decrement registers zero] using run

/-- A successful U20 step from an occupied address lands either at another
occupied address or at Stop. -/
theorem u20Step_target_valid
    {before after : KorecU20.Configuration}
    (stateMem : before.state ∈ KorecU20.states)
    (stepEq : KorecU20.step before = some after) :
    after.state = 0 ∨ after.state ∈ KorecU20.states := by
  rcases before with ⟨state, registers⟩
  simp [KorecU20.states] at stateMem
  rcases stateMem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl <;>
    simp [KorecU20.step, KorecU20.instruction] at stepEq <;>
    (try split at stepEq) <;> (try simp at stepEq) <;> subst after <;>
    simp [KorecU20.states]

/-- Compile a whole U20 run whose initial state is an occupied address.  The
validity component is carried simultaneously so that every later macro step
may use the concrete twenty-case theorem. -/
theorem u20Run_compiles_and_valid
    {start finish : KorecU20.Configuration}
    (run : Reaches KorecU20.step start finish)
    (initialMem : start.state ∈ KorecU20.states) :
    Reaches u2Step (encodedConfiguration start) (encodedConfiguration finish) ∧
      (finish.state = 0 ∨ finish.state ∈ KorecU20.states) := by
  induction run with
  | refl => exact ⟨.refl _, Or.inr initialMem⟩
  | @tail middle finish prefixRun stepEq inductionHypothesis =>
      rcases inductionHypothesis with ⟨compiledPrefix, middleValid⟩
      rcases middleValid with middleHalt | middleMem
      · have impossible : KorecU20.step middle = none := by
          rcases middle with ⟨state, registers⟩
          simp at middleHalt
          subst state
          rfl
        rw [impossible] at stepEq
        contradiction
      · exact
          ⟨compiledPrefix.trans
              (u20Step_compiles_of_state_mem middleMem stepEq),
            u20Step_target_valid middleMem stepEq⟩

theorem u20Run_compiles
    {start finish : KorecU20.Configuration}
    (run : Reaches KorecU20.step start finish)
    (initialMem : start.state ∈ KorecU20.states) :
    Reaches u2Step (encodedConfiguration start) (encodedConfiguration finish) :=
  (u20Run_compiles_and_valid run initialMem).1

/-- The forward half of the Korec--Ivanov halting bridge, for an arbitrary
initial vector of the eight simulated registers. -/
theorem u20HaltsFrom_implies_u2Halts (initialRegisters : KorecU20.Registers) :
    KorecU20.HaltsFrom initialRegisters →
      U2Halts (encodeRegisters initialRegisters) := by
  rintro ⟨registers, sourceRun⟩
  have compiled := u20Run_compiles sourceRun (by simp [KorecU20.states])
  refine ⟨encodeRegisters registers, 0, ?_⟩
  simpa [encodedConfiguration, KorecU20.HaltsFrom,
    KorecU20.haltConfiguration, SourceMachine.initialConfiguration,
    SourceMachine.haltConfiguration, compiledState,
    U20Compilation.blockConfiguration] using compiled

theorem u20Halts_implies_u2Halts (input : Nat) :
    KorecU20.Halts input → U2Halts (13 ^ input) := by
  simpa [KorecU20.Halts, encodeRegisters_initial] using
    u20HaltsFrom_implies_u2Halts (KorecU20.initialRegisters input)

/-- Exact iteration count for a deterministic partial step function.  The
successor case appends one step, matching the `Reaches.tail` constructor. -/
def iterate {α : Type} (step : α → Option α) : Nat → α → Option α
  | 0, start => some start
  | fuel + 1, start => (iterate step fuel start).bind step

theorem iterate_add {α : Type} (step : α → Option α)
    (first second : Nat) (start : α) :
    iterate step (first + second) start =
      (iterate step first start).bind (iterate step second) := by
  induction second with
  | zero => simp [iterate]
  | succ second inductionHypothesis =>
      rw [Nat.add_succ, iterate, inductionHypothesis]
      cases iterate step first start <;> rfl

theorem reaches_iff_exists_iterate {α : Type} {step : α → Option α}
    {start finish : α} :
    Reaches step start finish ↔
      ∃ fuel, iterate step fuel start = some finish := by
  constructor
  · intro run
    induction run with
    | refl => exact ⟨0, rfl⟩
    | tail prefixRun stepEq inductionHypothesis =>
        rcases inductionHypothesis with ⟨fuel, execution⟩
        refine ⟨fuel + 1, ?_⟩
        simp [iterate, execution, stepEq]
  · rintro ⟨fuel, execution⟩
    induction fuel generalizing finish with
    | zero =>
        simp [iterate] at execution
        subst finish
        exact .refl _
    | succ fuel inductionHypothesis =>
        simp only [iterate] at execution
        cases prefixEq : iterate step fuel start with
        | none => simp [prefixEq] at execution
        | some middle =>
            have prefixRun := inductionHypothesis prefixEq
            have finalStep : step middle = some finish := by
              simpa [prefixEq] using execution
            exact .tail prefixRun finalStep

theorem iterate_halt_none {α : Type} {step : α → Option α}
    {halt : α} {fuel : Nat} (haltEq : step halt = none) (positive : 0 < fuel) :
    iterate step fuel halt = none := by
  induction fuel with
  | zero => omega
  | succ fuel inductionHypothesis =>
      by_cases fuelZero : fuel = 0
      · subst fuel
        simp [iterate, haltEq]
      · rw [iterate, inductionHypothesis (Nat.pos_of_ne_zero fuelZero)]
        rfl

theorem successful_iterations_before_halt
    {α : Type} {step : α → Option α} {start halt finish : α}
    {haltFuel finishFuel : Nat}
    (haltEq : step halt = none)
    (reachesHalt : iterate step haltFuel start = some halt)
    (reachesFinish : iterate step finishFuel start = some finish) :
    finishFuel ≤ haltFuel := by
  apply Nat.le_of_not_lt
  intro greater
  let extra := finishFuel - haltFuel - 1
  have finishFuelEq : finishFuel = haltFuel + (extra + 1) := by
    dsimp [extra]
    omega
  rw [finishFuelEq, iterate_add, reachesHalt] at reachesFinish
  have noneAfter := iterate_halt_none haltEq (fuel := extra + 1) (by omega)
  simp [noneAfter] at reachesFinish

theorem strip_iteration_prefix
    {α : Type} {step : α → Option α} {start middle finish : α}
    {whole prefixLength : Nat}
    (prefixBound : prefixLength ≤ whole)
    (wholeEq : iterate step whole start = some finish)
    (prefixEq : iterate step prefixLength start = some middle) :
    iterate step (whole - prefixLength) middle = some finish := by
  have decomposition : whole = prefixLength + (whole - prefixLength) := by omega
  rw [decomposition, iterate_add, prefixEq] at wholeEq
  simpa using wholeEq

theorem u20Step_exists_of_state_mem (configuration : KorecU20.Configuration)
    (stateMem : configuration.state ∈ KorecU20.states) :
    ∃ next, KorecU20.step configuration = some next := by
  rcases configuration with ⟨state, registers⟩
  simp [KorecU20.states] at stateMem
  rcases stateMem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl <;>
    simp [KorecU20.step, KorecU20.instruction] <;>
    split <;> simp

/-- Every source instruction changes the compiled macro address.  Hence the
finite U2 run simulating it has strictly positive length. -/
theorem compiledState_changes_on_step
    {before after : KorecU20.Configuration}
    (stateMem : before.state ∈ KorecU20.states)
    (stepEq : KorecU20.step before = some after) :
    compiledState before.state ≠ compiledState after.state := by
  rcases before with ⟨state, registers⟩
  simp [KorecU20.states] at stateMem
  rcases stateMem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl <;>
    simp [KorecU20.step, KorecU20.instruction] at stepEq <;>
    (try split at stepEq) <;> (try simp at stepEq) <;> subst after <;>
    simp [compiledState]

theorem encodedConfiguration_ne_of_step
    {before after : KorecU20.Configuration}
    (stateMem : before.state ∈ KorecU20.states)
    (stepEq : KorecU20.step before = some after) :
    encodedConfiguration before ≠ encodedConfiguration after := by
  intro equal
  have stateEqual := congrArg SourceMachine.Configuration.state equal
  exact compiledState_changes_on_step stateMem stepEq <| by
    simpa [encodedConfiguration, blockConfiguration] using stateEqual

/-- Reflection for a finite U2 execution from any valid encoded macro
configuration to the unique U2 halt address. -/
theorem u2Halt_iteration_implies_u20_halt
    (fuel : Nat) (source : KorecU20.Configuration)
    (sourceValid : source.state = 0 ∨ source.state ∈ KorecU20.states)
    (counterZero counterOne : Nat)
    (execution : iterate u2Step fuel (encodedConfiguration source) =
      some (SourceMachine.haltConfiguration counterZero counterOne)) :
    ∃ registers,
      Reaches KorecU20.step source (KorecU20.haltConfiguration registers) := by
  induction fuel using Nat.strongRecOn generalizing source with
  | ind fuel inductionHypothesis =>
      rcases sourceValid with sourceHalt | sourceMem
      · rcases source with ⟨state, registers⟩
        simp at sourceHalt
        subst state
        exact ⟨registers, .refl _⟩
      · obtain ⟨next, sourceStep⟩ :=
          u20Step_exists_of_state_mem source sourceMem
        have compiledRun := u20Step_compiles_of_state_mem sourceMem sourceStep
        obtain ⟨blockFuel, blockExecution⟩ :=
          reaches_iff_exists_iterate.mp compiledRun
        have blockPositive : 0 < blockFuel := by
          apply Nat.pos_of_ne_zero
          intro blockZero
          subst blockFuel
          simp [iterate] at blockExecution
          exact encodedConfiguration_ne_of_step sourceMem sourceStep
            blockExecution
        have u2HaltStep :
            u2Step (SourceMachine.haltConfiguration counterZero counterOne) = none := by
          rfl
        have blockBound : blockFuel ≤ fuel :=
          successful_iterations_before_halt u2HaltStep execution blockExecution
        have suffixExecution :
            iterate u2Step (fuel - blockFuel) (encodedConfiguration next) =
              some (SourceMachine.haltConfiguration counterZero counterOne) :=
          strip_iteration_prefix blockBound execution blockExecution
        have suffixSmaller : fuel - blockFuel < fuel := by omega
        have nextValid := u20Step_target_valid sourceMem sourceStep
        obtain ⟨registers, suffixRun⟩ :=
          inductionHypothesis (fuel - blockFuel) suffixSmaller next nextValid
            suffixExecution
        exact ⟨registers, (Reaches.single sourceStep).trans suffixRun⟩

/-- Exact semantic equivalence between Korec's U20 and Ivanov's U2 for an
arbitrary initial vector of the eight simulated registers. -/
theorem u2Halts_encodeRegisters_iff_u20HaltsFrom
    (initialRegisters : KorecU20.Registers) :
    U2Halts (encodeRegisters initialRegisters) ↔
      KorecU20.HaltsFrom initialRegisters := by
  constructor
  · rintro ⟨counterZero, counterOne, run⟩
    obtain ⟨fuel, execution⟩ := reaches_iff_exists_iterate.mp run
    have initialEq :
        encodedConfiguration
            ({ state := 1, registers := initialRegisters } :
              KorecU20.Configuration) =
          SourceMachine.initialConfiguration
            (encodeRegisters initialRegisters) := by
      simp [encodedConfiguration, SourceMachine.initialConfiguration,
        blockConfiguration, compiledState]
    rw [← initialEq] at execution
    exact u2Halt_iteration_implies_u20_halt fuel
      ({ state := 1, registers := initialRegisters } : KorecU20.Configuration)
      (Or.inr (by simp [KorecU20.states]))
      counterZero counterOne execution
  · exact u20HaltsFrom_implies_u2Halts initialRegisters

theorem u2Halts_iff_u20Halts (input : Nat) :
    U2Halts (13 ^ input) ↔ KorecU20.Halts input := by
  simpa [KorecU20.Halts, encodeRegisters_initial] using
    u2Halts_encodeRegisters_iff_u20HaltsFrom
      (KorecU20.initialRegisters input)

/-- The specialization matching Korec's two-input universality convention. -/
theorem u2Halts_iff_u20HaltsTwo (programInput dataInput : Nat) :
    U2Halts (11 ^ programInput * 13 ^ dataInput) ↔
      KorecU20.HaltsTwo programInput dataInput := by
  simpa [KorecU20.HaltsTwo, encodeRegisters_initialTwo] using
    u2Halts_encodeRegisters_iff_u20HaltsFrom
      (KorecU20.initialRegistersTwo programInput dataInput)

end Mortality.SourceMachine.U20Compilation
