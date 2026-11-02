import LeanWang.Kari.Hooper.GlobalSourceLiveness
import LeanWang.Kari.Hooper.GlobalSourceSemantics
import Mortality.SourceMachine.FourCounterSemantics

namespace Mortality.SourceMachine.LeanWangBridge

open LeanWang.Kari.Hooper

noncomputable section


def encodeRegister : CounterMachine.Register → FourCounter.Register
  | .left => .left
  | .right => .right
  | .temp => .temp
  | .clock => .clock

def decodeRegister : FourCounter.Register → CounterMachine.Register
  | .left => .left
  | .right => .right
  | .temp => .temp
  | .clock => .clock

def encodeRegisters (registers : CounterMachine.Registers) : FourCounter.Registers :=
  ⟨registers.left, registers.right, registers.temp, registers.clock⟩

def decodeRegisters (registers : FourCounter.Registers) : CounterMachine.Registers :=
  ⟨registers.left, registers.right, registers.temp, registers.clock⟩

def encodeInstruction : CounterMachine.Instruction → FourCounter.Instruction
  | .increment register target => .increment (encodeRegister register) target
  | .decrement register zeroTarget positiveTarget =>
      .decrement (encodeRegister register) zeroTarget positiveTarget

def encodeConfiguration (configuration : CounterMachine.Cfg) : FourCounter.Configuration :=
  ⟨configuration.state, encodeRegisters configuration.registers⟩

def decodeConfiguration (configuration : FourCounter.Configuration) : CounterMachine.Cfg :=
  ⟨configuration.state, decodeRegisters configuration.registers⟩

@[simp] theorem decodeRegister_encodeRegister (register : CounterMachine.Register) :
    decodeRegister (encodeRegister register) = register := by
  cases register <;> rfl

@[simp] theorem encodeRegister_decodeRegister (register : FourCounter.Register) :
    encodeRegister (decodeRegister register) = register := by
  cases register <;> rfl

@[simp] theorem decodeRegisters_encodeRegisters (registers : CounterMachine.Registers) :
    decodeRegisters (encodeRegisters registers) = registers := by
  cases registers
  rfl

@[simp] theorem encodeRegisters_decodeRegisters (registers : FourCounter.Registers) :
    encodeRegisters (decodeRegisters registers) = registers := by
  cases registers
  rfl

@[simp] theorem decodeConfiguration_encodeConfiguration
    (configuration : CounterMachine.Cfg) :
    decodeConfiguration (encodeConfiguration configuration) = configuration := by
  cases configuration
  simp [encodeConfiguration, decodeConfiguration]

@[simp] theorem encodeConfiguration_decodeConfiguration
    (configuration : FourCounter.Configuration) :
    encodeConfiguration (decodeConfiguration configuration) = configuration := by
  cases configuration
  simp [encodeConfiguration, decodeConfiguration]

@[simp] theorem encodeRegisters_get (registers : CounterMachine.Registers)
    (register : CounterMachine.Register) :
    (encodeRegisters registers).get (encodeRegister register) =
      registers.get register := by
  cases register <;> rfl

@[simp] theorem encodeRegisters_increment (registers : CounterMachine.Registers)
    (register : CounterMachine.Register) :
    encodeRegisters (registers.increment register) =
      (encodeRegisters registers).increment (encodeRegister register) := by
  cases register <;> cases registers <;> rfl

@[simp] theorem encodeRegisters_decrement (registers : CounterMachine.Registers)
    (register : CounterMachine.Register) :
    encodeRegisters (registers.decrement register) =
      (encodeRegisters registers).decrement (encodeRegister register) := by
  cases register <;> cases registers <;> rfl

@[simp] theorem decodeRegisters_get (registers : FourCounter.Registers)
    (register : FourCounter.Register) :
    (decodeRegisters registers).get (decodeRegister register) =
      registers.get register := by
  cases register <;> rfl

@[simp] theorem decodeRegisters_increment (registers : FourCounter.Registers)
    (register : FourCounter.Register) :
    decodeRegisters (registers.increment register) =
      (decodeRegisters registers).increment (decodeRegister register) := by
  cases register <;> cases registers <;> rfl

@[simp] theorem decodeRegisters_decrement (registers : FourCounter.Registers)
    (register : FourCounter.Register) :
    decodeRegisters (registers.decrement register) =
      (decodeRegisters registers).decrement (decodeRegister register) := by
  cases register <;> cases registers <;> rfl

/-- The one fixed external association-list program, viewed through the
project's extensional four-counter interface. -/
def fixedProgram : FourCounter.Program := fun state =>
  (CounterMachine.lookupInstruction GlobalSourceProgram.program state).map
    encodeInstruction

theorem encode_step (configuration : CounterMachine.Cfg) :
    FourCounter.step fixedProgram (encodeConfiguration configuration) =
      (CounterMachine.step GlobalSourceProgram.program configuration).map
        encodeConfiguration := by
  cases configuration with
  | mk state registers =>
      cases hlookup : CounterMachine.lookupInstruction GlobalSourceProgram.program state with
      | none =>
          simp [FourCounter.step, fixedProgram, CounterMachine.step, encodeConfiguration, hlookup]
      | some instruction =>
          cases instruction with
          | increment register target =>
              simp [FourCounter.step, fixedProgram, CounterMachine.step, encodeInstruction,
                encodeConfiguration, hlookup]
          | decrement register zeroTarget positiveTarget =>
              by_cases hzero : registers.get register = 0 <;>
                simp [FourCounter.step, fixedProgram, CounterMachine.step, encodeInstruction,
                  encodeConfiguration, hlookup, hzero]

theorem decode_step (configuration : FourCounter.Configuration) :
    CounterMachine.step GlobalSourceProgram.program (decodeConfiguration configuration) =
      (FourCounter.step fixedProgram configuration).map decodeConfiguration := by
  cases configuration with
  | mk state registers =>
      cases hlookup : CounterMachine.lookupInstruction GlobalSourceProgram.program state with
      | none =>
          simp [FourCounter.step, fixedProgram, CounterMachine.step, decodeConfiguration, hlookup]
      | some instruction =>
          cases instruction with
          | increment register target =>
              cases register <;> cases registers <;>
                simp [FourCounter.step, fixedProgram, CounterMachine.step, encodeInstruction,
                  decodeConfiguration, decodeRegisters,
                  encodeRegister, hlookup, FourCounter.Registers.increment,
                  FourCounter.Registers.set, FourCounter.Registers.get,
                  CounterMachine.Registers.increment,
                  CounterMachine.Registers.set,
                  CounterMachine.Registers.get]
          | decrement register zeroTarget positiveTarget =>
              cases register <;> cases registers <;>
                simp [FourCounter.step, fixedProgram, CounterMachine.step, encodeInstruction,
                  decodeConfiguration, decodeRegisters,
                  encodeRegister, hlookup, FourCounter.Registers.decrement,
                  FourCounter.Registers.set, FourCounter.Registers.get,
                  CounterMachine.Registers.decrement,
                  CounterMachine.Registers.set,
                  CounterMachine.Registers.get] <;>
                split <;> rfl

theorem encode_reaches {start finish : CounterMachine.Cfg}
    (run : StateTransition.Reaches
      (CounterMachine.step GlobalSourceProgram.program) start finish) :
    Mortality.SourceMachine.Reaches (FourCounter.step fixedProgram)
      (encodeConfiguration start) (encodeConfiguration finish) := by
  change Relation.ReflTransGen
    (fun before after => after ∈ CounterMachine.step GlobalSourceProgram.program before)
    start finish at run
  induction run with
  | refl => exact .refl _
  | @tail middle final hreach lastStep ih =>
      refine Mortality.SourceMachine.Reaches.tail ih ?_
      rw [encode_step]
      have stepEq : CounterMachine.step GlobalSourceProgram.program middle =
          some final := by
        simpa using lastStep
      simp [stepEq]

theorem decode_reaches {start finish : FourCounter.Configuration}
    (run : Mortality.SourceMachine.Reaches (FourCounter.step fixedProgram)
      start finish) :
    StateTransition.Reaches (CounterMachine.step GlobalSourceProgram.program)
      (decodeConfiguration start) (decodeConfiguration finish) := by
  change Relation.ReflTransGen
    (fun before after => after ∈ CounterMachine.step GlobalSourceProgram.program before)
    (decodeConfiguration start) (decodeConfiguration finish)
  induction run with
  | refl => exact .refl
  | @tail middle final hreach lastStep ih =>
      refine Relation.ReflTransGen.tail ih ?_
      simp [decode_step, lastStep]

theorem haltsFrom_iff (start : CounterMachine.Cfg) :
    FourCounter.HaltsFrom fixedProgram (encodeConfiguration start) ↔
      CounterLiveness.HaltsFrom GlobalSourceProgram.program start := by
  constructor
  · rintro ⟨finish, run, terminal⟩
    refine ⟨decodeConfiguration finish, ?_, ?_⟩
    · simpa using decode_reaches run
    · rw [decode_step, terminal]
      rfl
  · rintro ⟨finish, run, terminal⟩
    refine ⟨encodeConfiguration finish, encode_reaches run, ?_⟩
    unfold FourCounter.Terminal
    rw [encode_step, terminal]
    rfl

/-- This is the first theorem of `GlobalSourceMortality`, restated without
that file's later geometric import. -/
theorem not_fixedNonhalting_haltsFrom {c : Nat.Partrec.Code}
    (h : ¬ LeanWang.DominoProblem.FixedNonhalting c) :
    CounterLiveness.HaltsFrom GlobalSourceProgram.program
      (GlobalSourceSemantics.canonicalCounterCfg c) := by
  have hmortal : ¬ LeanWang.Kari.Dynamics.ImmortalFrom SourceControl.registerStep
      (SourceRegisterSemantics.canonical c) := by
    intro himmortal
    exact h ((SourceRegisterSemantics.fixedNonhalting_iff_immortalFrom c).2
      himmortal)
  have hdom :
      (StateTransition.eval SourceControl.registerStep
        (SourceRegisterSemantics.canonical c)).Dom := by
    by_contra hnotdom
    exact hmortal
      ((LeanWang.Kari.Dynamics.not_eval_dom_iff_immortalFrom _ _).1 hnotdom)
  rcases Part.dom_iff_mem.mp hdom with ⟨terminal, hterminalMem⟩
  rcases StateTransition.mem_eval.mp hterminalMem with
    ⟨hsourceReach, hterminal⟩
  rcases LeanWang.Kari.Dynamics.exists_iterate_eq_some_of_reaches hsourceReach with
    ⟨steps, hsteps⟩
  let terminalCounter : CounterMachine.Cfg :=
    ⟨SourceProgram.controlCode terminal.state terminal.tape.head,
      SourceProgram.logicalRegisters terminal.tape steps⟩
  refine ⟨terminalCounter, ?_, ?_⟩
  · simpa [terminalCounter, GlobalSourceSemantics.canonicalCounterCfg] using
      (GlobalSourceProgram.iterate_registerStep_reaches steps hsteps 0)
  · simpa [terminalCounter] using
      (GlobalSourceLiveness.step_logical_eq_none_of_registerStep_none
        terminal steps hterminal)

theorem counterHalts_iff_evalDom (c : Nat.Partrec.Code) :
    CounterLiveness.HaltsFrom GlobalSourceProgram.program
        (GlobalSourceSemantics.canonicalCounterCfg c) ↔
      (Nat.Partrec.Code.eval c 0).Dom := by
  constructor
  · intro halts
    by_contra notDom
    have fixedNonhalting : LeanWang.DominoProblem.FixedNonhalting c :=
      notDom
    exact CounterLiveness.not_haltsFrom_of_immortalFrom
      (GlobalSourceSemantics.fixedNonhalting_immortalFrom fixedNonhalting)
      halts
  · intro dom
    apply not_fixedNonhalting_haltsFrom
    simpa [LeanWang.DominoProblem.FixedNonhalting] using dom

theorem fixedProgram_halts_iff_evalDom (c : Nat.Partrec.Code) :
    FourCounter.HaltsFrom fixedProgram
        (encodeConfiguration
          (GlobalSourceSemantics.canonicalCounterCfg c)) ↔
      (Nat.Partrec.Code.eval c 0).Dom :=
  (haltsFrom_iff _).trans (counterHalts_iff_evalDom c)

/-- Halting of one fixed four-counter program from its code-dependent
canonical start is undecidable. -/
theorem fixedProgram_halting_not_computable :
    ¬ ComputablePred fun c : Nat.Partrec.Code =>
      FourCounter.HaltsFrom fixedProgram
        (encodeConfiguration
          (GlobalSourceSemantics.canonicalCounterCfg c)) := by
  intro computableHalting
  exact ComputablePred.halting_problem 0
    (computableHalting.of_eq fixedProgram_halts_iff_evalDom)

end

end Mortality.SourceMachine.LeanWangBridge
