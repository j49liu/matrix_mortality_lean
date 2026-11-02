import Std

/-!
# Ivanov's two-counter machine U2

This file records the complete 278-instruction table on pp. 128--129
of Sergiu Ivanov's thesis, *On the Power and Universality of
Biologically-inspired Models of Computation* (2014).  State numbers are
kept one-based so that they can be compared directly with the source.

`A(c)` is represented by `RawInstruction.inc c`, and `S(c)` by
`RawInstruction.dec c positive zero`.  The bounds and counts below are
checked by kernel evaluation; they are not transcribed as assumptions.
-/

namespace Mortality.SourceMachine

set_option maxRecDepth 100000

/-- The two counters used by the source machine. -/
inductive Counter where
  | zero
  | one
  deriving DecidableEq, Repr

/-- A source instruction before state-bound validation. -/
inductive RawInstruction where
  | inc (counter : Counter) (next : Nat)
  | dec (counter : Counter) (positive zeroDest : Nat)
  | halt
  deriving DecidableEq, Repr

namespace RawInstruction

/-- Every destination appearing in an instruction. -/
def destinations : RawInstruction → List Nat
  | .inc _ next => [next]
  | .dec _ positive zeroDest => [positive, zeroDest]
  | .halt => []

/-- Decide whether all destinations are valid one-based states of size `n`. -/
def destinationsIn (n : Nat) (instruction : RawInstruction) : Bool :=
  instruction.destinations.all fun q => 1 ≤ q && q ≤ n

end RawInstruction

/-- Ivanov's U2 table, in states `q1, ..., q278`. -/
def u2Table : List RawInstruction := [
  .dec .zero 2 25,
  .dec .zero 3 23,
  .dec .zero 4 22,
  .dec .zero 5 21,
  .dec .zero 6 20,
  .dec .zero 7 19,
  .dec .zero 8 18,
  .dec .zero 9 17,
  .dec .zero 10 16,
  .dec .zero 11 15,
  .dec .zero 12 14,
  .inc .one 1,
  .inc .zero 14,
  .inc .zero 15,
  .inc .zero 16,
  .inc .zero 17,
  .inc .zero 18,
  .inc .zero 19,
  .inc .zero 20,
  .inc .zero 21,
  .inc .zero 22,
  .inc .zero 23,
  .inc .zero 24,
  .dec .one 13 55,
  .dec .one 26 27,
  .inc .zero 25,
  .dec .zero 28 45,
  .inc .one 29,
  .inc .one 30,
  .inc .one 31,
  .inc .one 32,
  .inc .one 33,
  .inc .one 34,
  .inc .one 35,
  .inc .one 36,
  .inc .one 37,
  .inc .one 38,
  .inc .one 39,
  .inc .one 40,
  .inc .one 41,
  .inc .one 42,
  .inc .one 43,
  .inc .one 44,
  .inc .one 27,
  .dec .one 46 1,
  .inc .zero 45,
  .dec .zero 48 53,
  .dec .zero 49 51,
  .inc .one 47,
  .inc .zero 51,
  .inc .zero 52,
  .dec .one 50 61,
  .dec .one 54 55,
  .inc .zero 53,
  .dec .zero 56 59,
  .inc .one 57,
  .inc .one 58,
  .inc .one 55,
  .dec .one 60 47,
  .inc .zero 59,
  .dec .zero 62 69,
  .dec .zero 63 67,
  .dec .zero 64 66,
  .inc .one 61,
  .inc .zero 66,
  .inc .zero 67,
  .inc .zero 68,
  .dec .one 65 47,
  .dec .one 70 71,
  .inc .zero 69,
  .dec .zero 72 74,
  .inc .one 73,
  .inc .one 71,
  .dec .one 75 76,
  .inc .zero 74,
  .dec .zero 77 112,
  .dec .zero 78 110,
  .dec .zero 79 109,
  .dec .zero 80 108,
  .dec .zero 81 107,
  .dec .zero 82 106,
  .dec .zero 83 105,
  .dec .zero 84 104,
  .dec .zero 85 103,
  .dec .zero 86 102,
  .dec .zero 87 101,
  .dec .zero 88 100,
  .dec .zero 89 99,
  .dec .zero 90 98,
  .dec .zero 91 97,
  .dec .zero 92 96,
  .dec .zero 93 95,
  .inc .one 76,
  .inc .zero 95,
  .inc .zero 96,
  .inc .zero 97,
  .inc .zero 98,
  .inc .zero 99,
  .inc .zero 100,
  .inc .zero 101,
  .inc .zero 102,
  .inc .zero 103,
  .inc .zero 104,
  .inc .zero 105,
  .inc .zero 106,
  .inc .zero 107,
  .inc .zero 108,
  .inc .zero 109,
  .inc .zero 110,
  .inc .zero 111,
  .dec .one 94 128,
  .dec .one 113 114,
  .inc .zero 112,
  .dec .zero 115 126,
  .inc .one 116,
  .inc .one 117,
  .inc .one 118,
  .inc .one 119,
  .inc .one 120,
  .inc .one 121,
  .inc .one 122,
  .inc .one 123,
  .inc .one 124,
  .inc .one 125,
  .inc .one 114,
  .dec .one 127 61,
  .inc .zero 126,
  .dec .zero 129 136,
  .dec .zero 130 134,
  .dec .zero 131 133,
  .inc .one 128,
  .inc .zero 133,
  .inc .zero 134,
  .inc .zero 135,
  .dec .one 132 1,
  .dec .one 137 272,
  .inc .zero 136,
  .dec .zero 139 150,
  .dec .zero 140 148,
  .dec .zero 141 147,
  .dec .zero 142 146,
  .dec .zero 143 145,
  .inc .one 138,
  .inc .zero 145,
  .inc .zero 146,
  .inc .zero 147,
  .inc .zero 148,
  .inc .zero 149,
  .dec .one 144 152,
  .dec .one 151 1,
  .inc .zero 150,
  .dec .zero 153 158,
  .dec .zero 154 156,
  .inc .one 152,
  .inc .zero 156,
  .inc .zero 157,
  .dec .one 155 184,
  .dec .one 159 160,
  .inc .zero 158,
  .dec .zero 161 166,
  .dec .zero 162 164,
  .inc .one 160,
  .inc .zero 164,
  .inc .zero 165,
  .dec .one 163 202,
  .dec .one 167 168,
  .inc .zero 166,
  .dec .zero 169 174,
  .dec .zero 170 172,
  .inc .one 168,
  .inc .zero 172,
  .inc .zero 173,
  .dec .one 171 232,
  .dec .one 175 176,
  .inc .zero 174,
  .dec .zero 177 182,
  .inc .one 178,
  .inc .one 179,
  .inc .one 180,
  .inc .one 181,
  .inc .one 176,
  .dec .one 183 152,
  .inc .zero 182,
  .dec .zero 185 200,
  .dec .zero 186 198,
  .dec .zero 187 197,
  .dec .zero 188 196,
  .dec .zero 189 195,
  .dec .zero 190 194,
  .dec .zero 191 193,
  .inc .one 184,
  .inc .zero 193,
  .inc .zero 194,
  .inc .zero 195,
  .inc .zero 196,
  .inc .zero 197,
  .inc .zero 198,
  .inc .zero 199,
  .dec .one 192 1,
  .dec .one 201 258,
  .inc .zero 200,
  .dec .zero 203 230,
  .dec .zero 204 228,
  .dec .zero 205 227,
  .dec .zero 206 226,
  .dec .zero 207 225,
  .dec .zero 208 224,
  .dec .zero 209 223,
  .dec .zero 210 222,
  .dec .zero 211 221,
  .dec .zero 212 220,
  .dec .zero 213 219,
  .dec .zero 214 218,
  .dec .zero 215 217,
  .inc .one 202,
  .inc .zero 217,
  .inc .zero 218,
  .inc .zero 219,
  .inc .zero 220,
  .inc .zero 221,
  .inc .zero 222,
  .inc .zero 223,
  .inc .zero 224,
  .inc .zero 225,
  .inc .zero 226,
  .inc .zero 227,
  .inc .zero 228,
  .inc .zero 229,
  .dec .one 216 1,
  .dec .one 231 258,
  .inc .zero 230,
  .dec .zero 233 240,
  .inc .one 234,
  .inc .one 235,
  .inc .one 236,
  .inc .one 237,
  .inc .one 238,
  .inc .one 239,
  .inc .one 232,
  .dec .one 241 242,
  .inc .zero 240,
  .dec .zero 243 256,
  .inc .one 244,
  .inc .one 245,
  .inc .one 246,
  .inc .one 247,
  .inc .one 248,
  .inc .one 249,
  .inc .one 250,
  .inc .one 251,
  .inc .one 252,
  .inc .one 253,
  .inc .one 254,
  .inc .one 255,
  .inc .one 242,
  .dec .one 257 258,
  .inc .zero 256,
  .dec .zero 259 270,
  .dec .zero 260 268,
  .dec .zero 261 267,
  .dec .zero 262 266,
  .dec .zero 263 265,
  .inc .one 258,
  .inc .zero 265,
  .inc .zero 266,
  .inc .zero 267,
  .inc .zero 268,
  .inc .zero 269,
  .dec .one 264 278,
  .dec .one 271 1,
  .inc .zero 270,
  .dec .zero 273 276,
  .inc .one 274,
  .inc .one 275,
  .inc .one 272,
  .dec .one 277 138,
  .inc .zero 276,
  .halt
]

/-- The four instruction counts used in the manuscript. -/
structure InstructionCounts where
  incZero : Nat
  incOne : Nat
  decZero : Nat
  decOne : Nat
  deriving DecidableEq, Repr

namespace InstructionCounts

/-- Add one source instruction to a count. -/
def addInstruction (counts : InstructionCounts) :
    RawInstruction → InstructionCounts
  | .inc .zero _ => { counts with incZero := counts.incZero + 1 }
  | .inc .one _ => { counts with incOne := counts.incOne + 1 }
  | .dec .zero _ _ => { counts with decZero := counts.decZero + 1 }
  | .dec .one _ _ => { counts with decOne := counts.decOne + 1 }
  | .halt => counts

end InstructionCounts

/-- Counts the instructions in a raw source table. -/
def instructionCounts (table : List RawInstruction) : InstructionCounts :=
  table.foldl InstructionCounts.addInstruction
    { incZero := 0, incOne := 0, decZero := 0, decOne := 0 }

/-- U2 has exactly the 278 states listed in Ivanov's appendix. -/
theorem u2Table_length : u2Table.length = 278 := by
  decide

/-- Every destination in the transcribed table is a valid U2 state. -/
theorem u2Table_destinations :
    u2Table.all (RawInstruction.destinationsIn 278) = true := by
  decide

/-- The raw U2 instruction counts before the quotient. -/
theorem u2Table_counts :
    instructionCounts u2Table =
      { incZero := 92, incOne := 73, decZero := 80, decOne := 32 } := by
  decide

/-- The last table entry is the unique halt instruction. -/
theorem u2Table_halt_positions :
    (u2Table.zipIdx.filter fun pair => pair.1 = .halt).map (fun pair => pair.2 + 1) = [278] := by
  decide

/-- The representative chosen for each of the four identified state classes. -/
def quotientState (q : Nat) : Nat :=
  if q = 150 ∨ q = 270 then 45
  else if q = 151 ∨ q = 271 then 46
  else if q = 230 ∨ q = 256 then 200
  else if q = 231 ∨ q = 257 then 201
  else q

@[simp] theorem quotientState_idempotent (q : Nat) :
    quotientState (quotientState q) = quotientState q := by
  by_cases first : q = 150 ∨ q = 270
  · simp [quotientState, first]
  by_cases second : q = 151 ∨ q = 271
  · simp [quotientState, first, second]
  by_cases third : q = 230 ∨ q = 256
  · simp [quotientState, first, second, third]
  by_cases fourth : q = 231 ∨ q = 257
  · simp [quotientState, first, second, third, fourth]
  · simp [quotientState, first, second, third, fourth]

@[simp] theorem quotientState_eq_278_iff (q : Nat) :
    quotientState q = 278 ↔ q = 278 := by
  by_cases first : q = 150 ∨ q = 270
  · rcases first with rfl | rfl <;> decide
  by_cases second : q = 151 ∨ q = 271
  · rcases second with rfl | rfl <;> decide
  by_cases third : q = 230 ∨ q = 256
  · rcases third with rfl | rfl <;> decide
  by_cases fourth : q = 231 ∨ q = 257
  · rcases fourth with rfl | rfl <;> decide
  · simp [quotientState, first, second, third, fourth]

/-- Apply the quotient map to every destination of an instruction. -/
def RawInstruction.mapStates (f : Nat → Nat) :
    RawInstruction → RawInstruction
  | .inc counter next => .inc counter (f next)
  | .dec counter positive zeroDest =>
      .dec counter (f positive) (f zeroDest)
  | .halt => .halt

/-- Look up a one-based U2 state number. -/
def u2At (q : Nat) : Option RawInstruction :=
  if q = 0 then none else u2Table[q - 1]?

/-- A successful lookup has a valid one-based state number. -/
theorem u2At_state_bounds {q : Nat} {instruction : RawInstruction}
    (lookup : u2At q = some instruction) : 1 ≤ q ∧ q ≤ 278 := by
  unfold u2At at lookup
  split at lookup
  · contradiction
  · rename_i nonzero
    have indexBound : q - 1 < u2Table.length :=
      getElem?_eq_some_iff.mp lookup |>.choose
    rw [u2Table_length] at indexBound
    omega

/-- A destination of any looked-up U2 instruction is a valid state number. -/
theorem u2At_destination_bounds {q : Nat} {instruction : RawInstruction}
    {destination : Nat} (lookup : u2At q = some instruction)
    (member : destination ∈ instruction.destinations) :
    1 ≤ destination ∧ destination ≤ 278 := by
  unfold u2At at lookup
  split at lookup
  · contradiction
  · have instructionMember : instruction ∈ u2Table :=
      List.mem_of_getElem? lookup
    have validInstruction :=
      (List.all_eq_true.mp u2Table_destinations) instruction instructionMember
    have validDestination :=
      (List.all_eq_true.mp validInstruction) destination member
    simpa [RawInstruction.destinationsIn] using validDestination

/-- The chosen one-based representatives of U2's quotient states. -/
def quotientStates : List Nat :=
  ((List.range 278).map fun i => i + 1).filter fun q => quotientState q == q

/-- The quotient table in increasing order of its chosen representatives. -/
def quotientTable : List RawInstruction :=
  quotientStates.filterMap fun q =>
    (u2At q).map (RawInstruction.mapStates quotientState)

/-- The four identifications reduce 278 states to 270 states. -/
theorem quotientStates_length : quotientStates.length = 270 := by
  decide

/-- Every original state has the same quotient instruction as its representative. -/
theorem quotient_instructions_wellDefined :
    (((List.range 278).map fun i => i + 1).all fun q =>
      (u2At q).map (RawInstruction.mapStates quotientState) ==
        (u2At (quotientState q)).map (RawInstruction.mapStates quotientState)) = true := by
  decide

/-- The finite compatibility check, exposed as a proposition for any valid state. -/
theorem quotient_instruction_eq {q : Nat} (positive : 1 ≤ q) (bounded : q ≤ 278) :
    (u2At q).map (RawInstruction.mapStates quotientState) =
      (u2At (quotientState q)).map (RawInstruction.mapStates quotientState) := by
  have member : q ∈ (List.range 278).map (fun i => i + 1) := by
    apply List.mem_map.2
    refine ⟨q - 1, ?_, ?_⟩
    · simp
      omega
    · omega
  have checked :=
    (List.all_eq_true.mp quotient_instructions_wellDefined) q member
  simpa using checked

/-- The quotient has the instruction counts used by the matrix bound. -/
theorem quotientTable_counts :
    instructionCounts quotientTable =
      { incZero := 88, incOne := 73, decZero := 80, decOne := 28 } := by
  decide

/-- The quotient still has one halt instruction, at the final representative. -/
theorem quotientTable_halt_positions :
    (quotientTable.zipIdx.filter fun pair => pair.1 = .halt).map
      (fun pair => pair.2 + 1) = [270] := by
  decide

end Mortality.SourceMachine
