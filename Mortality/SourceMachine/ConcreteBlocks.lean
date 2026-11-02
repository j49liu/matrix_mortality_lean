import Mortality.SourceMachine.BlockSemantics

/-!
# Certified locations of the twenty compiler blocks

Each theorem below checks a bounded interval of Ivanov's literal U2 table.
Together they connect the symbolic block semantics to all twenty instructions
of Korec's U20.  The certificates use kernel evaluation over a finite type;
there is no trusted external computation.
-/

namespace Mortality.SourceMachine.U20Compilation

set_option maxRecDepth 100000

theorem realizes_q1 : RealizesBlock 1 (decrementBlock 1 11 27 55) := by
  intro offset bound
  have certificate : ∀ i : Fin 26,
      u2At (1 + i.val) = (decrementBlock 1 11 27 55)[i.val]? := by decide
  exact certificate ⟨offset, by simpa using bound⟩

theorem realizes_q3 : RealizesBlock 27 (incrementBlock 27 17 1) := by
  intro offset bound
  have certificate : ∀ i : Fin 20,
      u2At (27 + i.val) = (incrementBlock 27 17 1)[i.val]? := by decide
  exact certificate ⟨offset, by simpa using bound⟩

theorem realizes_q4 : RealizesBlock 47 (decrementBlock 47 2 55 61) := by
  intro offset bound
  have certificate : ∀ i : Fin 8,
      u2At (47 + i.val) = (decrementBlock 47 2 55 61)[i.val]? := by decide
  exact certificate ⟨offset, by simpa using bound⟩

theorem realizes_q6 : RealizesBlock 55 (incrementBlock 55 3 47) := by
  intro offset bound
  have certificate : ∀ i : Fin 6,
      u2At (55 + i.val) = (incrementBlock 55 3 47)[i.val]? := by decide
  exact certificate ⟨offset, by simpa using bound⟩

theorem realizes_q7 : RealizesBlock 61 (decrementBlock 61 3 71 47) := by
  intro offset bound
  have certificate : ∀ i : Fin 10,
      u2At (61 + i.val) = (decrementBlock 61 3 71 47)[i.val]? := by decide
  exact certificate ⟨offset, by simpa using bound⟩

theorem realizes_q9 : RealizesBlock 71 (incrementBlock 71 2 76) := by
  intro offset bound
  have certificate : ∀ i : Fin 5,
      u2At (71 + i.val) = (incrementBlock 71 2 76)[i.val]? := by decide
  exact certificate ⟨offset, by simpa using bound⟩

theorem realizes_q10 : RealizesBlock 76 (decrementBlock 76 17 114 128) := by
  intro offset bound
  have certificate : ∀ i : Fin 38,
      u2At (76 + i.val) = (decrementBlock 76 17 114 128)[i.val]? := by decide
  exact certificate ⟨offset, by simpa using bound⟩

theorem realizes_q12 : RealizesBlock 114 (incrementBlock 114 11 61) := by
  intro offset bound
  have certificate : ∀ i : Fin 14,
      u2At (114 + i.val) = (incrementBlock 114 11 61)[i.val]? := by decide
  exact certificate ⟨offset, by simpa using bound⟩

theorem realizes_q13 : RealizesBlock 128 (decrementBlock 128 3 272 1) := by
  intro offset bound
  have certificate : ∀ i : Fin 10,
      u2At (128 + i.val) = (decrementBlock 128 3 272 1)[i.val]? := by decide
  exact certificate ⟨offset, by simpa using bound⟩

theorem realizes_q14 : RealizesBlock 138 (decrementBlock 138 5 1 152) := by
  intro offset bound
  have certificate : ∀ i : Fin 14,
      u2At (138 + i.val) = (decrementBlock 138 5 1 152)[i.val]? := by decide
  exact certificate ⟨offset, by simpa using bound⟩

theorem realizes_q16 : RealizesBlock 152 (decrementBlock 152 2 160 184) := by
  intro offset bound
  have certificate : ∀ i : Fin 8,
      u2At (152 + i.val) = (decrementBlock 152 2 160 184)[i.val]? := by decide
  exact certificate ⟨offset, by simpa using bound⟩

theorem realizes_q18 : RealizesBlock 160 (decrementBlock 160 2 168 202) := by
  intro offset bound
  have certificate : ∀ i : Fin 8,
      u2At (160 + i.val) = (decrementBlock 160 2 168 202)[i.val]? := by decide
  exact certificate ⟨offset, by simpa using bound⟩

theorem realizes_q20 : RealizesBlock 168 (decrementBlock 168 2 176 232) := by
  intro offset bound
  have certificate : ∀ i : Fin 8,
      u2At (168 + i.val) = (decrementBlock 168 2 176 232)[i.val]? := by decide
  exact certificate ⟨offset, by simpa using bound⟩

theorem realizes_q22 : RealizesBlock 176 (incrementBlock 176 5 152) := by
  intro offset bound
  have certificate : ∀ i : Fin 8,
      u2At (176 + i.val) = (incrementBlock 176 5 152)[i.val]? := by decide
  exact certificate ⟨offset, by simpa using bound⟩

theorem realizes_q23 : RealizesBlock 184 (decrementBlock 184 7 258 1) := by
  intro offset bound
  have certificate : ∀ i : Fin 18,
      u2At (184 + i.val) = (decrementBlock 184 7 258 1)[i.val]? := by decide
  exact certificate ⟨offset, by simpa using bound⟩

theorem realizes_q27 : RealizesBlock 202 (decrementBlock 202 13 258 1) := by
  intro offset bound
  have certificate : ∀ i : Fin 30,
      u2At (202 + i.val) = (decrementBlock 202 13 258 1)[i.val]? := by decide
  exact certificate ⟨offset, by simpa using bound⟩

theorem realizes_q30 : RealizesBlock 232 (incrementBlock 232 7 242) := by
  intro offset bound
  have certificate : ∀ i : Fin 10,
      u2At (232 + i.val) = (incrementBlock 232 7 242)[i.val]? := by decide
  exact certificate ⟨offset, by simpa using bound⟩

theorem realizes_q31 : RealizesBlock 242 (incrementBlock 242 13 258) := by
  intro offset bound
  have certificate : ∀ i : Fin 16,
      u2At (242 + i.val) = (incrementBlock 242 13 258)[i.val]? := by decide
  exact certificate ⟨offset, by simpa using bound⟩

theorem realizes_q32 : RealizesBlock 258 (decrementBlock 258 5 1 278) := by
  intro offset bound
  have certificate : ∀ i : Fin 14,
      u2At (258 + i.val) = (decrementBlock 258 5 1 278)[i.val]? := by decide
  exact certificate ⟨offset, by simpa using bound⟩

theorem realizes_q15 : RealizesBlock 272 (incrementBlock 272 3 138) := by
  intro offset bound
  have certificate : ∀ i : Fin 6,
      u2At (272 + i.val) = (incrementBlock 272 3 138)[i.val]? := by decide
  exact certificate ⟨offset, by simpa using bound⟩

end Mortality.SourceMachine.U20Compilation
