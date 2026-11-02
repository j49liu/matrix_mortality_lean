import Std.Data.TreeSet.Lemmas
import Mortality.Compiler.FixedAllocation

/-!
# Efficient distinctness certificate for the fixed matrices

The standard decision procedure for `List.Nodup` compares every pair and is
too slow on 5,798 large matrices.  This file checks the already sufficient
`b` entry with a balanced tree set.  The scanner has a proved semantic
specification, so the finite computation yields an ordinary kernel theorem;
it does not use `native_decide` or add an axiom.
-/

namespace Mortality.Compiler.DistinctCertificate

open Mortality
open Mortality.Compiler.FixedAllocation

set_option maxRecDepth 1000000
set_option maxHeartbeats 8000000

/-- Insert a list into a balanced tree, rejecting the first repeated value. -/
def allDistinctFrom (seen : Std.TreeSet Int) : List Int → Bool
  | [] => true
  | value :: values =>
      if seen.contains value then false
      else allDistinctFrom (seen.insert value) values

def DistinctFromSpec (seen : Std.TreeSet Int) (values : List Int) : Prop :=
  values.Nodup ∧ ∀ value ∈ values, value ∉ seen

theorem allDistinctFrom_sound {seen : Std.TreeSet Int} {values : List Int}
    (checked : allDistinctFrom seen values = true) :
    DistinctFromSpec seen values := by
  induction values generalizing seen with
  | nil => simp [DistinctFromSpec]
  | cons value values inductionHypothesis =>
      simp only [allDistinctFrom] at checked
      split at checked
      · contradiction
      · rename_i notContained
        have tailSpec := inductionHypothesis checked
        constructor
        · rw [List.nodup_cons]
          constructor
          · intro valueMem
            have valueNotInserted := tailSpec.2 value valueMem
            exact valueNotInserted (Std.TreeSet.mem_insert_self)
          · exact tailSpec.1
        · intro candidate candidateMem
          simp only [List.mem_cons] at candidateMem
          rcases candidateMem with rfl | candidateMem
          · intro valueMem
            have containsTrue : seen.contains candidate = true := by
              simpa using (Std.TreeSet.mem_iff_contains.mp valueMem)
            exact notContained containsTrue
          · intro candidateSeen
            apply tailSpec.2 candidate candidateMem
            exact Std.TreeSet.mem_insert.mpr (Or.inr candidateSeen)

/-- A finite, logarithmic-search certificate for the `b` entries of all
5,798 listed matrices. -/
private theorem listedMatrixBValues_distinct_check :
    allDistinctFrom ∅ (listedMatrices.map IntMatrix2.b) = true := by
  decide

theorem listedMatrixBValues_nodup :
    (listedMatrices.map IntMatrix2.b).Nodup :=
  (allDistinctFrom_sound listedMatrixBValues_distinct_check).1

theorem nodup_of_projection_nodup {α β : Type} (projection : α → β)
    {values : List α} (projectedNodup : (values.map projection).Nodup) :
    values.Nodup := by
  induction values with
  | nil => simp
  | cons value values inductionHypothesis =>
      rw [List.map_cons, List.nodup_cons] at projectedNodup
      rw [List.nodup_cons]
      constructor
      · intro valueMem
        apply projectedNodup.1
        exact List.mem_map.mpr ⟨value, valueMem, rfl⟩
      · exact inductionHypothesis projectedNodup.2

/-- The concrete list already consists of 5,798 distinct matrices; dummy
padding is not needed for this allocation. -/
theorem listedMatrices_nodup : listedMatrices.Nodup :=
  nodup_of_projection_nodup IntMatrix2.b listedMatrixBValues_nodup

end Mortality.Compiler.DistinctCertificate
