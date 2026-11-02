import Mortality.SourceMachine.KorecNormalizedShell

/-!
# Korec's ordered-prime system

This file separates the finite combinatorics of Korec's Lemma 6.1 from its
analytic existence proof.  The quotient-rank function below is Korec's `h`.
The main conversion proves that the ordered factors and inequalities used in
conditions (6.1.1)--(6.1.5) supply the program-independent `RankFrame` needed
by the checked machine reduction.
-/

namespace Mortality.SourceMachine.KorecPrimeSystem

open Mortality.SourceMachine.KorecNormalizedShell

/-- Korec's quotient sum `h(value)` for a finite factor list. -/
def quotientRank (factors : List Nat) (value : Nat) : Nat :=
  (factors.map fun factor => value / factor).sum

@[simp] theorem quotientRank_nil (value : Nat) :
    quotientRank [] value = 0 := rfl

@[simp] theorem quotientRank_cons (factor : Nat) (factors : List Nat)
    (value : Nat) :
    quotientRank (factor :: factors) value =
      value / factor + quotientRank factors value := rfl

@[simp] theorem quotientRank_append (left right : List Nat) (value : Nat) :
    quotientRank (left ++ right) value =
      quotientRank left value + quotientRank right value := by
  simp [quotientRank]

/-- Quotient rank is monotone in its numerical argument. -/
theorem quotientRank_mono (factors : List Nat) {left right : Nat}
    (ordered : left ≤ right) :
    quotientRank factors left ≤ quotientRank factors right := by
  induction factors with
  | nil => simp
  | cons factor factors inductionHypothesis =>
      simp only [quotientRank_cons]
      exact Nat.add_le_add (Nat.div_le_div_right ordered)
        inductionHypothesis

/-- Factors strictly above the argument contribute zero to the quotient
rank. -/
theorem quotientRank_eq_zero_of_lt
    (factors : List Nat) (value : Nat)
    (above : ∀ factor, factor ∈ factors → value < factor) :
    quotientRank factors value = 0 := by
  induction factors with
  | nil => rfl
  | cons factor factors inductionHypothesis =>
      have headAbove := above factor (by simp)
      have tailAbove : ∀ other, other ∈ factors → value < other := by
        intro other otherMem
        exact above other (by simp [otherMem])
      rw [quotientRank_cons, Nat.div_eq_of_lt headAbove,
        inductionHypothesis tailAbove]

/-- Every positive factor at most the argument contributes at least one. -/
theorem length_le_quotientRank
    (factors : List Nat) (value : Nat)
    (positive : ∀ factor, factor ∈ factors → 0 < factor)
    (below : ∀ factor, factor ∈ factors → factor ≤ value) :
    factors.length ≤ quotientRank factors value := by
  induction factors with
  | nil => simp
  | cons factor factors inductionHypothesis =>
      have headPositive := positive factor (by simp)
      have headBelow := below factor (by simp)
      have tailPositive : ∀ other, other ∈ factors → 0 < other := by
        intro other otherMem
        exact positive other (by simp [otherMem])
      have tailBelow : ∀ other, other ∈ factors → other ≤ value := by
        intro other otherMem
        exact below other (by simp [otherMem])
      have headContribution : 1 ≤ value / factor :=
        (Nat.one_le_div_iff headPositive).2 headBelow
      have tailContribution := inductionHypothesis tailPositive tailBelow
      simp only [List.length_cons, quotientRank_cons]
      omega

/-- If `newFactors` lie strictly above `base` and at most `upper`, appending
them raises quotient rank by at least their number. -/
theorem quotientRank_append_increase
    (oldFactors newFactors : List Nat) {base upper : Nat}
    (baseBelow : base ≤ upper)
    (newAbove : ∀ factor, factor ∈ newFactors → base < factor)
    (newBelow : ∀ factor, factor ∈ newFactors → factor ≤ upper) :
    quotientRank (oldFactors ++ newFactors) base + newFactors.length ≤
      quotientRank (oldFactors ++ newFactors) upper := by
  have oldMonotone := quotientRank_mono oldFactors baseBelow
  have newZero := quotientRank_eq_zero_of_lt newFactors base newAbove
  have newPositive : ∀ factor, factor ∈ newFactors → 0 < factor := by
    intro factor factorMem
    have := newAbove factor factorMem
    omega
  have newContribution :=
    length_le_quotientRank newFactors upper newPositive newBelow
  simp only [quotientRank_append, newZero, Nat.add_zero]
  omega

/-- Korec only states the rank difference at the final candidate in (6.1.3).
Strict ordering forces every intermediate candidate to raise the rank by
exactly one. -/
theorem quotientRank_getElem_eq_base_add
    (lowerFactors candidates : List Nat) {base upper index : Nat}
    (ordered : candidates.Pairwise (· < ·))
    (aboveBase : ∀ factor, factor ∈ candidates → base < factor)
    (belowUpper : ∀ factor, factor ∈ candidates → factor ≤ upper)
    (endpoint : quotientRank (lowerFactors ++ candidates) upper =
      quotientRank (lowerFactors ++ candidates) base + candidates.length)
    (indexBound : index < candidates.length) :
    quotientRank (lowerFactors ++ candidates) candidates[index] =
      quotientRank (lowerFactors ++ candidates) base + index + 1 := by
  induction candidates generalizing lowerFactors base index with
  | nil => simp at indexBound
  | cons candidate candidates inductionHypothesis =>
      rw [List.pairwise_cons] at ordered
      have candidateAbove : base < candidate :=
        aboveBase candidate (by simp)
      have candidateBelow : candidate ≤ upper :=
        belowUpper candidate (by simp)
      have tailAboveBase : ∀ factor, factor ∈ candidates → base < factor := by
        intro factor factorMem
        exact aboveBase factor (by simp [factorMem])
      have tailAboveCandidate :
          ∀ factor, factor ∈ candidates → candidate < factor :=
        ordered.1
      have tailBelowUpper :
          ∀ factor, factor ∈ candidates → factor ≤ upper := by
        intro factor factorMem
        exact belowUpper factor (by simp [factorMem])
      have tailZeroBase := quotientRank_eq_zero_of_lt candidates base
        tailAboveBase
      have tailZeroCandidate := quotientRank_eq_zero_of_lt candidates candidate
        tailAboveCandidate
      have baseSplit :
          quotientRank (lowerFactors ++ candidate :: candidates) base =
            quotientRank (lowerFactors ++ [candidate]) base := by
        rw [show lowerFactors ++ candidate :: candidates =
          (lowerFactors ++ [candidate]) ++ candidates by simp]
        simp [quotientRank_append, tailZeroBase]
      have candidateSplit :
          quotientRank (lowerFactors ++ candidate :: candidates) candidate =
            quotientRank (lowerFactors ++ [candidate]) candidate := by
        rw [show lowerFactors ++ candidate :: candidates =
          (lowerFactors ++ [candidate]) ++ candidates by simp]
        simp [quotientRank_append, tailZeroCandidate]
      have headIncrease := quotientRank_append_increase
        lowerFactors [candidate] (Nat.le_of_lt candidateAbove)
        (by simp [candidateAbove]) (by simp)
      have headLower :
          quotientRank (lowerFactors ++ candidate :: candidates) base + 1 ≤
            quotientRank (lowerFactors ++ candidate :: candidates) candidate := by
        rw [baseSplit, candidateSplit]
        simpa using headIncrease
      have tailIncrease := quotientRank_append_increase
        (lowerFactors ++ [candidate]) candidates candidateBelow
        tailAboveCandidate tailBelowUpper
      have tailLower :
          quotientRank (lowerFactors ++ candidate :: candidates) candidate +
              candidates.length ≤
            quotientRank (lowerFactors ++ candidate :: candidates) upper := by
        simpa using tailIncrease
      have headRank :
          quotientRank (lowerFactors ++ candidate :: candidates) candidate =
            quotientRank (lowerFactors ++ candidate :: candidates) base + 1 := by
        simp only [List.length_cons] at endpoint
        omega
      cases index with
      | zero =>
          simpa using headRank
      | succ index =>
          have tailIndexBound : index < candidates.length := by
            simp only [List.length_cons] at indexBound
            omega
          have tailEndpoint :
              quotientRank ((lowerFactors ++ [candidate]) ++ candidates) upper =
                quotientRank ((lowerFactors ++ [candidate]) ++ candidates)
                    candidate + candidates.length := by
            rw [← show lowerFactors ++ candidate :: candidates =
              (lowerFactors ++ [candidate]) ++ candidates by simp]
            rw [endpoint, headRank]
            simp only [List.length_cons]
            omega
          have tailResult := inductionHypothesis
            (lowerFactors := lowerFactors ++ [candidate])
            (base := candidate) (index := index)
            ordered.2 tailAboveCandidate tailBelowUpper tailEndpoint
            tailIndexBound
          rw [List.getElem_cons_succ]
          rw [show lowerFactors ++ candidate :: candidates =
            (lowerFactors ++ [candidate]) ++ candidates by simp]
          rw [tailResult]
          rw [← show lowerFactors ++ candidate :: candidates =
            (lowerFactors ++ [candidate]) ++ candidates by simp]
          rw [headRank]
          omega

/-- The finite conclusions of Korec's Lemma 6.1 needed by the normalized
direct-entry construction.  `lowerFactors` represents `r₁,...,rₛ=p₀`, while
`candidates` represents `p₁,...,pₖ`.  The four final fields
`leastSquareAboveBound`, `endpointRank`, `lowerEnvelope`, and `upperEnvelope`
are conditions (6.1.2)--(6.1.5), specialized to `c = 3` and written without
truncated subtraction. -/
structure System (span : Nat) where
  least : Nat
  base : Nat
  bound : Nat
  lowerFactors : List Nat
  candidates : List Nat
  candidateLength : candidates.length + 1 = span
  lowerLength : 3 < lowerFactors.length
  selectedOrdered : (lowerFactors ++ candidates).Pairwise (· < ·)
  leastMem : least ∈ lowerFactors ++ candidates
  selectedAtLeastLeast : ∀ factor, factor ∈ lowerFactors ++ candidates →
    least ≤ factor
  selectedAtMostBound : ∀ factor, factor ∈ lowerFactors ++ candidates →
    factor ≤ bound
  primeLike : ∀ factor, factor ∈ lowerFactors ++ candidates →
    2 ≤ factor ∧ ∀ divisor, divisor ∣ factor →
      divisor = 1 ∨ divisor = factor
  lowerAtMostBase : ∀ factor, factor ∈ lowerFactors → factor ≤ base
  baseBelowCandidates : ∀ factor, factor ∈ candidates → base < factor
  leastSquareAboveBound : bound < least * least
  endpointRank : quotientRank (lowerFactors ++ candidates) bound =
    quotientRank (lowerFactors ++ candidates) base + candidates.length
  lowerEnvelope :
    3 * quotientRank (lowerFactors ++ candidates) bound + 3 < base
  upperEnvelope :
    bound < 3 * quotientRank (lowerFactors ++ candidates) base + least

def System.selectedFactors {span : Nat} (system : System span) : List Nat :=
  system.lowerFactors ++ system.candidates

def System.offset {span : Nat} (system : System span) : Nat :=
  quotientRank system.selectedFactors system.base

/-- Candidate `state` is `p_state` in Korec's one-based notation.  The
fallback is irrelevant on the positive states below `span`. -/
def System.candidate {span : Nat} (system : System span)
    (state : Nat) : Nat :=
  system.candidates.getD (state - 1) 0

theorem System.candidate_index_bound
    {span : Nat} (system : System span) {state : Nat}
    (statePositive : 0 < state) (stateBounded : state < span) :
    state - 1 < system.candidates.length := by
  have lengthEq := system.candidateLength
  omega

theorem System.candidate_eq_getElem
    {span : Nat} (system : System span) {state : Nat}
    (statePositive : 0 < state) (stateBounded : state < span) :
    system.candidate state =
      system.candidates[state - 1]'(system.candidate_index_bound
        statePositive stateBounded) := by
  have indexBound := system.candidate_index_bound statePositive stateBounded
  simp [System.candidate, List.getD_eq_getElem?_getD,
    List.getElem?_eq_getElem indexBound]

theorem System.candidate_mem
    {span : Nat} (system : System span) {state : Nat}
    (statePositive : 0 < state) (stateBounded : state < span) :
    system.candidate state ∈ system.selectedFactors := by
  rw [system.candidate_eq_getElem statePositive stateBounded]
  apply List.mem_append_right
  exact List.getElem_mem _

theorem System.candidate_rank
    {span : Nat} (system : System span) {state : Nat}
    (statePositive : 0 < state) (stateBounded : state < span) :
    quotientRank system.selectedFactors (system.candidate state) =
      system.offset + state := by
  have indexBound := system.candidate_index_bound statePositive stateBounded
  have candidateRank := quotientRank_getElem_eq_base_add
    system.lowerFactors system.candidates
    (base := system.base) (upper := system.bound)
    (List.pairwise_append.mp system.selectedOrdered).2.1
    system.baseBelowCandidates
    (fun factor factorMem =>
      system.selectedAtMostBound factor (List.mem_append_right _ factorMem))
    system.endpointRank indexBound
  rw [system.candidate_eq_getElem statePositive stateBounded]
  change quotientRank (system.lowerFactors ++ system.candidates)
      system.candidates[state - 1] =
        quotientRank (system.lowerFactors ++ system.candidates)
          system.base + state
  rw [candidateRank]
  omega

theorem System.candidate_above_base
    {span : Nat} (system : System span) {state : Nat}
    (statePositive : 0 < state) (stateBounded : state < span) :
    system.base < system.candidate state := by
  apply system.baseBelowCandidates
  rw [system.candidate_eq_getElem statePositive stateBounded]
  exact List.getElem_mem _

theorem System.candidate_at_most_bound
    {span : Nat} (system : System span) {state : Nat}
    (statePositive : 0 < state) (stateBounded : state < span) :
    system.candidate state ≤ system.bound :=
  system.selectedAtMostBound _
    (system.candidate_mem statePositive stateBounded)

theorem System.selected_nodup
    {span : Nat} (system : System span) :
    system.selectedFactors.Nodup := by
  rw [List.nodup_iff_pairwise_ne]
  exact system.selectedOrdered.imp fun ordered => Nat.ne_of_lt ordered

theorem System.selected_product_separated
    {span : Nat} (system : System span) :
    system.selectedFactors.Pairwise fun left right =>
      system.bound < left * right := by
  rw [List.pairwise_iff_getElem]
  intro leftIndex rightIndex leftBound rightBound indexOrdered
  have leftMem : system.selectedFactors[leftIndex] ∈
      system.lowerFactors ++ system.candidates := by
    exact List.getElem_mem leftBound
  have rightMem : system.selectedFactors[rightIndex] ∈
      system.lowerFactors ++ system.candidates := by
    exact List.getElem_mem rightBound
  have leftAtLeast := system.selectedAtLeastLeast _ leftMem
  have rightAtLeast := system.selectedAtLeastLeast _ rightMem
  exact Nat.lt_of_lt_of_le system.leastSquareAboveBound
    (Nat.mul_le_mul leftAtLeast rightAtLeast)

theorem System.candidate_lower
    {span : Nat} (system : System span) {state : Nat}
    (statePositive : 0 < state) (stateBounded : state < span) :
    3 * (system.offset + span) ≤ system.candidate state := by
  have endpoint := system.endpointRank
  have lengthEq := system.candidateLength
  have lower := system.lowerEnvelope
  have candidateAbove :=
    system.candidate_above_base statePositive stateBounded
  unfold System.offset at endpoint ⊢
  change quotientRank system.selectedFactors system.bound =
    quotientRank system.selectedFactors system.base +
      system.candidates.length at endpoint
  change 3 * quotientRank system.selectedFactors system.bound + 3 <
    system.base at lower
  omega

/-- Korec's hypothesis `s > c`, with `c = 3`, makes the relocation offset
large enough for the checked R2 relocation. -/
theorem System.offset_large
    {span : Nat} (system : System span) : 3 ≤ system.offset := by
  have lowerPositive : ∀ factor, factor ∈ system.lowerFactors → 0 < factor := by
    intro factor factorMem
    have prime := system.primeLike factor
      (List.mem_append_left system.candidates factorMem)
    omega
  have lowerContribution := length_le_quotientRank system.lowerFactors
    system.base lowerPositive system.lowerAtMostBase
  have candidateZero := quotientRank_eq_zero_of_lt system.candidates
    system.base system.baseBelowCandidates
  unfold System.offset System.selectedFactors
  rw [quotientRank_append, candidateZero]
  have lowerLength := system.lowerLength
  omega

theorem System.candidate_upper
    {span : Nat} (system : System span) {state : Nat}
    (statePositive : 0 < state) (stateBounded : state < span) :
    system.candidate state < 3 * system.offset + system.least := by
  exact Nat.lt_of_le_of_lt
    (system.candidate_at_most_bound statePositive stateBounded)
    system.upperEnvelope

/-- Conditions (6.1.1)--(6.1.5) imply the exact arithmetic frame consumed by
the normalized machine and matrix pipeline.  Korec's entry-chain conditions
(6.1.6)--(6.1.7) are unnecessary because the checked reduction initializes
the shifted state and reader carry directly. -/
def System.toRankFrame {span : Nat} (system : System span) :
    RankFrame system.offset span system.least system.bound where
  leastAtLeastTwo := (system.primeLike system.least system.leastMem).1
  leastBounded := system.selectedAtMostBound system.least system.leastMem
  selectedFactors := system.selectedFactors
  selectedNodup := system.selected_nodup
  selectedProductSeparated := system.selected_product_separated
  selectedAtLeastLeast := system.selectedAtLeastLeast
  selectedAtMostBound := system.selectedAtMostBound
  selectedDivisorClassification := fun factor factorMem =>
    (system.primeLike factor factorMem).2
  candidate := system.candidate
  candidateMem := system.candidate_mem
  candidateRankSum := by
    intro state statePositive stateBounded
    exact system.candidate_rank statePositive stateBounded
  candidateLower := system.candidate_lower
  candidateUpper := system.candidate_upper

/-- The analytic statement isolated from every finite combinatorial and
machine-semantic deduction.  Here `span = k + 1`, so `2 < span` is Korec's
hypothesis `k > 1`.  It is proved in `KorecPrimeSystemExistence`. -/
def ExistsForEverySpan : Prop :=
  ∀ span, 2 < span → Nonempty (System span)

/-- The analytic existence statement supplies the rank frames required by
the checked reduction. -/
theorem rankFrame_exists_of_existsForEverySpan
    (existence : ExistsForEverySpan)
    (span : Nat) (spanLarge : 2 < span) :
    ∃ offset least bound,
      3 ≤ offset ∧ Nonempty (RankFrame offset span least bound) := by
  obtain ⟨system⟩ := existence span spanLarge
  exact ⟨system.offset, system.least, system.bound,
    system.offset_large, ⟨system.toRankFrame⟩⟩

end Mortality.SourceMachine.KorecPrimeSystem
