import Mortality.Matrix2

/-!
# Conversion from projective reachability to mortality

This file proves the one-rank-one lemma with no restriction on the number
of rank-one occurrences.  The converse scans an arbitrary mixed word and
tracks the nonsingular block since its most recent rank-one letter.
-/

namespace Mortality

/-- The row associated with a target line. -/
def targetRow (target : Vec2) : Vec2 := Vec2.perp target

/-- The rank-one matrix whose image is the source line and whose kernel is
the target line. -/
def rankOneMatrix (source target : Vec2) : Matrix2 :=
  Matrix2.outer source (targetRow target)

@[simp] theorem rankOneMatrix_det (source target : Vec2) :
    (rankOneMatrix source target).det = 0 := by
  cases source
  cases target
  simp only [rankOneMatrix, targetRow, Vec2.perp, Matrix2.outer, Matrix2.det]
  grind

theorem rankOneMatrix_nonzero {source target : Vec2}
    (sourceNonzero : source.Nonzero) (targetNonzero : target.Nonzero) :
    rankOneMatrix source target ≠ Matrix2.zero :=
  Matrix2.outer_nonzero sourceNonzero (Vec2.perp_nonzero targetNonzero)

theorem rankOneMatrix_rankOne {source target : Vec2}
    (sourceNonzero : source.Nonzero) (targetNonzero : target.Nonzero) :
    (rankOneMatrix source target).RankOne := by
  exact ⟨source, targetRow target, sourceNonzero,
    Vec2.perp_nonzero targetNonzero, rfl⟩

theorem rankOneMatrix_not_mem_nonsingular (alphabet : List Matrix2)
    (source target : Vec2)
    (alphabetNonsingular : ∀ matrix ∈ alphabet, matrix.Nonsingular) :
    rankOneMatrix source target ∉ alphabet := by
  intro member
  have nonsingular := alphabetNonsingular _ member
  exact nonsingular (rankOneMatrix_det source target)

theorem rankOne_cons_nodup {alphabet : List Matrix2} {source target : Vec2}
    (alphabetNodup : alphabet.Nodup)
    (alphabetNonsingular : ∀ matrix ∈ alphabet, matrix.Nonsingular) :
    (rankOneMatrix source target :: alphabet).Nodup := by
  exact List.nodup_cons.mpr
    ⟨rankOneMatrix_not_mem_nonsingular alphabet source target
      alphabetNonsingular, alphabetNodup⟩

/-- Every nonzero image of the constructed matrix lies on its fixed source
line. -/
theorem rankOneMatrix_apply (source target vector : Vec2) :
    Matrix2.apply (rankOneMatrix source target) vector =
      Vec2.scale (Vec2.dot (targetRow target) vector) source := by
  exact Matrix2.apply_outer source (targetRow target) vector

/-- The scalar condition found between two consecutive rank-one factors. -/
def HasRankOneWitness (alphabet : List Matrix2)
    (source target : Vec2) : Prop :=
  ∃ word, WordOver alphabet word ∧
    Vec2.dot (targetRow target)
      (Matrix2.apply (matrixWordProduct word) source) = 0

/-- If no accepting block has appeared, a scanned prefix is either wholly
nonsingular or is an outer product whose column records the nonsingular
block after the most recent rank-one factor. -/
inductive SafeProduct (alphabet : List Matrix2) (source : Vec2) :
    Matrix2 → Prop
  | before {product : Matrix2} : product.Nonsingular →
      SafeProduct alphabet source product
  | after (block : List Matrix2) (row : Vec2) {product : Matrix2} :
      WordOver alphabet block → row.Nonzero →
      product = Matrix2.outer
        (Matrix2.apply (matrixWordProduct block) source) row →
      SafeProduct alphabet source product

/-- Left-multiply an accumulator by the letters in application order. -/
def scanProduct : List Matrix2 → Matrix2 → Matrix2
  | [], product => product
  | matrix :: word, product => scanProduct word (Matrix2.mul matrix product)

theorem scanProduct_eq (word : List Matrix2) (product : Matrix2) :
    scanProduct word product =
      Matrix2.mul (matrixWordProduct word) product := by
  induction word generalizing product with
  | nil => simp [scanProduct]
  | cons matrix word inductionHypothesis =>
      rw [scanProduct, inductionHypothesis]
      simp [Matrix2.mul_assoc]

@[simp] theorem scanProduct_identity (word : List Matrix2) :
    scanProduct word Matrix2.identity = matrixWordProduct word := by
  rw [scanProduct_eq, Matrix2.mul_identity]

/-- A safe product is nonzero. -/
theorem SafeProduct.nonzero {alphabet : List Matrix2} {source : Vec2}
    {product : Matrix2}
    (alphabetNonsingular : ∀ matrix ∈ alphabet, matrix.Nonsingular)
    (sourceNonzero : source.Nonzero)
    (safe : SafeProduct alphabet source product) :
    product ≠ Matrix2.zero := by
  cases safe with
  | before nonsingular =>
      intro productZero
      subst product
      exact Matrix2.not_nonsingular_zero nonsingular
  | after block row blockOver rowNonzero productEq =>
      have blockNonsingular :=
        matrixWordProduct_nonsingular alphabetNonsingular blockOver
      have columnNonzero :=
        Matrix2.apply_nonzero blockNonsingular sourceNonzero
      rw [productEq]
      exact Matrix2.outer_nonzero columnNonzero rowNonzero

/-- One further mixed-alphabet letter either exposes an accepting block or
preserves the safe-product invariant. -/
theorem safeProduct_step {alphabet : List Matrix2} {source target : Vec2}
    {product matrix : Matrix2}
    (alphabetNonsingular : ∀ candidate ∈ alphabet, candidate.Nonsingular)
    (targetNonzero : target.Nonzero)
    (safe : SafeProduct alphabet source product)
    (matrixMem : matrix ∈ rankOneMatrix source target :: alphabet) :
    HasRankOneWitness alphabet source target ∨
      SafeProduct alphabet source (Matrix2.mul matrix product) := by
  by_cases isRankOne : matrix = rankOneMatrix source target
  · subst matrix
    cases safe with
    | before productNonsingular =>
        right
        apply SafeProduct.after []
          (Matrix2.rowMul (targetRow target) product)
        · exact wordOver_nil alphabet
        · exact Matrix2.rowMul_nonzero
            (Vec2.perp_nonzero targetNonzero) productNonsingular
        · simp [rankOneMatrix, targetRow, Matrix2.outer_mul]
    | after block row blockOver rowNonzero productEq =>
        let scalar := Vec2.dot (targetRow target)
          (Matrix2.apply (matrixWordProduct block) source)
        by_cases scalarZero : scalar = 0
        · left
          exact ⟨block, blockOver, scalarZero⟩
        · right
          apply SafeProduct.after [] (Vec2.scale scalar row)
          · exact wordOver_nil alphabet
          · exact Vec2.scale_nonzero scalarZero rowNonzero
          · rw [productEq]
            simp only [rankOneMatrix, Matrix2.outer_outer]
            rw [Matrix2.outer_scale_left]
            simp [scalar]
  · have matrixInAlphabet : matrix ∈ alphabet := by
      simp only [List.mem_cons] at matrixMem
      exact matrixMem.resolve_left isRankOne
    cases safe with
    | before productNonsingular =>
        right
        exact SafeProduct.before
          (Matrix2.Nonsingular.mul
            (alphabetNonsingular matrix matrixInAlphabet)
            productNonsingular)
    | after block row blockOver rowNonzero productEq =>
        right
        apply SafeProduct.after (block ++ [matrix]) row
        · exact wordOver_append blockOver
            (wordOver_cons matrixInAlphabet (wordOver_nil alphabet))
        · exact rowNonzero
        · rw [productEq, Matrix2.mul_outer]
          simp [matrixWordProduct_append, Matrix2.apply_mul]

/-- Scanning an arbitrary mixed word preserves the invariant until an
accepting nonsingular block appears. -/
theorem scanProduct_classification {alphabet : List Matrix2}
    {source target : Vec2} {initial : Matrix2} (word : List Matrix2)
    (alphabetNonsingular : ∀ matrix ∈ alphabet, matrix.Nonsingular)
    (targetNonzero : target.Nonzero)
    (initialSafe : SafeProduct alphabet source initial)
    (wordOver : WordOver (rankOneMatrix source target :: alphabet) word) :
    HasRankOneWitness alphabet source target ∨
      SafeProduct alphabet source (scanProduct word initial) := by
  induction word generalizing initial with
  | nil => exact Or.inr initialSafe
  | cons matrix word inductionHypothesis =>
      have matrixMem := wordOver matrix (by simp)
      have tailOver : WordOver (rankOneMatrix source target :: alphabet) word :=
        fun letter letterMem => wordOver letter (by simp [letterMem])
      rcases safeProduct_step alphabetNonsingular targetNonzero
          initialSafe matrixMem with witness | nextSafe
      · exact Or.inl witness
      · exact inductionHypothesis nextSafe tailOver

/-- A reachability witness gives a zero sandwich `R W R`. -/
theorem rankOne_sandwich_zero {source target : Vec2} {wordMatrix : Matrix2}
    (annihilated : Vec2.dot (targetRow target)
      (Matrix2.apply wordMatrix source) = 0) :
    Matrix2.mul (rankOneMatrix source target)
        (Matrix2.mul wordMatrix (rankOneMatrix source target)) =
      Matrix2.zero := by
  rw [rankOneMatrix, Matrix2.mul_outer, Matrix2.outer_outer,
    annihilated, Vec2.scale_zero, Matrix2.outer_zero_column]

/-- The paper's one-rank-one equivalence, including empty reachability
words and arbitrary repetitions of the rank-one matrix in mortality words. -/
theorem one_rankOne_mortality_iff (alphabet : List Matrix2)
    (source target : Vec2)
    (alphabetNonsingular : ∀ matrix ∈ alphabet, matrix.Nonsingular)
    (sourceNonzero : source.Nonzero) (targetNonzero : target.Nonzero) :
    Mortal (rankOneMatrix source target :: alphabet) ↔
      ProjectivelyReachable alphabet source target := by
  constructor
  · rintro ⟨word, wordNonempty, wordOver, productZero⟩
    have initialSafe : SafeProduct alphabet source Matrix2.identity :=
      SafeProduct.before Matrix2.Nonsingular.identity
    rcases scanProduct_classification word alphabetNonsingular targetNonzero
        initialSafe wordOver with witness | safe
    · obtain ⟨block, blockOver, annihilated⟩ := witness
      have blockNonsingular :=
        matrixWordProduct_nonsingular alphabetNonsingular blockOver
      have imageNonzero :=
        Matrix2.apply_nonzero blockNonsingular sourceNonzero
      exact ⟨block, blockOver,
        (sameLine_iff_dot_perp_eq_zero imageNonzero targetNonzero).mpr
          annihilated⟩
    · have nonzero := safe.nonzero alphabetNonsingular sourceNonzero
      rw [scanProduct_identity, productZero] at nonzero
      exact False.elim (nonzero rfl)
  · rintro ⟨word, wordOver, sameLine⟩
    let wordMatrix := matrixWordProduct word
    have wordNonsingular :=
      matrixWordProduct_nonsingular alphabetNonsingular wordOver
    have imageNonzero := Matrix2.apply_nonzero wordNonsingular sourceNonzero
    have annihilated : Vec2.dot (targetRow target)
        (Matrix2.apply wordMatrix source) = 0 := by
      exact (sameLine_iff_dot_perp_eq_zero imageNonzero targetNonzero).mp
        sameLine
    let mortalityWord := [rankOneMatrix source target] ++ word ++
      [rankOneMatrix source target]
    refine ⟨mortalityWord, ?_, ?_, ?_⟩
    · simp [mortalityWord]
    · apply wordOver_append
      · apply wordOver_append
        · exact wordOver_cons (by simp) (wordOver_nil _)
        · exact wordOver.mono (fun matrix matrixMem => by simp [matrixMem])
      · exact wordOver_cons (by simp) (wordOver_nil _)
    · simp only [mortalityWord, matrixWordProduct_append]
      simpa [wordMatrix] using
        rankOne_sandwich_zero (source := source) (target := target)
          (wordMatrix := wordMatrix) annihilated

end Mortality
