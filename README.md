# Lean formalization of two-dimensional matrix mortality

This repository contains the Lean 4 formalization accompanying the paper
[*Mortality Is Undecidable for 2 × 2 Integer
Matrices*](https://arxiv.org/abs/2611.06562). The formalized construction uses
5,798 fixed nonsingular matrices and one input-dependent rank-one matrix, for
exactly 5,799 distinct matrices in each instance.

The paper-facing endpoint is
`Mortality.PaperTheorem.paper_result`. It collects the structural,
cardinality, effectiveness, and undecidability claims in one theorem.

## The problem

Let `A` be a finite family of square integer matrices. The family is
*mortal* if some nonempty product of matrices from `A`, with repetition
allowed and in an arbitrary order, is the zero matrix. The matrix mortality
problem asks whether mortality can be decided from `A`.

Mortality is elementary in dimension one and was already known to be
undecidable in every dimension at least three. The two-dimensional case was
the remaining open dimension. The companion paper proves the following
strong form of undecidability.

There are a prime `p`, a fixed family `G` of 5,798 distinct nonsingular
integer `2 × 2` matrices with determinant `p` or `-p`, and a fixed rational
line `L` such that no algorithm decides mortality of `G ∪ {R}` when the input
is a nonzero rank-one integer matrix `R` with image `L`. Only the kernel of
`R` varies with the input.

In the formalization, `p = 51859`, `G` is
`Mortality.Compiler.FixedAllocation.listedMatrices`, and the varying matrix
is `Mortality.PaperTheorem.variableMatrix`.

## Proof outline

The reduction has four main layers.

1. **A fixed universal source.** A kernel-checked fixed universal Turing
   machine is compiled through fixed register- and counter-machine models.
   The input changes the initial numerical data, not the program.

2. **A reversed one-counter program.** Two counters are stored as prime
   exponents in one integer. A cleanup routine gives all halting runs one
   common endpoint, and reversing the program turns that endpoint into a
   fixed source configuration.

3. **Self-checking projective simulation.** A configuration is encoded by a
   rational line in `ℚ²`. Integer `2 × 2` matrices read a periodic base-`p`
   code one digit at a time. A wrong phase or digit introduces a factor of
   `p` into the denominator. Every later nonsingular generator preserves
   that error, so an arbitrary matrix word can connect two configuration
   codes only by following a valid program run. Separate instruction
   modules implement increment, residue tests, division, and the two
   contraction operations.

4. **Rank-one conversion.** A rank-one matrix has the fixed source line as
   its image and the input-dependent target line as its kernel. A
   nonsingular word reaches the target line exactly when a rank-one sandwich
   is zero. This converts projective reachability into mortality without
   assuming that a mortality word uses the rank-one matrix only twice.

The concrete universal source contributes 5,798 distinct nonsingular
generators. The rank-one conversion adds one more matrix. The reduction from
the ordinary halting problem to the resulting family is effective.

## What Lean checks

The development checks the complete chain used by the paper:

- the fixed universal source and each machine compiler;
- the arithmetic construction that supplies the fixed numerical program,
  including the required prime-system existence theorem;
- the forward simulation of every instruction module;
- the converse for unrestricted words over the full 5,798-generator
  alphabet, including wrong guesses and cross-module interleavings;
- the passage from rational projective codes to integer matrices;
- the rank-one conversion for arbitrary mixed mortality words;
- primality of `51859`, determinants `±51859`, nonsingularity, pairwise
  distinctness, and the exact counts 5,798 and 5,799;
- the fixed image line and rank-one property of the variable matrix;
- primitive recursiveness of the input-to-matrix map; and
- a many-one reduction from the ordinary halting problem, followed by the
  matrix-input undecidability theorem.

The analytic source construction derives the required prime system from a
formal Mertens estimate and Chebyshev bounds. No unformalized short-interval
prime assertion is assumed.

The most direct endpoints are:

| Lean theorem | Role |
| --- | --- |
| `Mortality.PaperTheorem.paper_result` | Bundles the claims corresponding to the paper's main theorem and fixed-cardinality corollary. |
| `Mortality.PaperTheorem.no_computable_matrix_decider` | States undecidability with the rank-one integer matrix itself as input. |
| `Mortality.PaperTheorem.variableMatrix_primrec` | Proves that the paper's input-to-matrix map is primitive recursive. |
| `Mortality.Compiler.GlobalConverse.projectivelyReachable_iff_u2Halts` | Gives the unrestricted-word equivalence for the fixed projective compiler. |
| `Mortality.Main.mortalityFamily_iff_u2Halts` | Converts the fixed-source reachability instance into a 5,799-matrix mortality instance. |
| `Mortality.SourceMachine.KorecPrimeSystem.existsForEverySpan` | Supplies the analytic prime-system construction. |
| `Mortality.SourceMachine.LeanWangMortality.mortality_iff_evalDom_unconditional` | Gives the unconditional semantic reduction from the ordinary halting problem. |

## Repository structure

- `Mortality/PaperTheorem.lean`: paper-facing statement and exact input
  interface;
- `Mortality/SourceMachine/`: the fixed universal source, machine compilers,
  arithmetic program construction, and computability reduction;
- `Mortality/OneCounter/`: the one-counter simulation, cleanup, and reversal;
- `Mortality/Compiler/`: periodic codes, instruction modules, phase guards,
  forward simulations, and unrestricted-word converses;
- `Mortality/Main.lean`: the integer matrix family and rank-one reduction;
- `Mortality.lean`: umbrella import;
- `AxiomAudit.lean`: reproducible axiom reports for the principal endpoints.

## Building

The repository pins Lean and every dependency. A fresh clone requires Git,
an `elan` installation, network access for the pinned dependencies, and
enough disk space for Mathlib and the companion developments.

```sh
git clone https://github.com/j49liu/matrix_mortality_lean.git
cd matrix_mortality_lean
lake build
```

The pinned environment is:

- Lean `4.31.0`;
- Mathlib commit `db127794c79fdeb86f6b0cf6ff2c804026fbaff1`;
- `edemaine/lean-wang` commit
  `a6935becf8bdefb026e83b682e2dde620839284c`; and
- `PrimeNumberTheoremAnd` commit
  `fde9497b2934b0df85407cbf1cf4860195c404c4`.

The project enables `warningAsError` for its own source. Warnings printed
while replaying pinned dependencies are upstream warnings.

## Auditing

Run the full build and principal axiom reports with:

```sh
lake build
lake env lean AxiomAudit.lean
rg -n '\bsorry\b|\badmit\b|^[[:space:]]*axiom[[:space:]]' \
  Mortality Mortality.lean
```

The placeholder scan is empty. The principal endpoints use only Lean's
standard logical principles `propext`, `Classical.choice`, and
`Quot.sound`; the project declares no additional axiom.

Lean checks the formal statements against the pinned dependencies. As with
any formalization, the correspondence between those statements and the
mathematical definitions in the paper must also be reviewed. The
paper-facing theorem is included to make that comparison explicit and
auditable.
