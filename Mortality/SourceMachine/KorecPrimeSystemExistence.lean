import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Combinatorics.Pigeonhole
import Mortality.SourceMachine.KorecPrimeSystem
import PrimeNumberTheoremAnd.IEANTN.Mertens

/-!
# Existence of Korec prime systems

This file proves the analytic existence statement isolated in
`KorecPrimeSystem.ExistsForEverySpan`.  The construction uses only Mertens'
estimate for the sum of reciprocal primes and Chebyshev's elementary bounds
for the prime-counting function.  In particular, it does not use a theorem
about primes in every short interval.  A pigeonhole argument finds one
prime-rich short interval inside a much longer interval.
-/

namespace Mortality.SourceMachine.KorecPrimeSystem

open Filter Finset Real
open scoped BigOperators Topology

noncomputable section

/-- The reciprocal sum over primes in the natural interval `(lower, upper]`. -/
def primeReciprocalInterval (lower upper : Nat) : Real :=
  ∑ p ∈ Finset.Ioc lower upper with p.Prime, (1 : Real) / p

private lemma pow_four_tendsto :
    Tendsto (fun t : Nat => (t : Real) ^ 4) atTop atTop := by
  have h : Tendsto (fun t : Nat => (t : Real)) atTop atTop :=
    tendsto_natCast_atTop_atTop
  apply Filter.tendsto_atTop_mono' atTop _ h
  filter_upwards [eventually_ge_atTop 1] with t ht
  have htReal : (1 : Real) ≤ t := by exact_mod_cast ht
  calc
    (t : Real) ≤ (t : Real) ^ 2 := by nlinarith [sq_nonneg ((t : Real) - 1)]
    _ ≤ ((t : Real) ^ 2) ^ 2 := by
      have : (1 : Real) ≤ (t : Real) ^ 2 := by
        nlinarith [mul_nonneg (sub_nonneg.mpr htReal)
          (show (0 : Real) ≤ (t : Real) + 1 by positivity)]
      nlinarith [sq_nonneg ((t : Real) ^ 2 - 1)]
    _ = (t : Real) ^ 4 := by ring

private lemma pow_six_tendsto :
    Tendsto (fun t : Nat => (t : Real) ^ 6) atTop atTop := by
  have h : Tendsto (fun t : Nat => (t : Real)) atTop atTop :=
    tendsto_natCast_atTop_atTop
  apply Filter.tendsto_atTop_mono' atTop _ h
  filter_upwards [eventually_ge_atTop 1] with t ht
  have htReal : (1 : Real) ≤ t := by exact_mod_cast ht
  calc
    (t : Real) ≤ (t : Real) ^ 2 := by nlinarith [sq_nonneg ((t : Real) - 1)]
    _ ≤ ((t : Real) ^ 2) ^ 2 := by
      have : (1 : Real) ≤ (t : Real) ^ 2 := by
        nlinarith [mul_nonneg (sub_nonneg.mpr htReal)
          (show (0 : Real) ≤ (t : Real) + 1 by positivity)]
      nlinarith [sq_nonneg ((t : Real) ^ 2 - 1)]
    _ ≤ (((t : Real) ^ 2) ^ 2) * (t : Real) ^ 2 := by
      have : (1 : Real) ≤ (t : Real) ^ 2 := by
        nlinarith [mul_nonneg (sub_nonneg.mpr htReal)
          (show (0 : Real) ≤ (t : Real) + 1 by positivity)]
      nlinarith [show 0 ≤ ((t : Real) ^ 2) ^ 2 by positivity]
    _ = (t : Real) ^ 6 := by ring

private lemma mertens_error_pow_four_tendsto :
    Tendsto (fun t : Nat => Mertens.E₂p ((t : Real) ^ 4)) atTop (𝓝 0) :=
  (Asymptotics.isLittleO_one_iff Real).mp Mertens.E₂p.bound' |>.comp
    pow_four_tendsto

private lemma mertens_error_pow_six_tendsto :
    Tendsto (fun t : Nat => Mertens.E₂p ((t : Real) ^ 6)) atTop (𝓝 0) :=
  (Asymptotics.isLittleO_one_iff Real).mp Mertens.E₂p.bound' |>.comp
    pow_six_tendsto

private lemma primeReciprocalInterval_eq_sub (lower upper : Nat)
    (h : lower ≤ upper) :
    primeReciprocalInterval lower upper =
      (∑ p ∈ Finset.Ioc 0 upper with p.Prime, (1 : Real) / p) -
        ∑ p ∈ Finset.Ioc 0 lower with p.Prime, (1 : Real) / p := by
  have hzero : 0 ≤ lower := Nat.zero_le lower
  have hunion := Finset.Ioc_union_Ioc_eq_Ioc hzero h
  have hdisjoint : Disjoint (Finset.Ioc 0 lower) (Finset.Ioc lower upper) :=
    Finset.Ioc_disjoint_Ioc_of_le le_rfl
  have hfiltered :
      Disjoint ((Finset.Ioc 0 lower).filter Nat.Prime)
        ((Finset.Ioc lower upper).filter Nat.Prime) :=
    hdisjoint.mono (Finset.filter_subset _ _) (Finset.filter_subset _ _)
  have hunionFiltered :
      (Finset.Ioc 0 lower).filter Nat.Prime ∪
          (Finset.Ioc lower upper).filter Nat.Prime =
        (Finset.Ioc 0 upper).filter Nat.Prime := by
    rw [← Finset.filter_union, hunion]
  have hsum :
      (∑ p ∈ Finset.Ioc 0 upper with p.Prime, (1 : Real) / p) =
        (∑ p ∈ Finset.Ioc 0 lower with p.Prime, (1 : Real) / p) +
          ∑ p ∈ Finset.Ioc lower upper with p.Prime, (1 : Real) / p := by
    rw [← hunionFiltered, Finset.sum_union hfiltered]
  rw [primeReciprocalInterval]
  linarith

/-- Mertens' estimate on the power interval needed by the construction. -/
theorem primeReciprocalInterval_pow_tendsto :
    Tendsto (fun t : Nat => primeReciprocalInterval (t ^ 4) (t ^ 6))
      atTop (𝓝 (Real.log (3 / 2))) := by
  have herr := mertens_error_pow_six_tendsto.sub mertens_error_pow_four_tendsto
  have hlim : Tendsto
      (fun t : Nat => Real.log (3 / 2) +
        (Mertens.E₂p ((t : Real) ^ 6) - Mertens.E₂p ((t : Real) ^ 4)))
      atTop (𝓝 (Real.log (3 / 2) + (0 - 0))) :=
    (tendsto_const_nhds : Tendsto (fun _ : Nat => Real.log (3 / 2))
      atTop (𝓝 (Real.log (3 / 2)))).add herr
  have heq :
      (fun t : Nat => Real.log (3 / 2) +
        (Mertens.E₂p ((t : Real) ^ 6) - Mertens.E₂p ((t : Real) ^ 4))) =ᶠ[atTop]
      (fun t : Nat => primeReciprocalInterval (t ^ 4) (t ^ 6)) := by
    filter_upwards [eventually_ge_atTop 2] with t ht
    rw [primeReciprocalInterval_eq_sub (t ^ 4) (t ^ 6)
      (Nat.pow_le_pow_right (by omega) (by norm_num))]
    have hsix := Mertens.sum_prime_div_eq ((t ^ 6 : Nat) : Real)
    have hfour := Mertens.sum_prime_div_eq ((t ^ 4 : Nat) : Real)
    simp only [Nat.floor_natCast] at hsix hfour
    rw [hsix, hfour]
    simp only [Nat.cast_pow]
    have htReal : (1 : Real) < t := by exact_mod_cast ht
    have hlogNe : Real.log (t : Real) ≠ 0 := (Real.log_pos htReal).ne'
    rw [Real.log_pow, Real.log_pow]
    norm_num only [Nat.cast_ofNat]
    rw [Real.log_mul (by norm_num : (6 : Real) ≠ 0) hlogNe,
      Real.log_mul (by norm_num : (4 : Real) ≠ 0) hlogNe]
    have hratio : Real.log 6 - Real.log 4 = Real.log (3 / 2) := by
      rw [← Real.log_div (by norm_num : (6 : Real) ≠ 0)
        (by norm_num : (4 : Real) ≠ 0)]
      norm_num
    rw [← hratio]
    ring
  simpa using hlim.congr' heq

/-- Eventually the primes in `(t^4,t^6]` have reciprocal mass greater than
`2/5`.  The strict margin follows from
`2/5 < log(3/2)`. -/
theorem eventually_two_fifths_lt_primeReciprocalInterval :
    ∀ᶠ t : Nat in atTop,
      (2 : Real) / 5 < primeReciprocalInterval (t ^ 4) (t ^ 6) := by
  apply (primeReciprocalInterval_pow_tendsto.eventually
    (Ioi_mem_nhds (show (2 : Real) / 5 < Real.log (3 / 2) by
      have h := Real.lt_log_one_add_of_pos (show (0 : Real) < 1 / 2 by norm_num)
      norm_num at h ⊢
      exact h)))

/-- The primes in the natural interval `(lower, upper]`. -/
def primesInInterval (lower upper : Nat) : Finset Nat :=
  (Finset.Ioc lower upper).filter Nat.Prime

@[simp] theorem mem_primesInInterval {lower upper p : Nat} :
    p ∈ primesInInterval lower upper ↔ lower < p ∧ p ≤ upper ∧ p.Prime := by
  simp [primesInInterval, and_assoc]

private lemma card_primesTo (n : Nat) :
    ((Finset.Ioc 0 n).filter Nat.Prime).card = n.primeCounting := by
  rw [← Nat.primesLE_card_eq_primeCounting]
  congr 1
  ext p
  simp only [Finset.mem_filter, Finset.mem_Ioc, Nat.mem_primesLE]
  constructor
  · rintro ⟨⟨_, hpn⟩, hp⟩
    exact ⟨hpn, hp⟩
  · rintro ⟨hpn, hp⟩
    exact ⟨⟨hp.pos, hpn⟩, hp⟩

theorem card_primesInInterval_eq_sub (lower upper : Nat) (h : lower ≤ upper) :
    (primesInInterval lower upper).card =
      upper.primeCounting - lower.primeCounting := by
  have hunion := Finset.Ioc_union_Ioc_eq_Ioc (Nat.zero_le lower) h
  have hdisjoint : Disjoint (Finset.Ioc 0 lower) (Finset.Ioc lower upper) :=
    Finset.Ioc_disjoint_Ioc_of_le le_rfl
  have hfiltered :
      Disjoint ((Finset.Ioc 0 lower).filter Nat.Prime)
        ((Finset.Ioc lower upper).filter Nat.Prime) :=
    hdisjoint.mono (Finset.filter_subset _ _) (Finset.filter_subset _ _)
  have hunionFiltered :
      (Finset.Ioc 0 lower).filter Nat.Prime ∪
          (Finset.Ioc lower upper).filter Nat.Prime =
        (Finset.Ioc 0 upper).filter Nat.Prime := by
    rw [← Finset.filter_union, hunion]
  have hcard := Finset.card_union_of_disjoint hfiltered
  rw [hunionFiltered, card_primesTo, card_primesTo] at hcard
  rw [primesInInterval]
  omega

/-- A quantitative Chebyshev bound convenient for the block argument.  The
constant `20` is deliberately loose. -/
theorem primeIntervalCard_real_lower {n : Nat} (hn : 101 ≤ n) :
    (20 : Real) * n / Real.log n ≤ (primesInInterval n (100 * n)).card := by
  have hnPos : 0 < n := by omega
  have hnReal : (1 : Real) < n := by exact_mod_cast (show 1 < n by omega)
  have hlogPos : 0 < Real.log (n : Real) := Real.log_pos hnReal
  have hlog100nPos : 0 < Real.log ((100 * n : Nat) : Real) := by
    exact Real.log_pos (by exact_mod_cast (show 1 < 100 * n by omega))
  have hlargeSquareNat : 100 * n + 1 ≤ n ^ 2 := by nlinarith
  have hlargeSquare : (100 : Real) * n + 1 ≤ (n : Real) ^ 2 := by
    exact_mod_cast hlargeSquareNat
  have hlogError : Real.log ((100 : Real) * n + 1) ≤ 2 * Real.log n := by
    calc
      Real.log ((100 : Real) * n + 1) ≤ Real.log ((n : Real) ^ 2) :=
        Real.log_le_log (by positivity) hlargeSquare
      _ = 2 * Real.log n := by rw [Real.log_pow]; norm_num
  have hlargeProductNat : 100 * n ≤ n ^ 2 := by nlinarith
  have hlargeProduct : (100 : Real) * n ≤ (n : Real) ^ 2 := by
    exact_mod_cast hlargeProductNat
  have hlogDenom : Real.log ((100 * n : Nat) : Real) ≤ 2 * Real.log n := by
    calc
      Real.log ((100 * n : Nat) : Real) = Real.log ((100 : Real) * n) := by norm_num
      _ ≤ Real.log ((n : Real) ^ 2) := Real.log_le_log (by positivity) hlargeProduct
      _ = 2 * Real.log n := by rw [Real.log_pow]; norm_num
  have hlogTwo : (2 : Real) / 3 < Real.log 2 :=
    (by norm_num : (2 : Real) / 3 < 0.6931471803).trans Real.log_two_gt_d9
  have hlogSelf : Real.log (n : Real) ≤ n :=
    (Real.log_le_sub_one_of_pos (by positivity)).trans (by linarith)
  have hnumerator :
      (64 : Real) * n ≤
        ((100 * n : Nat) : Real) * Real.log 2 -
          Real.log (((100 * n : Nat) : Real) + 1) := by
    norm_num only [Nat.cast_mul, Nat.cast_ofNat]
    nlinarith [mul_lt_mul_of_pos_right hlogTwo (show (0 : Real) < n by positivity)]
  have hlowerRatio :
      (32 : Real) * n / Real.log n ≤
        (((100 * n : Nat) : Real) * Real.log 2 -
          Real.log (((100 * n : Nat) : Real) + 1)) /
            Real.log ((100 * n : Nat) : Real) := by
    rw [div_le_div_iff₀ hlogPos hlog100nPos]
    nlinarith [mul_nonneg (show (0 : Real) ≤ 2 * Real.log n -
      Real.log ((100 * n : Nat) : Real) by linarith)
      (show (0 : Real) ≤ 32 * n by positivity),
      mul_nonneg (show (0 : Real) ≤
        ((100 * n : Nat) : Real) * Real.log 2 -
          Real.log (((100 * n : Nat) : Real) + 1) - 64 * n by linarith)
        hlogPos.le]
  have hlowerCount :
      (32 : Real) * n / Real.log n ≤ ((100 * n).primeCounting : Real) :=
    hlowerRatio.trans (Chebyshev.pi_ge (100 * n))
  have hupperRaw := Chebyshev.pi_le_log4_mul_div (x := (n : Real)) hnReal
  simp only [Nat.floor_natCast] at hupperRaw
  have hlogTwoUpper : Real.log 2 < 1 := by
    nlinarith [Real.log_lt_sub_one_of_pos (show (0 : Real) < 2 by norm_num)
      (by norm_num : (2 : Real) ≠ 1)]
  have hlogFour : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4 : Real) = 2 ^ 2 by norm_num, Real.log_pow]
    norm_num
  have hsqrtPos : 0 < Real.sqrt (n : Real) := Real.sqrt_pos.2 (by positivity)
  have hlogSqrtPos : 0 < Real.log (Real.sqrt (n : Real)) := by
    rw [Real.log_sqrt (by positivity)]
    linarith
  have hfirstUpper :
      Real.log 4 * (n : Real) / Real.log (Real.sqrt n) ≤
        (4 : Real) * n / Real.log n := by
    rw [Real.log_sqrt (by positivity)]
    rw [div_le_div_iff₀ (by positivity : (0 : Real) < Real.log n / 2) hlogPos]
    rw [hlogFour]
    nlinarith [mul_pos (show (0 : Real) < n by positivity) hlogPos]
  have hlogLeTwoSqrt : Real.log (n : Real) ≤ 2 * Real.sqrt n := by
    have h := Real.log_le_rpow_div (show (0 : Real) ≤ n by positivity)
      (show (0 : Real) < 1 / 2 by norm_num)
    rw [← Real.sqrt_eq_rpow] at h
    calc
      Real.log (n : Real) ≤ Real.sqrt n / (1 / 2) := h
      _ = 2 * Real.sqrt n := by ring
  have hsqrtUpper : Real.sqrt (n : Real) ≤
      (2 : Real) * n / Real.log n := by
    rw [le_div_iff₀ hlogPos]
    nlinarith [Real.sq_sqrt (show (0 : Real) ≤ n by positivity)]
  have hupperCount : (n.primeCounting : Real) ≤
      (6 : Real) * n / Real.log n := by
    calc
      (n.primeCounting : Real) ≤
          Real.log 4 * n / Real.log (Real.sqrt n) + Real.sqrt n := hupperRaw
      _ ≤ (4 : Real) * n / Real.log n + (2 : Real) * n / Real.log n :=
        add_le_add hfirstUpper hsqrtUpper
      _ = (6 : Real) * n / Real.log n := by ring
  have hcountMono : n.primeCounting ≤ (100 * n).primeCounting :=
    Nat.monotone_primeCounting (by omega)
  have hratioNonneg : (0 : Real) ≤ (n : Real) / Real.log n :=
    (div_pos (show (0 : Real) < n by positivity) hlogPos).le
  have hgap : (20 : Real) * n / Real.log n ≤
      ((100 * n).primeCounting : Real) - (n.primeCounting : Real) := by
    calc
      (20 : Real) * n / Real.log n = 20 * ((n : Real) / Real.log n) := by ring
      _ ≤ 26 * ((n : Real) / Real.log n) :=
        mul_le_mul_of_nonneg_right (by norm_num) hratioNonneg
      _ = (32 : Real) * n / Real.log n -
          (6 : Real) * n / Real.log n := by ring
      _ ≤ ((100 * n).primeCounting : Real) - (n.primeCounting : Real) :=
        sub_le_sub hlowerCount hupperCount
  rw [card_primesInInterval_eq_sub n (100 * n) (by omega),
    Nat.cast_sub hcountMono]
  exact hgap

/-- Left endpoint of the long interval used for candidate primes. -/
def scaleStart (t : Nat) : Nat := 100 * t ^ 6

/-- Width of each candidate block. -/
def blockWidth (t : Nat) : Nat := t ^ 3

/-- Number of blocks partitioning `(scaleStart t, 100 * scaleStart t]`. -/
def blockCount (t : Nat) : Nat := 9900 * t ^ 3

/-- Left endpoint of block `i`. -/
def blockLeft (t i : Nat) : Nat := scaleStart t + i * blockWidth t

@[simp] theorem blockLeft_zero (t : Nat) : blockLeft t 0 = scaleStart t := by
  simp [blockLeft]

theorem block_partition_endpoint (t : Nat) :
    blockLeft t (blockCount t) = 100 * scaleStart t := by
  simp [blockLeft, blockCount, blockWidth, scaleStart]
  ring

theorem scaleStart_le_blockLeft (t i : Nat) :
    scaleStart t ≤ blockLeft t i := by
  simp [blockLeft]

theorem blockLeft_succ (t i : Nat) :
    blockLeft t (i + 1) = blockLeft t i + blockWidth t := by
  simp [blockLeft]
  ring

theorem blockLeft_mono (t : Nat) {i j : Nat} (indexOrder : i ≤ j) :
    blockLeft t i ≤ blockLeft t j := by
  simp only [blockLeft]
  exact Nat.add_le_add_left (Nat.mul_le_mul_right _ indexOrder) _

theorem blockLeft_lt_partition_endpoint {t i : Nat}
    (indexBound : i < blockCount t) (widthPositive : 0 < blockWidth t) :
    blockLeft t i < blockLeft t (blockCount t) := by
  simp only [blockLeft]
  exact Nat.add_lt_add_left
    (Nat.mul_lt_mul_of_pos_right indexBound widthPositive) _

/-- The deliberately generous scale threshold simultaneously supplies all
elementary polynomial inequalities used below. -/
private theorem construction_numeric {k t : Nat}
    (large : 100000 * (k + 1) ≤ t) :
    40 ≤ t ∧
    t ^ 3 < 100 * t ^ 6 ∧
    10000 * t ^ 6 < (t ^ 4) ^ 2 ∧
    4 * (10000 * t ^ 2) + k + 2 ≤ (100 * t ^ 6) / 3 ∧
    3 * (10000 * t ^ 2) + 3 * k + 8 + t ^ 3 < t ^ 4 := by
  have ht : 100000 ≤ t := by omega
  have htPos : 0 < t := by omega
  have hk : k ≤ t := by omega
  have ht2Pos : 0 < t ^ 2 := Nat.pow_pos htPos
  have ht6Pos : 0 < t ^ 6 := Nat.pow_pos htPos
  have hpow36 : t ^ 3 ≤ t ^ 6 :=
    Nat.pow_le_pow_right (show 0 < t by omega) (by norm_num)
  have hwidth : t ^ 3 < 100 * t ^ 6 := by nlinarith
  have ht2Large : 10000 < t ^ 2 := by nlinarith
  have hseparatedRaw := Nat.mul_lt_mul_of_pos_right ht2Large ht6Pos
  have hseparated : 10000 * t ^ 6 < (t ^ 4) ^ 2 := by
    calc
      10000 * t ^ 6 < t ^ 2 * t ^ 6 := by
        simpa [Nat.mul_comm] using hseparatedRaw
      _ = (t ^ 4) ^ 2 := by ring
  have hk2 : k + 2 ≤ t ^ 2 := by nlinarith
  have hcoefficient : 120003 ≤ 100 * t ^ 4 := by
    have htPow : t ≤ t ^ 4 := by
      simpa using Nat.pow_le_pow_right htPos (by norm_num : 1 ≤ 4)
    omega
  have hscaled := Nat.mul_le_mul_right (t ^ 2) hcoefficient
  have hcapMul : 3 * (4 * (10000 * t ^ 2) + k + 2) ≤
      100 * t ^ 6 := by
    calc
      3 * (4 * (10000 * t ^ 2) + k + 2) ≤ 120003 * t ^ 2 := by
        nlinarith
      _ ≤ (100 * t ^ 4) * t ^ 2 := hscaled
      _ = 100 * t ^ 6 := by ring
  have hcap : 4 * (10000 * t ^ 2) + k + 2 ≤
      (100 * t ^ 6) / 3 := by
    exact (Nat.le_div_iff_mul_le (by norm_num : 0 < 3)).2 (by
      simpa [Nat.mul_comm] using hcapMul)
  have hsmall : 3 * k + 8 ≤ t ^ 2 := by nlinarith
  have hcoefficientLt : t + 30001 < t ^ 2 := by nlinarith
  have hscaledLt := Nat.mul_lt_mul_of_pos_right hcoefficientLt ht2Pos
  have henvelope :
      3 * (10000 * t ^ 2) + 3 * k + 8 + t ^ 3 < t ^ 4 := by
    calc
      3 * (10000 * t ^ 2) + 3 * k + 8 + t ^ 3 ≤
          (t + 30001) * t ^ 2 := by
        nlinarith
      _ < t ^ 2 * t ^ 2 := hscaledLt
      _ = t ^ 4 := by ring
  exact ⟨by omega, hwidth, hseparated, hcap, henvelope⟩

/-- For any requested cardinality, the long Chebyshev interval eventually
contains enough primes to put that many in one of its `t^3`-wide blocks. -/
theorem eventually_block_capacity (k : Nat) :
    ∀ᶠ t : Nat in atTop,
      blockCount t * k ≤
        (primesInInterval (scaleStart t) (100 * scaleStart t)).card := by
  filter_upwards [eventually_ge_atTop (max 101 (100 * (k + 1)))] with t ht
  have ht101 : 101 ≤ t := le_trans (le_max_left _ _) ht
  have htk : 100 * (k + 1) ≤ t := le_trans (le_max_right _ _) ht
  have htPos : 0 < t := by omega
  have hstart101 : 101 ≤ scaleStart t := by
    have htPow : t ≤ t ^ 6 := by
      simpa using Nat.pow_le_pow_right htPos (by norm_num : 1 ≤ 6)
    simp only [scaleStart]
    omega
  have hcard := primeIntervalCard_real_lower hstart101
  have htReal : (0 : Real) < t := by exact_mod_cast htPos
  have htOne : (1 : Real) ≤ t := by exact_mod_cast (show 1 ≤ t by omega)
  have hstartCast : ((scaleStart t : Nat) : Real) = 100 * (t : Real) ^ 6 := by
    norm_num [scaleStart]
  have hstartPos : (0 : Real) < scaleStart t := by positivity
  have hlogStartPos : 0 < Real.log ((scaleStart t : Nat) : Real) := by
    apply Real.log_pos
    exact_mod_cast (show 1 < scaleStart t by omega)
  have hlogHundred : Real.log (100 : Real) ≤ 99 := by
    convert Real.log_le_sub_one_of_pos (show (0 : Real) < 100 by norm_num) using 1
    norm_num
  have hlogT : Real.log (t : Real) ≤ t :=
    (Real.log_le_sub_one_of_pos htReal).trans (by linarith)
  have hlogStart : Real.log ((scaleStart t : Nat) : Real) ≤ 7 * t := by
    rw [hstartCast, Real.log_mul (by norm_num) (pow_ne_zero 6 htReal.ne'), Real.log_pow]
    norm_num only [Nat.cast_ofNat]
    have ht99 : (99 : Real) ≤ t := by exact_mod_cast (show 99 ≤ t by omega)
    nlinarith
  have hkey : (69300 : Real) * k ≤ 2000 * (t : Real) ^ 2 := by
    have htkReal : (100 : Real) * (k + 1) ≤ t := by exact_mod_cast htk
    have hprod : 0 ≤ ((t : Real) - 100 * (k + 1)) *
        ((t : Real) + 100 * (k + 1)) :=
      mul_nonneg (sub_nonneg.mpr htkReal) (by positivity)
    nlinarith [sq_nonneg (k : Real)]
  have hdemandReal : ((blockCount t * k : Nat) : Real) ≤
      (20 : Real) * scaleStart t / Real.log (scaleStart t : Nat) := by
    rw [le_div_iff₀ hlogStartPos]
    calc
      ((blockCount t * k : Nat) : Real) * Real.log (scaleStart t : Nat) ≤
          ((blockCount t * k : Nat) : Real) * (7 * t) :=
        mul_le_mul_of_nonneg_left hlogStart (by positivity)
      _ = ((69300 : Real) * k) * (t : Real) ^ 4 := by
        simp [blockCount]
        ring
      _ ≤ (2000 * (t : Real) ^ 2) * (t : Real) ^ 4 :=
        mul_le_mul_of_nonneg_right hkey (by positivity)
      _ = (20 : Real) * scaleStart t := by
        rw [hstartCast]
        ring
  have hdemandCast : ((blockCount t * k : Nat) : Real) ≤
      ((primesInInterval (scaleStart t) (100 * scaleStart t)).card : Real) :=
    hdemandReal.trans hcard
  exact_mod_cast hdemandCast

/-- Some block of width `t^3` contains at least `k` primes, for all
sufficiently large `t`. -/
theorem eventually_prime_rich_block (k : Nat) :
    ∀ᶠ t : Nat in atTop, ∃ i < blockCount t,
      k ≤ (primesInInterval (blockLeft t i) (blockLeft t (i + 1))).card := by
  filter_upwards [eventually_block_capacity k,
    eventually_ge_atTop 1] with t hcapacity ht
  have hwidth : 0 < blockWidth t := by
    simp only [blockWidth]
    exact Nat.pow_pos (by omega)
  let source := primesInInterval (scaleStart t) (100 * scaleStart t)
  let bins := Finset.range (blockCount t)
  let index : Nat → Nat := fun p => (p - scaleStart t - 1) / blockWidth t
  have hblocksPos : 0 < blockCount t := by
    simp only [blockCount]
    positivity
  have hmaps : ∀ p ∈ source, index p ∈ bins := by
    intro p hp
    rw [mem_primesInInterval] at hp
    simp only [bins, Finset.mem_range]
    have : p - scaleStart t - 1 < blockCount t * blockWidth t := by
      have hproduct : blockCount t * blockWidth t = 99 * scaleStart t := by
        simp [blockCount, blockWidth, scaleStart]
        ring
      rw [hproduct]
      omega
    change (p - scaleStart t - 1) / blockWidth t < blockCount t
    exact (Nat.div_lt_iff_lt_mul hwidth).2 this
  have hbins : bins.Nonempty :=
    ⟨0, by exact Finset.mem_range.mpr hblocksPos⟩
  have hcapacity' : bins.card * k ≤ source.card := by
    simpa [bins, source] using hcapacity
  obtain ⟨i, hi, hik⟩ :=
    Finset.exists_le_card_fiber_of_mul_le_card_of_maps_to hmaps hbins hcapacity'
  refine ⟨i, by simpa [bins] using hi, hik.trans ?_⟩
  apply Finset.card_le_card
  intro p hp
  simp only [Finset.mem_filter] at hp
  have hpSource := hp.1
  have hpIndex := hp.2
  change (p - scaleStart t - 1) / blockWidth t = i at hpIndex
  rw [mem_primesInInterval] at hpSource ⊢
  have hlowerDiv : i * blockWidth t ≤ p - scaleStart t - 1 := by
    have := Nat.mul_div_le (p - scaleStart t - 1) (blockWidth t)
    rw [hpIndex] at this
    simpa [Nat.mul_comm] using this
  have hupperDiv : p - scaleStart t - 1 < (i + 1) * blockWidth t := by
    have := Nat.lt_mul_div_succ (p - scaleStart t - 1) hwidth
    rw [hpIndex] at this
    simpa [Nat.mul_comm] using this
  constructor
  · simp [blockLeft]
    omega
  constructor
  · simp [blockLeft]
    omega
  · exact hpSource.2.2

/-- The first multiple of `factor` strictly above `base`. -/
def nextMultiple (base factor : Nat) : Nat := (base / factor + 1) * factor

theorem lt_nextMultiple {base factor : Nat} (factorPositive : 0 < factor) :
    base < nextMultiple base factor := by
  simpa [nextMultiple, Nat.mul_comm] using Nat.lt_mul_div_succ base factorPositive

theorem nextMultiple_le_of_div_ne {base bound factor : Nat}
    (baseBound : base ≤ bound)
    (changes : base / factor ≠ bound / factor) :
    nextMultiple base factor ≤ bound := by
  have hdiv : base / factor < bound / factor :=
    lt_of_le_of_ne (Nat.div_le_div_right baseBound) changes
  exact Nat.mul_le_of_le_div factor _ _ (Nat.succ_le_iff.mpr hdiv)

/-- Lower primes whose quotient changes between the two endpoints. -/
def badLowerPrimes (t base bound : Nat) : Finset Nat :=
  (primesInInterval (t ^ 4) (t ^ 6)).filter
    fun p => base / p ≠ bound / p

/-- Lower primes whose quotient is stable between the two endpoints. -/
def stableLowerPrimes (t base bound : Nat) : Finset Nat :=
  (primesInInterval (t ^ 4) (t ^ 6)).filter
    fun p => base / p = bound / p

theorem badLowerPrimes_card_le {t base bound : Nat}
    (baseBound : base ≤ bound) (boundSeparated : bound < (t ^ 4) ^ 2) :
    (badLowerPrimes t base bound).card ≤ bound - base := by
  let bad := badLowerPrimes t base bound
  let image := bad.image (nextMultiple base)
  have hmaps : image ⊆ Finset.Ioc base bound := by
    intro m hm
    simp only [image, Finset.mem_image] at hm
    obtain ⟨p, hpBad, rfl⟩ := hm
    simp only [bad, badLowerPrimes, Finset.mem_filter] at hpBad
    rw [mem_primesInInterval] at hpBad
    exact Finset.mem_Ioc.mpr ⟨lt_nextMultiple hpBad.1.2.2.pos,
      nextMultiple_le_of_div_ne baseBound hpBad.2⟩
  have hinj : Set.InjOn (nextMultiple base) (bad : Set Nat) := by
    intro p hp q hq heq
    simp only [bad, badLowerPrimes, Finset.coe_filter, Set.mem_setOf_eq] at hp hq
    rw [mem_primesInInterval] at hp hq
    by_contra hpq
    have hcoprime : p.Coprime q := (Nat.coprime_primes hp.1.2.2 hq.1.2.2).mpr hpq
    have hpDvd : p ∣ nextMultiple base p := by
      simp [nextMultiple]
    have hqDvd : q ∣ nextMultiple base p := by
      rw [heq]
      simp [nextMultiple]
    have hpqDvd : p * q ∣ nextMultiple base p :=
      hcoprime.mul_dvd_of_dvd_of_dvd hpDvd hqDvd
    have hmPos : 0 < nextMultiple base p :=
      (lt_nextMultiple hp.1.2.2.pos).trans_le' (Nat.zero_le base)
    have hpqLe : p * q ≤ nextMultiple base p := Nat.le_of_dvd hmPos hpqDvd
    have hmLe : nextMultiple base p ≤ bound :=
      nextMultiple_le_of_div_ne baseBound hp.2
    have hleastPos : 0 < t ^ 4 := by
      by_contra h
      have hz : t ^ 4 = 0 := Nat.eq_zero_of_not_pos h
      simp [hz] at boundSeparated
    have hleastProduct : (t ^ 4) ^ 2 < p * q :=
      by
        simpa [pow_two] using
          (mul_lt_mul hp.1.1 hq.1.1.le hleastPos (Nat.zero_le p))
    omega
  have hcardImage : image.card = bad.card := by
    exact Finset.card_image_of_injOn hinj
  have := Finset.card_le_card hmaps
  rw [hcardImage, Nat.card_Ioc] at this
  exact this

theorem stable_bad_partition (t base bound : Nat) :
    stableLowerPrimes t base bound ∪ badLowerPrimes t base bound =
      primesInInterval (t ^ 4) (t ^ 6) := by
  ext p
  simp only [stableLowerPrimes, badLowerPrimes, Finset.mem_union, Finset.mem_filter]
  tauto

theorem stable_bad_disjoint (t base bound : Nat) :
    Disjoint (stableLowerPrimes t base bound) (badLowerPrimes t base bound) := by
  rw [Finset.disjoint_left]
  intro p hpStable hpBad
  simp only [stableLowerPrimes, Finset.mem_filter] at hpStable
  simp only [badLowerPrimes, Finset.mem_filter] at hpBad
  exact hpBad.2 hpStable.2

theorem primeReciprocalInterval_eq_stable_add_bad (t base bound : Nat) :
    primeReciprocalInterval (t ^ 4) (t ^ 6) =
      (∑ p ∈ stableLowerPrimes t base bound, (1 : Real) / p) +
        ∑ p ∈ badLowerPrimes t base bound, (1 : Real) / p := by
  have hsum := Finset.sum_union (stable_bad_disjoint t base bound)
    (f := fun p : Nat => (1 : Real) / p)
  rw [stable_bad_partition] at hsum
  simpa [primeReciprocalInterval, primesInInterval] using hsum

/-- Removing all lower primes whose quotient changes over the candidate block
costs at most the reciprocal of `t`. -/
theorem badLowerPrimes_reciprocal_le {t base bound : Nat}
    (ht : 0 < t) (baseBound : base ≤ bound)
    (widthBound : bound - base ≤ t ^ 3)
    (boundSeparated : bound < (t ^ 4) ^ 2) :
    (∑ p ∈ badLowerPrimes t base bound, (1 : Real) / p) ≤ 1 / t := by
  have hleastPosNat : 0 < t ^ 4 := Nat.pow_pos ht
  have hleastPos : (0 : Real) < ((t ^ 4 : Nat) : Real) := by
    exact_mod_cast hleastPosNat
  have hterm : ∀ p ∈ badLowerPrimes t base bound,
      (1 : Real) / p ≤ 1 / (t ^ 4 : Nat) := by
    intro p hp
    simp only [badLowerPrimes, Finset.mem_filter] at hp
    rw [mem_primesInInterval] at hp
    exact one_div_le_one_div_of_le hleastPos (by exact_mod_cast hp.1.1.le)
  have hcard := (badLowerPrimes_card_le baseBound boundSeparated).trans widthBound
  calc
    (∑ p ∈ badLowerPrimes t base bound, (1 : Real) / p) ≤
        ∑ _p ∈ badLowerPrimes t base bound, (1 : Real) / (t ^ 4 : Nat) := by
      exact Finset.sum_le_sum fun p hp => hterm p hp
    _ = ((badLowerPrimes t base bound).card : Real) / (t ^ 4 : Nat) := by
      simp [div_eq_mul_inv]
    _ ≤ ((t ^ 3 : Nat) : Real) / (t ^ 4 : Nat) := by
      exact div_le_div_of_nonneg_right (by exact_mod_cast hcard) hleastPos.le
    _ = (1 : Real) / t := by
      norm_num only [Nat.cast_pow]
      field_simp

/-- The stable lower primes retain reciprocal mass greater than `3/8`. -/
theorem three_eighths_lt_stable_reciprocal {t base bound : Nat}
    (ht : 40 ≤ t) (baseBound : base ≤ bound)
    (widthBound : bound - base ≤ t ^ 3)
    (boundSeparated : bound < (t ^ 4) ^ 2)
    (mass : (2 : Real) / 5 < primeReciprocalInterval (t ^ 4) (t ^ 6)) :
    (3 : Real) / 8 <
      ∑ p ∈ stableLowerPrimes t base bound, (1 : Real) / p := by
  have htPos : 0 < t := by omega
  have hbad := badLowerPrimes_reciprocal_le htPos baseBound widthBound boundSeparated
  have hinv : (1 : Real) / t ≤ 1 / 40 := by
    exact one_div_le_one_div_of_le (by norm_num) (by exact_mod_cast ht)
  rw [primeReciprocalInterval_eq_stable_add_bad t base bound] at mass
  linarith

/-- Quotient sum over a finite set of factors. -/
def quotientSum (factors : Finset Nat) (base : Nat) : Nat :=
  ∑ p ∈ factors, base / p

/-- A finite list whose total weight exceeds `cap` has a first element at
which its running sum exceeds `cap`.  The preceding prefix is still below
the cap. -/
private theorem exists_prefix_weight {α : Type*} (weight : α → Nat)
    (xs : List α) (cap : Nat)
    (totalLarge : cap < (xs.map weight).sum) :
    ∃ pre next suffix,
      xs = pre ++ next :: suffix ∧
      (pre.map weight).sum ≤ cap ∧
      cap < (pre.map weight).sum + weight next := by
  induction xs generalizing cap with
  | nil => simp at totalLarge
  | cons x xs inductionHypothesis =>
      by_cases headLarge : cap < weight x
      · exact ⟨[], x, xs, by simp, by simp, by simpa using headLarge⟩
      · have headSmall : weight x ≤ cap := Nat.le_of_not_gt headLarge
        have tailLarge : cap - weight x < (xs.map weight).sum := by
          simp only [List.map_cons, List.sum_cons] at totalLarge
          omega
        obtain ⟨pre, next, suffix, split, preSmall, crossing⟩ :=
          inductionHypothesis (cap - weight x) tailLarge
        refine ⟨x :: pre, next, suffix, ?_, ?_, ?_⟩
        · simp [split]
        · simp only [List.map_cons, List.sum_cons]
          omega
        · simp only [List.map_cons, List.sum_cons]
          omega

private theorem list_sum_le_length_mul (xs : List Nat) (bound : Nat)
    (termBound : ∀ x ∈ xs, x ≤ bound) :
    xs.sum ≤ xs.length * bound := by
  induction xs with
  | nil => simp
  | cons x xs inductionHypothesis =>
      have hx : x ≤ bound := termBound x (by simp)
      have htail : ∀ y ∈ xs, y ≤ bound := by
        intro y hy
        exact termBound y (by simp [hy])
      calc
        (x :: xs).sum = x + xs.sum := by simp
        _ ≤ bound + xs.length * bound :=
          Nat.add_le_add hx (inductionHypothesis htail)
        _ = (x :: xs).length * bound := by
          simp [Nat.add_mul, Nat.add_comm]

theorem quotientRank_sort_eq_quotientSum (factors : Finset Nat) (base : Nat) :
    quotientRank factors.sort base = quotientSum factors base := by
  rw [quotientRank, quotientSum]
  change
    (Multiset.map (fun p => base / p) (↑factors.sort : Multiset Nat)).sum =
      (factors.1.map fun p => base / p).sum
  rw [factors.sort_eq]

private theorem quotientRank_eq_of_pointwise (factors : List Nat)
    {left right : Nat}
    (equal : ∀ factor, factor ∈ factors → left / factor = right / factor) :
    quotientRank factors left = quotientRank factors right := by
  induction factors with
  | nil => rfl
  | cons factor factors inductionHypothesis =>
      rw [quotientRank_cons, quotientRank_cons,
        equal factor (by simp)]
      exact congrArg (fun value => right / factor + value)
        (inductionHypothesis fun other otherMem =>
          equal other (by simp [otherMem]))

private theorem quotientRank_eq_length_of_pointwise_one
    (factors : List Nat) (value : Nat)
    (equalOne : ∀ factor, factor ∈ factors → value / factor = 1) :
    quotientRank factors value = factors.length := by
  induction factors with
  | nil => rfl
  | cons factor factors inductionHypothesis =>
      rw [quotientRank_cons, equalOne factor (by simp)]
      rw [inductionHypothesis fun other otherMem =>
        equalOne other (by simp [otherMem])]
      simp [Nat.add_comm]

private theorem stable_quotient_le_scale {t base bound p : Nat}
    (baseUpper : base ≤ 10000 * t ^ 6)
    (stableMem : p ∈ stableLowerPrimes t base bound) :
    base / p ≤ 10000 * t ^ 2 := by
  simp only [stableLowerPrimes, Finset.mem_filter] at stableMem
  rw [mem_primesInInterval] at stableMem
  have pPositive : 0 < p := stableMem.1.2.2.pos
  apply Nat.div_le_of_le_mul
  calc
    base ≤ 10000 * t ^ 6 := baseUpper
    _ = (10000 * t ^ 2) * t ^ 4 := by ring
    _ ≤ (10000 * t ^ 2) * p :=
      Nat.mul_le_mul_left _ stableMem.1.1.le
    _ = p * (10000 * t ^ 2) := Nat.mul_comm _ _

private theorem quotient_term_real_lower {base p : Nat} (pPositive : 0 < p)
    (hundredMul : 100 * p ≤ base) :
    (99 : Real) / 100 * base / p ≤ (base / p : Nat) := by
  let q := base / p
  have hq : 100 ≤ q := (Nat.le_div_iff_mul_le pPositive).2 hundredMul
  have hnext : base < (q + 1) * p := by
    simpa [q, nextMultiple] using lt_nextMultiple (base := base) pPositive
  have hscaled : 99 * base ≤ 100 * q * p := by
    have hfirst : 99 * base ≤ 99 * ((q + 1) * p) :=
      Nat.mul_le_mul_left 99 hnext.le
    have hcoeff : 99 * (q + 1) ≤ 100 * q := by omega
    have hsecond : 99 * ((q + 1) * p) ≤ 100 * q * p := by
      nlinarith [Nat.mul_le_mul_right p hcoeff]
    exact hfirst.trans hsecond
  have hscaledReal : (99 : Real) * base ≤ 100 * q * p := by
    exact_mod_cast hscaled
  rw [div_le_iff₀ (show (0 : Real) < p by exact_mod_cast pPositive)]
  change (99 : Real) / 100 * base ≤ (q : Nat) * p
  nlinarith

/-- The stable lower primes contribute quotient rank greater than one third of
the base. -/
theorem base_lt_three_mul_stable_quotientSum {t base bound : Nat}
    (baseLarge : 100 * t ^ 6 ≤ base)
    (mass : (3 : Real) / 8 <
      ∑ p ∈ stableLowerPrimes t base bound, (1 : Real) / p) :
    base < 3 * quotientSum (stableLowerPrimes t base bound) base := by
  let stable := stableLowerPrimes t base bound
  have hterm : ∀ p ∈ stable,
      (99 : Real) / 100 * base / p ≤ (base / p : Nat) := by
    intro p hp
    simp only [stable, stableLowerPrimes, Finset.mem_filter] at hp
    rw [mem_primesInInterval] at hp
    apply quotient_term_real_lower hp.1.2.2.pos
    exact (Nat.mul_le_mul_left 100 hp.1.2.1).trans baseLarge
  have hsum : (99 : Real) / 100 * base *
      (∑ p ∈ stable, (1 : Real) / p) ≤
        (quotientSum stable base : Real) := by
    rw [quotientSum]
    push_cast
    calc
      (99 : Real) / 100 * base * (∑ p ∈ stable, (1 : Real) / p) =
          ∑ p ∈ stable, ((99 : Real) / 100 * base / p) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro p _
        ring
      _ ≤ ∑ p ∈ stable, ((base / p : Nat) : Real) :=
        Finset.sum_le_sum fun p hp => hterm p hp
  have hbaseNonneg : (0 : Real) ≤ base := by positivity
  have hbaseNatPos : 0 < base := by
    by_contra hbase
    have hbaseZero : base = 0 := Nat.eq_zero_of_not_pos hbase
    subst base
    have htZero : t = 0 := by
      by_contra htNe
      have htPow : 0 < t ^ 6 := Nat.pow_pos (Nat.pos_of_ne_zero htNe)
      omega
    subst t
    simp [stableLowerPrimes, primesInInterval] at mass
    norm_num at mass
  have hbasePos : (0 : Real) < base := by exact_mod_cast hbaseNatPos
  have hthird : (base : Real) / 3 < (quotientSum stable base : Real) := by
    calc
      (base : Real) / 3 < (99 : Real) / 100 * base * ((3 : Real) / 8) := by
        nlinarith
      _ < (99 : Real) / 100 * base *
          (∑ p ∈ stable, (1 : Real) / p) := by
        exact mul_lt_mul_of_pos_left mass (mul_pos (by norm_num) hbasePos)
      _ ≤ (quotientSum stable base : Real) := hsum
  have : (base : Real) < 3 * (quotientSum stable base : Real) := by linarith
  exact_mod_cast this

/-- Greedy truncation of the sorted stable primes.  The factor four in
`capRoom` ensures that the retained prefix contains at least four primes. -/
private theorem exists_long_stable_prefix {k t base bound : Nat}
    (baseUpper : base ≤ 10000 * t ^ 6)
    (capRoom : 4 * (10000 * t ^ 2) + k + 2 ≤ base / 3)
    (totalLarge : base <
      3 * quotientSum (stableLowerPrimes t base bound) base) :
    ∃ pre next suffix,
      (stableLowerPrimes t base bound).sort = pre ++ next :: suffix ∧
      3 < pre.length ∧
      (pre.map fun p => base / p).sum ≤ base / 3 - k - 2 ∧
      base / 3 - k - 2 <
        (pre.map fun p => base / p).sum + base / next := by
  let stable := stableLowerPrimes t base bound
  let available := stable.sort
  let cap := base / 3 - k - 2
  have thirdLarge : base / 3 < quotientSum stable base := by
    apply (Nat.div_lt_iff_lt_mul (by norm_num : 0 < 3)).2
    simpa [Nat.mul_comm] using totalLarge
  have capLarge : cap < (available.map fun p => base / p).sum := by
    have capLe : cap ≤ base / 3 := by simp only [cap]; omega
    rw [← quotientRank_sort_eq_quotientSum stable base] at thirdLarge
    exact capLe.trans_lt (by simpa [available, quotientRank] using thirdLarge)
  obtain ⟨pre, next, suffix, split, preSmall, crossing⟩ :=
    exists_prefix_weight (fun p => base / p) available cap capLarge
  have preMem : ∀ p ∈ pre, p ∈ stable := by
    intro p hp
    have : p ∈ available := by
      rw [split]
      simp [hp]
    simpa [available] using this
  have nextMem : next ∈ stable := by
    have : next ∈ available := by
      rw [split]
      simp
    simpa [available] using this
  have preTermBound : ∀ value ∈ pre.map (fun p => base / p),
      value ≤ 10000 * t ^ 2 := by
    intro value valueMem
    simp only [List.mem_map] at valueMem
    obtain ⟨p, hp, rfl⟩ := valueMem
    exact stable_quotient_le_scale baseUpper (preMem p hp)
  have preSumBound : (pre.map fun p => base / p).sum ≤
      pre.length * (10000 * t ^ 2) := by
    simpa using list_sum_le_length_mul
      (pre.map fun p => base / p) (10000 * t ^ 2) preTermBound
  have nextBound : base / next ≤ 10000 * t ^ 2 :=
    stable_quotient_le_scale baseUpper nextMem
  have preLong : 3 < pre.length := by
    by_contra short
    have lengthShort : pre.length ≤ 3 := by omega
    have sumShort : (pre.map fun p => base / p).sum ≤
        3 * (10000 * t ^ 2) :=
      preSumBound.trans (Nat.mul_le_mul_right _ lengthShort)
    have fourBelowCap : 4 * (10000 * t ^ 2) ≤ cap := by
      simp only [cap]
      omega
    omega
  exact ⟨pre, next, suffix, by simpa [available, stable] using split,
    preLong, by simpa [cap] using preSmall, by simpa [cap] using crossing⟩

/-- One sufficiently large prime-rich block produces a complete Korec
system. -/
private theorem system_nonempty_of_rich_block {span t i : Nat}
    (spanLarge : 2 < span)
    (scaleLarge : 100000 * ((span - 1) + 1) ≤ t)
    (indexBound : i < blockCount t)
    (rich : span - 1 ≤
      (primesInInterval (blockLeft t i) (blockLeft t (i + 1))).card)
    (mass : (2 : Real) / 5 <
      primeReciprocalInterval (t ^ 4) (t ^ 6)) :
    Nonempty (System span) := by
  let k := span - 1
  let base := blockLeft t i
  let bound := blockLeft t (i + 1)
  have kLength : k + 1 = span := by simp only [k]; omega
  obtain ⟨tForty, widthSmall, separatedScale, capScale, envelopeScale⟩ :=
    construction_numeric (k := k) scaleLarge
  have tPositive : 0 < t := by omega
  have widthPositive : 0 < blockWidth t := by
    simp only [blockWidth]
    exact Nat.pow_pos tPositive
  have baseBound : base < bound := by
    rw [show bound = base + blockWidth t by
      simp only [base, bound]; exact blockLeft_succ t i]
    omega
  have widthEq : bound - base = t ^ 3 := by
    rw [show bound = base + blockWidth t by
      simp only [base, bound]; exact blockLeft_succ t i]
    simp [blockWidth]
  have baseLarge : 100 * t ^ 6 ≤ base := by
    simpa [base, scaleStart] using scaleStart_le_blockLeft t i
  have baseLtEndpoint : base < blockLeft t (blockCount t) := by
    simpa [base] using blockLeft_lt_partition_endpoint indexBound widthPositive
  have baseUpper : base ≤ 10000 * t ^ 6 := by
    have : base < 100 * scaleStart t := by
      simpa [block_partition_endpoint] using baseLtEndpoint
    calc
      base ≤ 100 * scaleStart t := this.le
      _ = 10000 * t ^ 6 := by simp [scaleStart]; ring
  have boundLeEndpoint : bound ≤ blockLeft t (blockCount t) := by
    have successorBound : i + 1 ≤ blockCount t := by omega
    simpa [bound] using blockLeft_mono t successorBound
  have boundUpper : bound ≤ 10000 * t ^ 6 := by
    rw [block_partition_endpoint] at boundLeEndpoint
    calc
      bound ≤ 100 * scaleStart t := boundLeEndpoint
      _ = 10000 * t ^ 6 := by simp [scaleStart]; ring
  have boundSeparated : bound < (t ^ 4) ^ 2 :=
    boundUpper.trans_lt separatedScale
  have stableMass : (3 : Real) / 8 <
      ∑ p ∈ stableLowerPrimes t base bound, (1 : Real) / p :=
    three_eighths_lt_stable_reciprocal tForty baseBound.le
      widthEq.le boundSeparated mass
  have totalLarge : base <
      3 * quotientSum (stableLowerPrimes t base bound) base :=
    base_lt_three_mul_stable_quotientSum baseLarge stableMass
  have capRoom : 4 * (10000 * t ^ 2) + k + 2 ≤ base / 3 := by
    have startDiv : (100 * t ^ 6) / 3 ≤ base / 3 :=
      Nat.div_le_div_right baseLarge
    exact capScale.trans startDiv
  obtain ⟨pre, next, suffix, stableSplit, preLong, preSmall, crossing⟩ :=
    exists_long_stable_prefix baseUpper capRoom totalLarge
  let candidatePool := primesInInterval base bound
  obtain ⟨candidateSet, candidateSubset, candidateCard⟩ :=
    Finset.exists_subset_card_eq (s := candidatePool) (n := k)
      (by simpa [candidatePool, base, bound, k] using rich)
  let candidates := candidateSet.sort
  have candidateLength : candidates.length = k := by
    simpa [candidates] using candidateCard
  have candidateMem : ∀ p, p ∈ candidates → p ∈ candidatePool := by
    intro p hp
    apply candidateSubset
    simpa [candidates] using hp
  have candidateOrdered : candidates.Pairwise (· < ·) := by
    simpa [candidates] using candidateSet.sortedLT_sort.pairwise
  have preMem : ∀ p, p ∈ pre → p ∈ stableLowerPrimes t base bound := by
    intro p hp
    have : p ∈ (stableLowerPrimes t base bound).sort := by
      rw [stableSplit]
      simp [hp]
    simpa using this
  have nextMem : next ∈ stableLowerPrimes t base bound := by
    have : next ∈ (stableLowerPrimes t base bound).sort := by
      rw [stableSplit]
      simp
    simpa using this
  have preOrdered : pre.Pairwise (· < ·) := by
    have ordered := (stableLowerPrimes t base bound).sortedLT_sort.pairwise
    rw [stableSplit, List.pairwise_append] at ordered
    exact ordered.1
  have preOrderedLE : pre.Pairwise (· ≤ ·) :=
    preOrdered.imp Nat.le_of_lt
  have preNonempty : pre ≠ [] := by
    intro empty
    rw [empty] at preLong
    simp at preLong
  let least := pre.head!
  have leastMemPre : least ∈ pre := by
    exact List.head!_mem_self preNonempty
  have leastLower : t ^ 4 < least := by
    have member := preMem least leastMemPre
    simp only [stableLowerPrimes, Finset.mem_filter] at member
    exact (mem_primesInInterval.mp member.1).1
  have leastUpper : least ≤ t ^ 6 := by
    have member := preMem least leastMemPre
    simp only [stableLowerPrimes, Finset.mem_filter] at member
    exact (mem_primesInInterval.mp member.1).2.1
  have candidatePrime : ∀ p, p ∈ candidates → p.Prime := by
    intro p hp
    exact (mem_primesInInterval.mp (candidateMem p hp)).2.2
  have candidateAbove : ∀ p, p ∈ candidates → base < p := by
    intro p hp
    exact (mem_primesInInterval.mp (candidateMem p hp)).1
  have candidateBelow : ∀ p, p ∈ candidates → p ≤ bound := by
    intro p hp
    exact (mem_primesInInterval.mp (candidateMem p hp)).2.1
  have prePrime : ∀ p, p ∈ pre → p.Prime := by
    intro p hp
    have member := preMem p hp
    simp only [stableLowerPrimes, Finset.mem_filter] at member
    exact (mem_primesInInterval.mp member.1).2.2
  have preUpper : ∀ p, p ∈ pre → p ≤ t ^ 6 := by
    intro p hp
    have member := preMem p hp
    simp only [stableLowerPrimes, Finset.mem_filter] at member
    exact (mem_primesInInterval.mp member.1).2.1
  have preBelowBase : ∀ p, p ∈ pre → p ≤ base := by
    intro p hp
    exact (preUpper p hp).trans (by omega)
  have crossOrdered : ∀ p ∈ pre, ∀ q ∈ candidates, p < q := by
    intro p hp q hq
    have := preUpper p hp
    have := candidateAbove q hq
    omega
  have selectedOrdered : (pre ++ candidates).Pairwise (· < ·) := by
    rw [List.pairwise_append]
    exact ⟨preOrdered, candidateOrdered, crossOrdered⟩
  have leastMinimal : ∀ p, p ∈ pre ++ candidates → least ≤ p := by
    intro p hp
    rw [List.mem_append] at hp
    cases hp with
    | inl hp => exact preOrderedLE.head!_le hp
    | inr hp =>
        have := candidateAbove p hp
        omega
  have selectedUpper : ∀ p, p ∈ pre ++ candidates → p ≤ bound := by
    intro p hp
    rw [List.mem_append] at hp
    cases hp with
    | inl hp => exact (preBelowBase p hp).trans baseBound.le
    | inr hp => exact candidateBelow p hp
  have selectedPrime : ∀ p, p ∈ pre ++ candidates → p.Prime := by
    intro p hp
    rw [List.mem_append] at hp
    exact hp.elim (prePrime p) (candidatePrime p)
  have leastSquare : bound < least * least := by
    have lowerSquare : (t ^ 4) ^ 2 < least * least := by
      simpa [pow_two] using mul_lt_mul leastLower leastLower.le
        (Nat.pow_pos tPositive) (Nat.zero_le least)
    exact boundSeparated.trans lowerSquare
  have preStable : quotientRank pre bound = quotientRank pre base := by
    apply quotientRank_eq_of_pointwise
    intro p hp
    have member := preMem p hp
    simp only [stableLowerPrimes, Finset.mem_filter] at member
    exact member.2.symm
  have candidatesZero : quotientRank candidates base = 0 := by
    exact quotientRank_eq_zero_of_lt candidates base candidateAbove
  have widthLtBase : t ^ 3 < base := widthSmall.trans_le baseLarge
  have candidateOne : ∀ p, p ∈ candidates → bound / p = 1 := by
    intro p hp
    have pPositive := (candidatePrime p hp).pos
    have oneLe : 1 ≤ bound / p :=
      (Nat.one_le_div_iff pPositive).2 (candidateBelow p hp)
    have boundLtTwice : bound < 2 * p := by
      rw [show bound = base + t ^ 3 by omega]
      have := candidateAbove p hp
      omega
    have belowTwo : bound / p < 2 :=
      (Nat.div_lt_iff_lt_mul pPositive).2 (by
        simpa [Nat.mul_comm] using boundLtTwice)
    omega
  have candidatesOne : quotientRank candidates bound = candidates.length :=
    quotientRank_eq_length_of_pointwise_one candidates bound candidateOne
  have endpointRank : quotientRank (pre ++ candidates) bound =
      quotientRank (pre ++ candidates) base + candidates.length := by
    simp only [quotientRank_append]
    rw [preStable, candidatesZero, candidatesOne]
    omega
  let preRank := (pre.map fun p => base / p).sum
  have baseRank : quotientRank (pre ++ candidates) base = preRank := by
    rw [quotientRank_append, candidatesZero, Nat.add_zero]
    rfl
  have boundRank : quotientRank (pre ++ candidates) bound = preRank + k := by
    rw [endpointRank, baseRank, candidateLength]
  have lowerEnvelope :
      3 * quotientRank (pre ++ candidates) bound + 3 < base := by
    have floorBound := Nat.mul_div_le base 3
    rw [boundRank]
    have rankRoom : preRank + k + 2 ≤ base / 3 := by
      simpa [preRank] using (show
        (pre.map fun p => base / p).sum + k + 2 ≤ base / 3 by omega)
    omega
  have nextBound : base / next ≤ 10000 * t ^ 2 :=
    stable_quotient_le_scale baseUpper nextMem
  have baseFloor : base ≤ 3 * (base / 3) + 2 := by
    have remainder := Nat.mod_lt base (by norm_num : 0 < 3)
    have decompose := Nat.mod_add_div base 3
    omega
  have baseNearRank : base ≤
      3 * (preRank + base / next + k + 2) + 2 := by
    have capExact : k + 2 ≤ base / 3 := by omega
    have thirdNear : base / 3 < preRank + base / next + k + 2 := by
      simpa [preRank] using (show base / 3 <
        (pre.map fun p => base / p).sum + base / next + k + 2 by omega)
    omega
  have upperRaw : bound < 3 * preRank + t ^ 4 := by
    rw [show bound = base + t ^ 3 by omega]
    omega
  have upperEnvelope :
      bound < 3 * quotientRank (pre ++ candidates) base + least := by
    rw [baseRank]
    omega
  exact ⟨{
    least := least
    base := base
    bound := bound
    lowerFactors := pre
    candidates := candidates
    candidateLength := by omega
    lowerLength := preLong
    selectedOrdered := selectedOrdered
    leastMem := by simp [leastMemPre]
    selectedAtLeastLeast := leastMinimal
    selectedAtMostBound := selectedUpper
    primeLike := by
      intro p hp
      have prime := selectedPrime p hp
      exact ⟨prime.two_le, fun divisor divides =>
        prime.eq_one_or_self_of_dvd divisor divides⟩
    lowerAtMostBase := preBelowBase
    baseBelowCandidates := candidateAbove
    leastSquareAboveBound := leastSquare
    endpointRank := endpointRank
    lowerEnvelope := lowerEnvelope
    upperEnvelope := upperEnvelope
  }⟩

/-- Korec prime systems exist for every span required by the normalized
machine reduction.  The proof combines Mertens' reciprocal-prime estimate,
Chebyshev's prime-counting bounds, and the finite construction above. -/
theorem existsForEverySpan : ExistsForEverySpan := by
  intro span spanLarge
  have eventualSystem : ∀ᶠ t : Nat in atTop, Nonempty (System span) := by
    filter_upwards [eventually_ge_atTop
        (100000 * ((span - 1) + 1)),
      eventually_two_fifths_lt_primeReciprocalInterval,
      eventually_prime_rich_block (span - 1)] with t scaleLarge mass richBlock
    obtain ⟨i, indexBound, rich⟩ := richBlock
    exact system_nonempty_of_rich_block spanLarge scaleLarge indexBound rich mass
  obtain ⟨_t, system⟩ := eventualSystem.exists
  exact system

end

end Mortality.SourceMachine.KorecPrimeSystem
