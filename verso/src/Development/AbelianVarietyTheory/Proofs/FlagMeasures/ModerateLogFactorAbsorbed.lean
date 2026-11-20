import Mathlib
open Matrix Finset Real

namespace GlobalTheory

/- English proof (translation)
Introduce `Cg`. Use `set K : ℝ := 22 * (|Cg| + 4) with hK`. Establish `hC : 0 ≤ |Cg|` using `abs_nonneg _`. Establish `hK0 : 0 ≤ K` using `by positivity`. Use `⟨⌈Real.exp (16 * (1 + K))⌉₊, ?_⟩` and prove the remaining obligations.

Introduce `n f q rd g b hn hf hq hqn hrd hlrd hlf hb hlb hg hgb`. Establish `hn' : Real.exp (16 * (1 + K)) ≤ (n : ℝ)` using `Nat.ceil_le.mp hn`. Establish `hn1 : (1 : ℝ) ≤ n` using `le_trans (Real.one_le_exp (by positivity)) hn'`. Establish `hn0 : (0 : ℝ) < n` using `by linarith`. Establish `hL : 16 * (1 + K) ≤ Real.log n` using `(Real.le_log_iff_exp_le hn0).mpr hn'`.

Establish `hf1 : (1 : ℝ) ≤ f` using `by exact_mod_cast hf`. Establish `hq1 : (1 : ℝ) ≤ q` using `by exact_mod_cast hq`. Establish `hqn' : (q : ℝ) ^ 2 ≤ n` using `by exact_mod_cast hqn`. Use `set L := Real.log n with hLdef`. Establish `hm1 : (n : ℝ) ≤ n * f` using `by nlinarith`.

Establish `hm : (1 : ℝ) ≤ n * f` using `by linarith`. Establish `hX : (n * f : ℝ) * (1 + K) ≤ 1 / 16 * n * f * L` using `by nlinarith`. Establish `hX1 : (n * f : ℝ) ≤ 1 / 16 * n * f * L` using `by nlinarith`. Establish `hX2 : (n * f : ℝ) + K ≤ 1 / 16 * n * f * L` using `by nlinarith`. Use `set E := Real.exp (1 / 16 * n * f * L) with hE`.

Establish `hE0 : 0 < E` using `Real.exp_pos _`. Establish `hEn : Real.exp n ≤ E` using `Real.exp_le_exp.mpr (by linarith)`. Establish `hnE : (n : ℝ) ≤ E`. Use `Real.add_one_le_exp (n : ℝ)` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion.

Prove the components needed by the constructor for the conclusion. Establish `hb0 : 0 < b` using `by linarith`. Establish `hlb0 : 0 ≤ Real.log b` using `Real.log_nonneg (by linarith)`. Establish `h1 : L ≤ E`. Use `Real.log_le_sub_one_of_pos hn0` as an intermediate fact.

Combine the linear equalities and inequalities to obtain the conclusion. Establish `h2 : Real.log f ≤ E`. Establish `: Real.sqrt n ≤ n` using `Real.sqrt_le_iff.mpr ⟨hn0.le, by nlinarith⟩`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `h3 : Real.log g ≤ |Cg| * E`.

Establish `h4 : Real.log g ≤ Real.log (b ^ Cg)` using `Real.log_le_log (by linarith) hgb`. Rewrite `h4` using `[Real.log_rpow hb0]`. Establish `h5 : Cg * Real.log b ≤ |Cg| * Real.log b` using `mul_le_mul_of_nonneg_right (le_abs_self _) hlb0`. Establish `h6 : |Cg| * Real.log b ≤ |Cg| * E` using `mul_le_mul_of_nonneg_left hlb hC`. Combine the linear equalities and inequalities to obtain the conclusion.

Establish `hlog : Real.log (n * f * rd * g * b) ≤ (|Cg| + 4) * E`. Establish `hf0 : (0 : ℝ) < f` using `by linarith`. Establish `hrd0 : 0 < rd` using `by linarith`. Establish `hg0 : 0 < g` using `by linarith`. Rewrite using `[Real.log_mul (by positivity) hb0.ne', Real.log_mul (by positivity) hg0.ne', Real.log_mul (by positivity) hrd0.ne', Real.log_mul hn0.ne' hf0.ne']`.

Combine the linear equalities and inequalities to obtain the conclusion. Establish `hKE : (n * f : ℝ) * K ≤ E`. Establish `a1 : (n * f : ℝ) ≤ Real.exp (n * f)`. Use `Real.add_one_le_exp (n * f : ℝ)` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion.

Establish `a2 : K ≤ Real.exp K`. Use `Real.add_one_le_exp K` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion. Combine the equalities or inequalities in the displayed calculation. Establish `hEE : Real.exp (1 / 8 * n * f * L) = E * E`.

Rewrite using `[hE, ← Real.exp_add]`. Use `congr 1`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[hEE]`. Combine the equalities or inequalities in the displayed calculation.

Establish `hqn2 : (q : ℝ) ≤ n` using `by nlinarith`. Establish `h2e : (2 : ℝ) ≤ Real.exp 1`. Use `Real.add_one_le_exp (1 : ℝ)` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hp : (2 : ℝ) ^ q ≤ Real.exp q`.

Combine the equalities or inequalities in the displayed calculation. Combine the equalities or inequalities in the displayed calculation.
-/
theorem moderate_log_factor_absorbed : ∀ Cg : ℝ, ∃ n₀ : ℕ, ∀ (n f q : ℕ) (rd g b : ℝ), n₀ ≤ n → 1 ≤ f → 1 ≤ q → q ^ 2 ≤ n → 1 ≤ rd → Real.log rd ≤ Real.exp n → Real.log f ≤ Real.sqrt n → 2 ≤ b → Real.log b ≤ Real.exp (1 / 16 * n * f * Real.log n) → 1 ≤ g → g ≤ b ^ Cg → 2 * f * q * (11 * q * Real.log (n * f * rd * g * b)) ≤ Real.exp (1 / 8 * n * f * Real.log n) ∧ 2 * (2 : ℝ) ^ q * Real.exp (-(3 / 8) * n * f * Real.log n) ≤ Real.exp (-(1 / 4) * n * f * Real.log n) := by
  intro Cg
  set K : ℝ := 22 * (|Cg| + 4) with hK
  have hC : 0 ≤ |Cg| := abs_nonneg _
  have hK0 : 0 ≤ K := by positivity
  refine ⟨⌈Real.exp (16 * (1 + K))⌉₊, ?_⟩
  intro n f q rd g b hn hf hq hqn hrd hlrd hlf hb hlb hg hgb
  have hn' : Real.exp (16 * (1 + K)) ≤ (n : ℝ) := Nat.ceil_le.mp hn
  have hn1 : (1 : ℝ) ≤ n := le_trans (Real.one_le_exp (by positivity)) hn'
  have hn0 : (0 : ℝ) < n := by linarith
  have hL : 16 * (1 + K) ≤ Real.log n := (Real.le_log_iff_exp_le hn0).mpr hn'
  have hf1 : (1 : ℝ) ≤ f := by exact_mod_cast hf
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast hq
  have hqn' : (q : ℝ) ^ 2 ≤ n := by exact_mod_cast hqn
  set L := Real.log n with hLdef
  have hm1 : (n : ℝ) ≤ n * f := by nlinarith
  have hm : (1 : ℝ) ≤ n * f := by linarith
  have hX : (n * f : ℝ) * (1 + K) ≤ 1 / 16 * n * f * L := by nlinarith
  have hX1 : (n * f : ℝ) ≤ 1 / 16 * n * f * L := by nlinarith
  have hX2 : (n * f : ℝ) + K ≤ 1 / 16 * n * f * L := by nlinarith
  set E := Real.exp (1 / 16 * n * f * L) with hE
  have hE0 : 0 < E := Real.exp_pos _
  have hEn : Real.exp n ≤ E := Real.exp_le_exp.mpr (by linarith)
  have hnE : (n : ℝ) ≤ E := by
    have := Real.add_one_le_exp (n : ℝ); linarith
  constructor
  · have hb0 : 0 < b := by linarith
    have hlb0 : 0 ≤ Real.log b := Real.log_nonneg (by linarith)
    have h1 : L ≤ E := by
      have := Real.log_le_sub_one_of_pos hn0; linarith
    have h2 : Real.log f ≤ E := by
      have : Real.sqrt n ≤ n := Real.sqrt_le_iff.mpr ⟨hn0.le, by nlinarith⟩
      linarith
    have h3 : Real.log g ≤ |Cg| * E := by
      have h4 : Real.log g ≤ Real.log (b ^ Cg) := Real.log_le_log (by linarith) hgb
      rw [Real.log_rpow hb0] at h4
      have h5 : Cg * Real.log b ≤ |Cg| * Real.log b :=
        mul_le_mul_of_nonneg_right (le_abs_self _) hlb0
      have h6 : |Cg| * Real.log b ≤ |Cg| * E := mul_le_mul_of_nonneg_left hlb hC
      linarith
    have hlog : Real.log (n * f * rd * g * b) ≤ (|Cg| + 4) * E := by
      have hf0 : (0 : ℝ) < f := by linarith
      have hrd0 : 0 < rd := by linarith
      have hg0 : 0 < g := by linarith
      rw [Real.log_mul (by positivity) hb0.ne', Real.log_mul (by positivity) hg0.ne',
        Real.log_mul (by positivity) hrd0.ne', Real.log_mul hn0.ne' hf0.ne']
      linarith
    have hKE : (n * f : ℝ) * K ≤ E := by
      have a1 : (n * f : ℝ) ≤ Real.exp (n * f) := by
        have := Real.add_one_le_exp (n * f : ℝ); linarith
      have a2 : K ≤ Real.exp K := by
        have := Real.add_one_le_exp K; linarith
      calc (n * f : ℝ) * K ≤ Real.exp (n * f) * Real.exp K :=
            mul_le_mul a1 a2 hK0 (Real.exp_pos _).le
        _ = Real.exp (n * f + K) := (Real.exp_add _ _).symm
        _ ≤ E := Real.exp_le_exp.mpr hX2
    have hEE : Real.exp (1 / 8 * n * f * L) = E * E := by
      rw [hE, ← Real.exp_add]; congr 1; ring
    rw [hEE]
    calc 2 * (f : ℝ) * q * (11 * q * Real.log (n * f * rd * g * b))
        = (22 * f * q ^ 2) * Real.log (n * f * rd * g * b) := by ring
      _ ≤ (22 * f * q ^ 2) * ((|Cg| + 4) * E) :=
          mul_le_mul_of_nonneg_left hlog (by positivity)
      _ ≤ (22 * f * n) * ((|Cg| + 4) * E) := by gcongr
      _ = (n * f * K) * E := by rw [hK]; ring
      _ ≤ E * E := by gcongr
  · have hqn2 : (q : ℝ) ≤ n := by nlinarith
    have h2e : (2 : ℝ) ≤ Real.exp 1 := by
      have := Real.add_one_le_exp (1 : ℝ); linarith
    have hp : (2 : ℝ) ^ q ≤ Real.exp q := by
      calc (2 : ℝ) ^ q ≤ (Real.exp 1) ^ q := by gcongr
        _ = Real.exp q := by rw [← Real.exp_nat_mul]; simp
    calc 2 * (2 : ℝ) ^ q * Real.exp (-(3 / 8) * n * f * L)
        ≤ Real.exp 1 * Real.exp q * Real.exp (-(3 / 8) * n * f * L) := by gcongr
      _ = Real.exp (1 + q + -(3 / 8) * n * f * L) := by rw [Real.exp_add, Real.exp_add]
      _ ≤ _ := Real.exp_le_exp.mpr (by linarith)

end GlobalTheory
