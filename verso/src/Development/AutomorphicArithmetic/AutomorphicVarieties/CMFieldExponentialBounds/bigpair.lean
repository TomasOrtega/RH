import Mathlib
import Development.AutomorphicArithmetic.AutomorphicVarieties.StmtFields

open NumberField Formalism.HC UpperTheory.Top UpperTheory.V

/- English proof (translation)
Introduce `eps J Ct P heps hJ`. Use `set δ : ℝ := 1 / J * (eps / 5) with hδ`. Establish `hδpos : 0 < δ` using `by positivity`. Use `set mC : ℝ := max Ct 0 with hmC`. Use `set n : ℕ := ⌈(mC + 1) / δ⌉₊ with hn_def`.

Establish `hn : mC + 1 ≤ δ * n`. Establish `h` using `Nat.le_ceil ((mC + 1) / δ)`. Rewrite `h` using `[div_le_iff₀ hδpos]`. Combine the linear equalities and inequalities to obtain the conclusion. Use `set M : ℝ := 2 ^ n * (n.factorial : ℝ) with hM_def`.

Establish `hM : 0 < M` using `by positivity`. Use `⟨max (Real.exp J) (M * (|P| + 3) + 1), fun X hX q d hw => ?_⟩` and prove the remaining obligations. Establish `hXe : Real.exp J ≤ X` using `le_trans (le_max_left _ _) hX`. Establish `hXM : M * (|P| + 3) + 1 ≤ X` using `le_trans (le_max_right _ _) hX`. Establish `hX1 : 1 ≤ X`.

Use `Real.add_one_le_exp J` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hX0 : 0 < X` using `by linarith`. Establish `hY : (X ^ (1 / J)) ^ (eps / 5) = X ^ δ`. Rewrite using `[← Real.rpow_mul hX0.le]`.

Establish `hlogY : 1 ≤ Real.log (X ^ (1 / J))`. Rewrite using `[Real.log_rpow hX0]`. Establish `hJl : J ≤ Real.log X` using `(Real.le_log_iff_exp_le hX0).2 hXe`. Rewrite using `[one_div, inv_mul_eq_div, le_div_iff₀ hJ]`. Combine the linear equalities and inequalities to obtain the conclusion.

Use `set y : ℝ := X ^ δ / 2 with hy_def`. Establish `hy0 : 0 ≤ y` using `by positivity`. Establish `hfac` using `Real.pow_div_factorial_le_exp y hy0 n`. Establish `hyn : y ^ n = X ^ (δ * n) / 2 ^ n`. Rewrite using `[hy_def, div_pow, ← Real.rpow_natCast (X ^ δ), ← Real.rpow_mul hX0.le]`.

Establish `hlow : X ^ (δ * n) / M ≤ Real.exp y`. Rewrite `hfac` using `[hyn, div_div]`. Conclude with `hfac`. Establish `hpow : X ^ mC * X ≤ X ^ (δ * n)`. Rewrite using `[← Real.rpow_add_one hX0.ne']`.

Conclude with `Real.rpow_le_rpow_of_exponent_le hX1 hn`. Establish `hCt : X ^ Ct ≤ X ^ mC` using `Real.rpow_le_rpow_of_exponent_le hX1 (le_max_left _ _)`. Establish `hmC1 : 1 ≤ X ^ mC` using `Real.one_le_rpow hX1 (le_max_right _ _)`. Establish `hXdiv : |P| + 3 < X / M`. Rewrite using `[lt_div_iff₀ hM]`.

Combine the linear equalities and inequalities to obtain the conclusion. Establish `hmain : X ^ mC * (|P| + 3) < Real.exp y`. Establish `h1 : X ^ mC * (|P| + 3) < X ^ mC * (X / M)` using `mul_lt_mul_of_pos_left hXdiv (by linarith)`. Establish `h2 : X ^ mC * (X / M) = X ^ mC * X / M` using `by ring`. Establish `h3 : X ^ mC * X / M ≤ X ^ (δ * n) / M` using `div_le_div_of_nonneg_right hpow hM.le`.

Combine the linear equalities and inequalities to obtain the conclusion. Establish `hP0 : 0 ≤ |P|` using `abs_nonneg P`. Establish `hB1 : 2 * X ^ Ct + 1 < Real.exp y` using `by nlinarith`. Establish `hB2 : P < Real.exp y`. Use `le_abs_self P` as an intermediate fact.

Use the polynomial consequences of the given equalities and inequalities. Establish `hq0 : (0 : ℝ) < q` using `by exact_mod_cast hw.q_prime.pos`. Establish `hd0 : (0 : ℝ) < d` using `by exact_mod_cast hw.d_prime.pos`. Establish `hqlo` using `hw.q_lo`. Establish `hdlo` using `hw.d_lo`.

Rewrite `hqlo`, `hdlo` using `[hY]`. Establish `hq : Real.exp y < q`. Rewrite using `[← Real.exp_log hq0]`. Conclude with `Real.exp_lt_exp.2 (by rw [hy_def]; exact hqlo)`. Establish `hd : Real.exp y < d`.

Rewrite using `[← Real.exp_log hd0]`. Apply `Real.exp_lt_exp.2` to reduce the goal to its premises. Establish `hXd : 0 ≤ X ^ δ` using `by positivity`. Establish `hl2 : 1 ≤ Real.log (X ^ (1 / J)) ^ 2` using `by nlinarith`. Establish `: X ^ δ / 2 ≤ X ^ δ * Real.log (X ^ (1 / J)) ^ 2 / 2` using `by nlinarith`.

Rewrite using `[hy_def]`. Combine the linear equalities and inequalities to obtain the conclusion. Conclude with `⟨by linarith, by linarith, by linarith, by linarith⟩`.
-/
theorem UpperTheory.V.eventually_winPair_gt_power :
    ∀ eps J Ct P : ℝ, 0 < eps → 0 < J → ∃ X0 : ℝ, ∀ X ≥ X0, ∀ q d : ℕ, WinPair eps (X ^ (1 / J)) q d →
      2 * X ^ Ct + 1 < (q : ℝ) ∧ 2 * X ^ Ct + 1 < (d : ℝ) ∧ P < (q : ℝ) ∧ P < (d : ℝ) := by
  intro eps J Ct P heps hJ
  set δ : ℝ := 1 / J * (eps / 5) with hδ
  have hδpos : 0 < δ := by positivity
  set mC : ℝ := max Ct 0 with hmC
  set n : ℕ := ⌈(mC + 1) / δ⌉₊ with hn_def
  have hn : mC + 1 ≤ δ * n := by
    have h := Nat.le_ceil ((mC + 1) / δ)
    rw [div_le_iff₀ hδpos] at h
    linarith
  set M : ℝ := 2 ^ n * (n.factorial : ℝ) with hM_def
  have hM : 0 < M := by positivity
  refine ⟨max (Real.exp J) (M * (|P| + 3) + 1), fun X hX q d hw => ?_⟩
  have hXe : Real.exp J ≤ X := le_trans (le_max_left _ _) hX
  have hXM : M * (|P| + 3) + 1 ≤ X := le_trans (le_max_right _ _) hX
  have hX1 : 1 ≤ X := by
    have := Real.add_one_le_exp J
    linarith
  have hX0 : 0 < X := by linarith
  have hY : (X ^ (1 / J)) ^ (eps / 5) = X ^ δ := by
    rw [← Real.rpow_mul hX0.le]
  have hlogY : 1 ≤ Real.log (X ^ (1 / J)) := by
    rw [Real.log_rpow hX0]
    have hJl : J ≤ Real.log X := (Real.le_log_iff_exp_le hX0).2 hXe
    rw [one_div, inv_mul_eq_div, le_div_iff₀ hJ]
    linarith
  set y : ℝ := X ^ δ / 2 with hy_def
  have hy0 : 0 ≤ y := by positivity
  have hfac := Real.pow_div_factorial_le_exp y hy0 n
  have hyn : y ^ n = X ^ (δ * n) / 2 ^ n := by
    rw [hy_def, div_pow, ← Real.rpow_natCast (X ^ δ), ← Real.rpow_mul hX0.le]
  have hlow : X ^ (δ * n) / M ≤ Real.exp y := by
    rw [hyn, div_div] at hfac
    exact hfac
  have hpow : X ^ mC * X ≤ X ^ (δ * n) := by
    rw [← Real.rpow_add_one hX0.ne']
    exact Real.rpow_le_rpow_of_exponent_le hX1 hn
  have hCt : X ^ Ct ≤ X ^ mC := Real.rpow_le_rpow_of_exponent_le hX1 (le_max_left _ _)
  have hmC1 : 1 ≤ X ^ mC := Real.one_le_rpow hX1 (le_max_right _ _)
  have hXdiv : |P| + 3 < X / M := by
    rw [lt_div_iff₀ hM]
    linarith
  have hmain : X ^ mC * (|P| + 3) < Real.exp y := by
    have h1 : X ^ mC * (|P| + 3) < X ^ mC * (X / M) :=
      mul_lt_mul_of_pos_left hXdiv (by linarith)
    have h2 : X ^ mC * (X / M) = X ^ mC * X / M := by ring
    have h3 : X ^ mC * X / M ≤ X ^ (δ * n) / M := div_le_div_of_nonneg_right hpow hM.le
    linarith
  have hP0 : 0 ≤ |P| := abs_nonneg P
  have hB1 : 2 * X ^ Ct + 1 < Real.exp y := by nlinarith
  have hB2 : P < Real.exp y := by
    have := le_abs_self P
    nlinarith
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hw.q_prime.pos
  have hd0 : (0 : ℝ) < d := by exact_mod_cast hw.d_prime.pos
  have hqlo := hw.q_lo
  have hdlo := hw.d_lo
  rw [hY] at hqlo hdlo
  have hq : Real.exp y < q := by
    rw [← Real.exp_log hq0]
    exact Real.exp_lt_exp.2 (by rw [hy_def]; exact hqlo)
  have hd : Real.exp y < d := by
    rw [← Real.exp_log hd0]
    apply Real.exp_lt_exp.2
    have hXd : 0 ≤ X ^ δ := by positivity
    have hl2 : 1 ≤ Real.log (X ^ (1 / J)) ^ 2 := by nlinarith
    have : X ^ δ / 2 ≤ X ^ δ * Real.log (X ^ (1 / J)) ^ 2 / 2 := by nlinarith
    rw [hy_def]
    linarith
  exact ⟨by linarith, by linarith, by linarith, by linarith⟩
