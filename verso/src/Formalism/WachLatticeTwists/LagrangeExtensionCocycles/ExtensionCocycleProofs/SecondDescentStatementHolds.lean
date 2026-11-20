import Formalism.WachLatticeTwists.LagrangeExtensionCocycles.Statement

noncomputable section

namespace Formalism.RepresentationBoundsCohomology.N2

/- English proof (translation)
Introduce `ℓ _ hℓ2 A _ D D' _ _ _ _ S Mi hi s H h1 h2 h3 h4 h5 n hn`. Use `set t := (s + (ℓ - 2)) / (ℓ - 1) with ht`. Use `set c := cW ℓ H with hc`. Establish `hℓ3 : 3 ≤ ℓ`. Use `(Fact.out : ℓ.Prime).two_le` as an intermediate fact.

Use linear arithmetic over natural numbers and integers. Establish `hts : s ≤ (ℓ - 1) * t`. Establish `e1` using `Nat.div_add_mod (s + (ℓ - 2)) (ℓ - 1)`. Establish `e2` using `Nat.mod_lt (s + (ℓ - 2)) (show 0 < ℓ - 1 by omega)`. Rewrite `e1` using `[← ht]`.

Generalize the expression as in `(ℓ - 1) * t = X at *`. Use linear arithmetic over natural numbers and integers. Establish `hℓR : (3 : ℝ) ≤ ℓ` using `by exact_mod_cast hℓ3`. Establish `hℓ1 : ((ℓ - 1 : ℕ) : ℝ) = (ℓ : ℝ) - 1`. Rewrite using `[Nat.cast_sub (by omega)]`.

Simplify using the standard rewrite rules. Establish `htsR : (s : ℝ) ≤ ((ℓ : ℝ) - 1) * t`. Use `(Nat.cast_le (α := ℝ)).2 hts` as an intermediate fact. Move the coercions through the operations in `[hℓ1] at this`. Rewrite using `[← hℓ1]`.

Conclude with `hts` after adjusting the coercions. Establish `hkey : ∀ r ∈ S.R, (S.π ^ t * S.q ^ (c + 2 + t)) • r ∈ S.R'`. Introduce `r hr`. Rewrite using `[S.hq, add_pow, Finset.mul_sum, Finset.sum_smul]`. Use `Submodule.sum_mem _ fun i hi => ?_` and prove the remaining obligations.

Rewrite `hi` using `[Finset.mem_range]`. Take `⟨U, hU⟩ : ∃ U, c + 2 + t - i = U` from `⟨_, rfl⟩`. Establish `hU' : c + 2 + t = i + U` using `by omega`. Rewrite using `[hU]`. Establish `e : S.π ^ t * (((ℓ : A) * S.w) ^ i * (S.π ^ (ℓ - 1)) ^ U * ((c + 2 + t).choose i : A)) = (S.w ^ i * ((c + 2 + t).choose i : A)) * ((ℓ : A) ^ i * S.π ^ ((ℓ - 1) * U + t))`.

Rewrite using `[← pow_mul, pow_add, mul_pow]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e, mul_smul]`. Use `Submodule.smul_mem _ _ ?_` and prove the remaining obligations. Distinguish the cases in `hj : s ≤ (ℓ - 1) * U + t`.

Rewrite using `[← Nat.sub_add_cancel hj, pow_add, ← mul_assoc, mul_smul]`. Conclude with `Submodule.smul_mem _ _ (h4 r hr)`. Use `h5 i ((ℓ - 1) * U + t) ?_ r hr` and prove the remaining obligations. Establish `hU0 : (0 : ℝ) ≤ U` using `by positivity`. Establish `ht0 : (0 : ℝ) ≤ t` using `by positivity`.

Establish `hiR : (i : ℝ) = c + 2 + t - U`. Use `congrArg (Nat.cast : ℕ → ℝ) hU'` as an intermediate fact. Move the coercions through the operations in `at this`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hpos : (0 : ℝ) < ((ℓ : ℝ) - 1) ^ 2` using `by nlinarith`.

Establish `hsl : (s : ℝ) * ℓ ≤ ((ℓ : ℝ) - 1) * t * ℓ` using `mul_le_mul_of_nonneg_right htsR (by linarith)`. Establish `hcU : (0 : ℝ) ≤ U * ((ℓ : ℝ) - 1)` using `mul_nonneg hU0 (by linarith)`. Establish `hj' : (((ℓ - 1) * U + t : ℕ) : ℝ) = ((ℓ : ℝ) - 1) * U + t`. Move the coercions through the operations in `[hℓ1]`. Expand and normalize the polynomial expressions, which then agree.

Rewrite using `[hj', hiR]`. Establish `hdiv : ((s : ℝ) - (((ℓ : ℝ) - 1) * U + t)) * ℓ / ((ℓ : ℝ) - 1) ^ 2 ≤ 2 + t - U`. Rewrite using `[div_le_iff₀ hpos]`. Use the polynomial consequences of the given equalities and inequalities. Combine the linear equalities and inequalities to obtain the conclusion.

Establish `hR1` using `hkey _ (h1 n hn)`. Establish `hR2 : (S.π ^ (Mi + hi + c + 2) * (S.π ^ t * S.q ^ (c + 2 + t))) • (S.q ^ Mi • S.φ n) ∈ S.R'`. Rewrite using `[mul_smul]`. Conclude with `Submodule.smul_mem _ _ hR1`. Establish `hsp` using `h2 _ hR2`.

Establish `hφ : S.φ (S.π ^ (Mi + hi + c + 2 + t) • n) = S.q ^ hi • ((S.π ^ (Mi + hi + c + 2) * (S.π ^ t * S.q ^ (c + 2 + t))) • (S.q ^ Mi • S.φ n))`. Rewrite using `[S.φ_smul, map_pow, S.φπ, smul_smul, smul_smul]`. Use `congr 1`. Expand and normalize the polynomial expressions, which then agree. Apply `h3 _ (Submodule.smul_mem _ _ hn)` to reduce the goal to its premises.

Rewrite using `[hφ]`. Conclude with `hsp`.
-/
theorem second_descent_statement_holds : Stat2 := by
  intro ℓ _ hℓ2 A _ D D' _ _ _ _ S Mi hi s H h1 h2 h3 h4 h5 n hn
  set t := (s + (ℓ - 2)) / (ℓ - 1) with ht
  set c := cW ℓ H with hc
  have hℓ3 : 3 ≤ ℓ := by
    have := (Fact.out : ℓ.Prime).two_le
    omega
  have hts : s ≤ (ℓ - 1) * t := by
    have e1 := Nat.div_add_mod (s + (ℓ - 2)) (ℓ - 1)
    have e2 := Nat.mod_lt (s + (ℓ - 2)) (show 0 < ℓ - 1 by omega)
    rw [← ht] at e1
    generalize (ℓ - 1) * t = X at *
    omega
  have hℓR : (3 : ℝ) ≤ ℓ := by exact_mod_cast hℓ3
  have hℓ1 : ((ℓ - 1 : ℕ) : ℝ) = (ℓ : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega)]
    simp
  have htsR : (s : ℝ) ≤ ((ℓ : ℝ) - 1) * t := by
    have := (Nat.cast_le (α := ℝ)).2 hts
    push_cast [hℓ1] at this
    rw [← hℓ1]
    exact_mod_cast hts
  have hkey : ∀ r ∈ S.R, (S.π ^ t * S.q ^ (c + 2 + t)) • r ∈ S.R' := by
    intro r hr
    rw [S.hq, add_pow, Finset.mul_sum, Finset.sum_smul]
    refine Submodule.sum_mem _ fun i hi => ?_
    rw [Finset.mem_range] at hi
    obtain ⟨U, hU⟩ : ∃ U, c + 2 + t - i = U := ⟨_, rfl⟩
    have hU' : c + 2 + t = i + U := by omega
    rw [hU]
    have e : S.π ^ t * (((ℓ : A) * S.w) ^ i * (S.π ^ (ℓ - 1)) ^ U * ((c + 2 + t).choose i : A)) =
        (S.w ^ i * ((c + 2 + t).choose i : A)) * ((ℓ : A) ^ i * S.π ^ ((ℓ - 1) * U + t)) := by
      rw [← pow_mul, pow_add, mul_pow]
      ring
    rw [e, mul_smul]
    refine Submodule.smul_mem _ _ ?_
    by_cases hj : s ≤ (ℓ - 1) * U + t
    · rw [← Nat.sub_add_cancel hj, pow_add, ← mul_assoc, mul_smul]
      exact Submodule.smul_mem _ _ (h4 r hr)
    · refine h5 i ((ℓ - 1) * U + t) ?_ r hr
      have hU0 : (0 : ℝ) ≤ U := by positivity
      have ht0 : (0 : ℝ) ≤ t := by positivity
      have hiR : (i : ℝ) = c + 2 + t - U := by
        have := congrArg (Nat.cast : ℕ → ℝ) hU'
        push_cast at this
        linarith
      have hpos : (0 : ℝ) < ((ℓ : ℝ) - 1) ^ 2 := by nlinarith
      have hsl : (s : ℝ) * ℓ ≤ ((ℓ : ℝ) - 1) * t * ℓ := mul_le_mul_of_nonneg_right htsR (by linarith)
      have hcU : (0 : ℝ) ≤ U * ((ℓ : ℝ) - 1) := mul_nonneg hU0 (by linarith)
      have hj' : (((ℓ - 1) * U + t : ℕ) : ℝ) = ((ℓ : ℝ) - 1) * U + t := by
        push_cast [hℓ1]
        ring
      rw [hj', hiR]
      have hdiv : ((s : ℝ) - (((ℓ : ℝ) - 1) * U + t)) * ℓ / ((ℓ : ℝ) - 1) ^ 2 ≤ 2 + t - U := by
        rw [div_le_iff₀ hpos]
        nlinarith
      linarith
  have hR1 := hkey _ (h1 n hn)
  have hR2 : (S.π ^ (Mi + hi + c + 2) * (S.π ^ t * S.q ^ (c + 2 + t))) • (S.q ^ Mi • S.φ n) ∈ S.R' := by
    rw [mul_smul]
    exact Submodule.smul_mem _ _ hR1
  have hsp := h2 _ hR2
  have hφ : S.φ (S.π ^ (Mi + hi + c + 2 + t) • n) = S.q ^ hi •
      ((S.π ^ (Mi + hi + c + 2) * (S.π ^ t * S.q ^ (c + 2 + t))) • (S.q ^ Mi • S.φ n)) := by
    rw [S.φ_smul, map_pow, S.φπ, smul_smul, smul_smul]
    congr 1
    ring
  apply h3 _ (Submodule.smul_mem _ _ hn)
  rw [hφ]
  exact hsp

end Formalism.RepresentationBoundsCohomology.N2
