import Mathlib
open Filter Topology

namespace GlobalTheory

/- English proof (translation)
Introduce `d n u γ hn h ε hε`. Establish `hnR : (0:ℝ) < n` using `Nat.cast_pos.mpr hn`. Establish `hnd : (0:ℝ) < (n:ℝ)^d` using `pow_pos hnR d`. Use `set ε' := ε * (n:ℝ)^d / 2 with hε'`. Establish `hε'pos : 0 < ε'` using `by positivity`.

Establish `h1 : ∀ᶠ q : ℕ in atTop, ∀ r ∈ Set.Iio n, (γ - ε') * (q:ℝ)^d ≤ u (n*q + r)` using `(Filter.eventually_all_finite (Set.finite_Iio n)).2 (fun r hr => h r hr ε' hε'pos)`. Establish `h2 : ∀ᶠ M : ℕ in atTop, ∀ r ∈ Set.Iio n, (γ - ε') * ((M / n : ℕ):ℝ)^d ≤ u (n*(M/n) + r)` using `(Nat.tendsto_div_const_atTop hn.ne').eventually h1`. Establish `hf : Tendsto (fun M : ℕ => ((M / n : ℕ):ℝ) / M) atTop (𝓝 (1 / n))`. Establish `hlow : Tendsto (fun M : ℕ => 1 / (n:ℝ) - 1 / (M:ℝ)) atTop (𝓝 (1 / n))`. Simplify using `using (tendsto_const_nhds (x := 1/(n:ℝ))).sub tendsto_one_div_atTop_nhds_zero_nat`.

Use `tendsto_of_tendsto_of_tendsto_of_le_of_le' hlow tendsto_const_nhds ?_ ?_` and prove the remaining obligations. Use `filter_upwards [eventually_gt_atTop 0] with M hM`. Establish `hMR : (0:ℝ) < M` using `Nat.cast_pos.mpr hM`. Establish `key : (n:ℝ) * ((M/n : ℕ):ℝ) + ((M % n : ℕ):ℝ) = M` using `by exact_mod_cast Nat.div_add_mod M n`. Establish `hmod : ((M % n : ℕ):ℝ) < n` using `by exact_mod_cast Nat.mod_lt M hn`.

Establish `hq : (M:ℝ) - n ≤ n * ((M/n : ℕ):ℝ)` using `by linarith`. Rewrite using `[div_sub_div _ _ hnR.ne' hMR.ne', div_le_div_iff₀ (by positivity) hMR]`. Use polynomial arithmetic with `[mul_le_mul_of_nonneg_right hq hMR.le]`. Use `filter_upwards [eventually_gt_atTop 0] with M hM`. Establish `hMR : (0:ℝ) < M` using `Nat.cast_pos.mpr hM`.

Rewrite using `[div_le_div_iff₀ hMR hnR]`. Establish `h0 : ((M / n : ℕ):ℝ) ≤ (M:ℝ) / n` using `Nat.cast_div_le`. Rewrite `h0` using `[le_div_iff₀ hnR]`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hg : Tendsto (fun M : ℕ => (γ - ε') * (((M / n : ℕ):ℝ) / M)^d) atTop (𝓝 ((γ - ε') * (1/(n:ℝ))^d))` using `(hf.pow d).const_mul _`.

Establish `hlim : (γ - ε') * (1/(n:ℝ))^d = γ / (n:ℝ)^d - ε/2`. Rewrite using `[one_div_pow, hε']`. Clear the denominators using the available nonvanishing facts. Establish `h3 : ∀ᶠ M : ℕ in atTop, γ / (n:ℝ)^d - ε < (γ - ε') * (((M / n : ℕ):ℝ) / M)^d`. Rewrite `hg` using `[hlim]`.

Conclude with `hg.eventually (lt_mem_nhds (by linarith))`. Use `filter_upwards [h2, h3, eventually_gt_atTop 0] with M hM2 hM3 hM`. Establish `hMR : (0:ℝ) < M` using `Nat.cast_pos.mpr hM`. Establish `hMd : (0:ℝ) < (M:ℝ)^d` using `pow_pos hMR d`. Establish `e1` using `hM2 (M % n) (Nat.mod_lt M hn)`.

Rewrite `e1` using `[Nat.div_add_mod]`. Rewrite `hM3` using `[div_pow, ← mul_div_assoc, lt_div_iff₀ hMd]`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem lowerBound_along_residues : ∀ (d n : ℕ) (u : ℕ → ℝ) (γ : ℝ), 0 < n → (∀ r < n, ∀ ε : ℝ, 0 < ε → ∀ᶠ q : ℕ in atTop, (γ - ε) * (q : ℝ) ^ d ≤ u (n * q + r)) → ∀ ε : ℝ, 0 < ε → ∀ᶠ M : ℕ in atTop, (γ / (n : ℝ) ^ d - ε) * (M : ℝ) ^ d ≤ u M := by
  intro d n u γ hn h ε hε
  have hnR : (0:ℝ) < n := Nat.cast_pos.mpr hn
  have hnd : (0:ℝ) < (n:ℝ)^d := pow_pos hnR d
  set ε' := ε * (n:ℝ)^d / 2 with hε'
  have hε'pos : 0 < ε' := by positivity
  have h1 : ∀ᶠ q : ℕ in atTop, ∀ r ∈ Set.Iio n, (γ - ε') * (q:ℝ)^d ≤ u (n*q + r) :=
    (Filter.eventually_all_finite (Set.finite_Iio n)).2 (fun r hr => h r hr ε' hε'pos)
  have h2 : ∀ᶠ M : ℕ in atTop, ∀ r ∈ Set.Iio n, (γ - ε') * ((M / n : ℕ):ℝ)^d ≤ u (n*(M/n) + r) :=
    (Nat.tendsto_div_const_atTop hn.ne').eventually h1
  have hf : Tendsto (fun M : ℕ => ((M / n : ℕ):ℝ) / M) atTop (𝓝 (1 / n)) := by
    have hlow : Tendsto (fun M : ℕ => 1 / (n:ℝ) - 1 / (M:ℝ)) atTop (𝓝 (1 / n)) := by
      simpa using (tendsto_const_nhds (x := 1/(n:ℝ))).sub tendsto_one_div_atTop_nhds_zero_nat
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlow tendsto_const_nhds ?_ ?_
    · filter_upwards [eventually_gt_atTop 0] with M hM
      have hMR : (0:ℝ) < M := Nat.cast_pos.mpr hM
      have key : (n:ℝ) * ((M/n : ℕ):ℝ) + ((M % n : ℕ):ℝ) = M := by exact_mod_cast Nat.div_add_mod M n
      have hmod : ((M % n : ℕ):ℝ) < n := by exact_mod_cast Nat.mod_lt M hn
      have hq : (M:ℝ) - n ≤ n * ((M/n : ℕ):ℝ) := by linarith
      rw [div_sub_div _ _ hnR.ne' hMR.ne', div_le_div_iff₀ (by positivity) hMR]
      nlinarith [mul_le_mul_of_nonneg_right hq hMR.le]
    · filter_upwards [eventually_gt_atTop 0] with M hM
      have hMR : (0:ℝ) < M := Nat.cast_pos.mpr hM
      rw [div_le_div_iff₀ hMR hnR]
      have h0 : ((M / n : ℕ):ℝ) ≤ (M:ℝ) / n := Nat.cast_div_le
      rw [le_div_iff₀ hnR] at h0
      linarith
  have hg : Tendsto (fun M : ℕ => (γ - ε') * (((M / n : ℕ):ℝ) / M)^d) atTop (𝓝 ((γ - ε') * (1/(n:ℝ))^d)) :=
    (hf.pow d).const_mul _
  have hlim : (γ - ε') * (1/(n:ℝ))^d = γ / (n:ℝ)^d - ε/2 := by
    rw [one_div_pow, hε']; field_simp
  have h3 : ∀ᶠ M : ℕ in atTop, γ / (n:ℝ)^d - ε < (γ - ε') * (((M / n : ℕ):ℝ) / M)^d := by
    rw [hlim] at hg
    exact hg.eventually (lt_mem_nhds (by linarith))
  filter_upwards [h2, h3, eventually_gt_atTop 0] with M hM2 hM3 hM
  have hMR : (0:ℝ) < M := Nat.cast_pos.mpr hM
  have hMd : (0:ℝ) < (M:ℝ)^d := pow_pos hMR d
  have e1 := hM2 (M % n) (Nat.mod_lt M hn)
  rw [Nat.div_add_mod] at e1
  rw [div_pow, ← mul_div_assoc, lt_div_iff₀ hMd] at hM3
  linarith

end GlobalTheory
