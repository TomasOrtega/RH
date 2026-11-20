import Mathlib

open Matrix
open scoped ComplexOrder

/- English proof (translation)
Introduce `ι _ _ G hG hc`. Rewrite using `[Matrix.posSemidef_iff_dotProduct_mulVec]`. Use `⟨hG, fun x => ?_⟩` and prove the remaining obligations. Simplify using `only [star_trivial]`. Set `Q : (ι → ℝ) → ℝ` to `fun v => v ⬝ᵥ (G *ᵥ v)`.

Establish `hQ : Continuous Q`. Simplify using `only [Q, dotProduct, mulVec]`. Use `fun_prop`. Set `u : ℕ → ι → ℝ` to `fun n i => (⌊(n : ℝ) * x i⌋ : ℝ) / n`. Establish `hu : Filter.Tendsto u Filter.atTop (nhds x)`.

Rewrite using `[tendsto_pi_nhds]`. Introduce `i`. Establish `h1 : Filter.Tendsto (fun n : ℕ => x i - 1 / (n : ℝ)) Filter.atTop (nhds (x i))`. Establish `h2` using `(tendsto_const_nhds (x := x i)).sub (tendsto_one_div_atTop_nhds_zero_nat (𝕜 := ℝ))`. Simplify using `using h2`.

Use `tendsto_of_tendsto_of_tendsto_of_le_of_le' h1 tendsto_const_nhds ?_ ?_` and prove the remaining obligations. Use `filter_upwards [Filter.eventually_gt_atTop 0] with n hn`. Establish `hn' : (0 : ℝ) < n` using `by exact_mod_cast hn`. Simplify using `only [u]`. Rewrite using `[le_div_iff₀ hn']`.

Use `Int.sub_one_lt_floor ((n : ℝ) * x i)` as an intermediate fact. Establish `e : (x i - 1 / n) * n = n * x i - 1` using `by field_simp`. Rewrite using `[e]`. Combine the linear equalities and inequalities to obtain the conclusion. Use `filter_upwards [Filter.eventually_gt_atTop 0] with n hn`.

Establish `hn' : (0 : ℝ) < n` using `by exact_mod_cast hn`. Simplify using `only [u]`. Rewrite using `[div_le_iff₀ hn']`. Use `Int.floor_le ((n : ℝ) * x i)` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion.

Establish `hnn : ∀ n, 0 ≤ Q (u n)`. Introduce `n`. Establish `h` using `hc (fun i => ⌊(n : ℝ) * x i⌋)`. Establish `e : u n = (1 / (n : ℝ)) • (fun i => ((⌊(n : ℝ) * x i⌋ : ℤ) : ℝ))`. Use function extensionality and compare the values at `i`.

Simplify using `[u, div_eq_inv_mul]`. Establish `h0 : 0 ≤ 1 / (n : ℝ)` using `by positivity`. Simplify using `only [Q, e, Matrix.mulVec_smul, dotProduct_smul, smul_dotProduct, smul_eq_mul]`. Conclude with `mul_nonneg h0 (mul_nonneg h0 h)`. Conclude with `ge_of_tendsto' ((hQ.tendsto x).comp hu) hnn`.
-/
theorem UpperTheory.V.KT.grampsd :
    ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (G : Matrix ι ι ℝ), G.IsHermitian →
    (∀ c : ι → ℤ, 0 ≤ (fun i => (c i : ℝ)) ⬝ᵥ (G *ᵥ fun i => (c i : ℝ))) → G.PosSemidef := by
  intro ι _ _ G hG hc
  rw [Matrix.posSemidef_iff_dotProduct_mulVec]
  refine ⟨hG, fun x => ?_⟩
  simp only [star_trivial]
  let Q : (ι → ℝ) → ℝ := fun v => v ⬝ᵥ (G *ᵥ v)
  have hQ : Continuous Q := by
    simp only [Q, dotProduct, mulVec]
    fun_prop
  let u : ℕ → ι → ℝ := fun n i => (⌊(n : ℝ) * x i⌋ : ℝ) / n
  have hu : Filter.Tendsto u Filter.atTop (nhds x) := by
    rw [tendsto_pi_nhds]
    intro i
    have h1 : Filter.Tendsto (fun n : ℕ => x i - 1 / (n : ℝ)) Filter.atTop (nhds (x i)) := by
      have h2 := (tendsto_const_nhds (x := x i)).sub (tendsto_one_div_atTop_nhds_zero_nat (𝕜 := ℝ))
      simpa using h2
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' h1 tendsto_const_nhds ?_ ?_
    · filter_upwards [Filter.eventually_gt_atTop 0] with n hn
      have hn' : (0 : ℝ) < n := by exact_mod_cast hn
      simp only [u]
      rw [le_div_iff₀ hn']
      have := Int.sub_one_lt_floor ((n : ℝ) * x i)
      have e : (x i - 1 / n) * n = n * x i - 1 := by field_simp
      rw [e]
      linarith
    · filter_upwards [Filter.eventually_gt_atTop 0] with n hn
      have hn' : (0 : ℝ) < n := by exact_mod_cast hn
      simp only [u]
      rw [div_le_iff₀ hn']
      have := Int.floor_le ((n : ℝ) * x i)
      linarith
  have hnn : ∀ n, 0 ≤ Q (u n) := by
    intro n
    have h := hc (fun i => ⌊(n : ℝ) * x i⌋)
    have e : u n = (1 / (n : ℝ)) • (fun i => ((⌊(n : ℝ) * x i⌋ : ℤ) : ℝ)) := by
      funext i
      simp [u, div_eq_inv_mul]
    have h0 : 0 ≤ 1 / (n : ℝ) := by positivity
    simp only [Q, e, Matrix.mulVec_smul, dotProduct_smul, smul_dotProduct, smul_eq_mul]
    exact mul_nonneg h0 (mul_nonneg h0 h)
  exact ge_of_tendsto' ((hQ.tendsto x).comp hu) hnn
