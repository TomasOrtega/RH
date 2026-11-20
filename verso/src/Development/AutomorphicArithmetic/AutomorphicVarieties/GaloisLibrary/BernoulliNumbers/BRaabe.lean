import Mathlib
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.BernoulliNumbers.MapGenBChar
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.BernoulliNumbers.Bcoef

open Finset UpperTheory.V.Bern

/- English proof (translation)
Introduce `N m k a hN hm`. Set `F : ℕ → ℕ → PowerSeries ℚ` to `fun M c => PowerSeries.mk fun i => bcoef M i c / (i.factorial : ℚ)`. Set `y : PowerSeries ℚ` to `PowerSeries.rescale (N : ℚ) (PowerSeries.exp ℚ)`. Set `E : PowerSeries ℚ` to `PowerSeries.rescale ((N * m : ℕ) : ℚ) (PowerSeries.exp ℚ) - 1`. Establish `hpow : ∀ j : ℕ, y ^ j = PowerSeries.rescale ((j : ℚ) * N) (PowerSeries.exp ℚ)`.

Introduce `j`. Simplify using `only [y]`. Rewrite using `[← map_pow, PowerSeries.exp_pow_eq_rescale_exp, PowerSeries.rescale_rescale]`. Establish `hE : E = (∑ j ∈ range m, y ^ j) * (y - 1)`. Rewrite using `[geom_sum_mul, hpow]`.

Simplify using `only [E]`. Use `push_cast`. Rewrite using `[mul_comm (m : ℚ)]`. Establish `hE0 : E ≠ 0`. Introduce `h`.

Establish `h1` using `congrArg (PowerSeries.coeff 1) h`. Simplify using `[E, PowerSeries.coeff_rescale, PowerSeries.coeff_exp] at h1`. Break down `h1 with h1 | h1` into its components or cases. Conclude with `hN.ne' h1`. Conclude with `hm.ne' h1`.

It suffices to establish `h : F N a = ∑ j ∈ range m, F (N * m) (a + j * N) by`. Establish `h2` using `congrArg (PowerSeries.coeff k) h`. Rewrite `h2` using `[map_sum]`. Simplify using `only [F, PowerSeries.coeff_mk] at h2`. Rewrite `h2` using `[← Finset.sum_div, div_left_inj' (by positivity)]`.

Conclude with `h2`. Apply `mul_right_cancel₀ hE0` to reduce the goal to its premises. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[b_egf N a hN]`. Use `_ = ∑ j ∈ range m, PowerSeries.X * PowerSeries.rescale ((a + j * N : ℕ) : ℚ) (PowerSeries.exp ℚ) := by`.

Rewrite using `[Finset.mul_sum]`. Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Rewrite using `[hpow, mul_assoc, PowerSeries.exp_mul_exp_eq_exp_add]`. Use `push_cast`. Both sides reduce to the same expression.

Use `_ = ∑ j ∈ range m, F (N * m) (a + j * N) * E := by`. Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Rewrite using `[b_egf (N * m) (a + j * N) (Nat.mul_pos hN hm)]`. Use `_ = (∑ j ∈ range m, F (N * m) (a + j * N)) * E := by rw [Finset.sum_mul]`.
-/
theorem UpperTheory.V.Bern.b_raabe :
    ∀ (N m k a : ℕ), 0 < N → 0 < m → bcoef N k a = ∑ j ∈ range m, bcoef (N * m) k (a + j * N) := by
  intro N m k a hN hm
  let F : ℕ → ℕ → PowerSeries ℚ := fun M c => PowerSeries.mk fun i => bcoef M i c / (i.factorial : ℚ)
  let y : PowerSeries ℚ := PowerSeries.rescale (N : ℚ) (PowerSeries.exp ℚ)
  let E : PowerSeries ℚ := PowerSeries.rescale ((N * m : ℕ) : ℚ) (PowerSeries.exp ℚ) - 1
  have hpow : ∀ j : ℕ, y ^ j = PowerSeries.rescale ((j : ℚ) * N) (PowerSeries.exp ℚ) := by
    intro j
    simp only [y]
    rw [← map_pow, PowerSeries.exp_pow_eq_rescale_exp, PowerSeries.rescale_rescale]
  have hE : E = (∑ j ∈ range m, y ^ j) * (y - 1) := by
    rw [geom_sum_mul, hpow]
    simp only [E]
    push_cast
    rw [mul_comm (m : ℚ)]
  have hE0 : E ≠ 0 := by
    intro h
    have h1 := congrArg (PowerSeries.coeff 1) h
    simp [E, PowerSeries.coeff_rescale, PowerSeries.coeff_exp] at h1
    rcases h1 with h1 | h1
    · exact hN.ne' h1
    · exact hm.ne' h1
  suffices h : F N a = ∑ j ∈ range m, F (N * m) (a + j * N) by
    have h2 := congrArg (PowerSeries.coeff k) h
    rw [map_sum] at h2
    simp only [F, PowerSeries.coeff_mk] at h2
    rw [← Finset.sum_div, div_left_inj' (by positivity)] at h2
    exact h2
  apply mul_right_cancel₀ hE0
  calc F N a * E = F N a * (y - 1) * ∑ j ∈ range m, y ^ j := by rw [hE]; ring
    _ = PowerSeries.X * PowerSeries.rescale (a : ℚ) (PowerSeries.exp ℚ) * ∑ j ∈ range m, y ^ j := by
        rw [b_egf N a hN]
    _ = ∑ j ∈ range m, PowerSeries.X * PowerSeries.rescale ((a + j * N : ℕ) : ℚ) (PowerSeries.exp ℚ) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [hpow, mul_assoc, PowerSeries.exp_mul_exp_eq_exp_add]
        push_cast
        rfl
    _ = ∑ j ∈ range m, F (N * m) (a + j * N) * E := by
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [b_egf (N * m) (a + j * N) (Nat.mul_pos hN hm)]
    _ = (∑ j ∈ range m, F (N * m) (a + j * N)) * E := by rw [Finset.sum_mul]
