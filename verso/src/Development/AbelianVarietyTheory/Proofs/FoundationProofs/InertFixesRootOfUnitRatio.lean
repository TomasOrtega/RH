import Development.AbelianVarietyTheory.Definitions.Foundations.IsFirstChernClassOfLineBundle
open GlobalTheory.NeedB Polynomial

namespace GlobalTheory

/- English proof (translation)
Introduce `hN hvN hin hgc hc hgθ hvθ`. Use `set v := B.valuation`. Distinguish the cases in `hθ : θ = 0`. Simplify using `[hθ]`. Use `set u := θ / c with hu`.

Establish `hu0 : u ≠ 0` using `div_ne_zero hθ hc`. Establish `hvu : v u = 1`. Establish `h1 : v u ^ N = 1` using `by rw [← map_pow, hu, div_pow]; exact hvθ`. Conclude with `(pow_eq_one_iff_left (Nat.pos_iff_ne_zero.mp hN)).mp h1`. Establish `hgu : g u = g θ / c` using `by rw [hu, map_div₀, hgc]`.

Establish `hguN : (g u) ^ N = u ^ N`. Rewrite using `[← map_pow, hu, div_pow, map_div₀, map_pow g c, hgc, hgθ]`. Use `set ξ := g u / u with hξ`. Establish `hξN : ξ ^ N = 1` using `by rw [hξ, div_pow, hguN, div_self (pow_ne_zero _ hu0)]`. Establish `hvξ1 : v (ξ - 1) < 1`.

Establish `h2 : ξ - 1 = (g u - u) / u` using `by rw [hξ, sub_div, div_self hu0]`. Rewrite using `[h2, map_div₀, hvu, div_one]`. Conclude with `hin u hvu.le`. Establish `hvξ : v ξ ≤ 1`. Establish `: ξ = (ξ - 1) + 1` using `by ring`.

Rewrite using `[this]`. Conclude with `(Valuation.map_add v _ _).trans (max_le hvξ1.le (by simp))`. Establish `hpow : ∀ j : ℕ, v (ξ ^ j - 1) < 1`. Introduce `j`. Establish `h3 : ξ ^ j - 1 = (∑ i ∈ Finset.range j, ξ ^ i) * (ξ - 1)` using `(geom_sum_mul ξ j).symm`.

Rewrite using `[h3, map_mul]`. Establish `h4 : v (∑ i ∈ Finset.range j, ξ ^ i) ≤ 1` using `Valuation.map_sum_le v (fun i _ => by rw [map_pow]; exact pow_le_one' hvξ i)`. Combine the equalities or inequalities in the displayed calculation. Use `set S := ∑ i ∈ Finset.range N, ξ ^ i with hS`. Establish `hSN : S - (N : Ω) = ∑ i ∈ Finset.range N, (ξ ^ i - 1)`.

Rewrite using `[hS, Finset.sum_sub_distrib]`. Simplify using the standard rewrite rules. Establish `hvSN : v (S - (N : Ω)) < 1`. Rewrite using `[hSN]`. Conclude with `Valuation.map_sum_lt v one_ne_zero (fun i _ => hpow i)`.

Establish `hS0 : S ≠ 0`. Introduce `h0`. Rewrite `hvSN` using `[h0, zero_sub, Valuation.map_neg, hvN]`. Conclude with `lt_irrefl _ hvSN`. Establish `hmul : S * (ξ - 1) = 0` using `by rw [hS, geom_sum_mul, hξN, sub_self]`.

Establish `hξ1 : ξ = 1`. Break down `mul_eq_zero.mp hmul with h | h` into its components or cases. Conclude with `absurd h hS0`. Conclude with `sub_eq_zero.mp h`. Establish `: g u = u`.

Rewrite `hξ1` using `[hξ, div_eq_one_iff_eq hu0]`. Conclude with `hξ1`. Rewrite `this` using `[hgu, hu]`. Conclude with `(div_left_inj' hc).mp this`.
-/
theorem inert_fixes_root_of_unit_ratio (K Ω : Type) [Field K] [Field Ω] [Algebra K Ω] (B : ValuationSubring Ω)
    (g : Ω ≃ₐ[K] Ω) (N : ℕ) (c θ : Ω) :
    0 < N → B.valuation (N : Ω) = 1 → Inert B g → g c = c → c ≠ 0 → g (θ ^ N) = θ ^ N →
      B.valuation (θ ^ N / c ^ N) = 1 → g θ = θ := by
  intro hN hvN hin hgc hc hgθ hvθ
  set v := B.valuation
  by_cases hθ : θ = 0
  · simp [hθ]
  set u := θ / c with hu
  have hu0 : u ≠ 0 := div_ne_zero hθ hc
  have hvu : v u = 1 := by
    have h1 : v u ^ N = 1 := by rw [← map_pow, hu, div_pow]; exact hvθ
    exact (pow_eq_one_iff_left (Nat.pos_iff_ne_zero.mp hN)).mp h1
  have hgu : g u = g θ / c := by rw [hu, map_div₀, hgc]
  have hguN : (g u) ^ N = u ^ N := by
    rw [← map_pow, hu, div_pow, map_div₀, map_pow g c, hgc, hgθ]
  set ξ := g u / u with hξ
  have hξN : ξ ^ N = 1 := by rw [hξ, div_pow, hguN, div_self (pow_ne_zero _ hu0)]
  have hvξ1 : v (ξ - 1) < 1 := by
    have h2 : ξ - 1 = (g u - u) / u := by rw [hξ, sub_div, div_self hu0]
    rw [h2, map_div₀, hvu, div_one]
    exact hin u hvu.le
  have hvξ : v ξ ≤ 1 := by
    have : ξ = (ξ - 1) + 1 := by ring
    rw [this]
    exact (Valuation.map_add v _ _).trans (max_le hvξ1.le (by simp))
  have hpow : ∀ j : ℕ, v (ξ ^ j - 1) < 1 := by
    intro j
    have h3 : ξ ^ j - 1 = (∑ i ∈ Finset.range j, ξ ^ i) * (ξ - 1) := (geom_sum_mul ξ j).symm
    rw [h3, map_mul]
    have h4 : v (∑ i ∈ Finset.range j, ξ ^ i) ≤ 1 :=
      Valuation.map_sum_le v (fun i _ => by rw [map_pow]; exact pow_le_one' hvξ i)
    calc v (∑ i ∈ Finset.range j, ξ ^ i) * v (ξ - 1) ≤ 1 * v (ξ - 1) := mul_le_mul_left h4 _
      _ = v (ξ - 1) := one_mul _
      _ < 1 := hvξ1
  set S := ∑ i ∈ Finset.range N, ξ ^ i with hS
  have hSN : S - (N : Ω) = ∑ i ∈ Finset.range N, (ξ ^ i - 1) := by
    rw [hS, Finset.sum_sub_distrib]; simp
  have hvSN : v (S - (N : Ω)) < 1 := by
    rw [hSN]; exact Valuation.map_sum_lt v one_ne_zero (fun i _ => hpow i)
  have hS0 : S ≠ 0 := by
    intro h0
    rw [h0, zero_sub, Valuation.map_neg, hvN] at hvSN
    exact lt_irrefl _ hvSN
  have hmul : S * (ξ - 1) = 0 := by rw [hS, geom_sum_mul, hξN, sub_self]
  have hξ1 : ξ = 1 := by
    rcases mul_eq_zero.mp hmul with h | h
    · exact absurd h hS0
    · exact sub_eq_zero.mp h
  have : g u = u := by
    rw [hξ, div_eq_one_iff_eq hu0] at hξ1; exact hξ1
  rw [hgu, hu] at this
  exact (div_left_inj' hc).mp this

end GlobalTheory
