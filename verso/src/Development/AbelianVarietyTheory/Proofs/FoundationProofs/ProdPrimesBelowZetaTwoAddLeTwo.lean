import Mathlib
open Filter Topology

namespace GlobalTheory

/- English proof (translation)
Proceed by induction on `M with`. Consider the case `zero => norm_num`. Consider the case `succ k ih`. Rewrite using `[show k + 1 + 2 = (k + 2) + 1 by ring, Finset.prod_Ico_succ_top (by omega), ih]`. Use `push_cast`.

Establish `h1 : (0:ℝ) < (k:ℝ) + 1` using `by positivity`. Establish `h3 : (1 - 1 / ((k:ℝ) + 2) ^ 2) = ((k:ℝ)+1)*((k:ℝ)+3) / ((k:ℝ)+2)^2` using `by field_simp; ring`. Rewrite using `[h3]`. Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree.
-/
theorem prod_Ico_inv_one_sub_inv_sq (M : ℕ) :
    ∏ n ∈ Finset.Ico 2 (M + 2), (1 - 1 / (n : ℝ) ^ 2)⁻¹ = 2 * ((M : ℝ) + 1) / ((M : ℝ) + 2) := by
  induction M with
  | zero => norm_num
  | succ k ih =>
    rw [show k + 1 + 2 = (k + 2) + 1 by ring, Finset.prod_Ico_succ_top (by omega), ih]
    push_cast
    have h1 : (0:ℝ) < (k:ℝ) + 1 := by positivity
    have h3 : (1 - 1 / ((k:ℝ) + 2) ^ 2) = ((k:ℝ)+1)*((k:ℝ)+3) / ((k:ℝ)+2)^2 := by
      field_simp; ring
    rw [h3]
    field_simp
    ring

/- English proof (translation)
Establish `hn' : (2:ℝ) ≤ n` using `by exact_mod_cast hn`. Establish `hpos : 0 < 1 / (n:ℝ)^2` using `by positivity`. Establish `hlt : 1 / (n:ℝ)^2 < 1`. Rewrite using `[div_lt_one (by positivity)]; nlinarith`. Conclude with `one_le_inv₀ (by linarith) |>.mpr (by linarith)`.
-/
theorem one_le_inv_one_sub_inv_sq {n : ℕ} (hn : 2 ≤ n) : 1 ≤ (1 - 1 / (n : ℝ) ^ 2)⁻¹ := by
  have hn' : (2:ℝ) ≤ n := by exact_mod_cast hn
  have hpos : 0 < 1 / (n:ℝ)^2 := by positivity
  have hlt : 1 / (n:ℝ)^2 < 1 := by
    rw [div_lt_one (by positivity)]; nlinarith
  exact one_le_inv₀ (by linarith) |>.mpr (by linarith)

/- English proof (translation)
Establish `hp' : (2:ℝ) ≤ p` using `by exact_mod_cast hp`. Establish `h1 : (1:ℝ) ≤ p` using `by linarith`. Establish `hle : (p:ℝ) ^ (2:ℝ) ≤ (p:ℝ) ^ (2 * (1 + s))` using `Real.rpow_le_rpow_of_exponent_le h1 (by linarith)`. Rewrite `hle` using `[Real.rpow_two]`. Establish `hsq : (4:ℝ) ≤ (p:ℝ)^2` using `by nlinarith`.

Establish `hlt : 1 / (p:ℝ)^2 < 1` using `by rw [div_lt_one (by positivity)]; linarith`. Apply `inv_anti₀` to reduce the goal to its premises. Combine the linear equalities and inequalities to obtain the conclusion. Establish `: 1 / (p:ℝ) ^ (2 * (1 + s)) ≤ 1 / (p:ℝ)^2` using `one_div_le_one_div_of_le (by positivity) hle`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem factor_le (s : ℝ) (hs : 0 ≤ s) {p : ℕ} (hp : 2 ≤ p) :
    (1 - 1 / (p : ℝ) ^ (2 * (1 + s)))⁻¹ ≤ (1 - 1 / (p : ℝ) ^ 2)⁻¹ := by
  have hp' : (2:ℝ) ≤ p := by exact_mod_cast hp
  have h1 : (1:ℝ) ≤ p := by linarith
  have hle : (p:ℝ) ^ (2:ℝ) ≤ (p:ℝ) ^ (2 * (1 + s)) :=
    Real.rpow_le_rpow_of_exponent_le h1 (by linarith)
  rw [Real.rpow_two] at hle
  have hsq : (4:ℝ) ≤ (p:ℝ)^2 := by nlinarith
  have hlt : 1 / (p:ℝ)^2 < 1 := by rw [div_lt_one (by positivity)]; linarith
  apply inv_anti₀
  · linarith
  · have : 1 / (p:ℝ) ^ (2 * (1 + s)) ≤ 1 / (p:ℝ)^2 :=
      one_div_le_one_div_of_le (by positivity) hle
    linarith

/- English proof (translation)
Introduce `s hs N`. Establish `hsub : N.primesBelow ⊆ Finset.Ico 2 (N + 2)`. Introduce `p hp`. Rewrite `hp` using `[Nat.mem_primesBelow]`. Rewrite using `[Finset.mem_Ico]`.

Conclude with `⟨hp.2.two_le, by omega⟩`. Establish `hmem : ∀ p ∈ N.primesBelow, 2 ≤ p` using `fun p hp => (Nat.prime_of_mem_primesBelow hp).two_le`. Combine the equalities or inequalities in the displayed calculation. Apply `Finset.prod_le_prod` to reduce the goal to its premises. Introduce `p hp`.

Use `one_le_inv_one_sub_inv_sq (hmem p hp)` as an intermediate fact. Establish `h2` using `factor_le s hs (hmem p hp)`. Establish `hp' : (2:ℝ) ≤ p` using `by exact_mod_cast hmem p hp`. Establish `hle : (p:ℝ) ^ (2:ℝ) ≤ (p:ℝ) ^ (2 * (1 + s))` using `Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)`. Establish `hpos : 0 < (p:ℝ) ^ (2 * (1 + s))` using `by positivity`.

Establish `hlt : 1 / (p:ℝ) ^ (2 * (1 + s)) < 1`. Rewrite using `[div_lt_one hpos]`. Rewrite `hle` using `[Real.rpow_two]`. Use the polynomial consequences of the given equalities and inequalities. Conclude with `inv_nonneg.mpr (by linarith)`.

Introduce `p hp`. Conclude with `factor_le s hs (hmem p hp)`. Use `_ ≤ ∏ n ∈ Finset.Ico 2 (N + 2), (1 - 1 / (n : ℝ) ^ 2)⁻¹ := by`. Rewrite using `[← Finset.prod_sdiff hsub]`. Establish `h0 : 0 ≤ ∏ p ∈ N.primesBelow, (1 - 1 / (p : ℝ) ^ 2)⁻¹` using `Finset.prod_nonneg fun p hp => le_trans zero_le_one (one_le_inv_one_sub_inv_sq (hmem p hp))`.

Establish `h1 : 1 ≤ ∏ n ∈ Finset.Ico 2 (N + 2) \ N.primesBelow, (1 - 1 / (n : ℝ) ^ 2)⁻¹`. Apply `Finset.one_le_prod` to reduce the goal to its premises. Introduce `n hn`. Conclude with `one_le_inv_one_sub_inv_sq (Finset.mem_Ico.mp (Finset.mem_sdiff.mp hn).1).1`. Use the polynomial consequences of the given equalities and inequalities.

Use `_ = 2 * ((N : ℝ) + 1) / ((N : ℝ) + 2) := prod_Ico_inv_one_sub_inv_sq N`. Use `_ ≤ 2 := by rw [div_le_iff₀ (by positivity)]; linarith`.
-/
theorem prod_primesBelow_zeta_two_add_le_two :
    ∀ (s : ℝ), 0 ≤ s → ∀ N : ℕ, ∏ p ∈ N.primesBelow, (1 - 1 / (p : ℝ) ^ (2 * (1 + s)))⁻¹ ≤ 2 := by
  intro s hs N
  have hsub : N.primesBelow ⊆ Finset.Ico 2 (N + 2) := by
    intro p hp
    rw [Nat.mem_primesBelow] at hp
    rw [Finset.mem_Ico]
    exact ⟨hp.2.two_le, by omega⟩
  have hmem : ∀ p ∈ N.primesBelow, 2 ≤ p := fun p hp => (Nat.prime_of_mem_primesBelow hp).two_le
  calc ∏ p ∈ N.primesBelow, (1 - 1 / (p : ℝ) ^ (2 * (1 + s)))⁻¹
      ≤ ∏ p ∈ N.primesBelow, (1 - 1 / (p : ℝ) ^ 2)⁻¹ := by
        apply Finset.prod_le_prod
        · intro p hp
          have := one_le_inv_one_sub_inv_sq (hmem p hp)
          have h2 := factor_le s hs (hmem p hp)

          have hp' : (2:ℝ) ≤ p := by exact_mod_cast hmem p hp
          have hle : (p:ℝ) ^ (2:ℝ) ≤ (p:ℝ) ^ (2 * (1 + s)) :=
            Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)
          have hpos : 0 < (p:ℝ) ^ (2 * (1 + s)) := by positivity
          have hlt : 1 / (p:ℝ) ^ (2 * (1 + s)) < 1 := by
            rw [div_lt_one hpos]; rw [Real.rpow_two] at hle; nlinarith
          exact inv_nonneg.mpr (by linarith)
        · intro p hp; exact factor_le s hs (hmem p hp)
    _ ≤ ∏ n ∈ Finset.Ico 2 (N + 2), (1 - 1 / (n : ℝ) ^ 2)⁻¹ := by
        rw [← Finset.prod_sdiff hsub]
        have h0 : 0 ≤ ∏ p ∈ N.primesBelow, (1 - 1 / (p : ℝ) ^ 2)⁻¹ :=
          Finset.prod_nonneg fun p hp => le_trans zero_le_one (one_le_inv_one_sub_inv_sq (hmem p hp))
        have h1 : 1 ≤ ∏ n ∈ Finset.Ico 2 (N + 2) \ N.primesBelow, (1 - 1 / (n : ℝ) ^ 2)⁻¹ := by
          apply Finset.one_le_prod
          intro n hn
          exact one_le_inv_one_sub_inv_sq (Finset.mem_Ico.mp (Finset.mem_sdiff.mp hn).1).1
        nlinarith
    _ = 2 * ((N : ℝ) + 1) / ((N : ℝ) + 2) := prod_Ico_inv_one_sub_inv_sq N
    _ ≤ 2 := by rw [div_le_iff₀ (by positivity)]; linarith

end GlobalTheory
