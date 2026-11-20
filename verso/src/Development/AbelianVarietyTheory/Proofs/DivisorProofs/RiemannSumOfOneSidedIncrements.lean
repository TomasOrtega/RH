import Mathlib

open Filter Topology

namespace GlobalTheory

/- English proof (translation)
Take `⟨c, hc, hcd⟩` from `exists_deriv_eq_slope (fun x => s.eval x) hab s.continuous.continuousOn (fun x _ => s.differentiableAt.differentiableWithinAt)`. Rewrite `hcd` using `[Polynomial.deriv]`. Establish `hpos : 0 < b - a` using `sub_pos.mpr hab`. Establish `hsc : s.eval b - s.eval a = (b - a) * s.derivative.eval c`. Rewrite using `[hcd]`.

Clear the denominators using the available nonvanishing facts. Apply the tactic sequence `have h1 := hδ c ⟨by linarith [hc.1], by linarith [hc.2]⟩ a ⟨ha, by linarith⟩ (by rw [Real.dist_eq, abs_lt]; constructor <;> linarith [hc.1, hc.2])`. Apply the tactic sequence `have h2 := hδ c ⟨by linarith [hc.1], by linarith [hc.2]⟩ b ⟨by linarith, hb⟩ (by rw [Real.dist_eq, abs_lt]; constructor <;> linarith [hc.1, hc.2])`. Rewrite `h1`, `h2` using `[Real.dist_eq, abs_lt]`. Prove the components needed by the constructor for the conclusion.

Rewrite using `[hsc]`. Use polynomial arithmetic with `[mul_lt_mul_of_pos_left h1.1 hpos]`. Rewrite using `[hsc]`. Use polynomial arithmetic with `[mul_lt_mul_of_pos_left h2.2 hpos]`.
-/
theorem polynomial_increment_near_derivative (s : Polynomial ℝ) {η δ : ℝ}
    (hδ : ∀ x ∈ Set.Icc (0:ℝ) 1, ∀ y ∈ Set.Icc (0:ℝ) 1, dist x y < δ →
      dist (s.derivative.eval x) (s.derivative.eval y) < η)
    {a b : ℝ} (ha : 0 ≤ a) (hab : a < b) (hb : b ≤ 1) (hba : b - a < δ) :
    (b - a) * s.derivative.eval a ≤ s.eval b - s.eval a + η * (b - a) ∧
    s.eval b - s.eval a ≤ (b - a) * s.derivative.eval b + η * (b - a) := by
  obtain ⟨c, hc, hcd⟩ := exists_deriv_eq_slope (fun x => s.eval x) hab
    s.continuous.continuousOn (fun x _ => s.differentiableAt.differentiableWithinAt)
  rw [Polynomial.deriv] at hcd
  have hpos : 0 < b - a := sub_pos.mpr hab
  have hsc : s.eval b - s.eval a = (b - a) * s.derivative.eval c := by
    rw [hcd]; field_simp
  have h1 := hδ c ⟨by linarith [hc.1], by linarith [hc.2]⟩ a ⟨ha, by linarith⟩
    (by rw [Real.dist_eq, abs_lt]; constructor <;> linarith [hc.1, hc.2])
  have h2 := hδ c ⟨by linarith [hc.1], by linarith [hc.2]⟩ b ⟨by linarith, hb⟩
    (by rw [Real.dist_eq, abs_lt]; constructor <;> linarith [hc.1, hc.2])
  rw [Real.dist_eq, abs_lt] at h1 h2
  constructor
  · rw [hsc]; nlinarith [mul_lt_mul_of_pos_left h1.1 hpos]
  · rw [hsc]; nlinarith [mul_lt_mul_of_pos_left h2.2 hpos]

/- English proof (translation)
Introduce `s ℓ h`. Rewrite using `[Metric.tendsto_nhds]`. Introduce `ε hε`. Take `⟨η, hη⟩ : ∃ η : ℝ, η = ε / 4` from `⟨_, rfl⟩`. Establish `hηpos : 0 < η` using `by rw [hη]; positivity`.

Take `⟨δ, hδpos, hδ⟩` from `Metric.uniformContinuousOn_iff.mp (isCompact_Icc.uniformContinuousOn_of_continuous s.derivative.continuous.continuousOn) η hηpos`. Take `⟨n, hn⟩` from `exists_nat_gt (1 / δ)`. Establish `hnpos : (0:ℝ) < n` using `lt_trans (by positivity) hn`. Establish `hn0 : n ≠ 0` using `by exact_mod_cast hnpos.ne'`. Establish `hstep : (1:ℝ) / n < δ`.

Rewrite using `[div_lt_iff₀ hnpos]`. Rewrite `hn` using `[div_lt_iff₀ hδpos]`. Combine the linear equalities and inequalities to obtain the conclusion. Take `⟨t, ht⟩ : ∃ t : ℕ → ℚ, t = fun j : ℕ => (j : ℚ) / n` from `⟨_, rfl⟩`. Establish `ht0 : ∀ j, 0 ≤ t j` using `fun j => by rw [ht]; positivity`.

Establish `ht1 : ∀ j ≤ n, t j ≤ 1` using `fun j hj => by`. Rewrite using `[ht]`. Use `show (j:ℚ) / n ≤ 1`. Rewrite using `[div_le_one (by exact_mod_cast Nat.pos_of_ne_zero hn0)]; exact_mod_cast hj`. Establish `htR : ∀ j, ((t j : ℚ) : ℝ) = (j : ℝ) / n` using `fun j => by rw [ht]; push_cast; ring`.

Establish `hdiff : ∀ j, ((t (j+1) : ℚ) : ℝ) - t j = 1 / n` using `fun j => by`. Rewrite using `[htR, htR]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Establish `hηn : η * (1 / (n:ℝ)) = η / n` using `by ring`.

Establish `hup : ∀ᶠ m in atTop, ∀ j ∈ Finset.range n, ℓ (t j) m - ℓ (t (j+1)) m ≤ (((t (j+1)) : ℝ) - t j) * s.derivative.eval (t j : ℝ) + η / n`. Rewrite using `[Filter.eventually_all_finset]`. Introduce `j hj`. Establish `hj'` using `Finset.mem_range.mp hj`. Conclude with `h _ _ (ht0 j) (ht1 j hj'.le) (ht0 (j+1)) (ht1 (j+1) hj') _ (by positivity)`.

Establish `hlo : ∀ᶠ m in atTop, ∀ j ∈ Finset.range n, ℓ (t (j+1)) m - ℓ (t j) m ≤ (((t j) : ℝ) - t (j+1)) * s.derivative.eval (t (j+1) : ℝ) + η / n`. Rewrite using `[Filter.eventually_all_finset]`. Introduce `j hj`. Establish `hj'` using `Finset.mem_range.mp hj`. Conclude with `h _ _ (ht0 (j+1)) (ht1 (j+1) hj') (ht0 j) (ht1 j hj'.le) _ (by positivity)`.

Use `filter_upwards [hup, hlo] with m hu hl`. Establish `t0 : t 0 = 0` using `by rw [ht]; simp`. Establish `tn : t n = 1`. Rewrite using `[ht]; show (n:ℚ) / n = 1; exact div_self (by exact_mod_cast hn0)`. Establish `hsumℓ : ℓ 0 m - ℓ 1 m = ∑ j ∈ Finset.range n, (ℓ (t j) m - ℓ (t (j+1)) m)`.

Use `Finset.sum_range_sub' (fun j => ℓ (t j) m) n` as an intermediate fact. Rewrite using `[this, t0, tn]`. Establish `hsums : s.eval 1 - s.eval 0 = ∑ j ∈ Finset.range n, (s.eval (t (j+1) : ℝ) - s.eval (t j : ℝ))`. Use `Finset.sum_range_sub (fun j => s.eval (t j : ℝ)) n` as an intermediate fact. Rewrite using `[this, t0, tn]`.

Simplify using the standard rewrite rules. Establish `hstepb : ∀ j ∈ Finset.range n, |(ℓ (t j) m - ℓ (t (j+1)) m) - (s.eval (t (j+1) : ℝ) - s.eval (t j : ℝ))| ≤ 2 * (η / n)`. Introduce `j hj`. Establish `hj'` using `Finset.mem_range.mp hj`. Establish `hd` using `hdiff j`.

Establish `h1n : (0:ℝ) < 1 / n` using `by positivity`. Take `⟨k1, k2⟩` from `polynomial_increment_near_derivative s hδ (a := t j) (b := t (j+1)) (by exact_mod_cast ht0 j) (by linarith) (by exact_mod_cast ht1 _ hj') (by rw [hd]; exact hstep)`. Establish `u` using `hu j hj`. Establish `l` using `hl j hj`. Establish `hd' : ((t j : ℚ) : ℝ) - t (j+1) = -(1 / n)` using `by linarith`.

Rewrite `k1`, `k2`, `u` using `[hd]`. Rewrite `l` using `[hd']`. Rewrite `k1`, `k2` using `[hηn]`. Rewrite using `[abs_le]`. Prove the components needed by the constructor for the conclusion.

Use the polynomial consequences of the given equalities and inequalities. Use the polynomial consequences of the given equalities and inequalities. Rewrite using `[Real.dist_eq, hsumℓ, hsums, ← Finset.sum_sub_distrib]`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem riemann_sum_of_one_sided_increments : ∀ (s : Polynomial ℝ) (ℓ : ℚ → ℕ → ℝ),
    (∀ t t' : ℚ, 0 ≤ t → t ≤ 1 → 0 ≤ t' → t' ≤ 1 → ∀ ε : ℝ, 0 < ε →
      ∀ᶠ m : ℕ in atTop, ℓ t m - ℓ t' m ≤ ((t' : ℝ) - t) * s.derivative.eval (t : ℝ) + ε) →
    Tendsto (fun m => ℓ 0 m - ℓ 1 m) atTop (𝓝 (s.eval 1 - s.eval 0)) := by
  intro s ℓ h
  rw [Metric.tendsto_nhds]
  intro ε hε
  obtain ⟨η, hη⟩ : ∃ η : ℝ, η = ε / 4 := ⟨_, rfl⟩
  have hηpos : 0 < η := by rw [hη]; positivity
  obtain ⟨δ, hδpos, hδ⟩ := Metric.uniformContinuousOn_iff.mp
    (isCompact_Icc.uniformContinuousOn_of_continuous s.derivative.continuous.continuousOn) η hηpos
  obtain ⟨n, hn⟩ := exists_nat_gt (1 / δ)
  have hnpos : (0:ℝ) < n := lt_trans (by positivity) hn
  have hn0 : n ≠ 0 := by exact_mod_cast hnpos.ne'
  have hstep : (1:ℝ) / n < δ := by
    rw [div_lt_iff₀ hnpos]; rw [div_lt_iff₀ hδpos] at hn; linarith
  obtain ⟨t, ht⟩ : ∃ t : ℕ → ℚ, t = fun j : ℕ => (j : ℚ) / n := ⟨_, rfl⟩
  have ht0 : ∀ j, 0 ≤ t j := fun j => by rw [ht]; positivity
  have ht1 : ∀ j ≤ n, t j ≤ 1 := fun j hj => by
    rw [ht]; show (j:ℚ) / n ≤ 1
    rw [div_le_one (by exact_mod_cast Nat.pos_of_ne_zero hn0)]; exact_mod_cast hj
  have htR : ∀ j, ((t j : ℚ) : ℝ) = (j : ℝ) / n := fun j => by rw [ht]; push_cast; ring
  have hdiff : ∀ j, ((t (j+1) : ℚ) : ℝ) - t j = 1 / n := fun j => by
    rw [htR, htR]; push_cast; ring
  have hηn : η * (1 / (n:ℝ)) = η / n := by ring
  have hup : ∀ᶠ m in atTop, ∀ j ∈ Finset.range n, ℓ (t j) m - ℓ (t (j+1)) m ≤
      (((t (j+1)) : ℝ) - t j) * s.derivative.eval (t j : ℝ) + η / n := by
    rw [Filter.eventually_all_finset]
    intro j hj
    have hj' := Finset.mem_range.mp hj
    exact h _ _ (ht0 j) (ht1 j hj'.le) (ht0 (j+1)) (ht1 (j+1) hj') _ (by positivity)
  have hlo : ∀ᶠ m in atTop, ∀ j ∈ Finset.range n, ℓ (t (j+1)) m - ℓ (t j) m ≤
      (((t j) : ℝ) - t (j+1)) * s.derivative.eval (t (j+1) : ℝ) + η / n := by
    rw [Filter.eventually_all_finset]
    intro j hj
    have hj' := Finset.mem_range.mp hj
    exact h _ _ (ht0 (j+1)) (ht1 (j+1) hj') (ht0 j) (ht1 j hj'.le) _ (by positivity)
  filter_upwards [hup, hlo] with m hu hl
  have t0 : t 0 = 0 := by rw [ht]; simp
  have tn : t n = 1 := by
    rw [ht]; show (n:ℚ) / n = 1; exact div_self (by exact_mod_cast hn0)
  have hsumℓ : ℓ 0 m - ℓ 1 m = ∑ j ∈ Finset.range n, (ℓ (t j) m - ℓ (t (j+1)) m) := by
    have := Finset.sum_range_sub' (fun j => ℓ (t j) m) n
    rw [this, t0, tn]
  have hsums : s.eval 1 - s.eval 0 =
      ∑ j ∈ Finset.range n, (s.eval (t (j+1) : ℝ) - s.eval (t j : ℝ)) := by
    have := Finset.sum_range_sub (fun j => s.eval (t j : ℝ)) n
    rw [this, t0, tn]; simp
  have hstepb : ∀ j ∈ Finset.range n,
      |(ℓ (t j) m - ℓ (t (j+1)) m) - (s.eval (t (j+1) : ℝ) - s.eval (t j : ℝ))| ≤ 2 * (η / n) := by
    intro j hj
    have hj' := Finset.mem_range.mp hj
    have hd := hdiff j
    have h1n : (0:ℝ) < 1 / n := by positivity
    obtain ⟨k1, k2⟩ := polynomial_increment_near_derivative s hδ (a := t j) (b := t (j+1))
      (by exact_mod_cast ht0 j) (by linarith) (by exact_mod_cast ht1 _ hj') (by rw [hd]; exact hstep)
    have u := hu j hj
    have l := hl j hj
    have hd' : ((t j : ℚ) : ℝ) - t (j+1) = -(1 / n) := by linarith
    rw [hd] at k1 k2 u
    rw [hd'] at l
    rw [hηn] at k1 k2
    rw [abs_le]; constructor
    · nlinarith
    · nlinarith
  rw [Real.dist_eq, hsumℓ, hsums, ← Finset.sum_sub_distrib]
  calc |∑ j ∈ Finset.range n, ((ℓ (t j) m - ℓ (t (j+1)) m) - (s.eval (t (j+1) : ℝ) - s.eval (t j : ℝ)))|
      ≤ ∑ j ∈ Finset.range n, |(ℓ (t j) m - ℓ (t (j+1)) m) - (s.eval (t (j+1) : ℝ) - s.eval (t j : ℝ))| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ j ∈ Finset.range n, 2 * (η / n) := Finset.sum_le_sum hstepb
    _ = 2 * η := by rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; field_simp
    _ < ε := by rw [hη]; linarith

end GlobalTheory
