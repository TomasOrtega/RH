import Mathlib
open NumberField

namespace GlobalTheory

/- English proof (translation)
Assume the negation of the conclusion as `hlt`. Use `push_neg at hlt`. Break down `Nat.eq_zero_or_pos y with hy | hy` into its components or cases. Substitute `hy` using the available equality. Use `h 1` as an intermediate fact.

Simplify using `at this`. Use linear arithmetic over natural numbers and integers. Establish `hyR : (0:ℝ) < y` using `by exact_mod_cast hy`. Establish `hq : (1:ℝ) < (x:ℝ) / y`. Rewrite using `[one_lt_div hyR]`.

Conclude with `hlt` after adjusting the coercions. Take `⟨j, hj⟩` from `((tendsto_pow_atTop_atTop_of_one_lt hq).eventually_gt_atTop (C:ℝ)).exists`. Establish `h1 : ((x:ℝ))^j ≤ C * (y:ℝ)^j` using `by exact_mod_cast h j`. Rewrite `hj` using `[div_pow, lt_div_iff₀ (pow_pos hyR j)]`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem nat_le_of_forall_pow_le_mul_pow (x y C : ℕ) (h : ∀ j, x ^ j ≤ C * y ^ j) : x ≤ y := by
  by_contra hlt
  push_neg at hlt
  rcases Nat.eq_zero_or_pos y with hy | hy
  · subst hy
    have := h 1
    simp at this
    omega
  · have hyR : (0:ℝ) < y := by exact_mod_cast hy
    have hq : (1:ℝ) < (x:ℝ) / y := by
      rw [one_lt_div hyR]; exact_mod_cast hlt
    obtain ⟨j, hj⟩ := ((tendsto_pow_atTop_atTop_of_one_lt hq).eventually_gt_atTop (C:ℝ)).exists
    have h1 : ((x:ℝ))^j ≤ C * (y:ℝ)^j := by exact_mod_cast h j
    rw [div_pow, lt_div_iff₀ (pow_pos hyR j)] at hj
    linarith

/- English proof (translation)
Introduce `g e C B he h0 hpos hlc hblk hgr`. Use `set r : ℕ → ℝ := fun k => (g (k+1) : ℝ) / g k with hr`. Establish `gpos : ∀ n, (0:ℝ) < g n` using `fun n => by exact_mod_cast hpos n`. Establish `rpos : ∀ k, 0 < r k` using `fun k => div_pos (gpos _) (gpos _)`. Establish `rstep : ∀ k, r (k+1) ≤ r k`.

Introduce `k`. Simplify using `only [hr]`. Rewrite using `[div_le_div_iff₀ (gpos _) (gpos _)]`. Establish `h1 : ((g (k+2) : ℝ)) * g k ≤ (g (k+1):ℝ)^2` using `by exact_mod_cast hlc k`. Establish `h2 : k + 1 + 1 = k + 2` using `by ring`.

Rewrite using `[h2]`. Use polynomial arithmetic with `[h1]`. Establish `ranti : Antitone r` using `antitone_nat_of_succ_le rstep`. Establish `gmul : ∀ a n, (g (a + n) : ℝ) = g a * ∏ i ∈ Finset.range n, r (a + i)`. Introduce `a n`.

Proceed by induction on `n with`. Consider the case `zero => simp`. Consider the case `succ n ih`. Rewrite using `[Finset.prod_range_succ, ← mul_assoc, ← ih]`. Simplify using `only [hr]`.

Rewrite using `[← add_assoc]`. Clear denominators, using `[(gpos (a+n)).ne']` for the nonvanishing conditions. Establish `g0 : (g 0 : ℝ) = 1` using `by exact_mod_cast h0`. Establish `ge : (g e : ℝ) = ∏ i ∈ Finset.range e, r i`. Use `gmul 0 e` as an intermediate fact.

Simplify `this` using `[g0]`. Establish `g2e : (g (e + e) : ℝ) = g e * g e`. Use `hblk 1` as an intermediate fact. Establish `h2 : e * (1+1) = e + e` using `by ring`. Rewrite `this` using `[h2, mul_one]`.

Conclude with `this` after adjusting the coercions. Establish `hprodeq : ∏ i ∈ Finset.range e, r (e + i) = ∏ i ∈ Finset.range e, r i`. Use `gmul e e` as an intermediate fact. Rewrite `this` using `[g2e]`. Establish `hne : (g e : ℝ) ≠ 0` using `(gpos e).ne'`.

Rewrite using `[← ge]`. Conclude with `(mul_left_cancel₀ hne this).symm`. Establish `hre : r e = r 0`. Apply `le_antisymm (ranti (Nat.zero_le e))` to reduce the goal to its premises. Assume the negation of the conclusion as `hlt`.

Use `push_neg at hlt`. Establish `: ∏ i ∈ Finset.range e, r (e + i) < ∏ i ∈ Finset.range e, r i`. Apply `Finset.prod_lt_prod` to reduce the goal to its premises. Introduce `i _`. Conclude with `rpos _`.

Introduce `i _; exact ranti (by omega)`. Conclude with `⟨0, Finset.mem_range.2 (by omega), by simpa using hlt⟩`. Rewrite `this` using `[hprodeq]`. Conclude with `lt_irrefl _ this`. Establish `hconst : ∀ i ∈ Finset.range e, r i = r 0`.

Introduce `i hi`. Establish `hi'` using `Finset.mem_range.1 hi`. Apply `le_antisymm (ranti (Nat.zero_le i))` to reduce the goal to its premises. Rewrite using `[← hre]; exact ranti (by omega)`. Establish `r0 : r 0 = g 1` using `by simp [hr, g0]`.

Establish `geR : (g e : ℝ) = (g 1 : ℝ) ^ e`. Rewrite using `[ge, Finset.prod_congr rfl hconst, Finset.prod_const, Finset.card_range, r0]`. Establish `geN : g e = g 1 ^ e` using `by exact_mod_cast geR`. Establish `gej : ∀ j, g (e * j) = (g 1 ^ e) ^ j`. Introduce `j`.

Proceed by induction on `j with`. Consider the case `zero => simp [h0]`. Consider the case `succ j ih => rw [hblk, ih, geN, pow_succ]`. Establish `hpow : g 1 ^ e ≤ B ^ e`. Apply `nat_le_of_forall_pow_le_mul_pow _ _ C` to reduce the goal to its premises.

Introduce `j`. Rewrite using `[← gej, ← pow_mul]`. Conclude with `hgr _`. Conclude with `(pow_le_pow_iff_left₀ (Nat.zero_le _) (Nat.zero_le _) (by omega : e ≠ 0)).1 hpow`.
-/
theorem first_term_le_of_logConcave_blocks :
    ∀ (g : ℕ → ℕ) (e C B : ℕ), 1 ≤ e → g 0 = 1 → (∀ n, 0 < g n) →
    (∀ k, g (k + 2) * g k ≤ g (k + 1) ^ 2) → (∀ j, g (e * (j + 1)) = g (e * j) * g e) →
    (∀ n, g n ≤ C * B ^ n) → g 1 ≤ B := by
  intro g e C B he h0 hpos hlc hblk hgr
  set r : ℕ → ℝ := fun k => (g (k+1) : ℝ) / g k with hr
  have gpos : ∀ n, (0:ℝ) < g n := fun n => by exact_mod_cast hpos n
  have rpos : ∀ k, 0 < r k := fun k => div_pos (gpos _) (gpos _)
  have rstep : ∀ k, r (k+1) ≤ r k := by
    intro k
    simp only [hr]
    rw [div_le_div_iff₀ (gpos _) (gpos _)]
    have h1 : ((g (k+2) : ℝ)) * g k ≤ (g (k+1):ℝ)^2 := by exact_mod_cast hlc k
    have h2 : k + 1 + 1 = k + 2 := by ring
    rw [h2]; nlinarith [h1]
  have ranti : Antitone r := antitone_nat_of_succ_le rstep
  have gmul : ∀ a n, (g (a + n) : ℝ) = g a * ∏ i ∈ Finset.range n, r (a + i) := by
    intro a n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [Finset.prod_range_succ, ← mul_assoc, ← ih]
      simp only [hr]
      rw [← add_assoc]
      field_simp [(gpos (a+n)).ne']
  have g0 : (g 0 : ℝ) = 1 := by exact_mod_cast h0
  have ge : (g e : ℝ) = ∏ i ∈ Finset.range e, r i := by
    have := gmul 0 e; simpa [g0] using this
  have g2e : (g (e + e) : ℝ) = g e * g e := by
    have := hblk 1
    have h2 : e * (1+1) = e + e := by ring
    rw [h2, mul_one] at this
    exact_mod_cast this
  have hprodeq : ∏ i ∈ Finset.range e, r (e + i) = ∏ i ∈ Finset.range e, r i := by
    have := gmul e e
    rw [g2e] at this
    have hne : (g e : ℝ) ≠ 0 := (gpos e).ne'
    rw [← ge]
    exact (mul_left_cancel₀ hne this).symm
  have hre : r e = r 0 := by
    apply le_antisymm (ranti (Nat.zero_le e))
    by_contra hlt
    push_neg at hlt
    have : ∏ i ∈ Finset.range e, r (e + i) < ∏ i ∈ Finset.range e, r i := by
      apply Finset.prod_lt_prod
      · intro i _; exact rpos _
      · intro i _; exact ranti (by omega)
      · exact ⟨0, Finset.mem_range.2 (by omega), by simpa using hlt⟩
    rw [hprodeq] at this
    exact lt_irrefl _ this
  have hconst : ∀ i ∈ Finset.range e, r i = r 0 := by
    intro i hi
    have hi' := Finset.mem_range.1 hi
    apply le_antisymm (ranti (Nat.zero_le i))
    rw [← hre]; exact ranti (by omega)
  have r0 : r 0 = g 1 := by simp [hr, g0]
  have geR : (g e : ℝ) = (g 1 : ℝ) ^ e := by
    rw [ge, Finset.prod_congr rfl hconst, Finset.prod_const, Finset.card_range, r0]
  have geN : g e = g 1 ^ e := by exact_mod_cast geR
  have gej : ∀ j, g (e * j) = (g 1 ^ e) ^ j := by
    intro j
    induction j with
    | zero => simp [h0]
    | succ j ih => rw [hblk, ih, geN, pow_succ]
  have hpow : g 1 ^ e ≤ B ^ e := by
    apply nat_le_of_forall_pow_le_mul_pow _ _ C
    intro j
    rw [← gej, ← pow_mul]
    exact hgr _
  exact (pow_le_pow_iff_left₀ (Nat.zero_le _) (Nat.zero_le _) (by omega : e ≠ 0)).1 hpow

end GlobalTheory
