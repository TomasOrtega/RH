import Mathlib
import Formalism.LocalRingCardinality.DataParams₂
open Formalism.BasicNotions

namespace GlobalTheory

/- English proof (translation)
Establish `hn : D.R.n0 ≤ D.R.n`. Establish `h : addOrderOf D.R.toFrame.a0 ≤ Fintype.card D.R.toFrame.A` using `addOrderOf_le_card_univ`. Rewrite `h` using `[D.R.toFrame.card_A]`. Conclude with `h`. Use `set n := D.R.n with hn'`.

Use `set Lw := D.host.Lw with hLw`. Establish `hL2 : 2 ≤ Lw` using `D.host.two_le_Lw`. Establish `hrange : ∀ s ∈ D.host.T2, 4 * Lw * s < n`. Introduce `s hs`. Conclude with `lt_of_lt_of_le (D.host.second_set_range s hs) hn`.

Use `set N := (n - 1) / (4 * Lw) + 1 with hN`. Establish `hsub : D.host.T2 ⊆ Finset.range N`. Introduce `s hs`. Establish `h` using `hrange s hs`. Rewrite using `[Finset.mem_range, hN, Nat.lt_succ_iff, Nat.le_div_iff_mul_le (by omega)]`.

Establish `: s * (4 * Lw) = 4 * Lw * s` using `by ring`. Use linear arithmetic over natural numbers and integers. Establish `hN3 : 3 ≤ N`. Establish `: 2 ≤ (n - 1) / (4 * Lw)`. Rewrite using `[Nat.le_div_iff_mul_le (by omega)]; omega`.

Use linear arithmetic over natural numbers and integers. Establish `hne : ¬ Finset.range N ⊆ D.host.T2`. Introduce `hs`. Establish `h0 : 0 ∈ D.host.T2` using `hs (Finset.mem_range.2 (by omega))`. Establish `h1 : 1 ∈ D.host.T2` using `hs (Finset.mem_range.2 (by omega))`.

Establish `h2 : 2 ∈ D.host.T2` using `hs (Finset.mem_range.2 (by omega))`. Establish `hnr` using `D.host.second_set_no_relation`. Establish `hL2' : (2 : ℤ) ≤ (Lw : ℤ)` using `by exact_mod_cast hL2`. Conclude with `hnr 0 h0 1 h1 2 h2 (by norm_num) (by norm_num) (by norm_num) 1 2 (by norm_num) (by simp; omega) (by norm_num) (by rw [abs_of_pos (by norm_num)]; exact hL2') (by norm_num) (by norm_num)`. Establish `hcard : D.host.T2.card ≤ (n - 1) / (4 * Lw)`.

Establish `h1 : D.host.T2.card ≤ N` using `by simpa using Finset.card_le_card hsub`. Establish `h2 : D.host.T2.card ≠ N`. Introduce `heq`. Conclude with `hne (Finset.eq_of_subset_of_card_le hsub (by simp [heq])).symm.subset`. Use linear arithmetic over natural numbers and integers.

Establish `hmul : D.host.T2.card * (4 * Lw) < n`. Use `(Nat.le_div_iff_mul_le (by omega)).1 hcard` as an intermediate fact. Use linear arithmetic over natural numbers and integers. Establish `hnpos : (0 : ℝ) < n` using `by exact_mod_cast (show 0 < n by omega)`. Establish `hLpos : (0 : ℝ) < 4 * (Lw : ℝ)`.

Establish `: (2 : ℝ) ≤ Lw` using `by exact_mod_cast hL2`. Combine the linear equalities and inequalities to obtain the conclusion. Rewrite using `[L.typeDensity_eq_card_div, div_le_div_iff₀ hnpos hLpos, one_mul]`. Establish `: ((D.host.T2.card * (4 * Lw) : ℕ) : ℝ) ≤ (n : ℝ)` using `by exact_mod_cast hmul.le`. Move the coercions through the operations in `at this`.

Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem thick_density_le (D : D7) (L : SizeData₂ D) (h8 : 8 * D.host.Lw < D.R.n) :
    L.de2 ≤ 1 / (4 * (D.host.Lw : ℝ)) := by
  have hn : D.R.n0 ≤ D.R.n := by
    have h : addOrderOf D.R.toFrame.a0 ≤ Fintype.card D.R.toFrame.A := addOrderOf_le_card_univ
    rw [D.R.toFrame.card_A] at h
    exact h
  set n := D.R.n with hn'
  set Lw := D.host.Lw with hLw
  have hL2 : 2 ≤ Lw := D.host.two_le_Lw
  have hrange : ∀ s ∈ D.host.T2, 4 * Lw * s < n := by
    intro s hs; exact lt_of_lt_of_le (D.host.second_set_range s hs) hn
  set N := (n - 1) / (4 * Lw) + 1 with hN
  have hsub : D.host.T2 ⊆ Finset.range N := by
    intro s hs
    have h := hrange s hs
    rw [Finset.mem_range, hN, Nat.lt_succ_iff, Nat.le_div_iff_mul_le (by omega)]
    have : s * (4 * Lw) = 4 * Lw * s := by ring
    omega
  have hN3 : 3 ≤ N := by
    have : 2 ≤ (n - 1) / (4 * Lw) := by
      rw [Nat.le_div_iff_mul_le (by omega)]; omega
    omega
  have hne : ¬ Finset.range N ⊆ D.host.T2 := by
    intro hs
    have h0 : 0 ∈ D.host.T2 := hs (Finset.mem_range.2 (by omega))
    have h1 : 1 ∈ D.host.T2 := hs (Finset.mem_range.2 (by omega))
    have h2 : 2 ∈ D.host.T2 := hs (Finset.mem_range.2 (by omega))
    have hnr := D.host.second_set_no_relation
    have hL2' : (2 : ℤ) ≤ (Lw : ℤ) := by exact_mod_cast hL2
    exact hnr 0 h0 1 h1 2 h2 (by norm_num) (by norm_num) (by norm_num) 1 2
      (by norm_num) (by simp; omega) (by norm_num) (by rw [abs_of_pos (by norm_num)]; exact hL2')
      (by norm_num) (by norm_num)
  have hcard : D.host.T2.card ≤ (n - 1) / (4 * Lw) := by
    have h1 : D.host.T2.card ≤ N := by simpa using Finset.card_le_card hsub
    have h2 : D.host.T2.card ≠ N := by
      intro heq
      exact hne (Finset.eq_of_subset_of_card_le hsub (by simp [heq])).symm.subset
    omega
  have hmul : D.host.T2.card * (4 * Lw) < n := by
    have := (Nat.le_div_iff_mul_le (by omega)).1 hcard
    omega
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hLpos : (0 : ℝ) < 4 * (Lw : ℝ) := by
    have : (2 : ℝ) ≤ Lw := by exact_mod_cast hL2
    linarith
  rw [L.typeDensity_eq_card_div, div_le_div_iff₀ hnpos hLpos, one_mul]
  have : ((D.host.T2.card * (4 * Lw) : ℕ) : ℝ) ≤ (n : ℝ) := by exact_mod_cast hmul.le
  push_cast at this
  linarith

end GlobalTheory
