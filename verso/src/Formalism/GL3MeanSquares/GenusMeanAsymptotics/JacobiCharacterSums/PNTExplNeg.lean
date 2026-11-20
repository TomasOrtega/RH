import Formalism.GL3MeanSquares.GenusMeanAsymptotics.JacobiCharacterSums.PNTExplLocL

open Complex Classical

noncomputable section

namespace Formalism.HermitianLattices.Ext.PrimesInProgressions

open Formalism.ZeroFreeDirichlet

/- English proof (translation)
Rewrite using `[Nat.cast_sum, Finset.sum_div]`. Use `(norm_sum_le _ _).trans (Finset.sum_le_sum fun ρ hρ => ?_)` and prove the remaining obligations. Rewrite using `[norm_div, Complex.norm_natCast]`. Conclude with `div_le_div_of_nonneg_left (Nat.cast_nonneg _) hδ (h ρ hρ)`.
-/
lemma ex_sum_le {δ : ℝ} (hδ : 0 < δ) (Z : Finset ℂ) (m : ℂ → ℕ) (s : ℂ)
    (h : ∀ ρ ∈ Z, δ ≤ ‖s - ρ‖) :
    ‖∑ ρ ∈ Z, (m ρ : ℂ) / (s - ρ)‖ ≤ ((∑ ρ ∈ Z, m ρ : ℕ) : ℝ) / δ := by
  rw [Nat.cast_sum, Finset.sum_div]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun ρ hρ => ?_)
  rw [norm_div, Complex.norm_natCast]
  exact div_le_div_of_nonneg_left (Nat.cast_nonneg _) hδ (h ρ hρ)

/- English proof (translation)
Establish `hM' : (3 : ℝ) ≤ M` using `by exact_mod_cast hM`. Establish `h0` using `abs_nonneg t`. Establish `h6 : (6 : ℝ) ≤ (M : ℝ) * (|t| + 2)` using `by nlinarith`. Rewrite using `[Real.le_log_iff_exp_le (by linarith)]`. Use `Real.exp_one_lt_d9` as an intermediate fact.

Combine the linear equalities and inequalities to obtain the conclusion.
-/
lemma ex_one_le_log {M : ℕ} (hM : 3 ≤ M) (t : ℝ) : 1 ≤ Real.log ((M : ℝ) * (|t| + 2)) := by
  have hM' : (3 : ℝ) ≤ M := by exact_mod_cast hM
  have h0 := abs_nonneg t
  have h6 : (6 : ℝ) ≤ (M : ℝ) * (|t| + 2) := by nlinarith
  rw [Real.le_log_iff_exp_le (by linarith)]
  have := Real.exp_one_lt_d9
  linarith

/- English proof (translation)
Take `⟨C₀, hC₀, hR⟩` from `Formalism.ZeroFreeDirichlet.l_log_deriv_right`. Take `⟨C₁, hC₁, hloc⟩` from `ex_local`. Use `⟨2 * C₁ + (100 / 7 + C₀), by positivity, ?_⟩` and prove the remaining obligations. Introduce `M _ χ s δ hM hδ hδ' hs1 _ hsne hz`. Use `set large₂ : ℝ := Real.log ((M : ℝ) * (|s.im| + 2)) with hLg`.

Establish `hL1 : 1 ≤ large₂` using `ex_one_le_log hM s.im`. Establish `hif : (0 : ℝ) ≤ (if χ = 1 then 1 / ‖s - 1‖ else 0)` using `by split_ifs`. Check the signs of the components of the expression. Conclude with `le_rfl`. Establish `hup : ∀ x : ℝ, 0 ≤ x → x ≤ x * large₂ / δ`.

Introduce `x hx`. Rewrite using `[le_div_iff₀ hδ]`. Establish `: x * δ ≤ x * 1` using `mul_le_mul_of_nonneg_left (by linarith) hx`. Establish `h2 : x * 1 ≤ x * large₂` using `mul_le_mul_of_nonneg_left hL1 hx`. Combine the linear equalities and inequalities to obtain the conclusion.

Distinguish the cases in `hcase : 107 / 100 ≤ s.re`. Establish `h1` using `hR M χ s (by linarith)`. Establish `h2 : 1 / (s.re - 1) ≤ 100 / 7`. Rewrite using `[div_le_div_iff₀ (by linarith) (by norm_num)]`. Combine the linear equalities and inequalities to obtain the conclusion.

Establish `h3` using `hup (2 * C₁ + (100 / 7 + C₀)) (by positivity)`. Combine the linear equalities and inequalities to obtain the conclusion. Rewrite `hcase` using `[not_le]`. Take `⟨Z, hZ, hcard, hexp⟩` from `hloc M χ s.im hM`. Establish `hne : exLF χ s ≠ 0`.

Introduce `h0`. Use `hz s h0 (by linarith) (by simp)` as an intermediate fact. Simplify using `at this`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hsb : s ∈ Metric.closedBall ((101 / 100 : ℂ) + s.im * I) (1 / 15)`.

Rewrite using `[Metric.mem_closedBall, dist_eq_norm]`. Establish `: s - ((101 / 100 : ℂ) + s.im * I) = ((s.re - 101 / 100 : ℝ) : ℂ)`. Apply the tactic sequence `apply Complex.ext <;> simp`. Rewrite using `[this, Complex.norm_real, Real.norm_eq_abs, abs_le]`. Apply the tactic sequence `constructor <;> linarith`.

Establish `hE` using `hexp s hsb hne`. Establish `hdist : ∀ ρ ∈ Z, δ ≤ ‖s - ρ‖`. Introduce `ρ hρ`. Take `⟨hρb, hρ0⟩` from `(hZ ρ).1 hρ`. Rewrite using `[norm_sub_rev]`.

Distinguish the cases in `h9 : 9 / 10 ≤ ρ.re`. Use `hz ρ hρ0 h9 ?_` and prove the remaining obligations. Rewrite `hρb`, `hsb` using `[Metric.mem_closedBall]`. Use `dist_triangle_right ρ s ((101 / 100 : ℂ) + s.im * I)` as an intermediate fact. Rewrite `this` using `[dist_eq_norm]`.

Combine the linear equalities and inequalities to obtain the conclusion. Rewrite `h9` using `[not_le]`. Use `Complex.abs_re_le_norm (ρ - s)` as an intermediate fact. Rewrite `this` using `[Complex.sub_re]`. Establish `h3` using `neg_abs_le (ρ.re - s.re)`.

Combine the linear equalities and inequalities to obtain the conclusion. Establish `hS` using `ex_sum_le hδ Z (exOrd χ) s hdist`. Establish `hS2 : ((∑ ρ ∈ Z, exOrd χ ρ : ℕ) : ℝ) / δ ≤ C₁ * large₂ / δ` using `div_le_div_of_nonneg_right hcard hδ.le`. Establish `hD : ‖deriv (exLF χ) s / exLF χ s‖ ≤ C₁ * large₂ + C₁ * large₂ / δ`. Use `norm_sub_norm_le (deriv (exLF χ) s / exLF χ s) (∑ ρ ∈ Z, (exOrd χ ρ : ℂ) / (s - ρ))` as an intermediate fact.

Combine the linear equalities and inequalities to obtain the conclusion. Establish `hCL : C₁ * large₂ ≤ C₁ * large₂ / δ`. Rewrite using `[le_div_iff₀ hδ]`. Establish `: 0 ≤ C₁ * large₂` using `by positivity`. Use the polynomial consequences of the given equalities and inequalities.

Apply the tactic sequence `have hI : ‖(if χ = 1 then 1 / (s - 1) else 0 : ℂ)‖ = (if χ = 1 then 1 / ‖s - 1‖ else 0) := by split_ifs <;> simp`. Rewrite using `[negLD_eq_exLF χ hsne hne]`. Establish `hN` using `norm_sub_le (if χ = 1 then 1 / (s - 1) else 0 : ℂ) (deriv (exLF χ) s / exLF χ s)`. Rewrite `hN` using `[hI]`. Establish `hex : (2 * C₁ + (100 / 7 + C₀)) * large₂ / δ = 2 * (C₁ * large₂ / δ) + (100 / 7 + C₀) * large₂ / δ` using `by ring`.

Establish `hpos : 0 ≤ (100 / 7 + C₀) * large₂ / δ` using `by positivity`. Rewrite using `[hex]`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem ex_negLD_bound : ∃ C : ℝ, 0 < C ∧ ∀ (M : ℕ) [NeZero M] (χ : DirichletCharacter ℂ M) (s : ℂ) (δ : ℝ),
    3 ≤ M → 0 < δ → δ ≤ 1 / 20 → 19 / 20 ≤ s.re → s.re ≤ 3 → s ≠ 1 →
    (∀ ρ : ℂ, exLF χ ρ = 0 → 9 / 10 ≤ ρ.re → ‖ρ - s‖ ≤ 1 / 5 → δ ≤ ‖ρ - s‖) →
    ‖negLD χ s‖ ≤ C * Real.log ((M : ℝ) * (|s.im| + 2)) / δ + (if χ = 1 then 1 / ‖s - 1‖ else 0) := by
  obtain ⟨C₀, hC₀, hR⟩ := Formalism.ZeroFreeDirichlet.l_log_deriv_right
  obtain ⟨C₁, hC₁, hloc⟩ := ex_local
  refine ⟨2 * C₁ + (100 / 7 + C₀), by positivity, ?_⟩
  intro M _ χ s δ hM hδ hδ' hs1 _ hsne hz
  set large₂ : ℝ := Real.log ((M : ℝ) * (|s.im| + 2)) with hLg
  have hL1 : 1 ≤ large₂ := ex_one_le_log hM s.im
  have hif : (0 : ℝ) ≤ (if χ = 1 then 1 / ‖s - 1‖ else 0) := by
    split_ifs
    · positivity
    · exact le_rfl

  have hup : ∀ x : ℝ, 0 ≤ x → x ≤ x * large₂ / δ := by
    intro x hx
    rw [le_div_iff₀ hδ]
    have : x * δ ≤ x * 1 := mul_le_mul_of_nonneg_left (by linarith) hx
    have h2 : x * 1 ≤ x * large₂ := mul_le_mul_of_nonneg_left hL1 hx
    linarith
  by_cases hcase : 107 / 100 ≤ s.re
  · have h1 := hR M χ s (by linarith)
    have h2 : 1 / (s.re - 1) ≤ 100 / 7 := by
      rw [div_le_div_iff₀ (by linarith) (by norm_num)]
      linarith
    have h3 := hup (2 * C₁ + (100 / 7 + C₀)) (by positivity)
    linarith
  · rw [not_le] at hcase
    obtain ⟨Z, hZ, hcard, hexp⟩ := hloc M χ s.im hM
    have hne : exLF χ s ≠ 0 := by
      intro h0
      have := hz s h0 (by linarith) (by simp)
      simp at this
      linarith
    have hsb : s ∈ Metric.closedBall ((101 / 100 : ℂ) + s.im * I) (1 / 15) := by
      rw [Metric.mem_closedBall, dist_eq_norm]
      have : s - ((101 / 100 : ℂ) + s.im * I) = ((s.re - 101 / 100 : ℝ) : ℂ) := by
        apply Complex.ext <;> simp
      rw [this, Complex.norm_real, Real.norm_eq_abs, abs_le]
      constructor <;> linarith
    have hE := hexp s hsb hne
    have hdist : ∀ ρ ∈ Z, δ ≤ ‖s - ρ‖ := by
      intro ρ hρ
      obtain ⟨hρb, hρ0⟩ := (hZ ρ).1 hρ
      rw [norm_sub_rev]
      by_cases h9 : 9 / 10 ≤ ρ.re
      · refine hz ρ hρ0 h9 ?_
        rw [Metric.mem_closedBall] at hρb hsb
        have := dist_triangle_right ρ s ((101 / 100 : ℂ) + s.im * I)
        rw [dist_eq_norm] at this
        linarith
      · rw [not_le] at h9
        have := Complex.abs_re_le_norm (ρ - s)
        rw [Complex.sub_re] at this
        have h3 := neg_abs_le (ρ.re - s.re)
        linarith
    have hS := ex_sum_le hδ Z (exOrd χ) s hdist
    have hS2 : ((∑ ρ ∈ Z, exOrd χ ρ : ℕ) : ℝ) / δ ≤ C₁ * large₂ / δ :=
      div_le_div_of_nonneg_right hcard hδ.le
    have hD : ‖deriv (exLF χ) s / exLF χ s‖ ≤ C₁ * large₂ + C₁ * large₂ / δ := by
      have := norm_sub_norm_le (deriv (exLF χ) s / exLF χ s) (∑ ρ ∈ Z, (exOrd χ ρ : ℂ) / (s - ρ))
      linarith
    have hCL : C₁ * large₂ ≤ C₁ * large₂ / δ := by
      rw [le_div_iff₀ hδ]
      have : 0 ≤ C₁ * large₂ := by positivity
      nlinarith
    have hI : ‖(if χ = 1 then 1 / (s - 1) else 0 : ℂ)‖ = (if χ = 1 then 1 / ‖s - 1‖ else 0) := by
      split_ifs <;> simp
    rw [negLD_eq_exLF χ hsne hne]
    have hN := norm_sub_le (if χ = 1 then 1 / (s - 1) else 0 : ℂ) (deriv (exLF χ) s / exLF χ s)
    rw [hI] at hN
    have hex : (2 * C₁ + (100 / 7 + C₀)) * large₂ / δ = 2 * (C₁ * large₂ / δ) + (100 / 7 + C₀) * large₂ / δ := by ring
    have hpos : 0 ≤ (100 / 7 + C₀) * large₂ / δ := by positivity
    rw [hex]
    linarith

end Formalism.HermitianLattices.Ext.PrimesInProgressions
