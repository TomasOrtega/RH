import Formalism.GL3MeanSquares.SecondEstimateOfIntervalHypothesis
import Formalism.LandauZeroFreeBounds.ExceptionalZeroBounds.LandauLemmaLfunctionZeros
import Formalism.LandauZeroFreeBounds.ExceptionalZeroBounds.LandauLocal3
import Formalism.LandauZeroFreeBounds.ExceptionalZeroBounds.LGrowth
import Formalism.LandauZeroFreeBounds.ExceptionalZeroBounds.LRight

open Complex

noncomputable section

namespace Formalism.HermitianLattices.Ext.BoxTail

/- English proof (translation)
Establish `hn0 : 0 < n` using `by linarith`. Establish `hpos : 0 < n * (|t| + 2)` using `mul_pos hn0 (by positivity)`. Establish `h1 : n * (|t| + 2) ≤ Q ^ 3`. Establish `ht2 : |t| + 2 ≤ Q + 1` using `by linarith`. Establish `hQ2 : Q + 1 ≤ Q ^ 2` using `by nlinarith`.

Combine the equalities or inequalities in the displayed calculation. Combine the equalities or inequalities in the displayed calculation.
-/
lemma tail_box_log {n t Q : ℝ} (hn : 1 ≤ n) (hQ : 2 ≤ Q) (hnQ : n ≤ Q) (ht : |t| ≤ Q - 1) :
    Real.log (n * (|t| + 2)) ≤ 3 * Real.log Q := by
  have hn0 : 0 < n := by linarith
  have hpos : 0 < n * (|t| + 2) := mul_pos hn0 (by positivity)
  have h1 : n * (|t| + 2) ≤ Q ^ 3 := by
    have ht2 : |t| + 2 ≤ Q + 1 := by linarith
    have hQ2 : Q + 1 ≤ Q ^ 2 := by nlinarith
    calc n * (|t| + 2) ≤ Q * (Q + 1) := mul_le_mul hnQ ht2 (by positivity) (by linarith)
      _ ≤ Q * Q ^ 2 := mul_le_mul_of_nonneg_left hQ2 (by linarith)
      _ = Q ^ 3 := by ring
  calc Real.log (n * (|t| + 2)) ≤ Real.log (Q ^ 3) := Real.log_le_log hpos h1
    _ = 3 * Real.log Q := by rw [Real.log_pow]; norm_num

/- English proof (translation)
Combine the equalities or inequalities in the displayed calculation. Rewrite using `[norm_div, Complex.norm_natCast]`. Conclude with `div_le_div_of_nonneg_left (Nat.cast_nonneg _) hδ (h ρ hρ)`. Use `_ = (∑ ρ ∈ Z, (m ρ : ℝ)) / δ := by rw [Finset.sum_div]`.
-/
lemma tail_box_sum {δ : ℝ} (hδ : 0 < δ) (Z : Finset ℂ) (m : ℂ → ℕ) (s : ℂ)
    (h : ∀ ρ ∈ Z, δ ≤ ‖s - ρ‖) :
    ‖∑ ρ ∈ Z, (m ρ : ℂ) / (s - ρ)‖ ≤ (∑ ρ ∈ Z, (m ρ : ℝ)) / δ := by
  calc ‖∑ ρ ∈ Z, (m ρ : ℂ) / (s - ρ)‖ ≤ ∑ ρ ∈ Z, ‖(m ρ : ℂ) / (s - ρ)‖ := norm_sum_le _ _
    _ ≤ ∑ ρ ∈ Z, (m ρ : ℝ) / δ := Finset.sum_le_sum fun ρ hρ => by
        rw [norm_div, Complex.norm_natCast]
        exact div_le_div_of_nonneg_left (Nat.cast_nonneg _) hδ (h ρ hρ)
    _ = (∑ ρ ∈ Z, (m ρ : ℝ)) / δ := by rw [Finset.sum_div]

/- English proof (translation)
Take `⟨C, hC⟩` from `Formalism.ZeroFreeDirichlet.lfunction_polynomial_growth`. Take `⟨CR, hCR0, hCR⟩` from `Formalism.ZeroFreeDirichlet.l_log_deriv_right`. Establish `hl2 : 0 < Real.log 2` using `Real.log_pos one_lt_two`. Establish `hA0 : 0 ≤ Real.log (2 * (21 * (|C| + 1))) / Real.log 2 + 1`. Establish `: 0 ≤ Real.log (2 * (21 * (|C| + 1)))` using `Real.log_nonneg (by have := abs_nonneg C; nlinarith)`.

Check the signs of the components of the expression. Use `⟨3 * (Real.log (2 * (21 * (|C| + 1))) / Real.log 2 + 1) * (1440 / 11 + 1 / (δ * Real.log 2)) + (10 + CR) / Real.log 2, by positivity, ?_⟩` and prove the remaining obligations. Introduce `N _ χ Q hχ hQ hNQ hbox s hs ht`. Establish `hlogQ : Real.log 2 ≤ Real.log Q` using `Real.log_le_log two_pos hQ`. Establish `hlogQ0 : 0 ≤ Real.log Q` using `hl2.le.trans hlogQ`.

Establish `hrest : 0 ≤ (10 + CR) / Real.log 2 * Real.log Q` using `by positivity`. Distinguish the cases in `hσ : s.re < 11 / 10`. Establish `hfs : DirichletCharacter.LFunction χ s ≠ 0` using `hbox s (by linarith) (by linarith)`. Take `⟨Z, m, hZ, -, hsum, hdiff⟩` from `Formalism.ZeroFreeDirichlet.landau_lemma_lfunction_zeros Formalism.ZeroFreeDirichlet.landau_local3 hC Formalism.ZeroFreeDirichlet.inverseBound hχ (by linarith) hσ hfs`. Establish `hN1 : (1 : ℝ) ≤ N` using `by exact_mod_cast Nat.one_le_iff_ne_zero.2 (NeZero.ne N)`.

Establish `hlog3` using `tail_box_log hN1 hQ hNQ ht`. Establish `hfar : ∀ ρ ∈ Z, δ ≤ ‖s - ρ‖`. Introduce `ρ hρ`. Take `⟨hball, hzero⟩` from `(hZ ρ).1 hρ`. Rewrite `hball` using `[Metric.mem_closedBall, dist_eq_norm]`.

Establish `him : |ρ.im - s.im| ≤ 11 / 20 / 3`. Use `Complex.abs_im_le_norm (ρ - ((21 / 20 : ℂ) + s.im * I))` as an intermediate fact. Simplify using `at this`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hre : ρ.re ≤ 1 - 1 / 400`.

Assume the negation of the conclusion as `hgt`. Use `push Not at hgt`. Establish `hρim : |ρ.im| ≤ Q`. Use `abs_sub_abs_le_abs_sub ρ.im s.im` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion.

Conclude with `hbox ρ hgt hρim hzero`. Use `Complex.re_le_norm (s - ρ)` as an intermediate fact. Rewrite `this` using `[Complex.sub_re]`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hS` using `tail_box_sum hδ Z m s hfar`.

Establish `e1 : ‖deriv (DirichletCharacter.LFunction χ) s / DirichletCharacter.LFunction χ s - ∑ ρ ∈ Z, (m ρ : ℂ) / (s - ρ)‖ ≤ 1440 / 11 * ((Real.log (2 * (21 * (|C| + 1))) / Real.log 2 + 1) * (3 * Real.log Q))` using `hdiff.trans (by gcongr)`. Establish `e2 : ‖∑ ρ ∈ Z, (m ρ : ℂ) / (s - ρ)‖ ≤ (Real.log (2 * (21 * (|C| + 1))) / Real.log 2 + 1) * (3 * Real.log Q) / Real.log 2 / δ`. Use `hS.trans (div_le_div_of_nonneg_right ?_ hδ.le)` and prove the remaining obligations. Conclude with `hsum.trans (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hlog3 hA0) hl2.le)`. Establish `htri : ‖Formalism.ZeroFreeDirichlet.negLD χ s‖ ≤ ‖deriv (DirichletCharacter.LFunction χ) s / DirichletCharacter.LFunction χ s - ∑ ρ ∈ Z, (m ρ : ℂ) / (s - ρ)‖ + ‖∑ ρ ∈ Z, (m ρ : ℂ) / (s - ρ)‖`.

Rewrite using `[Formalism.ZeroFreeDirichlet.negLD, norm_neg]`. Conclude with `(norm_add_le _ _).trans_eq' (by rw [sub_add_cancel])`. Establish `hδ0 : δ ≠ 0` using `hδ.ne'`. Establish `hl20 : Real.log 2 ≠ 0` using `hl2.ne'`. Establish `e3 : 1440 / 11 * ((Real.log (2 * (21 * (|C| + 1))) / Real.log 2 + 1) * (3 * Real.log Q)) + (Real.log (2 * (21 * (|C| + 1))) / Real.log 2 + 1) * (3 * Real.log Q) / Real.log 2 / δ = 3 * (Real.log (2 * (21 * (|C| + 1))) / Real.log 2 + 1) * (1440 / 11 + 1 / (δ * Real.log 2)) * Real.l …`.

Clear the denominators using the available nonvanishing facts. Combine the equalities or inequalities in the displayed calculation. Use `push Not at hσ`. Establish `h1 : 1 < s.re` using `by linarith`. Establish `hb` using `hCR N χ s h1`.

Establish `hinv : 1 / (s.re - 1) ≤ 10`. Rewrite using `[div_le_iff₀ (by linarith)]`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `e5 : 10 + CR ≤ (10 + CR) / Real.log 2 * Real.log Q`. Rewrite using `[div_mul_eq_mul_div, le_div_iff₀ hl2]`.

Conclude with `mul_le_mul_of_nonneg_left hlogQ (by linarith)`. Establish `hbig : 0 ≤ 3 * (Real.log (2 * (21 * (|C| + 1))) / Real.log 2 + 1) * (1440 / 11 + 1 / (δ * Real.log 2)) * Real.log Q` using `by positivity`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem tail_box_negLD (δ : ℝ) (hδ : 0 < δ) : ∃ K : ℝ, 0 ≤ K ∧
    ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N) (Q : ℝ), χ ≠ 1 → 2 ≤ Q → (N : ℝ) ≤ Q →
      Formalism.HermitianLattices.ZeroFreeRegionGL2.ZeroFreeBox Q χ →
      ∀ s : ℂ, 1 - 1 / 400 + δ ≤ s.re → |s.im| ≤ Q - 1 →
        ‖Formalism.ZeroFreeDirichlet.negLD χ s‖ ≤ K * Real.log Q := by
  obtain ⟨C, hC⟩ := Formalism.ZeroFreeDirichlet.lfunction_polynomial_growth
  obtain ⟨CR, hCR0, hCR⟩ := Formalism.ZeroFreeDirichlet.l_log_deriv_right
  have hl2 : 0 < Real.log 2 := Real.log_pos one_lt_two
  have hA0 : 0 ≤ Real.log (2 * (21 * (|C| + 1))) / Real.log 2 + 1 := by
    have : 0 ≤ Real.log (2 * (21 * (|C| + 1))) :=
      Real.log_nonneg (by have := abs_nonneg C; nlinarith)
    positivity
  refine ⟨3 * (Real.log (2 * (21 * (|C| + 1))) / Real.log 2 + 1) * (1440 / 11 + 1 / (δ * Real.log 2)) +
    (10 + CR) / Real.log 2, by positivity, ?_⟩
  intro N _ χ Q hχ hQ hNQ hbox s hs ht
  have hlogQ : Real.log 2 ≤ Real.log Q := Real.log_le_log two_pos hQ
  have hlogQ0 : 0 ≤ Real.log Q := hl2.le.trans hlogQ
  have hrest : 0 ≤ (10 + CR) / Real.log 2 * Real.log Q := by positivity
  by_cases hσ : s.re < 11 / 10
  ·
    have hfs : DirichletCharacter.LFunction χ s ≠ 0 := hbox s (by linarith) (by linarith)
    obtain ⟨Z, m, hZ, -, hsum, hdiff⟩ := Formalism.ZeroFreeDirichlet.landau_lemma_lfunction_zeros Formalism.ZeroFreeDirichlet.landau_local3 hC
      Formalism.ZeroFreeDirichlet.inverseBound hχ (by linarith) hσ hfs
    have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast Nat.one_le_iff_ne_zero.2 (NeZero.ne N)
    have hlog3 := tail_box_log hN1 hQ hNQ ht

    have hfar : ∀ ρ ∈ Z, δ ≤ ‖s - ρ‖ := by
      intro ρ hρ
      obtain ⟨hball, hzero⟩ := (hZ ρ).1 hρ
      rw [Metric.mem_closedBall, dist_eq_norm] at hball
      have him : |ρ.im - s.im| ≤ 11 / 20 / 3 := by
        have := Complex.abs_im_le_norm (ρ - ((21 / 20 : ℂ) + s.im * I))
        simp at this
        linarith
      have hre : ρ.re ≤ 1 - 1 / 400 := by
        by_contra hgt
        push Not at hgt
        have hρim : |ρ.im| ≤ Q := by
          have := abs_sub_abs_le_abs_sub ρ.im s.im
          linarith
        exact hbox ρ hgt hρim hzero
      have := Complex.re_le_norm (s - ρ)
      rw [Complex.sub_re] at this
      linarith
    have hS := tail_box_sum hδ Z m s hfar
    have e1 : ‖deriv (DirichletCharacter.LFunction χ) s / DirichletCharacter.LFunction χ s -
        ∑ ρ ∈ Z, (m ρ : ℂ) / (s - ρ)‖ ≤
        1440 / 11 * ((Real.log (2 * (21 * (|C| + 1))) / Real.log 2 + 1) * (3 * Real.log Q)) :=
      hdiff.trans (by gcongr)
    have e2 : ‖∑ ρ ∈ Z, (m ρ : ℂ) / (s - ρ)‖ ≤
        (Real.log (2 * (21 * (|C| + 1))) / Real.log 2 + 1) * (3 * Real.log Q) / Real.log 2 / δ := by
      refine hS.trans (div_le_div_of_nonneg_right ?_ hδ.le)
      exact hsum.trans (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hlog3 hA0) hl2.le)
    have htri : ‖Formalism.ZeroFreeDirichlet.negLD χ s‖ ≤
        ‖deriv (DirichletCharacter.LFunction χ) s / DirichletCharacter.LFunction χ s -
          ∑ ρ ∈ Z, (m ρ : ℂ) / (s - ρ)‖ + ‖∑ ρ ∈ Z, (m ρ : ℂ) / (s - ρ)‖ := by
      rw [Formalism.ZeroFreeDirichlet.negLD, norm_neg]
      exact (norm_add_le _ _).trans_eq' (by rw [sub_add_cancel])
    have hδ0 : δ ≠ 0 := hδ.ne'
    have hl20 : Real.log 2 ≠ 0 := hl2.ne'
    have e3 : 1440 / 11 * ((Real.log (2 * (21 * (|C| + 1))) / Real.log 2 + 1) * (3 * Real.log Q)) +
        (Real.log (2 * (21 * (|C| + 1))) / Real.log 2 + 1) * (3 * Real.log Q) / Real.log 2 / δ =
        3 * (Real.log (2 * (21 * (|C| + 1))) / Real.log 2 + 1) * (1440 / 11 + 1 / (δ * Real.log 2)) *
          Real.log Q := by
      field_simp
    calc ‖Formalism.ZeroFreeDirichlet.negLD χ s‖ ≤ _ := htri
      _ ≤ _ := add_le_add e1 e2
      _ = _ := e3
      _ ≤ _ := by rw [add_mul]; linarith
  ·
    push Not at hσ
    have h1 : 1 < s.re := by linarith
    have hb := hCR N χ s h1
    have hinv : 1 / (s.re - 1) ≤ 10 := by
      rw [div_le_iff₀ (by linarith)]
      linarith
    have e5 : 10 + CR ≤ (10 + CR) / Real.log 2 * Real.log Q := by
      rw [div_mul_eq_mul_div, le_div_iff₀ hl2]
      exact mul_le_mul_of_nonneg_left hlogQ (by linarith)
    have hbig : 0 ≤ 3 * (Real.log (2 * (21 * (|C| + 1))) / Real.log 2 + 1) *
        (1440 / 11 + 1 / (δ * Real.log 2)) * Real.log Q := by positivity
    calc ‖Formalism.ZeroFreeDirichlet.negLD χ s‖ ≤ 1 / (s.re - 1) + CR := hb
      _ ≤ 10 + CR := by linarith
      _ ≤ (10 + CR) / Real.log 2 * Real.log Q := e5
      _ ≤ _ := by rw [add_mul]; linarith

end Formalism.HermitianLattices.Ext.BoxTail
