import Mathlib

open Metric MeasureTheory Module Set

namespace GlobalTheory

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

/- English proof (translation)
Use `borelize E`. Set `μ : Measure E` to `Measure.addHaar`. Establish `hδ : 0 < d / 2` using `by positivity`. Establish `hρ : 0 < R + d / 2` using `by positivity`. Establish `D : Set.Pairwise (s : Set E) (Function.onFun Disjoint fun c => ball (c : E) (d / 2))`.

Introduce `a ha b hb hab`. Conclude with `ball_disjoint_ball (by have := hsep ha hb hab; linarith)`. Establish `hsub : (⋃ c ∈ s, ball (c : E) (d / 2)) ⊆ ball x (R + d / 2)`. Use `iUnion₂_subset fun a ha => ball_subset_ball' ?_` and prove the remaining obligations. Use `hs a ha` as an intermediate fact.

Combine the linear equalities and inequalities to obtain the conclusion. Establish `I : (s.card : ENNReal) * ENNReal.ofReal ((d / 2) ^ finrank ℝ E) * μ (ball 0 1) ≤ ENNReal.ofReal ((R + d / 2) ^ finrank ℝ E) * μ (ball 0 1)`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[measure_biUnion_finset D fun c _ => measurableSet_ball]`. Simplify using `only [μ.addHaar_ball_of_pos _ hδ, Finset.sum_const, nsmul_eq_mul, mul_assoc]`.

Use `_ ≤ μ (ball x (R + d / 2)) := measure_mono hsub`. Use `_ = _ := μ.addHaar_ball_of_pos _ hρ`. Establish `J : (s.card : ENNReal) * ENNReal.ofReal ((d / 2) ^ finrank ℝ E) ≤ ENNReal.ofReal ((R + d / 2) ^ finrank ℝ E)` using `(ENNReal.mul_le_mul_iff_left (measure_ball_pos μ _ zero_lt_one).ne' measure_ball_lt_top.ne).1 I`. Establish `K : (s.card : ℝ) * (d / 2) ^ finrank ℝ E ≤ (R + d / 2) ^ finrank ℝ E`. Use `ENNReal.toReal_mono ENNReal.ofReal_ne_top J` as an intermediate fact.

Rewrite `this` using `[ENNReal.toReal_mul, ENNReal.toReal_natCast, ENNReal.toReal_ofReal (by positivity), ENNReal.toReal_ofReal (by positivity)]`. Then use the resulting hypothesis. Establish `e : 1 + 2 * R / d = (R + d / 2) / (d / 2)` using `by field_simp; ring`. Rewrite using `[e, div_pow, le_div_iff₀ (by positivity)]`. Conclude with `K`.
-/
theorem finset_card_le_of_separated (s : Finset E) {d R : ℝ} (hd : 0 < d) (hR : 0 ≤ R) (x : E)
    (hs : ∀ a ∈ s, dist a x ≤ R) (hsep : (s : Set E).Pairwise fun a b => d ≤ dist a b) :
    (s.card : ℝ) ≤ (1 + 2 * R / d) ^ finrank ℝ E := by
  borelize E
  let μ : Measure E := Measure.addHaar
  have hδ : 0 < d / 2 := by positivity
  have hρ : 0 < R + d / 2 := by positivity
  have D : Set.Pairwise (s : Set E) (Function.onFun Disjoint fun c => ball (c : E) (d / 2)) := by
    intro a ha b hb hab
    exact ball_disjoint_ball (by have := hsep ha hb hab; linarith)
  have hsub : (⋃ c ∈ s, ball (c : E) (d / 2)) ⊆ ball x (R + d / 2) := by
    refine iUnion₂_subset fun a ha => ball_subset_ball' ?_
    have := hs a ha
    linarith
  have I : (s.card : ENNReal) * ENNReal.ofReal ((d / 2) ^ finrank ℝ E) * μ (ball 0 1) ≤
      ENNReal.ofReal ((R + d / 2) ^ finrank ℝ E) * μ (ball 0 1) := by
    calc (s.card : ENNReal) * ENNReal.ofReal ((d / 2) ^ finrank ℝ E) * μ (ball 0 1)
        = μ (⋃ c ∈ s, ball (c : E) (d / 2)) := by
          rw [measure_biUnion_finset D fun c _ => measurableSet_ball]
          simp only [μ.addHaar_ball_of_pos _ hδ, Finset.sum_const, nsmul_eq_mul, mul_assoc]
      _ ≤ μ (ball x (R + d / 2)) := measure_mono hsub
      _ = _ := μ.addHaar_ball_of_pos _ hρ
  have J : (s.card : ENNReal) * ENNReal.ofReal ((d / 2) ^ finrank ℝ E) ≤
      ENNReal.ofReal ((R + d / 2) ^ finrank ℝ E) :=
    (ENNReal.mul_le_mul_iff_left (measure_ball_pos μ _ zero_lt_one).ne' measure_ball_lt_top.ne).1 I
  have K : (s.card : ℝ) * (d / 2) ^ finrank ℝ E ≤ (R + d / 2) ^ finrank ℝ E := by
    have := ENNReal.toReal_mono ENNReal.ofReal_ne_top J
    rwa [ENNReal.toReal_mul, ENNReal.toReal_natCast, ENNReal.toReal_ofReal (by positivity),
      ENNReal.toReal_ofReal (by positivity)] at this
  have e : 1 + 2 * R / d = (R + d / 2) / (d / 2) := by field_simp; ring
  rw [e, div_pow, le_div_iff₀ (by positivity)]
  exact K

/- English proof (translation)
Establish `hR0 : 0 ≤ R` using `hd.le.trans hR`. Use `pow_le_pow_left₀ (by positivity) ?_ n` and prove the remaining obligations. Establish `h1 : 1 ≤ R / d` using `(one_le_div hd).2 hR`. Establish `: 3 * R / d = R / d + 2 * R / d` using `by ring`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem one_add_two_mul_div_pow_le {d R : ℝ} (hd : 0 < d) (hR : d ≤ R) (n : ℕ) :
    (1 + 2 * R / d) ^ n ≤ (3 * R / d) ^ n := by
  have hR0 : 0 ≤ R := hd.le.trans hR
  refine pow_le_pow_left₀ (by positivity) ?_ n
  have h1 : 1 ≤ R / d := (one_le_div hd).2 hR
  have : 3 * R / d = R / d + 2 * R / d := by ring
  linarith

end GlobalTheory
