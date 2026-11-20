import Formalism.LandauZeroFreeBounds.NoZeroComplexOf

open Complex LSeries ArithmeticFunction DirichletCharacter
open scoped LSeries.notation

noncomputable section

namespace Formalism.ZeroFreeDirichlet

/- English proof (translation)
Unfold `negLD`. Rewrite using `[DirichletCharacter.LSeries_twist_vonMangoldt_eq χ hs, DirichletCharacter.deriv_LFunction_eq_deriv_LSeries χ hs, DirichletCharacter.LFunction_eq_LSeries χ hs]`. Expand and normalize the polynomial expressions, which then agree.
-/
lemma negLogDeriv_eq_LSeries {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) {s : ℂ}
    (hs : 1 < s.re) : negLD χ s = LSeries (↗χ * ↗Λ) s := by
  unfold negLD
  rw [DirichletCharacter.LSeries_twist_vonMangoldt_eq χ hs,
    DirichletCharacter.deriv_LFunction_eq_deriv_LSeries χ hs,
    DirichletCharacter.LFunction_eq_LSeries χ hs]
  ring

/- English proof (translation)
Rewrite using `[negLogDeriv_eq_LSeries χ hs]`. Conclude with `Complex.hasSum_re (DirichletCharacter.LSeriesSummable_twist_vonMangoldt χ hs).hasSum`.
-/
lemma hasSum_re_term {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) {s : ℂ}
    (hs : 1 < s.re) : HasSum (fun n ↦ (term (↗χ * ↗Λ) s n).re) (negLD χ s).re := by
  rw [negLogDeriv_eq_LSeries χ hs]
  exact Complex.hasSum_re (DirichletCharacter.LSeriesSummable_twist_vonMangoldt χ hs).hasSum

/- English proof (translation)
Break down `eq_or_ne n 0 with rfl | hn` into its components or cases. Simplify using `[LSeries.term_def]`. Establish `hn' : (n : ℂ) ≠ 0` using `Nat.cast_ne_zero.mpr hn`. Rewrite using `[LSeries.term_def, if_neg hn, Complex.cpow_add _ _ hn']`. Use `push_cast`.

Rewrite using `[Complex.ofReal_cpow (Nat.cast_nonneg n)]`. Use `push_cast`. Simplify using `only [Pi.mul_apply]`. Rewrite using `[div_mul_div_comm]`. Expand and normalize the polynomial expressions, which then agree.
-/
lemma term_ofReal_add_mul_I {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (σ u : ℝ) (n : ℕ) :
    term (↗χ * ↗Λ) ((σ : ℂ) + u * I) n =
      ((Λ n / (n : ℝ) ^ σ : ℝ) : ℂ) * (χ n / (n : ℂ) ^ ((u : ℂ) * I)) := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp [LSeries.term_def]
  · have hn' : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hn
    rw [LSeries.term_def, if_neg hn, Complex.cpow_add _ _ hn']
    push_cast
    rw [Complex.ofReal_cpow (Nat.cast_nonneg n)]
    push_cast
    simp only [Pi.mul_apply]
    rw [div_mul_div_comm]
    ring

/- English proof (translation)
Break down `eq_or_ne n 0 with rfl | hn` into its components or cases. Simplify using `[LSeries.term_def]`. Rewrite using `[LSeries.term_def, if_neg hn]`. Use `push_cast`. Rewrite using `[Complex.ofReal_cpow (Nat.cast_nonneg n)]`.

Use `push_cast`. Simplify using `only [Pi.mul_apply]`. Expand and normalize the polynomial expressions, which then agree.
-/
lemma term_ofReal {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (σ : ℝ) (n : ℕ) :
    term (↗χ * ↗Λ) (σ : ℂ) n = ((Λ n / (n : ℝ) ^ σ : ℝ) : ℂ) * χ n := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp [LSeries.term_def]
  · rw [LSeries.term_def, if_neg hn]
    push_cast
    rw [Complex.ofReal_cpow (Nat.cast_nonneg n)]
    push_cast
    simp only [Pi.mul_apply]
    ring

/- English proof (translation)
The claim follows from `div_nonneg ArithmeticFunction.vonMangoldt_nonneg (Real.rpow_nonneg (Nat.cast_nonneg n) σ)`.
-/
lemma vonMangoldt_div_rpow_nonneg (σ : ℝ) (n : ℕ) : 0 ≤ Λ n / (n : ℝ) ^ σ :=
  div_nonneg ArithmeticFunction.vonMangoldt_nonneg (Real.rpow_nonneg (Nat.cast_nonneg n) σ)

/- English proof (translation)
Break down `eq_or_ne n 0 with rfl | hn` into its components or cases. Simplify using `[LSeries.term_def]`. Establish `ha` using `vonMangoldt_div_rpow_nonneg σ n`. Rewrite using `[term_ofReal, term_ofReal_add_mul_I, term_ofReal_add_mul_I]`. Distinguish the cases in `hu : IsUnit (n : ZMod q)`.

Establish `h1 : (1 : DirichletCharacter ℂ q) n = 1` using `MulChar.one_apply hu`. Establish `h2 : (χ ^ 2) n = (χ n) ^ 2` using `MulChar.pow_apply' χ two_ne_zero _`. Establish `hχ1 : ‖χ n‖ = 1`. Use `DirichletCharacter.unit_norm_eq_one χ hu.unit` as an intermediate fact. Rewrite `this` using `[IsUnit.unit_spec]`. Then use the resulting hypothesis.

Establish `hc : ‖(n : ℂ) ^ ((t : ℂ) * I)‖ = 1`. Rewrite using `[Complex.norm_natCast_cpow_of_pos (Nat.pos_of_ne_zero hn)]`. Simplify using the standard rewrite rules. Establish `hc2 : (n : ℂ) ^ (((2 * t : ℝ) : ℂ) * I) = ((n : ℂ) ^ ((t : ℂ) * I)) ^ 2`. Rewrite using `[← Complex.cpow_nat_mul]`.

Use `push_cast`. Put the polynomial expressions in normal form. Use `set w := χ n / (n : ℂ) ^ ((t : ℂ) * I) with hw_def`. Establish `hw : ‖w‖ = 1` using `by rw [hw_def, norm_div, hχ1, hc, div_one]`. Establish `hw2 : (χ ^ 2) n / (n : ℂ) ^ (((2 * t : ℝ) : ℂ) * I) = w ^ 2`.

Rewrite using `[h2, hc2, div_pow]`. Rewrite using `[h1, hw2]`. Establish `hn1 : w.re * w.re + w.im * w.im = 1`. Rewrite using `[← Complex.normSq_apply, Complex.normSq_eq_norm_sq, hw]`. Evaluate the numerical expressions.

Establish `hre : (w ^ 2).re = 2 * w.re ^ 2 - 1`. Rewrite using `[sq, Complex.mul_re]`. Use polynomial arithmetic with `[hn1]`. Rewrite using `[Complex.re_ofReal_mul, Complex.re_ofReal_mul, Complex.re_ofReal_mul, hre, Complex.one_re]`. Use polynomial arithmetic with `[mul_nonneg ha (sq_nonneg (1 + w.re))]`.

Establish `h1 : (1 : DirichletCharacter ℂ q) n = 0` using `MulChar.map_nonunit _ hu`. Establish `h2 : χ n = 0` using `MulChar.map_nonunit _ hu`. Establish `h3 : (χ ^ 2) n = 0` using `MulChar.map_nonunit _ hu`. Simplify using `[h1, h2, h3]`.
-/
lemma term_three_four_one_nonneg {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (σ t : ℝ) (n : ℕ) :
    0 ≤ 3 * (term (↗(1 : DirichletCharacter ℂ q) * ↗Λ) (σ : ℂ) n).re
      + 4 * (term (↗χ * ↗Λ) ((σ : ℂ) + t * I) n).re
      + (term (↗(χ ^ 2) * ↗Λ) ((σ : ℂ) + ((2 * t : ℝ) : ℂ) * I) n).re := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp [LSeries.term_def]
  have ha := vonMangoldt_div_rpow_nonneg σ n
  rw [term_ofReal, term_ofReal_add_mul_I, term_ofReal_add_mul_I]
  by_cases hu : IsUnit (n : ZMod q)
  · have h1 : (1 : DirichletCharacter ℂ q) n = 1 := MulChar.one_apply hu
    have h2 : (χ ^ 2) n = (χ n) ^ 2 := MulChar.pow_apply' χ two_ne_zero _
    have hχ1 : ‖χ n‖ = 1 := by
      have := DirichletCharacter.unit_norm_eq_one χ hu.unit
      rwa [IsUnit.unit_spec] at this
    have hc : ‖(n : ℂ) ^ ((t : ℂ) * I)‖ = 1 := by
      rw [Complex.norm_natCast_cpow_of_pos (Nat.pos_of_ne_zero hn)]
      simp
    have hc2 : (n : ℂ) ^ (((2 * t : ℝ) : ℂ) * I) = ((n : ℂ) ^ ((t : ℂ) * I)) ^ 2 := by
      rw [← Complex.cpow_nat_mul]
      push_cast
      ring_nf
    set w := χ n / (n : ℂ) ^ ((t : ℂ) * I) with hw_def
    have hw : ‖w‖ = 1 := by rw [hw_def, norm_div, hχ1, hc, div_one]
    have hw2 : (χ ^ 2) n / (n : ℂ) ^ (((2 * t : ℝ) : ℂ) * I) = w ^ 2 := by
      rw [h2, hc2, div_pow]
    rw [h1, hw2]
    have hn1 : w.re * w.re + w.im * w.im = 1 := by
      rw [← Complex.normSq_apply, Complex.normSq_eq_norm_sq, hw]
      norm_num
    have hre : (w ^ 2).re = 2 * w.re ^ 2 - 1 := by
      rw [sq, Complex.mul_re]
      nlinarith [hn1]
    rw [Complex.re_ofReal_mul, Complex.re_ofReal_mul, Complex.re_ofReal_mul, hre, Complex.one_re]
    nlinarith [mul_nonneg ha (sq_nonneg (1 + w.re))]
  · have h1 : (1 : DirichletCharacter ℂ q) n = 0 := MulChar.map_nonunit _ hu
    have h2 : χ n = 0 := MulChar.map_nonunit _ hu
    have h3 : (χ ^ 2) n = 0 := MulChar.map_nonunit _ hu
    simp [h1, h2, h3]

/- English proof (translation)
Establish `h : χ n * χ n = 1`. Rewrite using `[← pow_two, ← MulChar.pow_apply' χ two_ne_zero, hχ, MulChar.one_apply hu]`. Conclude with `mul_self_eq_one_iff.mp h`.
-/
lemma eq_one_or_eq_neg_one_of_sq_eq_one {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (hχ : χ ^ 2 = 1)
    {n : ℕ} (hu : IsUnit (n : ZMod q)) : χ n = 1 ∨ χ n = -1 := by
  have h : χ n * χ n = 1 := by
    rw [← pow_two, ← MulChar.pow_apply' χ two_ne_zero, hχ, MulChar.one_apply hu]
  exact mul_self_eq_one_iff.mp h

/- English proof (translation)
Break down `eq_or_ne n 0 with rfl | hn` into its components or cases. Simplify using `[LSeries.term_def]`. Establish `ha` using `vonMangoldt_div_rpow_nonneg σ n`. Rewrite using `[term_ofReal, term_ofReal]`. Distinguish the cases in `hu : IsUnit (n : ZMod q)`.

Rewrite using `[MulChar.one_apply hu]`. Apply the tactic sequence `rcases eq_one_or_eq_neg_one_of_sq_eq_one χ hχ hu with h | h <;> rw [h] <;>`. Apply the tactic sequence `simp only [Complex.re_ofReal_mul, Complex.one_re, Complex.neg_re] <;> linarith`. Rewrite using `[MulChar.map_nonunit _ hu, MulChar.map_nonunit _ hu]`. Simplify using the standard rewrite rules.
-/
lemma term_one_add_real_nonneg {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (hχ : χ ^ 2 = 1)
    (σ : ℝ) (n : ℕ) :
    0 ≤ (term (↗(1 : DirichletCharacter ℂ q) * ↗Λ) (σ : ℂ) n).re
      + (term (↗χ * ↗Λ) (σ : ℂ) n).re := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp [LSeries.term_def]
  have ha := vonMangoldt_div_rpow_nonneg σ n
  rw [term_ofReal, term_ofReal]
  by_cases hu : IsUnit (n : ZMod q)
  · rw [MulChar.one_apply hu]
    rcases eq_one_or_eq_neg_one_of_sq_eq_one χ hχ hu with h | h <;> rw [h] <;>
      simp only [Complex.re_ofReal_mul, Complex.one_re, Complex.neg_re] <;> linarith
  · rw [MulChar.map_nonunit _ hu, MulChar.map_nonunit _ hu]
    simp

/- English proof (translation)
Break down `eq_or_ne n 0 with rfl | hn` into its components or cases. Simplify using `[LSeries.term_def]`. Establish `ha` using `vonMangoldt_div_rpow_nonneg σ n`. Rewrite using `[term_ofReal, term_ofReal, term_ofReal, term_ofReal, MulChar.mul_apply]`. Distinguish the cases in `hu : IsUnit (n : ZMod q)`.

Rewrite using `[MulChar.one_apply hu]`. Apply the tactic sequence `rcases eq_one_or_eq_neg_one_of_sq_eq_one χ₁ h₁ hu with h | h <;>`. Apply the tactic sequence `rcases eq_one_or_eq_neg_one_of_sq_eq_one χ₂ h₂ hu with h' | h' <;> rw [h, h'] <;>`. Apply the tactic sequence `generalize Λ n / (n : ℝ) ^ σ = a at ha ⊢ <;>`. Apply the tactic sequence `simp [Complex.re_ofReal_mul] <;> linarith`.

Rewrite using `[MulChar.map_nonunit _ hu, MulChar.map_nonunit _ hu, MulChar.map_nonunit _ hu]`. Simplify using the standard rewrite rules.
-/
lemma term_two_real_nonneg {q : ℕ} [NeZero q] (χ₁ χ₂ : DirichletCharacter ℂ q)
    (h₁ : χ₁ ^ 2 = 1) (h₂ : χ₂ ^ 2 = 1) (σ : ℝ) (n : ℕ) :
    0 ≤ (term (↗(1 : DirichletCharacter ℂ q) * ↗Λ) (σ : ℂ) n).re
      + (term (↗χ₁ * ↗Λ) (σ : ℂ) n).re + (term (↗χ₂ * ↗Λ) (σ : ℂ) n).re
      + (term (↗(χ₁ * χ₂) * ↗Λ) (σ : ℂ) n).re := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp [LSeries.term_def]
  have ha := vonMangoldt_div_rpow_nonneg σ n
  rw [term_ofReal, term_ofReal, term_ofReal,
    term_ofReal, MulChar.mul_apply]
  by_cases hu : IsUnit (n : ZMod q)
  · rw [MulChar.one_apply hu]
    rcases eq_one_or_eq_neg_one_of_sq_eq_one χ₁ h₁ hu with h | h <;>
      rcases eq_one_or_eq_neg_one_of_sq_eq_one χ₂ h₂ hu with h' | h' <;> rw [h, h'] <;>
      generalize Λ n / (n : ℝ) ^ σ = a at ha ⊢ <;>
      simp [Complex.re_ofReal_mul] <;> linarith
  · rw [MulChar.map_nonunit _ hu, MulChar.map_nonunit _ hu, MulChar.map_nonunit _ hu]
    simp

/- English proof (translation)
Introduce `q _ σ hσ`. Establish `hs1 : 1 < ((σ : ℂ)).re` using `by simpa using hσ`. Establish `H1 : ∀ χ : DirichletCharacter ℂ q, HasSum (fun n ↦ (term (↗χ * ↗Λ) (σ : ℂ) n).re) (negLD χ (σ : ℂ)).re` using `fun χ => hasSum_re_term χ hs1`. Use `⟨fun χ t => ?_, fun χ hχ => ?_, fun χ₁ χ₂ h₁ h₂ => ?_⟩` and prove the remaining obligations. Establish `hs2 : 1 < ((σ : ℂ) + t * I).re` using `by simpa using hσ`.

Establish `hs3 : 1 < ((σ : ℂ) + ((2 * t : ℝ) : ℂ) * I).re` using `by simpa using hσ`. Establish `HS` using `(((H1 1).mul_left 3).add ((hasSum_re_term χ hs2).mul_left 4)).add (hasSum_re_term (χ ^ 2) hs3)`. Establish `e : ((σ : ℂ) + 2 * t * I) = (σ : ℂ) + ((2 * t : ℝ) : ℂ) * I` using `by push_cast; ring`. Rewrite using `[e]`. Conclude with `HasSum.nonneg (fun n => term_three_four_one_nonneg χ σ t n) HS`.

Conclude with `HasSum.nonneg (fun n => term_one_add_real_nonneg χ hχ σ n) ((H1 1).add (H1 χ))`. Conclude with `HasSum.nonneg (fun n => term_two_real_nonneg χ₁ χ₂ h₁ h₂ σ n) ((((H1 1).add (H1 χ₁)).add (H1 χ₂)).add (H1 (χ₁ * χ₂)))`.
-/
theorem negLogDerivPositivity : Positivity := by
  intro q _ σ hσ
  have hs1 : 1 < ((σ : ℂ)).re := by simpa using hσ
  have H1 : ∀ χ : DirichletCharacter ℂ q, HasSum (fun n ↦ (term (↗χ * ↗Λ) (σ : ℂ) n).re)
      (negLD χ (σ : ℂ)).re := fun χ => hasSum_re_term χ hs1
  refine ⟨fun χ t => ?_, fun χ hχ => ?_, fun χ₁ χ₂ h₁ h₂ => ?_⟩
  · have hs2 : 1 < ((σ : ℂ) + t * I).re := by simpa using hσ
    have hs3 : 1 < ((σ : ℂ) + ((2 * t : ℝ) : ℂ) * I).re := by simpa using hσ
    have HS := (((H1 1).mul_left 3).add ((hasSum_re_term χ hs2).mul_left 4)).add
      (hasSum_re_term (χ ^ 2) hs3)
    have e : ((σ : ℂ) + 2 * t * I) = (σ : ℂ) + ((2 * t : ℝ) : ℂ) * I := by push_cast; ring
    rw [e]
    exact HasSum.nonneg (fun n => term_three_four_one_nonneg χ σ t n) HS
  · exact HasSum.nonneg (fun n => term_one_add_real_nonneg χ hχ σ n) ((H1 1).add (H1 χ))
  · exact HasSum.nonneg (fun n => term_two_real_nonneg χ₁ χ₂ h₁ h₂ σ n)
      ((((H1 1).add (H1 χ₁)).add (H1 χ₂)).add (H1 (χ₁ * χ₂)))

end Formalism.ZeroFreeDirichlet
