import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsPolySandwich
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open Polynomial Filter

/- English proof (translation)
Assume the negation of the conclusion as `h`. Use `push Not at h`. Break down `Nat.eq_zero_or_pos f.natDegree with h0 | hpos` into its components or cases. Take `⟨n, hn⟩` from `hf.exists`. Rewrite `hn` using `[eq_C_of_natDegree_eq_zero h0, eval_C]`.

Establish `: f.leadingCoeff = f.coeff 0` using `by rw [leadingCoeff, h0]`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hdeg : 0 < f.degree` using `natDegree_pos_iff_degree_pos.mp hpos`. Establish `ht` using `(f.tendsto_atBot_of_leadingCoeff_nonpos hdeg h.le).comp tendsto_natCast_atTop_atTop`. Take `⟨n, hn1, hn2⟩` from `(hf.and (ht.eventually (eventually_lt_atBot 0))).exists`.

Simplify using `only [Function.comp] at hn2`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem PolySandwich.leadingCoeff_nonneg_of_eventually (f : ℚ[X])
    (hf : ∀ᶠ n : ℕ in atTop, 0 ≤ f.eval (n : ℚ)) : 0 ≤ f.leadingCoeff := by
  by_contra h
  push Not at h
  rcases Nat.eq_zero_or_pos f.natDegree with h0 | hpos
  · obtain ⟨n, hn⟩ := hf.exists
    rw [eq_C_of_natDegree_eq_zero h0, eval_C] at hn
    have : f.leadingCoeff = f.coeff 0 := by rw [leadingCoeff, h0]
    linarith
  · have hdeg : 0 < f.degree := natDegree_pos_iff_degree_pos.mp hpos
    have ht := (f.tendsto_atBot_of_leadingCoeff_nonpos hdeg h.le).comp tendsto_natCast_atTop_atTop
    obtain ⟨n, hn1, hn2⟩ := (hf.and (ht.eventually (eventually_lt_atBot 0))).exists
    simp only [Function.comp] at hn2
    linarith

/- English proof (translation)
Break down `hE.lt_or_eq with hlt | heq` into its components or cases. Rewrite using `[coeff_eq_zero_of_natDegree_lt hlt]`. Rewrite using `[← heq]`. Conclude with `PolySandwich.leadingCoeff_nonneg_of_eventually f hf`.
-/
theorem PolySandwich.coeff_nonneg_of_eventually (f : ℚ[X]) (E : ℕ) (hE : f.natDegree ≤ E)
    (hf : ∀ᶠ n : ℕ in atTop, 0 ≤ f.eval (n : ℚ)) : 0 ≤ f.coeff E := by
  rcases hE.lt_or_eq with hlt | heq
  · rw [coeff_eq_zero_of_natDegree_lt hlt]
  · rw [← heq]
    exact PolySandwich.leadingCoeff_nonneg_of_eventually f hf

/- English proof (translation)
Rewrite using `[natDegree_comp, natDegree_X_add_C, mul_one]`.
-/
theorem PolySandwich.natDegree_shift (p : ℚ[X]) (c : ℚ) : (p.comp (X + C c)).natDegree = p.natDegree := by
  rw [natDegree_comp, natDegree_X_add_C, mul_one]

/- English proof (translation)
Break down `hE.lt_or_eq with hlt | heq` into its components or cases. Rewrite using `[coeff_eq_zero_of_natDegree_lt hlt, coeff_eq_zero_of_natDegree_lt (by rwa [PolySandwich.natDegree_shift])]`. Substitute `heq` using the available equality. Establish `h1 : (p.comp (X + C c)).leadingCoeff = p.leadingCoeff`. Rewrite using `[leadingCoeff_comp (by rw [natDegree_X_add_C]; exact one_ne_zero), leadingCoeff_X_add_C, one_pow, mul_one]`.

Rewrite `h1` using `[leadingCoeff, PolySandwich.natDegree_shift]`. Conclude with `h1`.
-/
theorem PolySandwich.coeff_shift (p : ℚ[X]) (c : ℚ) (E : ℕ) (hE : p.natDegree ≤ E) :
    (p.comp (X + C c)).coeff E = p.coeff E := by
  rcases hE.lt_or_eq with hlt | heq
  · rw [coeff_eq_zero_of_natDegree_lt hlt,
      coeff_eq_zero_of_natDegree_lt (by rwa [PolySandwich.natDegree_shift])]
  · subst heq
    have h1 : (p.comp (X + C c)).leadingCoeff = p.leadingCoeff := by
      rw [leadingCoeff_comp (by rw [natDegree_X_add_C]; exact one_ne_zero), leadingCoeff_X_add_C, one_pow,
        mul_one]
    rw [leadingCoeff, PolySandwich.natDegree_shift] at h1
    exact h1

/- English proof (translation)
Introduce `D c p q hq hev`. Use `set g : ℚ[X] := p.comp (X + C (c : ℚ)) with hg`. Establish `h1 : ∀ᶠ n : ℕ in atTop, 0 ≤ (q - p).eval (n : ℚ)` using `hev.mono fun n hn => by rw [eval_sub]; linarith [hn.1]`. Establish `h2 : ∀ᶠ n : ℕ in atTop, 0 ≤ (g - q).eval (n : ℚ)` using `hev.mono fun n hn => by`. Rewrite using `[eval_sub, hg, eval_comp, eval_add, eval_X, eval_C]`.

Combine the linear relations using `[hn.2]`. Establish `hgdeg : g.natDegree = p.natDegree` using `PolySandwich.natDegree_shift p c`. Establish `key : ∀ E : ℕ, p.natDegree ≤ E → q.natDegree ≤ E → p.coeff E = q.coeff E`. Introduce `E hp hqE`. Establish `a` using `PolySandwich.coeff_nonneg_of_eventually (q - p) E ((natDegree_sub_le _ _).trans (max_le hqE hp)) h1`.

Establish `b` using `PolySandwich.coeff_nonneg_of_eventually (g - q) E ((natDegree_sub_le _ _).trans (max_le (hgdeg ▸ hp) hqE)) h2`. Rewrite `a`, `b` using `[coeff_sub]`. Rewrite `b` using `[hg, PolySandwich.coeff_shift p c E hp]`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hpD : p.natDegree ≤ D`.

Assume the negation of the conclusion as `hlt`. Use `push Not at hlt`. Establish `e` using `key p.natDegree le_rfl (hq.trans hlt.le)`. Rewrite `e` using `[coeff_eq_zero_of_natDegree_lt (hq.trans_lt hlt)]`. Establish `hp0 : p = 0` using `leadingCoeff_eq_zero.mp e`.

Rewrite `hlt` using `[hp0, natDegree_zero]`. Conclude with `absurd hlt (Nat.not_lt_zero _)`. Conclude with `⟨hpD, key D hpD hq⟩`.
-/
theorem PolySandwich.proof : PolySandwich.Statement := by
  intro D c p q hq hev
  set g : ℚ[X] := p.comp (X + C (c : ℚ)) with hg
  have h1 : ∀ᶠ n : ℕ in atTop, 0 ≤ (q - p).eval (n : ℚ) :=
    hev.mono fun n hn => by rw [eval_sub]; linarith [hn.1]
  have h2 : ∀ᶠ n : ℕ in atTop, 0 ≤ (g - q).eval (n : ℚ) :=
    hev.mono fun n hn => by
      rw [eval_sub, hg, eval_comp, eval_add, eval_X, eval_C]; linarith [hn.2]
  have hgdeg : g.natDegree = p.natDegree := PolySandwich.natDegree_shift p c

  have key : ∀ E : ℕ, p.natDegree ≤ E → q.natDegree ≤ E → p.coeff E = q.coeff E := by
    intro E hp hqE
    have a := PolySandwich.coeff_nonneg_of_eventually (q - p) E
      ((natDegree_sub_le _ _).trans (max_le hqE hp)) h1
    have b := PolySandwich.coeff_nonneg_of_eventually (g - q) E
      ((natDegree_sub_le _ _).trans (max_le (hgdeg ▸ hp) hqE)) h2
    rw [coeff_sub] at a b
    rw [hg, PolySandwich.coeff_shift p c E hp] at b
    linarith
  have hpD : p.natDegree ≤ D := by
    by_contra hlt
    push Not at hlt
    have e := key p.natDegree le_rfl (hq.trans hlt.le)
    rw [coeff_eq_zero_of_natDegree_lt (hq.trans_lt hlt)] at e
    have hp0 : p = 0 := leadingCoeff_eq_zero.mp e
    rw [hp0, natDegree_zero] at hlt
    exact absurd hlt (Nat.not_lt_zero _)
  exact ⟨hpD, key D hpD hq⟩

end GroundTheory.Heights₂.Heights.HilbertSamuel
