import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsPolySandwich
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open Polynomial Filter

/- English proof (translation)
Assume the negation of the conclusion and derive a contradiction. Separate the alternatives or extract the components of the hypothesis. Extract witnesses or component facts from the available result. Rewrite the indicated hypotheses using the stated equalities. Establish an intermediate fact.

Combine the linear equalities and inequalities to obtain the conclusion. Establish an intermediate fact. Establish an intermediate fact. Extract witnesses or component facts from the available result. Simplify using the standard rewrite rules.

Combine the linear equalities and inequalities to obtain the conclusion. A detailed English derivation is pending.
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
Separate the alternatives or extract the components of the hypothesis. Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem PolySandwich.coeff_nonneg_of_eventually (f : ℚ[X]) (E : ℕ) (hE : f.natDegree ≤ E)
    (hf : ∀ᶠ n : ℕ in atTop, 0 ≤ f.eval (n : ℚ)) : 0 ≤ f.coeff E := by
  rcases hE.lt_or_eq with hlt | heq
  · rw [coeff_eq_zero_of_natDegree_lt hlt]
  · rw [← heq]
    exact PolySandwich.leadingCoeff_nonneg_of_eventually f hf

/- English proof (translation)
Rewrite the conclusion using the stated equalities.
-/
theorem PolySandwich.natDegree_shift (p : ℚ[X]) (c : ℚ) : (p.comp (X + C c)).natDegree = p.natDegree := by
  rw [natDegree_comp, natDegree_X_add_C, mul_one]

/- English proof (translation)
Separate the alternatives or extract the components of the hypothesis. Rewrite the conclusion using the stated equalities. Substitute using the available equality. Establish an intermediate fact. Rewrite the conclusion using the stated equalities.

Rewrite the indicated hypotheses using the stated equalities. A detailed English derivation is pending.
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
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Combine the linear equalities and inequalities to obtain the conclusion.

Establish an intermediate fact. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Establish an intermediate fact.

Rewrite the indicated hypotheses using the stated equalities. Rewrite the indicated hypotheses using the stated equalities. Combine the linear equalities and inequalities to obtain the conclusion. Establish an intermediate fact. Assume the negation of the conclusion and derive a contradiction.

Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Supply the required witnesses or components.

A detailed English derivation is pending.
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
