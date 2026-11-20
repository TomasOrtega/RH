import Mathlib
import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.StatementsCoinv
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.RestTerms

open MvPolynomial Finset Coinv

noncomputable section

/- English proof (translation)
Introduce `K _ _ f n e`. Set `r : Fin f × Fin n → Fin f × Fin n → Prop` to `fun u v => toLex u < toLex v`. Establish `: IsStrictTotalOrder (Fin f × Fin n) r` using `inferInstanceAs (IsStrictTotalOrder (Lex (Fin f × Fin n)) (· < ·))`. Establish `wf : WellFounded (Finsupp.Lex r (· < ·) : (Fin f × Fin n →₀ ℕ) → (Fin f × Fin n →₀ ℕ) → Prop)` using `Finsupp.Lex.wellFounded_of_finite r wellFounded_lt`. Proceed by induction on `e using wf.induction with`.

Consider the case `_ e ih`. Distinguish the cases in `hu : IsUnderStaircase e`. Conclude with `⟨monomial e 1, Submodule.subset_span ⟨e, hu, rfl⟩, by simp⟩`. Simplify using `only [IsUnderStaircase, not_forall, not_le] at hu`. Take `⟨⟨b, k⟩, hbk⟩` from `hu`.

Take `⟨T, c, hT, hmem⟩` from `h1 K f n b k e (by simpa using hbk)`. Establish `hlt : ∀ e' ∈ T, Finsupp.Lex r (· < ·) e' e`. Introduce `e' he'`. Use `Finsupp.lex_def.mpr ⟨(b, k), fun j hj => (hT e' he').1 j ?_, (hT e' he').2⟩` and prove the remaining obligations. Conclude with `Prod.Lex.toLex_lt_toLex.mp hj`.

Use `choose! w hw hwm using fun e' (he' : e' ∈ T) => ih e' (hlt e' he')`. Use `⟨∑ e' ∈ T, c e' • w e', Submodule.sum_mem _ fun e' he' => Submodule.smul_mem _ _ (hw e' he'), ?_⟩` and prove the remaining obligations. Establish `hsplit : monomial e (1 : K) - ∑ e' ∈ T, c e' • w e' = (monomial e 1 - ∑ e' ∈ T, c e' • monomial e' 1) + ∑ e' ∈ T, C (c e') * (monomial e' 1 - w e')`. Simplify using `only [smul_eq_C_mul, mul_sub, Finset.sum_sub_distrib]`. Expand and normalize the polynomial expressions, which then agree.

Rewrite using `[hsplit]`. Conclude with `Ideal.add_mem _ hmem (Ideal.sum_mem _ fun e' he' => Ideal.mul_mem_left _ _ (hwm e' he'))`.
-/
theorem CoinvMonomialReduction.proof (h1 : CoinvStepReduction.Statement) :
    CoinvMonomialReduction.Statement := by
  intro K _ _ f n e
  classical
  let r : Fin f × Fin n → Fin f × Fin n → Prop := fun u v => toLex u < toLex v
  have : IsStrictTotalOrder (Fin f × Fin n) r :=
    inferInstanceAs (IsStrictTotalOrder (Lex (Fin f × Fin n)) (· < ·))
  have wf : WellFounded
      (Finsupp.Lex r (· < ·) : (Fin f × Fin n →₀ ℕ) → (Fin f × Fin n →₀ ℕ) → Prop) :=
    Finsupp.Lex.wellFounded_of_finite r wellFounded_lt
  induction e using wf.induction with
  | _ e ih =>
  by_cases hu : IsUnderStaircase e
  · exact ⟨monomial e 1, Submodule.subset_span ⟨e, hu, rfl⟩, by simp⟩
  · simp only [IsUnderStaircase, not_forall, not_le] at hu
    obtain ⟨⟨b, k⟩, hbk⟩ := hu
    obtain ⟨T, c, hT, hmem⟩ := h1 K f n b k e (by simpa using hbk)
    have hlt : ∀ e' ∈ T, Finsupp.Lex r (· < ·) e' e := by
      intro e' he'
      refine Finsupp.lex_def.mpr ⟨(b, k), fun j hj => (hT e' he').1 j ?_, (hT e' he').2⟩
      exact Prod.Lex.toLex_lt_toLex.mp hj
    choose! w hw hwm using fun e' (he' : e' ∈ T) => ih e' (hlt e' he')
    refine ⟨∑ e' ∈ T, c e' • w e',
      Submodule.sum_mem _ fun e' he' => Submodule.smul_mem _ _ (hw e' he'), ?_⟩
    have hsplit : monomial e (1 : K) - ∑ e' ∈ T, c e' • w e' =
        (monomial e 1 - ∑ e' ∈ T, c e' • monomial e' 1) +
          ∑ e' ∈ T, C (c e') * (monomial e' 1 - w e') := by
      simp only [smul_eq_C_mul, mul_sub, Finset.sum_sub_distrib]
      ring
    rw [hsplit]
    exact Ideal.add_mem _ hmem (Ideal.sum_mem _ fun e' he' => Ideal.mul_mem_left _ _ (hwm e' he'))

end

end GroundTheory.Heights₂.Heights.RestTerms
