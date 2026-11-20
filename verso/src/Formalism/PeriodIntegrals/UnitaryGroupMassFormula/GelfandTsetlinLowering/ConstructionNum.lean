import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.GelfandTsetlinLowering.ZScalarVanish
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.GelfandTsetlinTopCoefficient.NumMore

noncomputable section

namespace PI.WGL

open Formalism.BasicNotions MvPolynomial

/- English proof (translation)
Introduce `n N h lam sg hI`. Conclude with `⟨PI.GTNum.cBr_ne_zero h lam sg hI, PI.GTNum.abs_cBr_le_cBd h lam sg hI, PI.GTNum.degZ_eq h lam sg⟩`.
-/
theorem numbers_dominant_large : Numbers := by
  intro n N h lam sg hI
  exact ⟨PI.GTNum.cBr_ne_zero h lam sg hI, PI.GTNum.abs_cBr_le_cBd h lam sg hI,
    PI.GTNum.degZ_eq h lam sg⟩

/- English proof (translation)
Introduce `n N h lam sg mu hsg hmu hne hw`. Establish `hsum : (∑ i : Fin n, mu.w i) = ∑ i : Fin n, sg.w i`. Unfold `wsum at hw`. Conclude with `hw`. Establish `hD : D0 h lam mu = D0 h lam sg`.

Unfold `D0`. Rewrite using `[Finset.sum_sub_distrib, Finset.sum_sub_distrib, hsum]`. Choose the witnesses or unpack the hypotheses as in `⟨i, hi⟩ : ∃ i, mu.w i ≠ sg.w i := by`. Assume the negation of the conclusion as `hc`. Use `push_neg at hc`.

Conclude with `hne (funext hc)`. Establish `hmem : mu.w i ∈ Rset h lam sg i`. Establish `hm` using `PI.GTNum.sg_mem_R h lam mu hmu i`. Unfold `Rset at hm ⊢`. Rewrite `hm` using `[hD]`.

Conclude with `hm`. Unfold `zScalar`. Apply `Finset.prod_eq_zero (Finset.mem_univ i)` to reduce the goal to its premises. Apply `Finset.prod_eq_zero (Finset.mem_erase.mpr ⟨hi, hmem⟩)` to reduce the goal to its premises. Apply `Finset.prod_eq_zero (Finset.mem_univ i)` to reduce the goal to its premises.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem scalar_vanishing_criterion : ZScalarVanish := by
  intro n N h lam sg mu hsg hmu hne hw
  have hsum : (∑ i : Fin n, mu.w i) = ∑ i : Fin n, sg.w i := by
    unfold wsum at hw
    exact hw
  have hD : D0 h lam mu = D0 h lam sg := by
    unfold D0
    rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib, hsum]
  obtain ⟨i, hi⟩ : ∃ i, mu.w i ≠ sg.w i := by
    by_contra hc
    push_neg at hc
    exact hne (funext hc)
  have hmem : mu.w i ∈ Rset h lam sg i := by
    have hm := PI.GTNum.sg_mem_R h lam mu hmu i
    unfold Rset at hm ⊢
    rw [hD] at hm
    exact hm
  unfold zScalar
  apply Finset.prod_eq_zero (Finset.mem_univ i)
  apply Finset.prod_eq_zero (Finset.mem_erase.mpr ⟨hi, hmem⟩)
  apply Finset.prod_eq_zero (Finset.mem_univ i)
  ring

end PI.WGL
