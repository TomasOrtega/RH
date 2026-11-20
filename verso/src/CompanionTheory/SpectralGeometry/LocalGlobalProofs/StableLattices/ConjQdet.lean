import CompanionTheory.RealGroups.DiscreteSeries.DiscreteSeriesClassification.DiscreteSeriesExhaustion.MatrixCoefficientDecay.InfinitesimalCharacterPaths.TensDecomp
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CentralCharacters.QuasiDeterminantConjInv

namespace GlobalTheory.CompanionTheory.RgConjQdet

open Finset

/- English proof (translation)
Simplify using the standard rewrite rules.
-/
theorem conj_single_apply {n : ℕ} (U Ui : Matrix (Fin n) (Fin n) ℂ) (p q a b : Fin n) :
    (U * Matrix.single p q 1 * Ui : Matrix (Fin n) (Fin n) ℂ) a b = U a p * Ui q b := by
  simp [Matrix.mul_apply, Matrix.single_apply, ite_and]

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Simplify using the standard rewrite rules.

Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities. Consider separately whether the proposition holds or fails.

Substitute using the available equality. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities.

Establish an intermediate fact. Apply function extensionality and compare values at an arbitrary argument. Rewrite the hypotheses and the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem conjQdet : CompanionTheory.RgExh.Dec.J.ConjQdet := by
  intro n X U Ui hUUi hUiU u
  have hE : ∀ (x : ℂ) (p q : Fin n),
      Formalism.REAL.Tm (fun p q => ReciprocityTheory.ChartRestriction.DS.actM X.E (U * Matrix.single p q 1 * Ui)) x p q =
        ∑ c, U.transpose p c • ∑ d, Ui.transpose d q • Formalism.REAL.Tm X.E x c d := by
    intro x p q
    have hd : ∑ c, ∑ d, (U c p * Ui q d) • (if c = d then algebraMap ℂ (Module.End ℂ X.V) x else 0)
        = if p = q then algebraMap ℂ (Module.End ℂ X.V) x else 0 := by
      simp only [smul_ite, smul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true]
      rw [← Finset.sum_smul]
      have hc : ∑ c, U c p * Ui q c = (Ui * U) q p := by
        rw [Matrix.mul_apply]
        exact Finset.sum_congr rfl (fun c _ => mul_comm _ _)
      rw [hc, hUiU, Matrix.one_apply]
      by_cases hpq : p = q
      · subst hpq
        simp
      · rw [if_neg (Ne.symm hpq), if_neg hpq, zero_smul]
    simp only [Formalism.REAL.Tm, ReciprocityTheory.ChartRestriction.DS.actM, conj_single_apply, Matrix.transpose_apply,
      Finset.smul_sum, smul_smul, smul_add, Finset.sum_add_distrib]
    rw [hd]
  have hT : Formalism.REAL.Tm (fun p q => ReciprocityTheory.ChartRestriction.DS.actM X.E (U * Matrix.single p q 1 * Ui)) =
      fun x p q => ∑ c, U.transpose p c • ∑ d, Ui.transpose d q • Formalism.REAL.Tm X.E x c d :=
    funext fun x => funext fun p => funext fun q => hE x p q
  rw [PI.UnitaryGroupMassFormula.DSIC.qdet_eq_qF (fun p q => ReciprocityTheory.ChartRestriction.DS.actM X.E (U * Matrix.single p q 1 * Ui)), hT,
    PI.UnitaryGroupMassFormula.DSIC.qF_row, PI.UnitaryGroupMassFormula.DSIC.qF_col X.E X.gl, smul_smul, Matrix.det_transpose,
    Matrix.det_transpose, ← Matrix.det_mul, hUUi, Matrix.det_one, one_smul]

end GlobalTheory.CompanionTheory.RgConjQdet
