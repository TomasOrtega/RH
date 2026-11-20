import Formalism.SharpRestriction.LevelLetterCocycles.CyclotomicPowerSeries.ConstSectionStatement

noncomputable section

namespace LevelStatements.Lv

open PowerSeries IsLocalRing

/- English proof (translation)
Introduce `LL ι _`. Use `⟨fun f => ?_, fun F => ⟨fun k => ?_, ?_⟩⟩` and prove the remaining obligations. Use `⟨PowerSeries.mk fun n i => coeff n (f i), fun i => ?_, fun G hG => ?_⟩` and prove the remaining obligations. Use extensionality with `n`. Simplify using `[coeff_map]`.

Use extensionality with `n i`. Rewrite using `[coeff_mk, ← hG i, coeff_map]`. Both sides reduce to the same expression. Simplify using `only [X_pow_dvd_iff, coeff_map]`. Prove the components needed by the constructor for the conclusion.

Introduce `h i d hd`. Rewrite using `[h d hd]`. Both sides reduce to the same expression. Introduce `h d hd`. Use function extensionality and compare the values at `i`.

Conclude with `h i d hd`. Rewrite using `[isUnit_iff_constantCoeff, Pi.isUnit_iff]`. Use `forall_congr' fun i => ?_` and prove the remaining obligations. Rewrite using `[isUnit_iff_constantCoeff, ← coeff_zero_eq_constantCoeff_apply, ← coeff_zero_eq_constantCoeff_apply, coeff_map]`. Both sides reduce to the same expression.
-/
theorem piSeries : PiSeriesStatement := by
  intro LL ι _
  refine ⟨fun f => ?_, fun F => ⟨fun k => ?_, ?_⟩⟩
  · refine ⟨PowerSeries.mk fun n i => coeff n (f i), fun i => ?_, fun G hG => ?_⟩
    · ext n
      simp [coeff_map]
    · ext n i
      rw [coeff_mk, ← hG i, coeff_map]
      rfl
  · simp only [X_pow_dvd_iff, coeff_map]
    constructor
    · intro h i d hd
      rw [h d hd]
      rfl
    · intro h d hd
      funext i
      exact h i d hd
  · rw [isUnit_iff_constantCoeff, Pi.isUnit_iff]
    refine forall_congr' fun i => ?_
    rw [isUnit_iff_constantCoeff, ← coeff_zero_eq_constantCoeff_apply, ← coeff_zero_eq_constantCoeff_apply,
      coeff_map]
    rfl

end LevelStatements.Lv
