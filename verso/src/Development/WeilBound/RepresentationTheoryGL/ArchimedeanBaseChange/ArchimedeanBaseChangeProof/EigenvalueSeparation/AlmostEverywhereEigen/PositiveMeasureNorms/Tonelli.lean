import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.EigenvalueSeparation.AlmostEverywhereEigen.OneStepOf

open MeasureTheory
open scoped ENNReal
open PositivityTheory.Rg.BcB.E1 PositivityTheory.Rg.BcB.E2

namespace PositivityTheory.Rg.BcB.E2.P.Tonelli

/- English proof (translation)
Rewrite using `[Lp.enorm_def, eLpNorm_eq_lintegral_rpow_enorm_toReal two_ne_zero ENNReal.ofNat_ne_top, ← ENNReal.rpow_two, ← ENNReal.rpow_mul]`. Evaluate the numerical expressions.
-/
theorem enorm_sq {S : Type} [MeasurableSpace S] {ν : Measure S} (g : Lp ℂ 2 ν) :
    ‖g‖ₑ ^ 2 = ∫⁻ s, ‖(g : S → ℂ) s‖ₑ ^ 2 ∂ν := by
  rw [Lp.enorm_def, eLpNorm_eq_lintegral_rpow_enorm_toReal two_ne_zero ENNReal.ofNat_ne_top,
    ← ENNReal.rpow_two, ← ENNReal.rpow_mul]
  norm_num

end PositivityTheory.Rg.BcB.E2.P.Tonelli

namespace PositivityTheory.Rg.BcB.E2.P

/- English proof (translation)
Introduce `Y S _ _ m _ ν _ F f W hf hW hfin`. Establish `hmeas : Measurable (Function.uncurry fun y s => W y * ‖f y s‖ₑ ^ 2)` using `(hW.comp measurable_fst).mul (hf.1.enorm.pow_const 2)`. Use `ae_lt_top hmeas.lintegral_prod_left' ?_` and prove the remaining obligations. Rewrite using `[← lintegral_lintegral_swap hmeas.aemeasurable]`. Use `ne_of_eq_of_ne (lintegral_congr fun y => ?_) hfin` and prove the remaining obligations.

Establish `hy : Measurable fun s => f y s` using `hf.1.comp measurable_prodMk_left`. Rewrite using `[lintegral_const_mul _ (hy.enorm.pow_const 2), Tonelli.enorm_sq]`. Use `congr 1`. Conclude with `lintegral_congr_ae ((hf.2 y).mono fun s hs => by simp only [hs])`.
-/
theorem tonelli : Tonelli := by
  intro Y S _ _ m _ ν _ F f W hf hW hfin
  have hmeas : Measurable (Function.uncurry fun y s => W y * ‖f y s‖ₑ ^ 2) :=
    (hW.comp measurable_fst).mul (hf.1.enorm.pow_const 2)
  refine ae_lt_top hmeas.lintegral_prod_left' ?_
  rw [← lintegral_lintegral_swap hmeas.aemeasurable]
  refine ne_of_eq_of_ne (lintegral_congr fun y => ?_) hfin
  have hy : Measurable fun s => f y s := hf.1.comp measurable_prodMk_left
  rw [lintegral_const_mul _ (hy.enorm.pow_const 2), Tonelli.enorm_sq]
  congr 1
  exact lintegral_congr_ae ((hf.2 y).mono fun s hs => by simp only [hs])

end PositivityTheory.Rg.BcB.E2.P
