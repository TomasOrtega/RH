import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels

open NumberField IsDedekindDomain
open scoped Matrix

namespace GlobalTheory.InertValRestr

/- English proof (translation)
Use `⟨?_⟩` and prove the remaining obligations. Establish `hP : w.asIdeal.IsPrime` using `w.isPrime`. Establish `hc : (w.asIdeal.comap (algebraMap (𝓞 F) (𝓞 E))).IsPrime` using `inferInstance`. Use `v.isMaximal.eq_of_le hc.ne_top ?_` and prove the remaining obligations. Use `show v.asIdeal ≤ w.asIdeal.comap (algebraMap (𝓞 F) (𝓞 E))`.

Rewrite using `[← hin]`. Conclude with `Ideal.le_comap_map`.
-/
theorem liesOver_of_isInertAt {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E]
    [Algebra F E] (v : HeightOneSpectrum (𝓞 F)) (w : HeightOneSpectrum (𝓞 E))
    (hin : Formalism.UG.IsInertAt F E v w) : w.asIdeal.LiesOver v.asIdeal := by
  refine ⟨?_⟩
  have hP : w.asIdeal.IsPrime := w.isPrime
  have hc : (w.asIdeal.comap (algebraMap (𝓞 F) (𝓞 E))).IsPrime := inferInstance
  refine v.isMaximal.eq_of_le hc.ne_top ?_
  show v.asIdeal ≤ w.asIdeal.comap (algebraMap (𝓞 F) (𝓞 E))
  rw [← hin]
  exact Ideal.le_comap_map

/- English proof (translation)
Establish `hP : w.asIdeal.IsPrime` using `w.isPrime`. Apply `Ideal.ramificationIdx'_spec` to reduce the goal to its premises. Rewrite using `[hin, pow_one]`. Rewrite using `[hin]`. Conclude with `not_le_of_gt (Ideal.pow_succ_lt_pow w.ne_bot 1 |>.trans_eq (pow_one _))`.
-/
theorem ramificationIdx'_eq_one_of_isInertAt {F E : Type} [Field F] [NumberField F] [Field E]
    [NumberField E] [Algebra F E] (v : HeightOneSpectrum (𝓞 F)) (w : HeightOneSpectrum (𝓞 E))
    (hin : Formalism.UG.IsInertAt F E v w) : v.asIdeal.ramificationIdx' w.asIdeal = 1 := by
  have hP : w.asIdeal.IsPrime := w.isPrime
  apply Ideal.ramificationIdx'_spec
  · rw [hin, pow_one]
  · rw [hin]
    exact not_le_of_gt (Ideal.pow_succ_lt_pow w.ne_bot 1 |>.trans_eq (pow_one _))

/- English proof (translation)
Introduce `F E _ _ _ _ _ v w hin x`. Use `liesOver_of_isInertAt v w hin` as an intermediate fact. Rewrite using `[← HeightOneSpectrum.valuation_liesOver (K := F) E v w x, ramificationIdx'_eq_one_of_isInertAt v w hin, pow_one]`.
-/
theorem valuation_algebraMap_of_isInertAt : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E]
    [Algebra F E] (v : HeightOneSpectrum (𝓞 F)) (w : HeightOneSpectrum (𝓞 E)),
    Formalism.UG.IsInertAt F E v w → ∀ x : F, w.valuation E (algebraMap F E x) = v.valuation F x := by
  intro F E _ _ _ _ _ v w hin x
  have := liesOver_of_isInertAt v w hin
  rw [← HeightOneSpectrum.valuation_liesOver (K := F) E v w x,
    ramificationIdx'_eq_one_of_isInertAt v w hin, pow_one]

end GlobalTheory.InertValRestr
