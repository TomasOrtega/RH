import Mathlib
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.IsPairLevel

noncomputable section

open NumberField IsDedekindDomain GlobalTheory.BCT Formalism.L2.Host PositivityTheory.Rg.BcB.F.Ex0 PositivityTheory.Rg.Bc.ArchbcB.B

namespace GlobalTheory.CompanionTheory.UnifFix

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

/- English proof (translation)
Conclude with `(IsCMField.complexConj E).commutes x`.
-/
theorem conj_real (x : maximalRealSubfield E) :
    IsCMField.complexConj E (algebraMap (maximalRealSubfield E) E x) = algebraMap (maximalRealSubfield E) E x := by
  exact (IsCMField.complexConj E).commutes x

/- English proof (translation)
Unfold `GlobalTheory.BCT.cj`. Use `split_ifs with h`. Rewrite using `[h.choose_spec.2, conj_real]`. Both sides reduce to the same expression.
-/
theorem cj_real (w : Pl E) (x : maximalRealSubfield E) :
    GlobalTheory.BCT.cj w (algebraMap E (w.adicCompletion E) (algebraMap (maximalRealSubfield E) E x)) =
      algebraMap E (w.adicCompletion E) (algebraMap (maximalRealSubfield E) E x) := by
  unfold GlobalTheory.BCT.cj
  split_ifs with h
  · rw [h.choose_spec.2, conj_real]
  · rfl

/- English proof (translation)
Use `hU w` as an intermediate fact. Establish `h1` using `HeightOneSpectrum.valuation_liesOver E (w.under (𝓞 (maximalRealSubfield E))) w x`. Establish `he : (w.under (𝓞 (maximalRealSubfield E))).asIdeal.ramificationIdx' w.asIdeal = 1`. Rewrite using `[Ideal.ramificationIdx'_eq_ramificationIdx]`. Conclude with `Ideal.ramificationIdx_eq_one_of_isUnramifiedAt`.

Conclude with `(w.under _).ne_bot`. Rewrite using `[← h1, he, pow_one]`.
-/
theorem valuation_up (hU : GlobalTheory.BCT.Unr E) (w : Pl E) (x : maximalRealSubfield E) :
    w.valuation E (algebraMap (maximalRealSubfield E) E x) =
      (w.under (𝓞 (maximalRealSubfield E))).valuation (maximalRealSubfield E) x := by
  have := hU w
  have h1 := HeightOneSpectrum.valuation_liesOver E (w.under (𝓞 (maximalRealSubfield E))) w x
  have he : (w.under (𝓞 (maximalRealSubfield E))).asIdeal.ramificationIdx' w.asIdeal = 1 := by
    rw [Ideal.ramificationIdx'_eq_ramificationIdx]
    · exact Ideal.ramificationIdx_eq_one_of_isUnramifiedAt
    · exact (w.under _).ne_bot
  rw [← h1, he, pow_one]

/- English proof (translation)
Substitute `ha` using the available equality. Both sides reduce to the same expression.
-/
theorem neg_toAdd_unzero (a : WithZero (Multiplicative ℤ)) (h : a ≠ 0) (ha : a = WithZero.exp (-1 : ℤ)) :
    -Multiplicative.toAdd (WithZero.unzero h) = 1 := by
  subst ha
  rfl

/- English proof (translation)
Introduce `E _ _ _ hU w`. Take `⟨π, hπ⟩` from `HeightOneSpectrum.valuation_exists_uniformizer (maximalRealSubfield E) (w.under (𝓞 (maximalRealSubfield E)))`. Establish `hy : w.valuation E (algebraMap (maximalRealSubfield E) E π) = WithZero.exp (-1)`. Rewrite using `[valuation_up hU w π, hπ]`. Establish `hy0 : algebraMap (maximalRealSubfield E) E π ≠ 0`.

Introduce `h0`. Rewrite `hy` using `[h0, map_zero]`. Conclude with `WithZero.zero_ne_coe hy`. Establish `hne : algebraMap E (w.adicCompletion E) (algebraMap (maximalRealSubfield E) E π) ≠ 0` using `(map_ne_zero _).2 hy0`. Establish `hv : Valued.v (algebraMap E (w.adicCompletion E) (algebraMap (maximalRealSubfield E) E π)) = WithZero.exp (-1)`.

Rewrite using `[HeightOneSpectrum.algebraMap_adicCompletion (𝓞 E) E w, Function.comp_apply, Algebra.algebraMap_self, RingHom.id_apply, HeightOneSpectrum.valuedAdicCompletion_eq_valuation', hy]`. Establish `hv0 : Valued.v (algebraMap E (w.adicCompletion E) (algebraMap (maximalRealSubfield E) E π)) ≠ 0`. Rewrite using `[hv]`. Conclude with `WithZero.coe_ne_zero`. Use `⟨Units.mk0 _ hne, ⟨?_, ?_⟩, ?_⟩` and prove the remaining obligations.

Use `show Formalism.UG.ordL (algebraMap E (w.adicCompletion E) (algebraMap (maximalRealSubfield E) E π)) = 1`. Unfold `Formalism.UG.ordL`. Rewrite using `[dif_neg hv0]`. Conclude with `neg_toAdd_unzero _ hv0 hv`. Conclude with `cj_real w π`.

Conclude with `hv`.
-/
theorem unifEx : UnifEx := by
  intro E _ _ _ hU w
  obtain ⟨π, hπ⟩ := HeightOneSpectrum.valuation_exists_uniformizer (maximalRealSubfield E)
    (w.under (𝓞 (maximalRealSubfield E)))
  have hy : w.valuation E (algebraMap (maximalRealSubfield E) E π) = WithZero.exp (-1) := by
    rw [valuation_up hU w π, hπ]
  have hy0 : algebraMap (maximalRealSubfield E) E π ≠ 0 := by
    intro h0
    rw [h0, map_zero] at hy
    exact WithZero.zero_ne_coe hy
  have hne : algebraMap E (w.adicCompletion E) (algebraMap (maximalRealSubfield E) E π) ≠ 0 :=
    (map_ne_zero _).2 hy0
  have hv : Valued.v (algebraMap E (w.adicCompletion E) (algebraMap (maximalRealSubfield E) E π)) =
      WithZero.exp (-1) := by
    rw [HeightOneSpectrum.algebraMap_adicCompletion (𝓞 E) E w, Function.comp_apply, Algebra.algebraMap_self,
      RingHom.id_apply, HeightOneSpectrum.valuedAdicCompletion_eq_valuation', hy]
  have hv0 : Valued.v (algebraMap E (w.adicCompletion E) (algebraMap (maximalRealSubfield E) E π)) ≠ 0 := by
    rw [hv]
    exact WithZero.coe_ne_zero
  refine ⟨Units.mk0 _ hne, ⟨?_, ?_⟩, ?_⟩
  · show Formalism.UG.ordL (algebraMap E (w.adicCompletion E) (algebraMap (maximalRealSubfield E) E π)) = 1
    unfold Formalism.UG.ordL
    rw [dif_neg hv0]
    exact neg_toAdd_unzero _ hv0 hv
  · exact cj_real w π
  · exact hv

end GlobalTheory.CompanionTheory.UnifFix
