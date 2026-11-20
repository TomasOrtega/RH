import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnifAt
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.ProdForm

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

/- English proof (translation)
Establish `hv : (Valued.v y : WithZero (Multiplicative ℤ)) ≠ 0` using `(Valuation.ne_zero_iff _).mpr hy`. Unfold `absHalf`. Use `congr 2`. Rewrite using `[FinitePlace.norm_def, WithZeroMulInt.toNNReal_neg_apply _ hv, ordL, dif_neg hv, neg_neg]`. Simplify using `[qV]`.
-/
theorem absHalf_eq_sqrt_norm (w : Pl E) {y : w.adicCompletion E} (hy : y ≠ 0) :
    absHalf w y = ((Real.sqrt ‖y‖ : ℝ) : ℂ) := by
  have hv : (Valued.v y : WithZero (Multiplicative ℤ)) ≠ 0 := (Valuation.ne_zero_iff _).mpr hy
  unfold absHalf
  congr 2
  rw [FinitePlace.norm_def, WithZeroMulInt.toNNReal_neg_apply _ hv, ordL, dif_neg hv, neg_neg]
  simp [qV]

/- English proof (translation)
Introduce `E _ _ _ x hx`. Establish `key : ∀ w : Pl E, absHalf w (algebraMap E (w.adicCompletion E) x) = ((Real.sqrt (FinitePlace.mk w x) : ℝ) : ℂ)` using `fun w => absHalf_eq_sqrt_norm w ((_root_.map_ne_zero _).mpr hx)`. Establish `hfin : (Function.mulSupport fun w : Pl E => FinitePlace.mk w x).Finite`. Establish `h0` using `FinitePlace.hasFiniteMulSupport (K := E) hx`. Establish `he : (fun w : Pl E => FinitePlace.mk w x) = (fun u : FinitePlace E => u x) ∘ FinitePlace.equivHeightOneSpectrum.symm` using `rfl`.

Rewrite using `[he, Function.mulSupport_comp_eq_preimage]`. Conclude with `Set.Finite.preimage (FinitePlace.equivHeightOneSpectrum.symm.injective.injOn) h0`. Establish `hsup : (Function.mulSupport fun w : Pl E => Real.sqrt (FinitePlace.mk w x)) = Function.mulSupport fun w : Pl E => FinitePlace.mk w x`. Use extensionality with `w`. Simplify using `[Real.sqrt_eq_one]`.

Use `⟨?_, ?_⟩` and prove the remaining obligations. Establish `hs : (Function.mulSupport fun w : Pl E => absHalf w (algebraMap E (w.adicCompletion E) x)) = Function.mulSupport fun w : Pl E => Real.sqrt (FinitePlace.mk w x)`. Use extensionality with `w`. Simplify using `only [Function.mem_mulSupport, key, ne_eq, Complex.ofReal_eq_one]`. Rewrite using `[hs, hsup]`.

Conclude with `hfin`. Establish `hA : (∏ᶠ w : Pl E, Real.sqrt (FinitePlace.mk w x)) ^ 2 = ∏ᶠ w : Pl E, FinitePlace.mk w x`. Establish `hfs : Function.HasFiniteMulSupport fun w : Pl E => Real.sqrt (FinitePlace.mk w x)`. Unfold `Function.HasFiniteMulSupport`. Rewrite using `[hsup]`.

Conclude with `hfin`. Rewrite using `[finprod_pow hfs]`. Use `congr 1`. Use function extensionality and compare the values at `w`. Conclude with `Real.sq_sqrt (apply_nonneg _ _)`.

Establish `hF : ∏ᶠ w : Pl E, FinitePlace.mk w x = ∏ᶠ u : FinitePlace E, u x` using `finprod_comp_equiv FinitePlace.equivHeightOneSpectrum.symm (f := fun u : FinitePlace E => u x)`. Establish `hP : (∏ v : InfinitePlace E, ‖v.embedding x‖) ^ 2 = ∏ v : InfinitePlace E, v x ^ v.mult`. Rewrite using `[← Finset.prod_pow]`. Use `congr 1`. Use function extensionality and compare the values at `v`.

Rewrite using `[InfinitePlace.norm_embedding_eq, InfinitePlace.mult, if_neg (InfinitePlace.not_isReal_iff_isComplex.mpr (IsTotallyComplex.isComplex v))]`. Establish `hprod` using `prod_abs_eq_one (K := E) hx`. Establish `hsq : ((∏ᶠ w : Pl E, Real.sqrt (FinitePlace.mk w x)) * ∏ v : InfinitePlace E, ‖v.embedding x‖) ^ 2 = 1`. Rewrite using `[mul_pow, hA, hP, hF, mul_comm]`. Conclude with `hprod`.

Establish `h1 : (∏ᶠ w : Pl E, Real.sqrt (FinitePlace.mk w x)) * ∏ v : InfinitePlace E, ‖v.embedding x‖ = 1` using `(pow_eq_one_iff_of_nonneg (mul_nonneg (finprod_nonneg fun w => Real.sqrt_nonneg _) (Finset.prod_nonneg fun v _ => norm_nonneg _)) two_ne_zero).mp hsq`. Establish `hc : ∏ᶠ w : Pl E, absHalf w (algebraMap E (w.adicCompletion E) x) = ((∏ᶠ w : Pl E, Real.sqrt (FinitePlace.mk w x) : ℝ) : ℂ)`. Repeatedly rewrite using `[key]`. Conclude with `(Complex.ofRealHom.toMonoidHom.map_finprod_of_injective Complex.ofReal_injective _).symm`. Rewrite using `[hc]`.

Conclude with `h1` after adjusting the coercions.
-/
theorem absHalf_prodFormula : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (x : E), x ≠ 0 →
    (Function.mulSupport fun w : Pl E => absHalf w (algebraMap E (w.adicCompletion E) x)).Finite ∧
      (∏ᶠ w : Pl E, absHalf w (algebraMap E (w.adicCompletion E) x)) * ∏ v : InfinitePlace E, (‖v.embedding x‖ : ℂ) = 1 := by
  intro E _ _ _ x hx
  have key : ∀ w : Pl E, absHalf w (algebraMap E (w.adicCompletion E) x) =
      ((Real.sqrt (FinitePlace.mk w x) : ℝ) : ℂ) := fun w =>
    absHalf_eq_sqrt_norm w ((_root_.map_ne_zero _).mpr hx)
  have hfin : (Function.mulSupport fun w : Pl E => FinitePlace.mk w x).Finite := by
    have h0 := FinitePlace.hasFiniteMulSupport (K := E) hx
    have he : (fun w : Pl E => FinitePlace.mk w x) =
        (fun u : FinitePlace E => u x) ∘ FinitePlace.equivHeightOneSpectrum.symm := rfl
    rw [he, Function.mulSupport_comp_eq_preimage]
    exact Set.Finite.preimage (FinitePlace.equivHeightOneSpectrum.symm.injective.injOn) h0
  have hsup : (Function.mulSupport fun w : Pl E => Real.sqrt (FinitePlace.mk w x)) =
      Function.mulSupport fun w : Pl E => FinitePlace.mk w x := by
    ext w
    simp [Real.sqrt_eq_one]
  refine ⟨?_, ?_⟩
  · have hs : (Function.mulSupport fun w : Pl E => absHalf w (algebraMap E (w.adicCompletion E) x)) =
        Function.mulSupport fun w : Pl E => Real.sqrt (FinitePlace.mk w x) := by
      ext w
      simp only [Function.mem_mulSupport, key, ne_eq, Complex.ofReal_eq_one]
    rw [hs, hsup]
    exact hfin
  · have hA : (∏ᶠ w : Pl E, Real.sqrt (FinitePlace.mk w x)) ^ 2 = ∏ᶠ w : Pl E, FinitePlace.mk w x := by
      have hfs : Function.HasFiniteMulSupport fun w : Pl E => Real.sqrt (FinitePlace.mk w x) := by
        unfold Function.HasFiniteMulSupport; rw [hsup]; exact hfin
      rw [finprod_pow hfs]
      congr 1
      funext w
      exact Real.sq_sqrt (apply_nonneg _ _)
    have hF : ∏ᶠ w : Pl E, FinitePlace.mk w x = ∏ᶠ u : FinitePlace E, u x :=
      finprod_comp_equiv FinitePlace.equivHeightOneSpectrum.symm (f := fun u : FinitePlace E => u x)
    have hP : (∏ v : InfinitePlace E, ‖v.embedding x‖) ^ 2 = ∏ v : InfinitePlace E, v x ^ v.mult := by
      rw [← Finset.prod_pow]
      congr 1
      funext v
      rw [InfinitePlace.norm_embedding_eq, InfinitePlace.mult,
        if_neg (InfinitePlace.not_isReal_iff_isComplex.mpr (IsTotallyComplex.isComplex v))]
    have hprod := prod_abs_eq_one (K := E) hx
    have hsq : ((∏ᶠ w : Pl E, Real.sqrt (FinitePlace.mk w x)) * ∏ v : InfinitePlace E, ‖v.embedding x‖) ^ 2 = 1 := by
      rw [mul_pow, hA, hP, hF, mul_comm]
      exact hprod
    have h1 : (∏ᶠ w : Pl E, Real.sqrt (FinitePlace.mk w x)) * ∏ v : InfinitePlace E, ‖v.embedding x‖ = 1 :=
      (pow_eq_one_iff_of_nonneg (mul_nonneg (finprod_nonneg fun w => Real.sqrt_nonneg _)
        (Finset.prod_nonneg fun v _ => norm_nonneg _)) two_ne_zero).mp hsq
    have hc : ∏ᶠ w : Pl E, absHalf w (algebraMap E (w.adicCompletion E) x) =
        ((∏ᶠ w : Pl E, Real.sqrt (FinitePlace.mk w x) : ℝ) : ℂ) := by
      simp_rw [key]
      exact (Complex.ofRealHom.toMonoidHom.map_finprod_of_injective Complex.ofReal_injective _).symm
    rw [hc]
    exact_mod_cast h1

end GlobalTheory.ProdForm
