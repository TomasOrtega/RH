import Mathlib
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.IsotropicMahlerBounds.LogAbsoluteWedges.LogAbsBasic

noncomputable section

open NumberField IsDedekindDomain PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.D1 GlobalTheory.CuspRep

namespace GlobalTheory.CompanionTheory.LogAbs

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E]

/- English proof (translation)
Establish `h` using `(FiniteAdeleRing.isUnit_iff.1 (hu.map (pFin E))).2`. Use `filter_upwards [h] with w hw`. Establish `e : cW w u = (pFin E u) w` using `rfl`. Rewrite using `[e, FinitePlace.norm_def, hw]`. Simplify using the standard rewrite rules.
-/
theorem norm_cW_eq_one (u : Ad E) (hu : IsUnit u) : ∀ᶠ w in Filter.cofinite, ‖cW w u‖ = 1 := by
  have h := (FiniteAdeleRing.isUnit_iff.1 (hu.map (pFin E))).2
  filter_upwards [h] with w hw
  have e : cW w u = (pFin E u) w := rfl
  rw [e, FinitePlace.norm_def, hw]
  simp

/- English proof (translation)
Use `(Filter.eventually_cofinite.1 (norm_cW_eq_one u hu)).subset fun w hw h1 => hw ?_` and prove the remaining obligations. Simplify using `[h1]`.
-/
theorem support_log_finite (u : Ad E) (hu : IsUnit u) :
    (Function.support fun w => Real.log ‖cW w u‖).Finite := by
  refine (Filter.eventually_cofinite.1 (norm_cW_eq_one u hu)).subset fun w hw h1 => hw ?_
  simp [h1]

/- English proof (translation)
Establish `h1 : ∀ v, Real.log (‖cV v (u * u')‖ ^ 2) = Real.log (‖cV v u‖ ^ 2) + Real.log (‖cV v u'‖ ^ 2)` using `fun v => by`. Rewrite using `[map_mul, norm_mul, mul_pow, Real.log_mul (pow_ne_zero 2 (norm_ne_zero_iff.2 (hu.map (cV v)).ne_zero)) (pow_ne_zero 2 (norm_ne_zero_iff.2 (hu'.map (cV v)).ne_zero))]`. Establish `h2 : ∀ w, Real.log ‖cW w (u * u')‖ = Real.log ‖cW w u‖ + Real.log ‖cW w u'‖` using `fun w => by`. Rewrite using `[map_mul, norm_mul, Real.log_mul (norm_ne_zero_iff.2 (hu.map (cW w)).ne_zero) (norm_ne_zero_iff.2 (hu'.map (cW w)).ne_zero)]`. Unfold `logAbs`.

Simplify using `only [h1, h2]`. Rewrite using `[Finset.sum_add_distrib, finsum_add_distrib (support_log_finite u hu) (support_log_finite u' hu')]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem logAbs_mul (u u' : Ad E) (hu : IsUnit u) (hu' : IsUnit u') :
    logAbs (u * u') = logAbs u + logAbs u' := by
  have h1 : ∀ v, Real.log (‖cV v (u * u')‖ ^ 2) = Real.log (‖cV v u‖ ^ 2) + Real.log (‖cV v u'‖ ^ 2) := fun v => by
    rw [map_mul, norm_mul, mul_pow, Real.log_mul
      (pow_ne_zero 2 (norm_ne_zero_iff.2 (hu.map (cV v)).ne_zero))
      (pow_ne_zero 2 (norm_ne_zero_iff.2 (hu'.map (cV v)).ne_zero))]
  have h2 : ∀ w, Real.log ‖cW w (u * u')‖ = Real.log ‖cW w u‖ + Real.log ‖cW w u'‖ := fun w => by
    rw [map_mul, norm_mul, Real.log_mul (norm_ne_zero_iff.2 (hu.map (cW w)).ne_zero)
      (norm_ne_zero_iff.2 (hu'.map (cW w)).ne_zero)]
  unfold logAbs
  simp only [h1, h2]
  rw [Finset.sum_add_distrib, finsum_add_distrib (support_log_finite u hu) (support_log_finite u' hu')]
  ring

/- English proof (translation)
Rewrite using `[← InfinitePlace.norm_embedding_eq]`. Conclude with `congrArg norm (pInf_algebraMap c v)`.
-/
theorem norm_cV_algebraMap (v : InfinitePlace E) (c : E) : ‖cV v (algebraMap E (Ad E) c)‖ = v c := by
  rw [← InfinitePlace.norm_embedding_eq]
  exact congrArg norm (pInf_algebraMap c v)

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem norm_cW_algebraMap (w : HeightOneSpectrum (𝓞 E)) (c : E) :
    ‖cW w (algebraMap E (Ad E) c)‖ = FinitePlace.mk w c := rfl

/- English proof (translation)
Establish `hprod` using `prod_abs_eq_one hc`. Establish `hA : (∏ w : InfinitePlace E, w c ^ w.mult) ≠ 0` using `left_ne_zero_of_mul_eq_one hprod`. Establish `hB : (∏ᶠ w : FinitePlace E, w c) ≠ 0` using `right_ne_zero_of_mul_eq_one hprod`. Establish `hlog` using `congrArg Real.log hprod`. Rewrite `hlog` using `[Real.log_mul hA hB, Real.log_one, Real.log_prod (fun w _ => pow_ne_zero _ ((InfinitePlace.pos_iff.2 hc).ne')), Real.log_finprod fun w : FinitePlace E => FinitePlace.pos_iff.2 hc]`.

Establish `hm : ∀ v : InfinitePlace E, v.mult = 2` using `fun v => InfinitePlace.mult_isComplex ⟨v, IsTotallyComplex.isComplex v⟩`. Unfold `logAbs`. Simplify using `only [norm_cV_algebraMap, norm_cW_algebraMap]`. Simplify using `only [hm] at hlog`. Rewrite using `[← hlog, ← finsum_comp_equiv (FinitePlace.equivHeightOneSpectrum (K := E)).symm]`.

Both sides reduce to the same expression.
-/
theorem logAbs_algebraMap (c : E) (hc : c ≠ 0) : logAbs (algebraMap E (Ad E) c) = 0 := by
  have hprod := prod_abs_eq_one hc
  have hA : (∏ w : InfinitePlace E, w c ^ w.mult) ≠ 0 := left_ne_zero_of_mul_eq_one hprod
  have hB : (∏ᶠ w : FinitePlace E, w c) ≠ 0 := right_ne_zero_of_mul_eq_one hprod
  have hlog := congrArg Real.log hprod
  rw [Real.log_mul hA hB, Real.log_one, Real.log_prod (fun w _ => pow_ne_zero _ ((InfinitePlace.pos_iff.2 hc).ne')),
    Real.log_finprod fun w : FinitePlace E => FinitePlace.pos_iff.2 hc] at hlog
  have hm : ∀ v : InfinitePlace E, v.mult = 2 := fun v =>
    InfinitePlace.mult_isComplex ⟨v, IsTotallyComplex.isComplex v⟩
  unfold logAbs
  simp only [norm_cV_algebraMap, norm_cW_algebraMap]
  simp only [hm] at hlog
  rw [← hlog, ← finsum_comp_equiv (FinitePlace.equivHeightOneSpectrum (K := E)).symm]
  rfl

/- English proof (translation)
Introduce `_ _ _ _` and use `⟨support_log_finite, logAbs_mul, logAbs_algebraMap⟩`.
-/
theorem logAbsBasic : LogAbsBasic := fun _ _ _ _ =>
  ⟨support_log_finite, logAbs_mul, logAbs_algebraMap⟩

end GlobalTheory.CompanionTheory.LogAbs

end
