import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.IdealLatticeBasis.IdealBasisAlt

open NumberField

namespace PI.IdealLatticeWork

/- English proof (translation)
Apply the tactic sequence `apply Complex.ext <;> simp [sq, Complex.mul_re, Complex.mul_im] <;> ring`.
-/
theorem sq_det_two (x y : ℂ) :
    (x * (starRingEnd ℂ) y - (starRingEnd ℂ) x * y) ^ 2
      = (((-4) * (((starRingEnd ℂ) x * y).im) ^ 2 : ℝ) : ℂ) := by
  apply Complex.ext <;> simp [sq, Complex.mul_re, Complex.mul_im] <;> ring

/- English proof (translation)
Introduce `h`. Establish `hr : NumberField.ComplexEmbedding.IsReal φ`. Rewrite using `[NumberField.ComplexEmbedding.isReal_iff]`. Use extensionality with `x`. Use `congrArg (fun f : K →+* ℂ => f x) h` as an intermediate fact.

Simplify `this.symm` using `[NumberField.ComplexEmbedding.conjugate_coe_eq]`. Conclude with `hnr.false hr.embedding`.
-/
theorem ne_conj {K : Type} [Field K] (φ : K →+* ℂ) (hnr : IsEmpty (K →+* ℝ)) :
    φ ≠ (starRingEnd ℂ).comp φ := by
  intro h
  have hr : NumberField.ComplexEmbedding.IsReal φ := by
    rw [NumberField.ComplexEmbedding.isReal_iff]
    ext x
    have := congrArg (fun f : K →+* ℂ => f x) h
    simpa [NumberField.ComplexEmbedding.conjugate_coe_eq] using this.symm
  exact hnr.false hr.embedding

/- English proof (translation)
Introduce `K _ _ φ hK hnr b`. Use `set bQ := b.localizationLocalization ℚ (nonZeroDivisors ℤ) K with hbQ`. Establish `hbQi : ∀ i, bQ i = (b i : K)` using `fun i => Module.Basis.localizationLocalization_apply ℚ (nonZeroDivisors ℤ) K b i`. Establish `hdQ : Algebra.discr ℚ bQ = (NumberField.discr K : ℚ)`. Rewrite using `[hbQ, Algebra.discr_localizationLocalization ℤ (nonZeroDivisors ℤ) K b, NumberField.discr_eq_discr]`.

Simplify using the standard rewrite rules. Set `φQ : K →ₐ[ℚ] ℂ` to `φ.toRatAlgHom`. Set `ψQ : K →ₐ[ℚ] ℂ` to `((starRingEnd ℂ).comp φ).toRatAlgHom`. Establish `hne : φQ ≠ ψQ`. Introduce `h`.

Apply `ne_conj φ hnr` to reduce the goal to its premises. Use extensionality with `x`. Use `congrArg (fun f : K →ₐ[ℚ] ℂ => f x) h` as an intermediate fact. Simplify `this` using `[φQ, ψQ]`. Establish `hcard : Fintype.card (K →ₐ[ℚ] ℂ) = 2`.

Rewrite using `[AlgHom.card ℚ K ℂ, hK]`. Establish `huniv : (Finset.univ : Finset (K →ₐ[ℚ] ℂ)) = {φQ, ψQ}`. Use `symm`. Apply `Finset.eq_of_subset_of_card_le (Finset.subset_univ _)` to reduce the goal to its premises. Rewrite using `[Finset.card_univ, hcard, Finset.card_pair hne]`.

Establish `htr : ∀ z : K, algebraMap ℚ ℂ (Algebra.trace ℚ K z) = φ z + (starRingEnd ℂ) (φ z)`. Introduce `z`. Rewrite using `[trace_eq_sum_embeddings ℂ (x := z), huniv, Finset.sum_pair hne]`. Simplify using `[φQ, ψQ]`. Use `set x := φ (b 0 : K)`.

Use `set y := φ (b 1 : K)`. Establish `key : algebraMap ℚ ℂ (Algebra.discr ℚ bQ) = (x * (starRingEnd ℂ) y - (starRingEnd ℂ) x * y) ^ 2`. Rewrite using `[Algebra.discr_def, RingHom.map_det, Matrix.det_fin_two]`. Simplify using `only [RingHom.mapMatrix_apply, Matrix.map_apply, Algebra.traceMatrix_apply, Algebra.traceForm_apply, htr, hbQi, map_mul]`. Expand and normalize the polynomial expressions, which then agree.

Establish `key2 : ((NumberField.discr K : ℝ) : ℂ) = (x * (starRingEnd ℂ) y - (starRingEnd ℂ) x * y) ^ 2`. Rewrite using `[← key, hdQ, map_intCast, Complex.ofReal_intCast]`. Establish `hreal : (NumberField.discr K : ℝ) = -4 * ((starRingEnd ℂ) x * y).im ^ 2`. Apply `Complex.ofReal_injective` to reduce the goal to its premises. Rewrite using `[key2, sq_det_two]`.

Establish `h4 : |(-4 * ((starRingEnd ℂ) x * y).im ^ 2 : ℝ)| = (2 * |((starRingEnd ℂ) x * y).im|) ^ 2`. Rewrite using `[abs_of_nonpos (by nlinarith [sq_nonneg ((starRingEnd ℂ) x * y).im]), mul_pow, sq_abs]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[hreal, h4, Real.sqrt_sq (by positivity)]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem okArea : OKArea := by
  classical
  intro K _ _ φ hK hnr b
  set bQ := b.localizationLocalization ℚ (nonZeroDivisors ℤ) K with hbQ
  have hbQi : ∀ i, bQ i = (b i : K) := fun i =>
    Module.Basis.localizationLocalization_apply ℚ (nonZeroDivisors ℤ) K b i
  have hdQ : Algebra.discr ℚ bQ = (NumberField.discr K : ℚ) := by
    rw [hbQ, Algebra.discr_localizationLocalization ℤ (nonZeroDivisors ℤ) K b,
      NumberField.discr_eq_discr]
    simp

  let φQ : K →ₐ[ℚ] ℂ := φ.toRatAlgHom
  let ψQ : K →ₐ[ℚ] ℂ := ((starRingEnd ℂ).comp φ).toRatAlgHom
  have hne : φQ ≠ ψQ := by
    intro h
    apply ne_conj φ hnr
    ext x
    have := congrArg (fun f : K →ₐ[ℚ] ℂ => f x) h
    simpa [φQ, ψQ] using this
  have hcard : Fintype.card (K →ₐ[ℚ] ℂ) = 2 := by
    rw [AlgHom.card ℚ K ℂ, hK]
  have huniv : (Finset.univ : Finset (K →ₐ[ℚ] ℂ)) = {φQ, ψQ} := by
    symm
    apply Finset.eq_of_subset_of_card_le (Finset.subset_univ _)
    rw [Finset.card_univ, hcard, Finset.card_pair hne]
  have htr : ∀ z : K, algebraMap ℚ ℂ (Algebra.trace ℚ K z) = φ z + (starRingEnd ℂ) (φ z) := by
    intro z
    rw [trace_eq_sum_embeddings ℂ (x := z), huniv, Finset.sum_pair hne]
    simp [φQ, ψQ]
  set x := φ (b 0 : K)
  set y := φ (b 1 : K)

  have key : algebraMap ℚ ℂ (Algebra.discr ℚ bQ) =
      (x * (starRingEnd ℂ) y - (starRingEnd ℂ) x * y) ^ 2 := by
    rw [Algebra.discr_def, RingHom.map_det, Matrix.det_fin_two]
    simp only [RingHom.mapMatrix_apply, Matrix.map_apply, Algebra.traceMatrix_apply,
      Algebra.traceForm_apply, htr, hbQi, map_mul]
    ring
  have key2 : ((NumberField.discr K : ℝ) : ℂ) = (x * (starRingEnd ℂ) y - (starRingEnd ℂ) x * y) ^ 2 := by
    rw [← key, hdQ, map_intCast, Complex.ofReal_intCast]
  have hreal : (NumberField.discr K : ℝ) = -4 * ((starRingEnd ℂ) x * y).im ^ 2 := by
    apply Complex.ofReal_injective
    rw [key2, sq_det_two]
  have h4 : |(-4 * ((starRingEnd ℂ) x * y).im ^ 2 : ℝ)| = (2 * |((starRingEnd ℂ) x * y).im|) ^ 2 := by
    rw [abs_of_nonpos (by nlinarith [sq_nonneg ((starRingEnd ℂ) x * y).im]), mul_pow, sq_abs]
    ring
  rw [hreal, h4, Real.sqrt_sq (by positivity)]
  ring

end PI.IdealLatticeWork
