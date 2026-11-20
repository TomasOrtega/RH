import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicUnitaryOrbits.InclRAlgebraMap
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicUnitaryOrbits.StLamOf
import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.IsEulerProd

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

namespace GlobalTheory.CompanionTheory.SW.LamUnit

/- English proof (translation)
Introduce `hσ`. Take `⟨τ⟩ : Nonempty (E →+* ℂ)` from `inferInstance`. Use `h.2.1` as an intermediate fact. Apply `IsTotallyComplex.complexEmbedding_not_isReal τ` to reduce the goal to its premises. Rewrite using `[ComplexEmbedding.isReal_iff]`.

Use extensionality with `x`. Use `h.2.2.2 τ x` as an intermediate fact. Rewrite `this` using `[hσ]`. Simplify `this.symm` using `[ComplexEmbedding.conjugate_coe_eq]`.
-/
theorem conj_ne_id {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {σ : E →ₐ[F] E} (h : IsCMExt F E σ) : σ ≠ AlgHom.id F E := by
  intro hσ
  obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
  have := h.2.1
  apply IsTotallyComplex.complexEmbedding_not_isReal τ
  rw [ComplexEmbedding.isReal_iff]
  ext x
  have := h.2.2.2 τ x
  rw [hσ] at this
  simpa [ComplexEmbedding.conjugate_coe_eq] using this.symm

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `ha`. Assume the negation of the conclusion as `hnot`. Establish `hli : LinearIndependent F ![(1 : E), a]`. Rewrite using `[LinearIndependent.pair_iff]`.

Introduce `s t hst`. Establish `ht : t = 0`. Assume the negation of the conclusion as `ht`. Apply `hnot` to reduce the goal to its premises. Use `⟨-(s / t), ?_⟩` and prove the remaining obligations.

Establish `ht' : algebraMap F E t ≠ 0` using `(map_ne_zero _).2 ht`. Establish `h1 : algebraMap F E s + algebraMap F E t * a = 0`. Simplify `hst` using `[Algebra.smul_def]`. Rewrite using `[map_neg, map_div₀]`. Clear the denominators using the available nonvanishing facts.

Take the linear combination `-h1`. Substitute `ht` using the available equality. Use `⟨?_, rfl⟩` and prove the remaining obligations. Simplify using `using hst`. Establish `hspan` using `hli.span_eq_top_of_card_eq_finrank (by simp [h.2.2.1])`.

Apply `conj_ne_id h` to reduce the goal to its premises. Establish `hlin : σ.toLinearMap = (AlgHom.id F E).toLinearMap`. Use `LinearMap.ext_on hspan ?_` and prove the remaining obligations. Introduce and unpack `_ ⟨i, rfl⟩`. Use `fin_cases i`.

Simplify using the standard rewrite rules. Simplify using `using ha`. Use extensionality with `x`. Conclude with `LinearMap.congr_fun hlin x`. Introduce and unpack `⟨c, rfl⟩`.

Conclude with `σ.commutes c`.
-/
theorem fixed_iff {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {σ : E →ₐ[F] E} (h : IsCMExt F E σ) (a : E) : σ a = a ↔ a ∈ (algebraMap F E).range := by
  constructor
  · intro ha
    by_contra hnot
    have hli : LinearIndependent F ![(1 : E), a] := by
      rw [LinearIndependent.pair_iff]
      intro s t hst
      have ht : t = 0 := by
        by_contra ht
        apply hnot
        refine ⟨-(s / t), ?_⟩
        have ht' : algebraMap F E t ≠ 0 := (map_ne_zero _).2 ht
        have h1 : algebraMap F E s + algebraMap F E t * a = 0 := by
          simpa [Algebra.smul_def] using hst
        rw [map_neg, map_div₀]
        field_simp
        linear_combination -h1
      subst ht
      refine ⟨?_, rfl⟩
      simpa using hst
    have hspan := hli.span_eq_top_of_card_eq_finrank (by simp [h.2.2.1])
    apply conj_ne_id h
    have hlin : σ.toLinearMap = (AlgHom.id F E).toLinearMap := by
      refine LinearMap.ext_on hspan ?_
      rintro _ ⟨i, rfl⟩
      fin_cases i
      · simp
      · simpa using ha
    ext x
    exact LinearMap.congr_fun hlin x
  · rintro ⟨c, rfl⟩
    exact σ.commutes c

/- English proof (translation)
Introduce `F E _ _ _ _ _ σ hcm R _ _ hU t β`. Take `⟨lam, h1, h2⟩` from `PIW.AdelicOrbitU.stLam F E σ hcm.2.2.1 (fixed_iff hcm) R hU (algebraMap R (R ⊗[F] E) ((β⁻¹ : Rˣ) : R) * t) 1 one_ne_zero`. Use `⟨lam, h1, ?_⟩` and prove the remaining obligations. Establish `hb : IsUnit (algebraMap R (R ⊗[F] E) (β : R))` using `β.isUnit.map _`. Establish `hinv : algebraMap R (R ⊗[F] E) (β : R) * algebraMap R (R ⊗[F] E) ((β⁻¹ : Rˣ) : R) = 1`.

Rewrite using `[← map_mul, Units.mul_inv, map_one]`. Establish `key : algebraMap R (R ⊗[F] E) (β : R) - sigR R σ lam * t = algebraMap R (R ⊗[F] E) (β : R) * (algebraMap F (R ⊗[F] E) 1 - Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR R σ lam * (algebraMap R (R ⊗[F] E) ((β⁻¹ : Rˣ) : R) * t))`. Establish `hs : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR R σ lam = sigR R σ lam` using `rfl`. Rewrite using `[map_one, hs]`. Take the linear combination `(sigR R σ lam * t) * hinv`.

Rewrite using `[key]`. Conclude with `hb.mul h2`.
-/
theorem exists_norm_one_sub_isUnit : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E]
    [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (R : Type) [CommRing R] [Algebra F R],
    PIW.AdelicOrbitU.UnitChoice R → ∀ (t : R ⊗[F] E) (β : Rˣ), ∃ lam : R ⊗[F] E,
      lam * sigR R σ lam = 1 ∧ IsUnit (algebraMap R (R ⊗[F] E) (β : R) - sigR R σ lam * t) := by
  intro F E _ _ _ _ _ σ hcm R _ _ hU t β
  obtain ⟨lam, h1, h2⟩ := PIW.AdelicOrbitU.stLam F E σ hcm.2.2.1 (fixed_iff hcm) R hU
    (algebraMap R (R ⊗[F] E) ((β⁻¹ : Rˣ) : R) * t) 1 one_ne_zero
  refine ⟨lam, h1, ?_⟩
  have hb : IsUnit (algebraMap R (R ⊗[F] E) (β : R)) := β.isUnit.map _
  have hinv : algebraMap R (R ⊗[F] E) (β : R) * algebraMap R (R ⊗[F] E) ((β⁻¹ : Rˣ) : R) = 1 := by
    rw [← map_mul, Units.mul_inv, map_one]
  have key : algebraMap R (R ⊗[F] E) (β : R) - sigR R σ lam * t =
      algebraMap R (R ⊗[F] E) (β : R) * (algebraMap F (R ⊗[F] E) 1 -
        Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR R σ lam * (algebraMap R (R ⊗[F] E) ((β⁻¹ : Rˣ) : R) * t)) := by
    have hs : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR R σ lam = sigR R σ lam := rfl
    rw [map_one, hs]
    linear_combination (sigR R σ lam * t) * hinv
  rw [key]
  exact hb.mul h2

end GlobalTheory.CompanionTheory.SW.LamUnit
