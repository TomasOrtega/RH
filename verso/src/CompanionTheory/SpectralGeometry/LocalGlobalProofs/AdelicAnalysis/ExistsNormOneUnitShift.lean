import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicUnitaryOrbits.InclRAlgebraMap
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicUnitaryOrbits.StLamOf
import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.IsEulerProd

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

namespace GlobalTheory.CompanionTheory.SW.LamUnit

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Establish an intermediate fact. Reduce the claim to the hypotheses of an applicable result. Rewrite the conclusion using the stated equalities.

By extensionality, compare the relevant components. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Simplify to obtain the desired conclusion from the available facts.
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
Prove the components needed by the constructor for the conclusion. Fix the arbitrary inputs or assume the hypotheses. Assume the negation of the conclusion and derive a contradiction. Establish an intermediate fact. Rewrite the conclusion using the stated equalities.

Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Assume the negation of the conclusion and derive a contradiction. Reduce the claim to the hypotheses of an applicable result. Reduce the conclusion to the remaining proof obligations.

Establish an intermediate fact. Establish an intermediate fact. Simplify to obtain the desired conclusion from the available facts. Rewrite the conclusion using the stated equalities. Clear the denominators using the available nonvanishing facts.

Take a linear combination of the given relations to obtain the conclusion. Substitute using the available equality. Reduce the conclusion to the remaining proof obligations. Simplify to obtain the desired conclusion from the available facts. Establish an intermediate fact.

Reduce the claim to the hypotheses of an applicable result. Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations. Assume the hypotheses and unpack their components. Simplify using the standard rewrite rules.

Simplify to obtain the desired conclusion from the available facts. By extensionality, compare the relevant components. Assume the hypotheses and unpack their components. A detailed English derivation is pending.
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
Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Establish an intermediate fact.

Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Take a linear combination of the given relations to obtain the conclusion.

Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
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
