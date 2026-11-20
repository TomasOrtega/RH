import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.QuadraticClassFieldTheory
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.HasseNormTheoremQuadraticExtension
import Development.AbelianVarietyTheory.Proofs.HeightProofs.QuadraticExtNormFormOverAlgebra

open NumberField IsDedekindDomain

namespace GlobalTheory.QuadSymbol

/- English proof (translation)
Establish `hr : Module.finrank K L = 2` using `Algebra.IsQuadraticExtension.finrank_eq_two K L`. Establish `: FiniteDimensional K L` using `Module.finite_of_finrank_pos (by omega)`. Establish `: IsGalois K L` using `inferInstance`. Establish `hc : Nat.card (L ≃ₐ[K] L) = 2` using `by rw [IsGalois.card_aut_eq_finrank, hr]`. Establish `: Nontrivial (L ≃ₐ[K] L)` using `Finite.one_lt_card_iff_nontrivial.1 (by omega)`.

Take `⟨σ, hσ⟩` from `exists_ne (1 : L ≃ₐ[K] L)`. Establish `h2 : σ * σ = 1`. Use `pow_card_eq_one' (x := σ)` as an intermediate fact. Rewrite `this` using `[hc, pow_two]`. Then use the resulting hypothesis. Take `⟨δ, b, hδ, h0, -, h1⟩` from `GlobalTheory.QuadNormBase.exists_basis K L (σ : L →ₐ[K] L) hr (fun x => by simpa using congrArg (fun f : L ≃ₐ[K] L => f x) h2) (by`.

Assume the negation of the conclusion as `h`. Use `push Not at h`. Conclude with `hσ (AlgEquiv.ext fun x => h x))`. Conclude with `⟨δ, b, hδ, h0, h1⟩`.
-/
theorem exists_basis_of_isQuadraticExtension (K L : Type) [Field K] [CharZero K] [Field L] [Algebra K L]
    [Algebra.IsQuadraticExtension K L] :
    ∃ (δ : K) (e : Module.Basis (Fin 2) K L), ¬ IsSquare δ ∧ e 0 = 1 ∧ e 1 * e 1 = algebraMap K L δ := by
  have hr : Module.finrank K L = 2 := Algebra.IsQuadraticExtension.finrank_eq_two K L
  have : FiniteDimensional K L := Module.finite_of_finrank_pos (by omega)
  have : IsGalois K L := inferInstance
  have hc : Nat.card (L ≃ₐ[K] L) = 2 := by rw [IsGalois.card_aut_eq_finrank, hr]
  have : Nontrivial (L ≃ₐ[K] L) := Finite.one_lt_card_iff_nontrivial.1 (by omega)
  obtain ⟨σ, hσ⟩ := exists_ne (1 : L ≃ₐ[K] L)
  have h2 : σ * σ = 1 := by
    have := pow_card_eq_one' (x := σ)
    rwa [hc, pow_two] at this
  obtain ⟨δ, b, hδ, h0, -, h1⟩ := GlobalTheory.QuadNormBase.exists_basis K L (σ : L →ₐ[K] L) hr
    (fun x => by simpa using congrArg (fun f : L ≃ₐ[K] L => f x) h2)
    (by
      by_contra h
      push Not at h
      exact hσ (AlgEquiv.ext fun x => h x))
  exact ⟨δ, b, hδ, h0, h1⟩

/- English proof (translation)
Establish `hφ : ComplexEmbedding.IsReal (Complex.ofRealHom.comp σ)`. Rewrite using `[ComplexEmbedding.isReal_iff]`. Use extensionality with `x`. Simplify using the standard rewrite rules. Establish `hw : (InfinitePlace.mk (Complex.ofRealHom.comp σ)).IsReal` using `InfinitePlace.isReal_mk_iff.2 hφ`.

Use `⟨_, InfinitePlace.Completion.extensionEmbeddingOfIsReal hw, fun x => ?_⟩` and prove the remaining obligations. Establish `he` using `InfinitePlace.Completion.extensionEmbeddingOfIsReal_coe hw ((WithAbs.equiv _).symm x)`. Use `Eq.trans he ?_` and prove the remaining obligations. Apply `Complex.ofReal_injective` to reduce the goal to its premises. Rewrite using `[InfinitePlace.embedding_of_isReal_apply, InfinitePlace.embedding_mk_eq_of_isReal hφ]`.

Simplify using the standard rewrite rules.
-/
theorem exists_completion_hom_real {K : Type} [Field K] (σ : K →+* ℝ) :
    ∃ (w : InfinitePlace K) (f : w.Completion →+* ℝ), ∀ x : K, f (algebraMap K w.Completion x) = σ x := by
  have hφ : ComplexEmbedding.IsReal (Complex.ofRealHom.comp σ) := by
    rw [ComplexEmbedding.isReal_iff]
    ext x
    simp
  have hw : (InfinitePlace.mk (Complex.ofRealHom.comp σ)).IsReal := InfinitePlace.isReal_mk_iff.2 hφ
  refine ⟨_, InfinitePlace.Completion.extensionEmbeddingOfIsReal hw, fun x => ?_⟩
  have he := InfinitePlace.Completion.extensionEmbeddingOfIsReal_coe hw
    ((WithAbs.equiv _).symm x)
  refine Eq.trans he ?_
  apply Complex.ofReal_injective
  rw [InfinitePlace.embedding_of_isReal_apply, InfinitePlace.embedding_mk_eq_of_isReal hφ]
  simp

/- English proof (translation)
Introduce `K L _ _ _ _ _ _ t`. Take `⟨δ, e, hδ, h0, h1⟩` from `exists_basis_of_isQuadraticExtension K L`. Establish `: FiniteDimensional K L` using `Module.Finite.of_basis e`. Use `⟨fun h => ⟨fun v => toUnits_mem_normGroup _ h, fun w => toUnits_mem_normGroup _ h⟩, ?_⟩` and prove the remaining obligations. Introduce and unpack `⟨hf, hi⟩`.

Establish `hδ0 : δ ≠ 0`. Introduce and unpack `rfl`. Conclude with `hδ ⟨0, by simp⟩`. Take `⟨a, b, hab⟩` from `GlobalTheory.QNorm.hasseNormSt K δ t hδ0 t.ne_zero (fun σ => by`. Take `⟨w, f, hw⟩` from `exists_completion_hom_real σ`.

Take `⟨a, b, hab⟩` from `(mem_normGroup_iff_form e h0 h1).1 (hi w)`. Use `⟨f a, f b, ?_⟩` and prove the remaining obligations. Establish `h3 : algebraMap K w.Completion t = a ^ 2 - algebraMap K w.Completion δ * b ^ 2` using `hab`. Rewrite using `[← hw, ← hw, h3, map_sub, map_mul, map_pow, map_pow])`. Use the proof step `(fun v => (mem_normGroup_iff_form e h0 h1).1 (hf v))`.

Use `mem_globalNorms_iff.2 ⟨a • e 0 + b • e 1, ?_⟩` and prove the remaining obligations. Rewrite using `[hab]`. Use `GlobalTheory.QuadNormBase.norm_of_basis e δ h0 ?_ a b` and prove the remaining obligations. Rewrite using `[h1, h0, Algebra.algebraMap_eq_smul_one]`.
-/
theorem normTheorem : ∀ (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    [Algebra.IsQuadraticExtension K L], NormTheorem K L := by
  intro K L _ _ _ _ _ _ t
  obtain ⟨δ, e, hδ, h0, h1⟩ := exists_basis_of_isQuadraticExtension K L
  have : FiniteDimensional K L := Module.Finite.of_basis e
  refine ⟨fun h => ⟨fun v => toUnits_mem_normGroup _ h, fun w => toUnits_mem_normGroup _ h⟩, ?_⟩
  rintro ⟨hf, hi⟩
  have hδ0 : δ ≠ 0 := by
    rintro rfl
    exact hδ ⟨0, by simp⟩
  obtain ⟨a, b, hab⟩ := GlobalTheory.QNorm.hasseNormSt K δ t hδ0 t.ne_zero
    (fun σ => by
      obtain ⟨w, f, hw⟩ := exists_completion_hom_real σ
      obtain ⟨a, b, hab⟩ := (mem_normGroup_iff_form e h0 h1).1 (hi w)
      refine ⟨f a, f b, ?_⟩
      have h3 : algebraMap K w.Completion t = a ^ 2 - algebraMap K w.Completion δ * b ^ 2 := hab
      rw [← hw, ← hw, h3, map_sub, map_mul, map_pow, map_pow])
    (fun v => (mem_normGroup_iff_form e h0 h1).1 (hf v))
  refine mem_globalNorms_iff.2 ⟨a • e 0 + b • e 1, ?_⟩
  rw [hab]
  refine GlobalTheory.QuadNormBase.norm_of_basis e δ h0 ?_ a b
  rw [h1, h0, Algebra.algebraMap_eq_smul_one]

end GlobalTheory.QuadSymbol
