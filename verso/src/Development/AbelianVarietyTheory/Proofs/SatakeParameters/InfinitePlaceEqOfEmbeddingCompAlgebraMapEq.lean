import Mathlib
open NumberField

namespace GlobalTheory

/- English proof (translation)
Use `set τ : F →+* ℂ := w₁.embedding.comp (algebraMap F E) with hτ`. Establish `hτreal : ComplexEmbedding.IsReal τ`. Use `IsTotallyReal.isReal (InfinitePlace.mk τ)` as an intermediate fact. Conclude with `InfinitePlace.isReal_mk_iff.mp this`. Use `letI : Algebra F ℂ := τ.toAlgebra`.

Establish `mkAlg : ∀ σ : E →+* ℂ, σ.comp (algebraMap F E) = τ → ∃ a : E →ₐ[F] ℂ, (a : E →+* ℂ) = σ` using `fun σ hσ => ⟨{ σ with commutes' := fun r => by`. Express the relevant statement in the definitionally equal form `σ (algebraMap F E r) = τ r`. Rewrite using `[← hσ]`. Use `rfl }, rfl⟩`. Take `⟨a, ha⟩` from `mkAlg w₁.embedding rfl`.

Take `⟨b, hb⟩` from `mkAlg (ComplexEmbedding.conjugate w₁.embedding) (by`. Use extensionality with `r`. Use `RingHom.congr_fun hτreal r` as an intermediate fact. Simplify using `only [RingHom.comp_apply, ComplexEmbedding.conjugate_coe_eq, Function.comp_apply]`. Simplify `this)` using `[ComplexEmbedding.conjugate_coe_eq, hτ]`.

Take `⟨c, hc⟩` from `mkAlg w₂.embedding h.symm`. Establish `hab : a ≠ b`. Introduce `hab`. Establish `hc1 : ¬ ComplexEmbedding.IsReal w₁.embedding`. Rewrite using `[← InfinitePlace.isReal_iff]`.

Conclude with `InfinitePlace.not_isReal_iff_isComplex.mpr (IsTotallyComplex.isComplex w₁)`. Apply `hc1` to reduce the goal to its premises. Rewrite using `[ComplexEmbedding.isReal_iff, ← hb, ← ha, hab]`. Establish `hcard : Fintype.card (E →ₐ[F] ℂ) = 2`. Rewrite using `[AlgHom.card, Algebra.IsQuadraticExtension.finrank_eq_two]`.

Establish `hcab : c = a ∨ c = b`. Assume the negation of the conclusion as `hne`. Use `push_neg at hne`. Establish `h3 : ({a, b, c} : Finset (E →ₐ[F] ℂ)).card = 3`. Rewrite using `[Finset.card_insert_of_notMem, Finset.card_pair]`.

Conclude with `fun e => hne.2 e.symm`. Simplify using `only [Finset.mem_insert, Finset.mem_singleton, not_or]`. Conclude with `⟨hab, fun e => hne.1 e.symm⟩`. Use `Finset.card_le_univ ({a, b, c} : Finset (E →ₐ[F] ℂ))` as an intermediate fact. Use linear arithmetic over natural numbers and integers.

Rewrite using `[← InfinitePlace.mk_embedding w₁, ← InfinitePlace.mk_embedding w₂, InfinitePlace.mk_eq_iff]`. Break down `hcab with e | e` into its components or cases. Use `left`. Rewrite using `[← ha, ← hc, e]`. Use `right`.

Rewrite using `[← hb, ← hc, e]`.
-/
theorem infinitePlace_eq_of_embedding_comp_algebraMap_eq (F E : Type) [Field F] [NumberField F]
    [Field E] [NumberField E] [Algebra F E] [IsTotallyReal F] [IsTotallyComplex E]
    [Algebra.IsQuadraticExtension F E] (w₁ w₂ : InfinitePlace E)
    (h : w₁.embedding.comp (algebraMap F E) = w₂.embedding.comp (algebraMap F E)) : w₁ = w₂ := by
  classical
  set τ : F →+* ℂ := w₁.embedding.comp (algebraMap F E) with hτ
  have hτreal : ComplexEmbedding.IsReal τ := by
    have := IsTotallyReal.isReal (InfinitePlace.mk τ)
    exact InfinitePlace.isReal_mk_iff.mp this
  letI : Algebra F ℂ := τ.toAlgebra
  have mkAlg : ∀ σ : E →+* ℂ, σ.comp (algebraMap F E) = τ → ∃ a : E →ₐ[F] ℂ, (a : E →+* ℂ) = σ :=
    fun σ hσ => ⟨{ σ with
      commutes' := fun r => by
        change σ (algebraMap F E r) = τ r
        rw [← hσ]; rfl }, rfl⟩
  obtain ⟨a, ha⟩ := mkAlg w₁.embedding rfl
  obtain ⟨b, hb⟩ := mkAlg (ComplexEmbedding.conjugate w₁.embedding) (by
    ext r
    have := RingHom.congr_fun hτreal r
    simp only [RingHom.comp_apply, ComplexEmbedding.conjugate_coe_eq, Function.comp_apply]
    simpa [ComplexEmbedding.conjugate_coe_eq, hτ] using this)
  obtain ⟨c, hc⟩ := mkAlg w₂.embedding h.symm
  have hab : a ≠ b := by
    intro hab
    have hc1 : ¬ ComplexEmbedding.IsReal w₁.embedding := by
      rw [← InfinitePlace.isReal_iff]
      exact InfinitePlace.not_isReal_iff_isComplex.mpr (IsTotallyComplex.isComplex w₁)
    apply hc1
    rw [ComplexEmbedding.isReal_iff, ← hb, ← ha, hab]
  have hcard : Fintype.card (E →ₐ[F] ℂ) = 2 := by
    rw [AlgHom.card, Algebra.IsQuadraticExtension.finrank_eq_two]
  have hcab : c = a ∨ c = b := by
    by_contra hne
    push_neg at hne
    have h3 : ({a, b, c} : Finset (E →ₐ[F] ℂ)).card = 3 := by
      rw [Finset.card_insert_of_notMem, Finset.card_pair]
      · exact fun e => hne.2 e.symm
      · simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
        exact ⟨hab, fun e => hne.1 e.symm⟩
    have := Finset.card_le_univ ({a, b, c} : Finset (E →ₐ[F] ℂ))
    omega
  rw [← InfinitePlace.mk_embedding w₁, ← InfinitePlace.mk_embedding w₂, InfinitePlace.mk_eq_iff]
  rcases hcab with e | e
  · left; rw [← ha, ← hc, e]
  · right; rw [← hb, ← hc, e]

end GlobalTheory
