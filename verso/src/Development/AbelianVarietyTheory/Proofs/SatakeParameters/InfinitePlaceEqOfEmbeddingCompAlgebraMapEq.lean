import Mathlib
open NumberField

namespace GlobalTheory

/- English proof (translation)
Establish an intermediate fact. Establish an intermediate fact. Equip the data with the indicated structure. Establish an intermediate fact. Express the relevant assertion in an equivalent form by its definition.

Rewrite the conclusion using the stated equalities. Both sides reduce to the same expression. Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result. By extensionality, compare the relevant components.

Establish an intermediate fact. Simplify using the standard rewrite rules. Simplify to obtain the desired conclusion from the available facts. Extract witnesses or component facts from the available result. Establish an intermediate fact.

Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Reduce the claim to the hypotheses of an applicable result. Rewrite the conclusion using the stated equalities.

Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Assume the negation of the conclusion and derive a contradiction. Establish an intermediate fact.

Rewrite the conclusion using the stated equalities. Fix the arbitrary inputs and assume any hypotheses. A detailed English derivation is pending. Simplify using the standard rewrite rules. Supply the required witnesses or components. Establish an intermediate fact.

Use linear arithmetic over natural numbers and integers. Rewrite the conclusion using the stated equalities. Separate the alternatives or extract the components of the hypothesis. Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities.

A detailed English derivation is pending.
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
