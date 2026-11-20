import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DiffsZeroOfLev
import Development.AbelianVarietyTheory.Proofs.HermitianTraceForms.PosIndexMapEqCardOfCongrDiagonal
open scoped Matrix
open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThK.DescB

namespace GlobalTheory.IdxAll

/- English proof (translation)
Take `⟨-, hc, h2, hσ⟩` from `h`. Use `haveI : Algebra.IsQuadraticExtension F E := { finrank_eq_two' := h2 }`. Take `⟨g, hg⟩` from `NumberField.ComplexEmbedding.exists_comp_symm_eq_of_comp_eq (k := F) e τ heτ`. Establish `hσσ : ∀ x, σ (σ x) = x` using `fun x => e.injective (by rw [hσ, hσ, star_star])`. Set `s : E ≃ₐ[F] E` to `AlgEquiv.ofAlgHom σ σ (AlgHom.ext hσσ) (AlgHom.ext hσσ)`.

Establish `hs : s ≠ 1`. Introduce `h1`. Use `IsTotallyComplex.complexEmbedding_not_isReal e ?_` and prove the remaining obligations. Rewrite using `[ComplexEmbedding.isReal_iff]`. Use extensionality with `x`.

Establish `: σ x = x` using `congrArg (fun t : E ≃ₐ[F] E => t x) h1`. Establish `h3` using `hσ e x`. Rewrite `h3` using `[this]`. Conclude with `h3.symm`. Establish `hcard : Nat.card (E ≃ₐ[F] E) = 2` using `by rw [IsGalois.card_aut_eq_finrank, h2]`.

Take `⟨y, -, hy⟩` from `(Nat.card_eq_two_iff' (1 : E ≃ₐ[F] E)).1 hcard`. Distinguish the cases in `hg1 : g.symm = 1`. Use `left`. Rewrite using `[← hg, hg1]`. Both sides reduce to the same expression.

Use `right`. Introduce `x`. Rewrite using `[← hg, (hy _ hg1).trans (hy _ hs).symm]`. Conclude with `hσ e x`.
-/
theorem eq_or_eq_comp {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (h : IsCMExt F E σ) (e τ : E →+* ℂ) (heτ : e.comp (algebraMap F E) = τ.comp (algebraMap F E)) :
    τ = e ∨ ∀ x, τ x = star (e x) := by
  obtain ⟨-, hc, h2, hσ⟩ := h
  haveI : Algebra.IsQuadraticExtension F E := { finrank_eq_two' := h2 }
  obtain ⟨g, hg⟩ := NumberField.ComplexEmbedding.exists_comp_symm_eq_of_comp_eq (k := F) e τ heτ
  have hσσ : ∀ x, σ (σ x) = x := fun x => e.injective (by rw [hσ, hσ, star_star])
  let s : E ≃ₐ[F] E := AlgEquiv.ofAlgHom σ σ (AlgHom.ext hσσ) (AlgHom.ext hσσ)
  have hs : s ≠ 1 := by
    intro h1
    refine IsTotallyComplex.complexEmbedding_not_isReal e ?_
    rw [ComplexEmbedding.isReal_iff]
    ext x
    have : σ x = x := congrArg (fun t : E ≃ₐ[F] E => t x) h1
    have h3 := hσ e x
    rw [this] at h3
    exact h3.symm
  have hcard : Nat.card (E ≃ₐ[F] E) = 2 := by rw [IsGalois.card_aut_eq_finrank, h2]
  obtain ⟨y, -, hy⟩ := (Nat.card_eq_two_iff' (1 : E ≃ₐ[F] E)).1 hcard
  by_cases hg1 : g.symm = 1
  · left
    rw [← hg, hg1]
    rfl
  · right
    intro x
    rw [← hg, (hy _ hg1).trans (hy _ hs).symm]
    exact hσ e x

/- English proof (translation)
Introduce `F E _ _ _ _ _ σ h emb n J hJ k hk τ`. Use `haveI := h.1`. Use `set w := InfinitePlace.mk (τ.comp (algebraMap F E)) with hw`. Establish `hreal : ComplexEmbedding.IsReal (τ.comp (algebraMap F E))` using `IsTotallyReal.complexEmbedding_isReal _`. Establish `he : (emb w).1.comp (algebraMap F E) = τ.comp (algebraMap F E)`.

Rewrite using `[(emb w).2, hw, InfinitePlace.embedding_mk_eq_of_isReal hreal]`. Break down `eq_or_eq_comp σ h _ _ he with h1 | h1` into its components or cases. Rewrite using `[h1]`. Conclude with `hk w`. Establish `hH : (Complex.I • J.map (emb w).1).IsHermitian`.

Use extensionality with `i j`. Establish `h3` using `h.2.2.2 (emb w).1 (J j i)`. Rewrite `h3` using `[hJ, map_neg]`. Simplify using `only [Matrix.conjTranspose_apply, Matrix.smul_apply, Matrix.map_apply, smul_eq_mul, star_mul', ← h3]`. Simplify using the standard rewrite rules.

Establish `h4 : Complex.I • J.map τ = -((Complex.I • J.map (emb w).1).map (starRingEnd ℂ))`. Use extensionality with `i j`. Simplify using `[h1]`. Rewrite using `[h4, GlobalTheory.Inertia.posIndex_neg, GlobalTheory.Inertia.negIndex_neg, GlobalTheory.Inertia.posIndex_map_conj hH, GlobalTheory.Inertia.negIndex_map_conj hH]`. Conclude with `(hk w).symm`.
-/
theorem index_bound_all : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ →
  ∀ (emb : ∀ w : InfinitePlace F, EmbOver E w) {n : ℕ} (J : Matrix (Fin n) (Fin n) E), (∀ i j, σ (J j i) = -J i j) → ∀ k : ℕ,
  (∀ w, k ≤ GlobalTheory.Inertia.posIndex (Complex.I • J.map (emb w).1) ∧ k ≤ GlobalTheory.Inertia.negIndex (Complex.I • J.map (emb w).1)) →
  ∀ τ : E →+* ℂ, k ≤ GlobalTheory.Inertia.posIndex (Complex.I • J.map τ) ∧ k ≤ GlobalTheory.Inertia.negIndex (Complex.I • J.map τ) := by
  intro F E _ _ _ _ _ σ h emb n J hJ k hk τ
  haveI := h.1
  set w := InfinitePlace.mk (τ.comp (algebraMap F E)) with hw
  have hreal : ComplexEmbedding.IsReal (τ.comp (algebraMap F E)) := IsTotallyReal.complexEmbedding_isReal _
  have he : (emb w).1.comp (algebraMap F E) = τ.comp (algebraMap F E) := by
    rw [(emb w).2, hw, InfinitePlace.embedding_mk_eq_of_isReal hreal]
  rcases eq_or_eq_comp σ h _ _ he with h1 | h1
  · rw [h1]; exact hk w
  · have hH : (Complex.I • J.map (emb w).1).IsHermitian := by
      ext i j
      have h3 := h.2.2.2 (emb w).1 (J j i)
      rw [hJ, map_neg] at h3
      simp only [Matrix.conjTranspose_apply, Matrix.smul_apply, Matrix.map_apply, smul_eq_mul, star_mul', ← h3]
      simp
    have h4 : Complex.I • J.map τ = -((Complex.I • J.map (emb w).1).map (starRingEnd ℂ)) := by
      ext i j
      simp [h1]
    rw [h4, GlobalTheory.Inertia.posIndex_neg, GlobalTheory.Inertia.negIndex_neg, GlobalTheory.Inertia.posIndex_map_conj hH,
      GlobalTheory.Inertia.negIndex_map_conj hH]
    exact (hk w).symm

end GlobalTheory.IdxAll
