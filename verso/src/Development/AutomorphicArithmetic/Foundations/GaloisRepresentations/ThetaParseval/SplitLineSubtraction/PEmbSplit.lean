import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.SplitLineSubtraction.TwoUpOKOf

open scoped TensorProduct
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Host Formalism.ConjugateSelfDual Formalism.BasicNotions GlobalTheory.HeckeGal GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open UpperTheory.V.Af (algSat)
open UpperTheory.Gal.TP.Sub

/- English proof (translation)
Introduce `E _ _ _ emb`. Establish `hcj : ∀ (φ : E →+* ℂ), (ComplexEmbedding.conjugate φ).comp (algebraMap (maximalRealSubfield E) E) = ComplexEmbedding.conjugate (φ.comp (algebraMap (maximalRealSubfield E) E))`. Introduce `φ`. Use extensionality with `x`. Simplify using `[ComplexEmbedding.conjugate_coe_eq]`.

Establish `hinj : ∀ (w w' : InfinitePlace (maximalRealSubfield E)), w.embedding = w'.embedding → w = w'`. Introduce `w w' h`. Rewrite using `[← InfinitePlace.mk_embedding w, ← InfinitePlace.mk_embedding w', h]`. Use `⟨?_, ?_, ?_⟩` and prove the remaining obligations. Introduce `τ`.

Set `w` to `InfinitePlace.mk (τ.comp (algebraMap (maximalRealSubfield E) E))`. Use `⟨w, ?_⟩` and prove the remaining obligations. Establish `hw : (InfinitePlace.mk τ).comap (algebraMap (maximalRealSubfield E) E) = (InfinitePlace.mk (emb w).1).comap (algebraMap (maximalRealSubfield E) E)`. Rewrite using `[InfinitePlace.comap_mk, InfinitePlace.comap_mk, (emb w).2, InfinitePlace.mk_embedding]`. Establish `hmk : InfinitePlace.mk τ = InfinitePlace.mk (emb w).1` using `(IsCMField.equivInfinitePlace E).injective hw`.

Break down `InfinitePlace.mk_eq_iff.1 hmk with h | h` into its components or cases. Conclude with `Or.inl h`. Use `right`. Rewrite using `[← h]`. Use extensionality with `x`.

Simplify using `[ComplexEmbedding.conjugate_coe_eq]`. Introduce `w w' h`. Apply `hinj` to reduce the goal to its premises. Rewrite using `[← (emb w).2, ← (emb w').2, h]`. Introduce `w w' h`.

Establish `h1 : w.embedding = ComplexEmbedding.conjugate w'.embedding`. Rewrite using `[← (emb w).2, ← (emb w').2, h, hcj]`. Establish `hww : w = w'`. Rewrite using `[← InfinitePlace.mk_embedding w, ← InfinitePlace.mk_embedding w', h1, InfinitePlace.mk_conjugate_eq]`. Substitute `hww` using the available equality.

Apply `IsTotallyComplex.complexEmbedding_not_isReal (emb w).1` to reduce the goal to its premises. Conclude with `h.symm`.
-/
theorem UpperTheory.Gal.TP.Sub.embSplit_holds :
    EmbSplit := by
  intro E _ _ _ emb
  have hcj : ∀ (φ : E →+* ℂ), (ComplexEmbedding.conjugate φ).comp
      (algebraMap (maximalRealSubfield E) E) =
      ComplexEmbedding.conjugate (φ.comp (algebraMap (maximalRealSubfield E) E)) := by
    intro φ
    ext x
    simp [ComplexEmbedding.conjugate_coe_eq]
  have hinj : ∀ (w w' : InfinitePlace (maximalRealSubfield E)), w.embedding = w'.embedding → w = w' := by
    intro w w' h
    rw [← InfinitePlace.mk_embedding w, ← InfinitePlace.mk_embedding w', h]
  refine ⟨?_, ?_, ?_⟩
  · intro τ
    let w := InfinitePlace.mk (τ.comp (algebraMap (maximalRealSubfield E) E))
    refine ⟨w, ?_⟩
    have hw : (InfinitePlace.mk τ).comap (algebraMap (maximalRealSubfield E) E) =
        (InfinitePlace.mk (emb w).1).comap (algebraMap (maximalRealSubfield E) E) := by
      rw [InfinitePlace.comap_mk, InfinitePlace.comap_mk, (emb w).2, InfinitePlace.mk_embedding]
    have hmk : InfinitePlace.mk τ = InfinitePlace.mk (emb w).1 :=
      (IsCMField.equivInfinitePlace E).injective hw
    rcases InfinitePlace.mk_eq_iff.1 hmk with h | h
    · exact Or.inl h
    · right
      rw [← h]
      ext x
      simp [ComplexEmbedding.conjugate_coe_eq]
  · intro w w' h
    apply hinj
    rw [← (emb w).2, ← (emb w').2, h]
  · intro w w' h
    have h1 : w.embedding = ComplexEmbedding.conjugate w'.embedding := by
      rw [← (emb w).2, ← (emb w').2, h, hcj]
    have hww : w = w' := by
      rw [← InfinitePlace.mk_embedding w, ← InfinitePlace.mk_embedding w', h1,
        InfinitePlace.mk_conjugate_eq]
    subst hww
    apply IsTotallyComplex.complexEmbedding_not_isReal (emb w).1
    exact h.symm
