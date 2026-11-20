import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.IdeleNormCharacters.AbsFactsAlt

noncomputable section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Host Formalism.ConjugateSelfDual Neutral.B1 ReciprocityTheory.Gal
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.HeckeGal GlobalTheory.CuspRep

namespace UpperTheory.Gal.TP.Chr

/- English proof (translation)
Unfold `pl`. Rewrite using `[InfinitePlace.comap_mk, τ.2, InfinitePlace.mk_embedding]`.
-/
private theorem pl_emb {E : Type} [Field E] [NumberField E] [IsCMField E]
    {w : InfinitePlace (maximalRealSubfield E)} (τ : EmbOver E w) : pl τ.1 = w := by
  unfold pl
  rw [InfinitePlace.comap_mk, τ.2, InfinitePlace.mk_embedding]

/- English proof (translation)
Unfold `pl`. Rewrite using `[InfinitePlace.mk_conjugate_eq]`.
-/
private theorem pl_conj {E : Type} [Field E] [NumberField E] [IsCMField E] (φ : E →+* ℂ) :
    pl (ComplexEmbedding.conjugate φ) = pl φ := by
  unfold pl
  rw [InfinitePlace.mk_conjugate_eq]

/- English proof (translation)
Introduce `h` and use `IsTotallyComplex.complexEmbedding_not_isReal φ (ComplexEmbedding.isReal_iff.mpr h)`.
-/
private theorem conj_ne {E : Type} [Field E] [NumberField E] [IsCMField E] (φ : E →+* ℂ) :
    ComplexEmbedding.conjugate φ ≠ φ := fun h =>
  IsTotallyComplex.complexEmbedding_not_isReal φ (ComplexEmbedding.isReal_iff.mpr h)

/- English proof (translation)
Introduce `E _ _ _ emb a b w`. Establish `h1 : pl (emb w).1 = w` using `pl_emb (emb w)`. Establish `h2 : pl (ComplexEmbedding.conjugate (emb w).1) = w` using `(pl_conj _).trans h1`. Prove the components needed by the constructor for the conclusion. Unfold `typ`.

Rewrite using `[h1]`. Conclude with `if_pos rfl`. Unfold `typ`. Rewrite using `[h2]`. Conclude with `if_neg (conj_ne _)`.
-/
theorem typVal : TypVal := by
  intro E _ _ _ emb a b w
  have h1 : pl (emb w).1 = w := pl_emb (emb w)
  have h2 : pl (ComplexEmbedding.conjugate (emb w).1) = w := (pl_conj _).trans h1
  constructor
  · unfold typ
    rw [h1]
    exact if_pos rfl
  · unfold typ
    rw [h2]
    exact if_neg (conj_ne _)

end UpperTheory.Gal.TP.Chr

end
