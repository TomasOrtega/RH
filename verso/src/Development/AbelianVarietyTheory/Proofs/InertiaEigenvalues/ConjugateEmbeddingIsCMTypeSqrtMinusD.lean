import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsAuxiliaryHeckeCharacter
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HostCmEmbeddingProperties

open NumberField IsDedekindDomain ReciprocityTheory.Gal Formalism.ConjugateSelfDual Formalism.BasicNotions Formalism.MainNotions Formalism.FrobeniusOrbits Formalism.L2.Host GlobalTheory.CMVal GlobalTheory.ToricDenom GlobalTheory.LamTie

namespace GlobalTheory.LamTie.CMType

/- English proof (translation)
Unfold `IsCMType`. Introduce `σ`. Establish `hmk : ∀ j, InfinitePlace.mk (φ j) = InfinitePlace.mk σ ↔ (σ = ComplexEmbedding.conjugate (φ j) ∨ σ = ComplexEmbedding.conjugate (ComplexEmbedding.conjugate (φ j)))`. Introduce `j`. Establish `cc : ComplexEmbedding.conjugate (ComplexEmbedding.conjugate (φ j)) = φ j` using `star_star (φ j)`.

Rewrite using `[InfinitePlace.mk_eq_iff, cc]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `(e | e)`. Conclude with `Or.inr e.symm`. Conclude with `Or.inl e.symm`.

Introduce and unpack `(e | e)`. Conclude with `Or.inr e.symm`. Conclude with `Or.inl e.symm`. Take `⟨i, hi⟩` from `h.2 (InfinitePlace.mk σ)`. Conclude with `⟨i, (hmk i).1 hi, fun j hj => h.1 (((hmk j).2 hj).trans hi.symm)⟩`.
-/
theorem isCMType_conj {E : Type} [Field E] {I : Type} (φ : I → E →+* ℂ)
    (h : Function.Bijective fun i => InfinitePlace.mk (φ i)) :
    IsCMType fun i => ComplexEmbedding.conjugate (φ i) := by
  unfold IsCMType
  intro σ
  have hmk : ∀ j, InfinitePlace.mk (φ j) = InfinitePlace.mk σ ↔
      (σ = ComplexEmbedding.conjugate (φ j) ∨
        σ = ComplexEmbedding.conjugate (ComplexEmbedding.conjugate (φ j))) := by
    intro j
    have cc : ComplexEmbedding.conjugate (ComplexEmbedding.conjugate (φ j)) = φ j := star_star (φ j)
    rw [InfinitePlace.mk_eq_iff, cc]
    constructor
    · rintro (e | e)
      · exact Or.inr e.symm
      · exact Or.inl e.symm
    · rintro (e | e)
      · exact Or.inr e.symm
      · exact Or.inl e.symm
  obtain ⟨i, hi⟩ := h.2 (InfinitePlace.mk σ)
  exact ⟨i, (hmk i).1 hi, fun j hj => h.1 (((hmk j).2 hj).trans hi.symm)⟩

/- English proof (translation)
Introduce `R H`. Take `⟨_, -, ⟨-, -, -, -, hbij⟩, -, hsq, -⟩` from `GlobalTheory.Mem.HostCM.host_cm_embedding_properties R H`. Use `⟨isCMType_conj (embPsi H) hbij, fun g g' => ?_⟩` and prove the remaining obligations. Use `show ComplexEmbedding.conjugate (embPsi H g) H.sqrtMinusD = ComplexEmbedding.conjugate (embPsi H g') H.sqrtMinusD`. Rewrite using `[ComplexEmbedding.conjugate_coe_eq, ComplexEmbedding.conjugate_coe_eq, hsq g, hsq g']`.
-/
theorem phi_cmType : ∀ (R : Ranks) (H : Formalism.BasicNotions.Host R),
    IsCMType (phi H) ∧ ∀ g g', phi H g H.sqrtMinusD = phi H g' H.sqrtMinusD := by
  intro R H
  obtain ⟨_, -, ⟨-, -, -, -, hbij⟩, -, hsq, -⟩ := GlobalTheory.Mem.HostCM.host_cm_embedding_properties R H
  refine ⟨isCMType_conj (embPsi H) hbij, fun g g' => ?_⟩
  show ComplexEmbedding.conjugate (embPsi H g) H.sqrtMinusD =
    ComplexEmbedding.conjugate (embPsi H g') H.sqrtMinusD
  rw [ComplexEmbedding.conjugate_coe_eq, ComplexEmbedding.conjugate_coe_eq, hsq g, hsq g']

end GlobalTheory.LamTie.CMType
