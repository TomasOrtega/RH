import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsAuxiliaryHeckeCharacter
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HostCmEmbeddingProperties

open NumberField IsDedekindDomain ReciprocityTheory.Gal Formalism.ConjugateSelfDual Formalism.BasicNotions Formalism.MainNotions Formalism.FrobeniusOrbits Formalism.L2.Host GlobalTheory.CMVal GlobalTheory.ToricDenom GlobalTheory.LamTie

namespace GlobalTheory.LamTie.CMType

/- English proof (translation)
Replace the relevant objects with their definitions. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact.

Rewrite the conclusion using the stated equalities. Prove the components needed by the constructor for the conclusion. Assume the hypotheses and unpack their components. Prove the second alternative. Prove the first alternative.

Assume the hypotheses and unpack their components. Prove the second alternative. Prove the first alternative. Extract witnesses or component facts from the available result. Supply the required witnesses or components.
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
Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
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
