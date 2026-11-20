import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StSliceReducedGeneral
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StSliceUnmixedGeneral
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StSliceReducedAway
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial Matrix ComplexSets

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Assume the negation of the conclusion and derive a contradiction. Simplify using the standard rewrite rules. Establish an intermediate fact. Establish an intermediate fact.

Fix the arbitrary inputs or assume the hypotheses. Express the relevant assertion in an equivalent form by its definition. Rewrite the conclusion using the stated equalities. Express the relevant assertion in an equivalent form by its definition. Rewrite the conclusion using the stated equalities.

Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Assume the negation of the conclusion and derive a contradiction. Extract witnesses or component facts from the available result. Establish an intermediate fact.

Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result. A detailed English derivation is pending.
-/
theorem isRadicalAt_of_associatedPrimes {n : ℕ} {I : Ideal (MvPolynomial (Fin n) ℂ)} {q : Fin n → ℂ}
    (hA : ∀ P ∈ associatedPrimes (MvPolynomial (Fin n) ℂ) (MvPolynomial (Fin n) ℂ ⧸ I),
      P ≤ RingHom.ker (eval q) → P ∈ I.minimalPrimes ∧ P ≠ RingHom.ker (eval q))
    (hB : ∀ P : Ideal (MvPolynomial (Fin n) ℂ), P.IsPrime → I ≤ P → P ≠ RingHom.ker (eval q) →
      ∀ g ∈ I.radical, ∃ s ∉ P, s * g ∈ I) :
    IsRadicalAt I q := by
  intro g hg
  by_contra hno
  simp only [not_exists, not_and] at hno
  have : (RingHom.ker (eval q : MvPolynomial (Fin n) ℂ →+* ℂ)).IsPrime := RingHom.ker_isPrime _
  set N : Submodule (MvPolynomial (Fin n) ℂ) (MvPolynomial (Fin n) ℂ ⧸ I) :=
    Submodule.span _ {Ideal.Quotient.mk I g}
  have hK : ∀ s, s ∈ Module.annihilator (MvPolynomial (Fin n) ℂ) N ↔ s * g ∈ I := by
    intro s
    change s ∈ N.annihilator ↔ _
    rw [Submodule.mem_annihilator_span_singleton]
    change Ideal.Quotient.mk I s * Ideal.Quotient.mk I g = 0 ↔ _
    rw [← map_mul, Ideal.Quotient.eq_zero_iff_mem]
  have hKq : Module.annihilator (MvPolynomial (Fin n) ℂ) N ≤ RingHom.ker (eval q) := by
    intro s hs
    by_contra h
    exact hno s h ((hK s).1 hs)
  obtain ⟨P, hPmin, hPq⟩ := Ideal.exists_minimalPrimes_le hKq
  have hPass : P ∈ associatedPrimes (MvPolynomial (Fin n) ℂ) (MvPolynomial (Fin n) ℂ ⧸ I) :=
    associatedPrimes.subset_of_injective (f := N.subtype) Subtype.val_injective
      (Module.associatedPrimes.minimalPrimes_annihilator_subset_associatedPrimes _ _ hPmin)
  obtain ⟨hPI, hPne⟩ := hA P hPass hPq
  obtain ⟨s, hsP, hsg⟩ := hB P hPI.1.1 hPI.1.2 hPne g hg
  exact hsP (hPmin.1.2 ((hK s).2 hsg))

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations. Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result.

Supply the required witnesses or components.
-/
theorem SliceReducedGeneral.proof (hU : SliceUnmixedGeneral.Statement)
    (hB : SliceReducedAway.Statement) : SliceReducedGeneral.Statement := by
  intro n d J W u hJ hdim hu hW
  obtain ⟨f, hfW, hf⟩ := hU n d J W u hJ hdim hu hW
  refine ⟨f, hfW, fun q hq hfq => ?_⟩
  obtain ⟨O₁, hO₁o, hO₁d, hO₁⟩ := hf q hq hfq
  obtain ⟨O₂, hO₂o, hO₂d, hO₂⟩ := hB n d J q hJ.isRadical
  exact ⟨O₁ ∩ O₂, hO₁o.inter hO₂o, hO₁d.inter_of_isOpen_left hO₂d hO₁o,
    fun L hL => isRadicalAt_of_associatedPrimes (hO₁ L hL.1) (hO₂ L hL.2)⟩

end GroundTheory.Heights₂.Heights
