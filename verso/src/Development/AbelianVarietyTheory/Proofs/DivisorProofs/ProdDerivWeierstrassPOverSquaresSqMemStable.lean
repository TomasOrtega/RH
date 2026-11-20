import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.DatumOfIsIntegersLattice
import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.MulStableIntegral
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsDiscreteValuationRingValuationSubringAtPrime
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.AddMonoidHomEqZeroOfEventually
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemIntermediateFieldOfForallComplexAutFixedStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProdDerivWeierstrassPOverSquaresConjStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProdDerivWeierstrassPOverSquaresNeZeroStatement
open NumberField IsDedekindDomain WeierstrassCurve GlobalTheory GlobalTheory.Published GlobalTheory.CMModel Formalism.L2.Th1.F
open scoped IntermediateField BigOperators Topology

/- English proof (translation)
Introduce `p F L t hp h4 h3 hD`. Use `⟨?_, ?_⟩` and prove the remaining obligations. Apply `GlobalTheory.T.mem_intermediateField_of_forall_complexAut_fixed F` to reduce the goal to its premises. Introduce `σ hσ`. Rewrite using `[map_pow]`.

Break down `GlobalTheory.T.prodDerivWeierstrassPOverSquares_conj p F L t hp h4 h3 hD σ hσ with ⟨h, _⟩ | h` into its components or cases. Rewrite using `[h]`. Rewrite using `[h, neg_sq]`. Introduce `hmem σ hσ`. Break down `GlobalTheory.T.prodDerivWeierstrassPOverSquares_conj p F L t hp h4 h3 hD σ hσ with ⟨_, he⟩ | h` into its components or cases.

Conclude with `he`. It suffices to derive a contradiction. Establish `hne` using `(GlobalTheory.T.prodDerivWeierstrassPOverSquares_ne_zero p F L t hp h4 h3 hD).2`. Establish `hfix : σ (sqProd p L t) = sqProd p L t` using `hσ _ hmem`. Rewrite `h` using `[hfix]`.

Establish `h2 : (2 : ℂ) * sqProd p L t = 0` using `by linear_combination h`. Break down `mul_eq_zero.mp h2 with h2 | h2` into its components or cases. Evaluate the numerical expressions using `at h2`. Conclude with `hne h2`.
-/
theorem GlobalTheory.CMModel.sqProd_sq_mem_and_stable : ∀ (p : ℕ) (F : IntermediateField ℚ ℂ) (L : PeriodPair) (t : ℂ),
    p.Prime → p % 4 = 3 → 3 < p → Datum p F L t →
    sqProd p L t ^ 2 ∈ F ∧ (sqProd p L t ∈ F → Stable L F (sqPt p t)) := by
  intro p F L t hp h4 h3 hD
  refine ⟨?_, ?_⟩
  · apply GlobalTheory.T.mem_intermediateField_of_forall_complexAut_fixed F
    intro σ hσ
    rw [map_pow]
    rcases GlobalTheory.T.prodDerivWeierstrassPOverSquares_conj p F L t hp h4 h3 hD σ hσ with ⟨h, _⟩ | h
    · rw [h]
    · rw [h, neg_sq]
  · intro hmem σ hσ
    rcases GlobalTheory.T.prodDerivWeierstrassPOverSquares_conj p F L t hp h4 h3 hD σ hσ with ⟨_, he⟩ | h
    · exact he
    · exfalso
      have hne := (GlobalTheory.T.prodDerivWeierstrassPOverSquares_ne_zero p F L t hp h4 h3 hD).2
      have hfix : σ (sqProd p L t) = sqProd p L t := hσ _ hmem
      rw [hfix] at h
      have h2 : (2 : ℂ) * sqProd p L t = 0 := by linear_combination h
      rcases mul_eq_zero.mp h2 with h2 | h2
      · norm_num at h2
      · exact hne h2
