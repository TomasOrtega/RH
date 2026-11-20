import Formalism.WachLatticeTwists.RealDisplaySplitting.GaloisTheoremWithGenerator
import Formalism.WachLatticeTwists.RealDisplaySplitting.RealDisplayProofs.GaloisTheoremWithExtension

variable [hT2Core : Fact ReciprocityTheory.ChartRestriction.T2.Core]

open Finset Classical

noncomputable section

namespace Formalism.RepresentationBoundsCohomology.SF

open Formalism.NG Formalism.RepresentationBoundsCohomology.FIN Formalism.RepresentationBoundsCohomology.BR Formalism.RepresentationBoundsCohomology.ringDataObjects

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Establish an intermediate fact.

Rewrite the conclusion using the stated equalities. Rewrite the indicated hypotheses using the stated equalities. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Reduce the conclusion to the remaining proof obligations.

Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Assume the negation of the conclusion and derive a contradiction. Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact.

Rewrite the indicated hypotheses using the stated equalities. Fix the arbitrary inputs or assume the hypotheses. Separate the alternatives or extract the components of the hypothesis. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact.

Simplify to obtain the desired conclusion from the available facts. A detailed English derivation is pending.
-/
theorem gen : StatGen := by
  intro ℓ hℓ O _ _ _ G _ ε g₀ s₀ y ⟨hu, h0, hs1, hs2, hx⟩
  have key : ∀ n : ℕ, n ≠ 0 → (ε g₀) ^ n ≠ 1 := by
    intro n hn h1
    have h := powSubOneO O ℓ hℓ hu s₀ hs1 hs2 ((ε g₀ : Oˣ) : O) y hx n hn
    have h2 : ((ε g₀ : Oˣ) : O) ^ n - 1 = 0 := by
      rw [← Units.val_pow_eq_pow_val, h1, Units.val_one, sub_self]
    rw [h2, IsDiscreteValuationRing.addVal_zero] at h
    have h3 : IsDiscreteValuationRing.addVal O (ℓ : O) ≠ ⊤ := by
      intro h4
      exact h0 (IsDiscreteValuationRing.addVal_eq_top_iff.1 h4)
    exact (WithTop.mul_ne_top h3 (ENat.natCast_ne_top _)) h.symm
  refine ⟨?_, ?_⟩
  · have aux : ∀ i j : ℕ, i ≤ j → (ε g₀) ^ i = (ε g₀) ^ j → i = j := by
      intro i j hij h
      by_contra hne
      refine key (j - i) (by omega) ?_
      have : (ε g₀) ^ j = (ε g₀) ^ i * (ε g₀) ^ (j - i) := by rw [← pow_add]; congr 1; omega
      rw [this] at h
      exact (mul_eq_left.1 h.symm)
    intro i j h
    rcases le_total i j with hij | hij
    · exact aux i j hij h
    · exact (aux j i hij h.symm).symm
  · intro O' _ _
    have h := congrArg (algebraMap O O') hx
    simpa [bcChar] using h

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations. Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations.

Establish an intermediate fact. Simplify to obtain the desired conclusion from the available facts.
-/
theorem cycBc : StatCycBc := by
  intro ℓ Ek Ω O O' _ _ _ _ _ _ ε h g n ζ hζ
  obtain ⟨a, h1, h2⟩ := h g n ζ hζ
  refine ⟨a, h1, ?_⟩
  obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.1 h2
  refine Ideal.mem_span_singleton'.2 ⟨algebraMap O O' c, ?_⟩
  have h3 := congrArg (algebraMap O O') hc
  simpa [bcChar] using h3

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result. Supply the required witnesses or components.
-/
theorem galois_theorem_with_generator : GaloisTheoremWithGenerator := by
  intro ℓ _ O _ _ _ _ X _ T d _ _ Ek Ω _ _ _ _ _ r π t ht bl χ₁ ε g₀ s₀ y hP hA h2 hG3 hg hcyc L ϖ hϖ
  obtain ⟨g1, g2⟩ := gen ℓ Fact.out O _ ε g₀ s₀ y hg
  obtain ⟨eB, e₁, s, hAB, O', i1, i2, i3, i4, i5, i6, e, he, hO⟩ := galois_theorem_with_extension ℓ O X T d Ek Ω r π t ht bl χ₁ ε g₀
    ⟨hP, hA, h2, hG3, fun i j _ _ h => g1 i j h⟩ L ϖ hϖ
  exact ⟨eB, e₁, s, hAB, O', i1, i2, i3, i4, i5, i6, e, he, hO, cycBc ℓ Ek Ω O O' ε hcyc, g2 O'⟩

end Formalism.RepresentationBoundsCohomology.SF
