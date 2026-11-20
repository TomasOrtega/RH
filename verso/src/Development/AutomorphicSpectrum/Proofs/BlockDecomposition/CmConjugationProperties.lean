import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsLatIntVec
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.AbsNormSqOfMulConjEqDifferentIdeal
open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.CompanionTheory.SiegelND.Integ.Hua GlobalTheory.CompanionTheory.SiegelND.Integ.Hua.HS
open scoped Matrix

noncomputable section

namespace GlobalTheory.CompanionTheory.SiegelND.Integ.Hua.HS

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Reduce the claim to the hypotheses of an applicable result.

Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Establish an intermediate fact. Assume the negation of the conclusion and derive a contradiction. Establish an intermediate fact.

Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. By extensionality, compare the relevant components. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities.

Simplify to obtain the desired conclusion from the available facts. Reduce the conclusion to the remaining proof obligations. Fix the arbitrary inputs or assume the hypotheses. Assume the negation of the conclusion and derive a contradiction. Establish an intermediate fact.

Rewrite the conclusion using the stated equalities. Fix the arbitrary inputs or assume the hypotheses. Consider separately whether the proposition holds or fails. Substitute using the available equality. Reduce the conclusion to the remaining proof obligations.

Simplify to obtain the desired conclusion from the available facts. It suffices to derive a contradiction. Reduce the claim to the hypotheses of an applicable result. Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact.

Simplify to obtain the desired conclusion from the available facts. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Take a linear combination of the given relations to obtain the conclusion. Establish an intermediate fact.

Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations. Fix the arbitrary inputs or assume the hypotheses. Simplify using the standard rewrite rules. Simplify to obtain the desired conclusion from the available facts.

Extract witnesses or component facts from the available result. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Reduce the claim to the hypotheses of an applicable result.

Rewrite the conclusion using the stated equalities. Introduce a local definition for the expression. A detailed English derivation is pending.
-/
theorem isCMExt_conj_fixed_integers : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E]
    [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → (∀ x, σ (σ x) = x) ∧
      (∀ x, σ x = x → ∃ y : F, algebraMap F E y = x) ∧
      (∀ (o : 𝓞 E), ((sO σ o : 𝓞 E) : E) = σ (o : E)) ∧
      (∀ I : Ideal (𝓞 E), Ideal.absNorm (I.map (sO σ)) = Ideal.absNorm I) := by
  intro F E _ _ _ _ _ σ h
  obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
  have hinv : ∀ x, σ (σ x) = x := by
    intro x
    apply τ.injective
    rw [h.2.2.2, h.2.2.2, star_star]
  have hval : ∀ o : 𝓞 E, ((sO σ o : 𝓞 E) : E) = σ (o : E) := fun o => rfl
  have hmoved : ∃ θ : E, σ θ ≠ θ := by
    by_contra hc
    push_neg at hc
    have hc' := h.2.1
    refine IsTotallyComplex.complexEmbedding_not_isReal τ ?_
    rw [ComplexEmbedding.isReal_iff]
    ext y
    have := h.2.2.2 τ y
    rw [hc y] at this
    simpa using this.symm
  refine ⟨hinv, ?_, hval, ?_⟩
  · intro x hx
    by_contra hne
    haveI : Module.Finite F E := Module.finite_of_finrank_pos (by rw [h.2.2.1]; norm_num)
    have hli : LinearIndependent F ![(1 : E), x] := by
      rw [LinearIndependent.pair_iff]
      intro s t hst
      by_cases ht : t = 0
      · subst ht
        refine ⟨?_, rfl⟩
        simpa using hst
      · exfalso
        apply hne
        refine ⟨-s / t, ?_⟩
        have h1 : algebraMap F E s + algebraMap F E t * x = 0 := by
          simpa [Algebra.smul_def] using hst
        have ht' : algebraMap F E t ≠ 0 := by simpa using ht
        rw [map_div₀, map_neg, div_eq_iff ht']
        linear_combination -h1
    have hspan : Submodule.span F (Set.range ![(1 : E), x]) = ⊤ :=
      hli.span_eq_top_of_card_eq_finrank' (by rw [h.2.2.1]; simp)
    have hid : σ.toLinearMap = LinearMap.id := by
      refine LinearMap.ext_on_range hspan ?_
      intro i
      fin_cases i
      · simp
      · simpa using hx
    obtain ⟨θ, hθ⟩ := hmoved
    exact hθ (by simpa using LinearMap.congr_fun hid θ)
  · intro I
    have hs : ∀ o : 𝓞 E, sO σ (sO σ o) = o := by
      intro o
      apply RingOfIntegers.ext
      rw [hval, hval, hinv]
    let e : 𝓞 E ≃+* 𝓞 E := RingEquiv.ofRingHom (sO σ) (sO σ)
      (RingHom.ext hs) (RingHom.ext hs)
    exact GlobalTheory.absNorm_map_ringEquiv_self e I

end GlobalTheory.CompanionTheory.SiegelND.Integ.Hua.HS
