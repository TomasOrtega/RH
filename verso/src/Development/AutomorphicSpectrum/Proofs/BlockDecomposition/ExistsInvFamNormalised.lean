import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.PoitouTateNormalised
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NormalisedLocalInvariantExistsStatement
import ReciprocityTheory.GaloisValuations.Global

noncomputable section

open NumberField IsDedekindDomain Representation Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.Published GlobalTheory.Published.PoitouTate

namespace GlobalTheory.CompanionTheory.PoitouTateInv

/- English proof (translation)
Introduce `F Ω _ _ _ _ _ l _ r hr ζ hζ`. Establish `key` using `GlobalTheory.T.normalised_local_invariant_exists F Ω l r hr ζ hζ`. Use `⟨fun A => if h : ∃ v : HeightOneSpectrum (𝓞 F), IsPlaceOver A v then Classical.choose (key A h.choose h.choose_spec) else 0, fun A v hv => ?_⟩` and prove the remaining obligations. Establish `h : ∃ v : HeightOneSpectrum (𝓞 F), IsPlaceOver A v` using `⟨v, hv⟩`. Establish `e : h.choose = v` using `eq_of_isPlaceOver h.choose_spec hv`.

Establish `spec` using `Classical.choose_spec (key A h.choose h.choose_spec)`. Simplify using `only [dif_pos h]`. Generalize the expression as in `Classical.choose (key A h.choose h.choose_spec) = f at spec ⊢`. Rewrite `spec` using `[e]`. Conclude with `spec`.
-/
theorem exists_invFam_normalised : ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω]
    [IsAlgClosure F Ω] (l : ℕ) [Fact l.Prime] (r : ℕ), 0 < r → ∀ ζ : Ω,
    IsPrimitiveRoot ζ (l ^ r) → ∃ inv : InvFam F Ω l r,
    ∀ (A : ValuationSubring Ω) (v : HeightOneSpectrum (𝓞 F)), IsPlaceOver A v →
      Function.Bijective (inv A) ∧ IsNormalised ζ A v (inv A) := by
  intro F Ω _ _ _ _ _ l _ r hr ζ hζ
  classical
  have key := GlobalTheory.T.normalised_local_invariant_exists F Ω l r hr ζ hζ
  refine ⟨fun A => if h : ∃ v : HeightOneSpectrum (𝓞 F), IsPlaceOver A v then
    Classical.choose (key A h.choose h.choose_spec) else 0, fun A v hv => ?_⟩
  have h : ∃ v : HeightOneSpectrum (𝓞 F), IsPlaceOver A v := ⟨v, hv⟩
  have e : h.choose = v := eq_of_isPlaceOver h.choose_spec hv
  have spec := Classical.choose_spec (key A h.choose h.choose_spec)
  simp only [dif_pos h]
  generalize Classical.choose (key A h.choose h.choose_spec) = f at spec ⊢
  rw [e] at spec
  exact spec

end GlobalTheory.CompanionTheory.PoitouTateInv

end
