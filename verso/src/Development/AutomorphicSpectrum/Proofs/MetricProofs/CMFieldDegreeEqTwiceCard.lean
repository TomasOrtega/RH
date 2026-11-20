import Mathlib
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.GroupDict
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsSheetCover
import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.StatementsProved
import GroundTheory.HeightsAndTheta.Heights.CountingLowerBound.Assembly
import Development.AutomorphicSpectrum.Proofs.MetricProofs.IntEmbInjective
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.BlockGLSupportedMemMirabolicSupported
open NumberField Matrix MeasureTheory Filter Topology GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GroundTheory.Heights₂.Heights.FiniteCovolume GroundTheory.Automorphic GlobalTheory.CompanionTheory.Ar.Cusp.Dict
open scoped ENNReal InnerProductSpace
open scoped ComplexOrder

namespace GlobalTheory.CompanionTheory.Ar.Cusp.CMRank

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `φ ψ h`. Conclude with `IsFractionRing.ringHom_ext (A := 𝓞 E) (K := E) (fun a => DFunLike.congr_fun h a)`. Introduce `s`. Use `⟨embOf s, ?_⟩` and prove the remaining obligations.

Use extensionality with `a`. Simplify using `[embOf]`.
-/
theorem restrict_bijective (E : Type) [Field E] [NumberField E] :
    Function.Bijective (fun φ : E →+* ℂ => φ.comp (algebraMap (𝓞 E) E)) := by
  constructor
  · intro φ ψ h
    exact IsFractionRing.ringHom_ext (A := 𝓞 E) (K := E) (fun a => DFunLike.congr_fun h a)
  · intro s
    refine ⟨embOf s, ?_⟩
    ext a
    simp [embOf]

/- English proof (translation)
Rewrite using `[← Nat.card_congr (Equiv.ofBijective _ (restrict_bijective E)), Nat.card_eq_fintype_card, NumberField.Embeddings.card]`.
-/
theorem natCard_intEmb (E : Type) [Field E] [NumberField E] :
    Nat.card (𝓞 E →+* ℂ) = Module.finrank ℚ E := by
  rw [← Nat.card_congr (Equiv.ofBijective _ (restrict_bijective E)), Nat.card_eq_fintype_card,
    NumberField.Embeddings.card]

/- English proof (translation)
Establish `hconj : ∀ s : 𝓞 E →+* ℂ, (starRingEnd ℂ).comp ((starRingEnd ℂ).comp s) = s`. Introduce `s`. Use extensionality with `a`. Simplify using the standard rewrite rules. Take `⟨hinj, hiff⟩` from `h`.

Prove the components needed by the constructor for the conclusion. Introduce and unpack `(a | a) (b | b) hab`. Conclude with `congrArg Sum.inl (hinj hab)`. Conclude with `absurd ⟨a, hab⟩ ((hiff (σ b)).1 ⟨b, rfl⟩)`. Conclude with `absurd ⟨b, hab.symm⟩ ((hiff (σ a)).1 ⟨a, rfl⟩)`.

Establish `hab' : (starRingEnd ℂ).comp (σ a) = (starRingEnd ℂ).comp (σ b)` using `hab`. Establish `: σ a = σ b`. Rewrite using `[← hconj (σ a), hab', hconj]`. Conclude with `congrArg Sum.inr (hinj this)`. Introduce `s`.

Distinguish the cases in `hs : ∃ τ, σ τ = s`. Take `⟨τ, rfl⟩` from `hs`. Conclude with `⟨Sum.inl τ, rfl⟩`. Establish `hn : ∃ τ, σ τ = (starRingEnd ℂ).comp s`. Assume the negation of the conclusion as `hc`.

Conclude with `hs ((hiff s).2 hc)`. Take `⟨τ, hτ⟩` from `hn`. Use `⟨Sum.inr τ, ?_⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `(starRingEnd ℂ).comp (σ τ) = s`. Rewrite using `[hτ, hconj]`.
-/
theorem cmFam_sum_bijective {E : Type} [Field E] [NumberField E] [IsCMField E] {Ψ : Type} [Fintype Ψ]
    {σ : Ψ → (𝓞 E →+* ℂ)} (h : IsCMFam σ) :
    Function.Bijective
      (Sum.elim σ (fun τ => (starRingEnd ℂ).comp (σ τ)) : Ψ ⊕ Ψ → (𝓞 E →+* ℂ)) := by
  have hconj : ∀ s : 𝓞 E →+* ℂ, (starRingEnd ℂ).comp ((starRingEnd ℂ).comp s) = s := by
    intro s
    ext a
    simp
  obtain ⟨hinj, hiff⟩ := h
  constructor
  · rintro (a | a) (b | b) hab
    · exact congrArg Sum.inl (hinj hab)
    · exact absurd ⟨a, hab⟩ ((hiff (σ b)).1 ⟨b, rfl⟩)
    · exact absurd ⟨b, hab.symm⟩ ((hiff (σ a)).1 ⟨a, rfl⟩)
    · have hab' : (starRingEnd ℂ).comp (σ a) = (starRingEnd ℂ).comp (σ b) := hab
      have : σ a = σ b := by
        rw [← hconj (σ a), hab', hconj]
      exact congrArg Sum.inr (hinj this)
  · intro s
    by_cases hs : ∃ τ, σ τ = s
    · obtain ⟨τ, rfl⟩ := hs
      exact ⟨Sum.inl τ, rfl⟩
    · have hn : ∃ τ, σ τ = (starRingEnd ℂ).comp s := by
        by_contra hc
        exact hs ((hiff s).2 hc)
      obtain ⟨τ, hτ⟩ := hn
      refine ⟨Sum.inr τ, ?_⟩
      change (starRingEnd ℂ).comp (σ τ) = s
      rw [hτ, hconj]

/- English proof (translation)
Introduce `E _ _ _ Ψ _ σ h`. Rewrite using `[← natCard_intEmb E, ← Nat.card_congr (Equiv.ofBijective _ (cmFam_sum_bijective h)), Nat.card_eq_fintype_card, Fintype.card_sum]`. Use linear arithmetic over natural numbers and integers.
-/
theorem finrank_eq_two_mul_card : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (Ψ : Type) [Fintype Ψ]
    (σ : Ψ → (𝓞 E →+* ℂ)), IsCMFam σ → Module.finrank ℚ E = 2 * Fintype.card Ψ := by
  intro E _ _ _ Ψ _ σ h
  rw [← natCard_intEmb E, ← Nat.card_congr (Equiv.ofBijective _ (cmFam_sum_bijective h)),
    Nat.card_eq_fintype_card, Fintype.card_sum]
  omega

end GlobalTheory.CompanionTheory.Ar.Cusp.CMRank
