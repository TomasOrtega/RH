import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.QuasiCompact
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GaloisTransitiveOnFibresFlatBaseChange

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum.GalFibre

/- English proof (translation)
Introduce `R R' _ _ ρ _ hG Y X p p' β hfl hpb act hact hactβ z₀ z hz`. Establish `: Flat p` using `hfl`. Set `π : R →+* ρ.range` to `ρ.rangeRestrict`. Establish `hπ : Function.Surjective π` using `ρ.rangeRestrict_surjective`. Establish `hfac : spMap ρ = spMap (algebraMap ρ.range R') ≫ spMap π`.

Rewrite using `[← Spec.map_comp]`. Both sides reduce to the same expression. Establish `hsq : IsPullback (pullback.fst p (spMap π)) (pullback.snd p (spMap π)) p (spMap π)` using `IsPullback.of_hasPullback _ _`. Set `p₀ : X ⟶ pullback p (spMap π)` to `hsq.lift β (p' ≫ spMap (algebraMap ρ.range R')) (by rw [hpb.w, hfac, Category.assoc])`. Establish `hp₀ : p₀ ≫ pullback.fst p (spMap π) = β` using `hsq.lift_fst _ _ _`.

Establish `hp₀' : p₀ ≫ pullback.snd p (spMap π) = p' ≫ spMap (algebraMap ρ.range R')` using `hsq.lift_snd _ _ _`. Establish `outer : IsPullback (p₀ ≫ pullback.fst p (spMap π)) p' p (spMap (algebraMap ρ.range R') ≫ spMap π)`. Rewrite using `[hp₀, ← hfac]`. Conclude with `hpb`. Establish `hpb₀ : IsPullback p₀ p' (Over.mk (pullback.snd p (spMap π))).hom (spMap (algebraMap ρ.range R'))` using `IsPullback.of_right outer hp₀' hsq`.

Establish `hinj : Function.Injective (algebraMap ρ.range R')` using `Subtype.val_injective`. Set `toG : Gal (algebraMap ρ.range R') → Gal ρ` to `fun σ => ⟨σ.1, fun r => σ.2 (π r)⟩`. Establish `hG₀ : IsGal (algebraMap ρ.range R')`. Use `⟨?_, fun x hx => ?_⟩` and prove the remaining obligations. Establish `: Finite (Gal ρ)` using `hG.1`.

Conclude with `Finite.of_injective toG (fun a b h => Subtype.ext (show a.1 = b.1 from congrArg (fun s : Gal ρ => s.1) h))`. Establish `hx' : ∀ σ ∈ Gal ρ, σ x = x` using `fun σ hσ => by`. Use `hx σ ?_` and prove the remaining obligations. Introduce and unpack `⟨_, r, rfl⟩`. Conclude with `hσ r`.

Conclude with `⟨⟨x, hG.2 x hx'⟩, rfl⟩`. Establish `hflat : Flat (Over.mk (pullback.snd p (spMap π))).hom`. Express the relevant statement in the definitionally equal form `Flat (pullback.snd p (spMap π))`. Use `infer_instance`. Establish `: IsClosedImmersion (spMap π)` using `IsClosedImmersion.spec_of_surjective _ hπ`.

Establish `hz₀ : p₀ z₀ = p₀ z`. Apply `(pullback.fst p (spMap π)).isClosedEmbedding.injective` to reduce the goal to its premises. Rewrite using `[← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, hp₀, hz]`. Take `⟨σ', h, h₁, h₂, h₃⟩` from `gal_transitive_on_fibres ρ.range R' hinj hG₀ (Over.mk (pullback.snd p (spMap π))) hflat X p₀ p' hpb₀ z₀ z hz₀`. Use `⟨toG σ', ?_⟩` and prove the remaining obligations.

Establish `he : act (toG σ') = h`. Use `hpb.hom_ext ?_ ?_` and prove the remaining obligations. Rewrite using `[hactβ, ← hp₀, ← Category.assoc, h₁]`. Rewrite using `[hact, h₂]`. Both sides reduce to the same expression.

Rewrite using `[he, h₃]`.
-/
theorem exists_act_apply_eq : ∀ (R R' : Type) [CommRing R] [CommRing R'] (ρ : R →+* R'), ρ.Finite → IsGal ρ →
    ∀ (Y X : Scheme.{0}) (p : Y ⟶ Sp R) (p' : X ⟶ Sp R') (β : X ⟶ Y), Flat p → IsPullback β p' p (spMap ρ) →
    ∀ (act : Gal ρ → (X ⟶ X)), (∀ σ, act σ ≫ p' = p' ≫ spMap (Gal.hom σ)) → (∀ σ, act σ ≫ β = β) →
    ∀ z₀ z : X, β z₀ = β z → ∃ σ : Gal ρ, act σ z₀ = z := by
  intro R R' _ _ ρ _ hG Y X p p' β hfl hpb act hact hactβ z₀ z hz
  have : Flat p := hfl
  let π : R →+* ρ.range := ρ.rangeRestrict
  have hπ : Function.Surjective π := ρ.rangeRestrict_surjective
  have hfac : spMap ρ = spMap (algebraMap ρ.range R') ≫ spMap π := by
    rw [← Spec.map_comp]; rfl
  have hsq : IsPullback (pullback.fst p (spMap π)) (pullback.snd p (spMap π)) p (spMap π) :=
    IsPullback.of_hasPullback _ _
  let p₀ : X ⟶ pullback p (spMap π) :=
    hsq.lift β (p' ≫ spMap (algebraMap ρ.range R')) (by rw [hpb.w, hfac, Category.assoc])
  have hp₀ : p₀ ≫ pullback.fst p (spMap π) = β := hsq.lift_fst _ _ _
  have hp₀' : p₀ ≫ pullback.snd p (spMap π) = p' ≫ spMap (algebraMap ρ.range R') := hsq.lift_snd _ _ _
  have outer : IsPullback (p₀ ≫ pullback.fst p (spMap π)) p' p (spMap (algebraMap ρ.range R') ≫ spMap π) := by
    rw [hp₀, ← hfac]; exact hpb
  have hpb₀ : IsPullback p₀ p' (Over.mk (pullback.snd p (spMap π))).hom (spMap (algebraMap ρ.range R')) :=
    IsPullback.of_right outer hp₀' hsq
  have hinj : Function.Injective (algebraMap ρ.range R') := Subtype.val_injective
  let toG : Gal (algebraMap ρ.range R') → Gal ρ := fun σ => ⟨σ.1, fun r => σ.2 (π r)⟩
  have hG₀ : IsGal (algebraMap ρ.range R') := by
    refine ⟨?_, fun x hx => ?_⟩
    · have : Finite (Gal ρ) := hG.1
      exact Finite.of_injective toG (fun a b h => Subtype.ext (show a.1 = b.1 from congrArg (fun s : Gal ρ => s.1) h))
    · have hx' : ∀ σ ∈ Gal ρ, σ x = x := fun σ hσ => by
        refine hx σ ?_
        rintro ⟨_, r, rfl⟩
        exact hσ r
      exact ⟨⟨x, hG.2 x hx'⟩, rfl⟩
  have hflat : Flat (Over.mk (pullback.snd p (spMap π))).hom := by
    change Flat (pullback.snd p (spMap π)); infer_instance
  have : IsClosedImmersion (spMap π) := IsClosedImmersion.spec_of_surjective _ hπ
  have hz₀ : p₀ z₀ = p₀ z := by
    apply (pullback.fst p (spMap π)).isClosedEmbedding.injective
    rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, hp₀, hz]
  obtain ⟨σ', h, h₁, h₂, h₃⟩ := gal_transitive_on_fibres ρ.range R' hinj hG₀ (Over.mk (pullback.snd p (spMap π)))
    hflat X p₀ p' hpb₀ z₀ z hz₀
  refine ⟨toG σ', ?_⟩
  have he : act (toG σ') = h := by
    refine hpb.hom_ext ?_ ?_
    · rw [hactβ, ← hp₀, ← Category.assoc, h₁]
    · rw [hact, h₂]; rfl
  rw [he, h₃]

end GlobalTheory.Mum.GalFibre
