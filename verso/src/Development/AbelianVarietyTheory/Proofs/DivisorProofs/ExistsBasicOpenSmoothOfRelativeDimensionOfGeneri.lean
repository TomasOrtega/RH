import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.TateUnramifiedOfTorsionUnramified
import Development.AbelianVarietyTheory.Definitions.Degenerations.OfDerivationFnOn
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.DimSplitPf
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj Pointwise
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.HTLat GlobalTheory.Published GlobalTheory.Published.AbVarRed IsLocalRing
attribute [local instance] Over.cartesianMonoidalCategory
open TopologicalSpace

namespace GlobalTheory.SmoothRelDim

/- English proof (translation)
Establish `hdom : IsDominant (spMap e)` using `⟨(PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical _).2 (by change RingHom.ker e ≤ _; rw [(RingHom.injective_iff_ker_eq_bot e).1 he]; exact bot_le)⟩`. Use `choose n W hW hd using ReciprocityTheory.ChartRestriction.G.H1.exists_dim X.hom`. Establish `: UniversallyOpen X.hom` using `UniversallyOpen.of_flat X.hom`. Establish `key : ∀ x, n x = g` using `fun x => by`. Establish `ho : IsOpen (X.hom.base '' (W x : Set X.left))` using `X.hom.isOpenMap _ (W x).isOpen`.

Take `⟨s, ⟨y, hyW, hy⟩, t, rfl⟩` from `hdom.denseRange.inter_open_nonempty _ ho ⟨_, x, hW x, rfl⟩`. Take `⟨z, hz1, -⟩` from `Scheme.Pullback.exists_preimage_pullback y t hy`. Conclude with `ReciprocityTheory.ChartRestriction.G.H1.dim_base (IsPullback.of_hasPullback X.hom (spMap e)) (hd x) hg z (hz1 ▸ hyW)`. Establish `: IsZariskiLocalAtSource (@SmoothOfRelativeDimension g)` using `HasRingHomProperty.instIsZariskiLocalAtSource`. Conclude with `IsZariskiLocalAtSource.of_iSup_eq_top (P := @SmoothOfRelativeDimension g) W (top_le_iff.1 fun x _ => Opens.mem_iSup.2 ⟨x, hW x⟩) fun x => key x ▸ hd x`.
-/
theorem smoothOfRelativeDimension_of_generic (R : Type) [CommRing R] [IsDomain R] (X : Over (Sp R))
    [Smooth X.hom] (K : Type) [Field K] (e : R →+* K) (he : Function.Injective e) (g : ℕ)
    (hg : SmoothOfRelativeDimension g (pullback.snd X.hom (spMap e))) :
    SmoothOfRelativeDimension g X.hom := by
  have hdom : IsDominant (spMap e) := ⟨(PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical _).2
      (by change RingHom.ker e ≤ _; rw [(RingHom.injective_iff_ker_eq_bot e).1 he]; exact bot_le)⟩
  choose n W hW hd using ReciprocityTheory.ChartRestriction.G.H1.exists_dim X.hom
  have : UniversallyOpen X.hom := UniversallyOpen.of_flat X.hom
  have key : ∀ x, n x = g := fun x => by
    have ho : IsOpen (X.hom.base '' (W x : Set X.left)) := X.hom.isOpenMap _ (W x).isOpen
    obtain ⟨s, ⟨y, hyW, hy⟩, t, rfl⟩ :=
      hdom.denseRange.inter_open_nonempty _ ho ⟨_, x, hW x, rfl⟩
    obtain ⟨z, hz1, -⟩ := Scheme.Pullback.exists_preimage_pullback y t hy
    exact ReciprocityTheory.ChartRestriction.G.H1.dim_base (IsPullback.of_hasPullback X.hom (spMap e)) (hd x) hg z (hz1 ▸ hyW)
  have : IsZariskiLocalAtSource (@SmoothOfRelativeDimension g) := HasRingHomProperty.instIsZariskiLocalAtSource
  exact IsZariskiLocalAtSource.of_iSup_eq_top (P := @SmoothOfRelativeDimension g) W
    (top_le_iff.1 fun x _ => Opens.mem_iSup.2 ⟨x, hW x⟩) fun x => key x ▸ hd x

/- English proof (translation)
Introduce `R _ _ _ X hX _ K _ e he g hg`. Use `haveI := hX`. Use `⟨1, by simp, fun F _ ψ _ => ?_⟩` and prove the remaining obligations. Conclude with `(smoothOfRelativeDimension_isStableUnderBaseChange g).of_isPullback (IsPullback.of_hasPullback _ _) (smoothOfRelativeDimension_of_generic R X K e he g hg)`.
-/
theorem exists_basicOpen : ∀ (R : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] (X : Over (Sp R)), Smooth X.hom → QuasiCompact X.hom → ∀ (K : Type) [Field K] (e : R →+* K), Function.Injective e → ∀ g : ℕ, SmoothOfRelativeDimension g (pullback.snd X.hom (spMap e)) → ∃ f : R, e f ≠ 0 ∧ ∀ (F : Type) [Field F] (ψ : R →+* F), IsUnit (ψ f) → SmoothOfRelativeDimension g (pullback.snd X.hom (spMap ψ)) := by
  intro R _ _ _ X hX _ K _ e he g hg
  haveI := hX
  refine ⟨1, by simp, fun F _ ψ _ => ?_⟩
  exact (smoothOfRelativeDimension_isStableUnderBaseChange g).of_isPullback (IsPullback.of_hasPullback _ _)
    (smoothOfRelativeDimension_of_generic R X K e he g hg)

end GlobalTheory.SmoothRelDim
