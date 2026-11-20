import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ThetaUnifAV

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory

/- English proof (translation)
Use `⟨fun y => ?_⟩` and prove the remaining obligations. Establish `hcl : IsClosed (Set.range f)` using `f.isClosedMap.isClosed_range`. Set `e : Sp V` to `(⊥ : PrimeSpectrum V)`. Establish `hη : e ⤳ g y` using `(PrimeSpectrum.le_iff_specializes _ _).mp (bot_le (α := PrimeSpectrum V))`. Take `⟨y', hy', hy''⟩` from `Flat.generalizingMap g hη`.

Use `hy'.mem_closed hcl (h y' ?_)` and prove the remaining obligations. Rewrite using `[hy'']`. Use `⟨(⊥ : PrimeSpectrum K), ?_⟩` and prove the remaining obligations. Apply `PrimeSpectrum.ext` to reduce the goal to its premises. Express the relevant statement in the definitionally equal form `Ideal.comap (algebraMap V K) ⊥ = ⊥`.

Conclude with `Ideal.comap_bot_of_injective _ (IsFractionRing.injective V K)`.
-/
theorem surjective_of_generic_fibre_subset_range
    {V K : Type} [CommRing V] [IsDomain V] [Field K] [Algebra V K] [IsFractionRing V K]
    {X Y : Scheme.{0}} (f : X ⟶ Y) (g : Y ⟶ Sp V) [UniversallyClosed f] [Flat g]
    (h : ∀ y : Y, g y ∈ Set.range (spMap (algebraMap V K)) → y ∈ Set.range f) :
    Surjective f := by
  refine ⟨fun y => ?_⟩
  have hcl : IsClosed (Set.range f) := f.isClosedMap.isClosed_range
  let e : Sp V := (⊥ : PrimeSpectrum V)
  have hη : e ⤳ g y := (PrimeSpectrum.le_iff_specializes _ _).mp (bot_le (α := PrimeSpectrum V))
  obtain ⟨y', hy', hy''⟩ := Flat.generalizingMap g hη
  refine hy'.mem_closed hcl (h y' ?_)
  rw [hy'']
  refine ⟨(⊥ : PrimeSpectrum K), ?_⟩
  apply PrimeSpectrum.ext
  change Ideal.comap (algebraMap V K) ⊥ = ⊥
  exact Ideal.comap_bot_of_injective _ (IsFractionRing.injective V K)

/- English proof (translation)
Introduce `V K _ _ _ _ _ _ B G _ _ hB hG ψ h`. Use `hB.proper` as an intermediate fact. Use `hG.smooth` as an intermediate fact. Use `hG.separated` as an intermediate fact. Establish `hw : ψ.left ≫ G.hom = B.hom` using `Over.w ψ`.

Establish `: IsProper (ψ.left ≫ G.hom)` using `hw ▸ hB.proper`. Establish `: IsProper ψ.left` using `IsProper.of_comp ψ.left G.hom`. Establish `: Surjective ψ.left` using `surjective_of_generic_fibre_subset_range ψ.left G.hom h`. Establish `: UniversallyClosed G.hom` using `UniversallyClosed.of_comp_surjective ψ.left G.hom`. Conclude with `⟨hG.comm, hG.smooth, ⟨⟩, hG.geomConnected⟩`.
-/
theorem isAbelianScheme_of_generically_surjective :
    ∀ (V K : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [Field K] [Algebra V K]
      [IsFractionRing V K] (B G : Over (Sp V)) [GrpObj B] [GrpObj G],
      IsAbelianScheme B → IsSemiAbelian G → ∀ ψ : B ⟶ G,
      (∀ x : G.left, G.hom x ∈ Set.range (spMap (algebraMap V K)) → x ∈ Set.range ψ.left) →
      IsAbelianScheme G := by
  intro V K _ _ _ _ _ _ B G _ _ hB hG ψ h
  have := hB.proper
  have := hG.smooth
  have := hG.separated
  have hw : ψ.left ≫ G.hom = B.hom := Over.w ψ
  have : IsProper (ψ.left ≫ G.hom) := hw ▸ hB.proper
  have : IsProper ψ.left := IsProper.of_comp ψ.left G.hom
  have : Surjective ψ.left := surjective_of_generic_fibre_subset_range ψ.left G.hom h
  have : UniversallyClosed G.hom := UniversallyClosed.of_comp_surjective ψ.left G.hom
  exact ⟨hG.comm, hG.smooth, ⟨⟩, hG.geomConnected⟩

end GlobalTheory
