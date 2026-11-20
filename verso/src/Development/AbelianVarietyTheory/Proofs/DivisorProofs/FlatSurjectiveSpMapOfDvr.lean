import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.TateUnramifiedOfTorsionUnramified
import Development.AbelianVarietyTheory.Definitions.Degenerations.OfDerivationFnOn
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj Pointwise
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.HTLat GlobalTheory.Published GlobalTheory.Published.AbVarRed IsLocalRing
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

/- English proof (translation)
Introduce `R K W K' _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ h`. Establish `hinj : Function.Injective (algebraMap R W)`. Establish `h1 : (algebraMap W K').comp (algebraMap R W) = (algebraMap K K').comp (algebraMap R K)`. Rewrite using `[← IsScalarTower.algebraMap_eq, ← IsScalarTower.algebraMap_eq]`. Establish `h2 : Function.Injective ((algebraMap K K').comp (algebraMap R K))` using `(algebraMap K K').injective.comp (IsFractionRing.injective R K)`.

Rewrite `h2` using `[← h1]`. Conclude with `Function.Injective.of_comp h2`. Establish `hfl : Module.Flat R W`. Rewrite using `[IsDedekindDomain.flat_iff_torsion_eq_bot, eq_bot_iff]`. Introduce `x hx`.

Take `⟨⟨a, ha⟩, hax⟩` from `(Submodule.mem_torsion_iff x).1 hx`. Establish `ha0 : a ≠ 0` using `nonZeroDivisors.ne_zero ha`. Express the relevant statement in the definitionally equal form `a • x = 0 at hax`. Rewrite `hax` using `[Algebra.smul_def]`. Break down `mul_eq_zero.1 hax with h0 | h0` into its components or cases.

Conclude with `absurd (hinj (h0.trans (map_zero _).symm)) ha0`. Simplify using `[h0]`. Establish `hloc : IsLocalHom (algebraMap R W)`. Use `((IsLocalRing.local_hom_TFAE (algebraMap R W)).out 0 2).2 ?_` and prove the remaining obligations. Rewrite using `[h]`.

Establish `hff : Module.FaithfullyFlat R W` using `Module.FaithfullyFlat.of_flat_of_isLocalHom`. Establish `hrf : (algebraMap R W).FaithfullyFlat` using `RingHom.faithfullyFlat_algebraMap_iff.2 hff`. Take `⟨h1, h2⟩` from `(flat_and_surjective_SpecMap_iff (CommRingCat.ofHom (algebraMap R W))).2 hrf`. Conclude with `⟨h1, h2⟩`.
-/
theorem flat_surjective_spMap_of_dvr : ∀ (R K W K' : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Field K] [Algebra R K] [IsFractionRing R K] [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [Field K'] [Algebra W K'] [IsFractionRing W K'] [Algebra R W] [Algebra K K'] [Algebra R K'] [IsScalarTower R W K'] [IsScalarTower R K K'], (maximalIdeal R).map (algebraMap R W) = maximalIdeal W → Flat (spMap (algebraMap R W)) ∧ Surjective (spMap (algebraMap R W)) := by
  intro R K W K' _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ h
  have hinj : Function.Injective (algebraMap R W) := by
    have h1 : (algebraMap W K').comp (algebraMap R W) = (algebraMap K K').comp (algebraMap R K) := by
      rw [← IsScalarTower.algebraMap_eq, ← IsScalarTower.algebraMap_eq]
    have h2 : Function.Injective ((algebraMap K K').comp (algebraMap R K)) :=
      (algebraMap K K').injective.comp (IsFractionRing.injective R K)
    rw [← h1] at h2
    exact Function.Injective.of_comp h2
  have hfl : Module.Flat R W := by
    rw [IsDedekindDomain.flat_iff_torsion_eq_bot, eq_bot_iff]
    intro x hx
    obtain ⟨⟨a, ha⟩, hax⟩ := (Submodule.mem_torsion_iff x).1 hx
    have ha0 : a ≠ 0 := nonZeroDivisors.ne_zero ha
    change a • x = 0 at hax
    rw [Algebra.smul_def] at hax
    rcases mul_eq_zero.1 hax with h0 | h0
    · exact absurd (hinj (h0.trans (map_zero _).symm)) ha0
    · simp [h0]
  have hloc : IsLocalHom (algebraMap R W) := by
    refine ((IsLocalRing.local_hom_TFAE (algebraMap R W)).out 0 2).2 ?_
    rw [h]
  have hff : Module.FaithfullyFlat R W := Module.FaithfullyFlat.of_flat_of_isLocalHom
  have hrf : (algebraMap R W).FaithfullyFlat := RingHom.faithfullyFlat_algebraMap_iff.2 hff
  obtain ⟨h1, h2⟩ := (flat_and_surjective_SpecMap_iff (CommRingCat.ofHom (algebraMap R W))).2 hrf
  exact ⟨h1, h2⟩

end GlobalTheory
