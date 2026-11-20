import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.AdelicGroupAlgebraActionInjective
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsHTFormOver
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.PushInvertible
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.GlueApplyOfNotInFibre
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsHodgeLine
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsStalkFractionOfGeneric

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar

namespace GlobalTheory.CompanionTheory.Ar.IntReg

/- English proof (translation)
Introduce `X Ω _ ξ p hξ hcl a ha`. Establish `hinj : Function.Injective (genMap ξ p)` using `hξ.inj p`. Set `_ : Algebra (X.presheaf.stalk p.1) Ω` to `(genMap ξ p).toAlgebra`. Establish `hmap : ∀ x, algebraMap (X.presheaf.stalk p.1) Ω x = genMap ξ p x` using `fun _ => rfl`. Establish `: IsDomain (X.presheaf.stalk p.1)` using `hinj.isDomain _`.

Establish `: FaithfulSMul (X.presheaf.stalk p.1) Ω` using `(faithfulSMul_iff_algebraMap_injective _ _).2 hinj`. Establish `: IsFractionRing (X.presheaf.stalk p.1) Ω` using `IsFractionRing.of_field _ _ fun z => by`. Take `⟨b, c, hc, e⟩` from `exists_frac_genMap ξ hξ p z`. Conclude with `⟨b, c, by rw [hmap, hmap, ← e, mul_div_cancel_right₀ _ hc]⟩`. Establish `hb : _root_.IsIntegral (X.presheaf.stalk p.1) a` using `ha.tower_top`.

Take `⟨w, rfl⟩` from `IsIntegrallyClosed.isIntegral_iff.1 hb`. Conclude with `⟨w, rfl⟩`.
-/
theorem mem_regAt_of_isIntegral_of_stalk :
    ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Sp Ω ⟶ X) (p : Cpt ξ), IsCptGen ξ →
      IsIntegrallyClosed (X.presheaf.stalk p.1) → ∀ a : Ω, IsIntegral ℤ a → a ∈ regAt ξ p := by
  intro X Ω _ ξ p hξ hcl a ha
  have hinj : Function.Injective (genMap ξ p) := hξ.inj p
  let _ : Algebra (X.presheaf.stalk p.1) Ω := (genMap ξ p).toAlgebra
  have hmap : ∀ x, algebraMap (X.presheaf.stalk p.1) Ω x = genMap ξ p x := fun _ => rfl
  have : IsDomain (X.presheaf.stalk p.1) := hinj.isDomain _
  have : FaithfulSMul (X.presheaf.stalk p.1) Ω :=
    (faithfulSMul_iff_algebraMap_injective _ _).2 hinj
  have : IsFractionRing (X.presheaf.stalk p.1) Ω := IsFractionRing.of_field _ _ fun z => by
    obtain ⟨b, c, hc, e⟩ := exists_frac_genMap ξ hξ p z
    exact ⟨b, c, by rw [hmap, hmap, ← e, mul_div_cancel_right₀ _ hc]⟩
  have hb : _root_.IsIntegral (X.presheaf.stalk p.1) a := ha.tower_top
  obtain ⟨w, rfl⟩ := IsIntegrallyClosed.isIntegral_iff.1 hb
  exact ⟨w, rfl⟩

end GlobalTheory.CompanionTheory.Ar.IntReg
