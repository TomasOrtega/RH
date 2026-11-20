import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SpMapCompSpMap
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AbProj

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits
open ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory

namespace GlobalTheory.HorComp

/- English proof (translation)
Take `⟨N, i, hi, rfl⟩` from `hq`. Establish `: IsProper (PSpace.str k N)` using `isProper_str k N`. Establish `hp : IsProper (pullback.snd (i ≫ PSpace.str k N) (spMap (σ.comp β)))` using `inferInstance`. Establish `h1 : IsLocallyNoetherian (cxFib β (i ≫ PSpace.str k N) σ)` using `LocallyOfFiniteType.isLocallyNoetherian (pullback.snd (i ≫ PSpace.str k N) (spMap (σ.comp β)))`. Establish `h2 : CompactSpace (cxFib β (i ≫ PSpace.str k N) σ)` using `QuasiCompact.compactSpace_of_compactSpace (pullback.snd (i ≫ PSpace.str k N) (spMap (σ.comp β)))`.

Conclude with `{}`.
-/
theorem isNoetherian_cxFib {k F : Type} [CommRing k] [CommRing F] (β : k →+* F) {Y : Scheme.{0}} {q : Y ⟶ Sp k}
    (σ : F →+* ℂ) (hq : IsProjOver q) : IsNoetherian (cxFib β q σ) := by
  obtain ⟨N, i, hi, rfl⟩ := hq
  have : IsProper (PSpace.str k N) := isProper_str k N
  have hp : IsProper (pullback.snd (i ≫ PSpace.str k N) (spMap (σ.comp β))) := inferInstance
  have h1 : IsLocallyNoetherian (cxFib β (i ≫ PSpace.str k N) σ) :=
    LocallyOfFiniteType.isLocallyNoetherian (pullback.snd (i ≫ PSpace.str k N) (spMap (σ.comp β)))
  have h2 : CompactSpace (cxFib β (i ≫ PSpace.str k N) σ) :=
    QuasiCompact.compactSpace_of_compactSpace (pullback.snd (i ≫ PSpace.str k N) (spMap (σ.comp β)))
  exact {}

/- English proof (translation)
Introduce `k F _ _ β Y q σ n h`. Use `isNoetherian_cxFib β σ h.isProjOver` as an intermediate fact. Conclude with `NoetherianSpace.finite_irreducibleComponents`.
-/
theorem finite_irreducibleComponents_cxFib : ∀ (k F : Type) [CommRing k] [CommRing F] (β : k →+* F) (Y : Scheme.{0})
    (q : Y ⟶ Sp k) (σ : F →+* ℂ) (n : ℕ), IsArithVar q n → (irreducibleComponents (cxFib β q σ)).Finite := by
  intro k F _ _ β Y q σ n h
  have := isNoetherian_cxFib β σ h.isProjOver
  exact NoetherianSpace.finite_irreducibleComponents

end GlobalTheory.HorComp
