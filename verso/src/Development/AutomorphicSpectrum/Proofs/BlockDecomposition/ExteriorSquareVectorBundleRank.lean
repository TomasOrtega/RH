import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IotaQInjective
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsAlgHomOfIsBaseChange

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TensorProduct Opposite MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR MainStatements.Hodge GlobalTheory.CompanionTheory.WedgeOf

namespace GlobalTheory.CompanionTheory.WedgeOf

/- English proof (translation)
Introduce `R V _ _ _ g h`. Take `⟨hf, hp, hr⟩` from `h`. Establish `hproj : Module.Projective R (⋀[R]^2 V)`. Take `⟨s, hs⟩` from `Module.projective_def'.1 hp`. Use `haveI : Module.Free R (⋀[R]^2 (V →₀ R)) := exteriorPower.instFree R 2`.

Use `Module.Projective.of_split (exteriorPower.map 2 s) (exteriorPower.map 2 (Finsupp.linearCombination R id)) ?_` and prove the remaining obligations. Rewrite using `[← exteriorPower.map_comp, hs, exteriorPower.map_id]`. Use `⟨inferInstance, hproj, fun p => ?_⟩` and prove the remaining obligations. Establish `hb` using `LocalizedModule.isBaseChange p.asIdeal.primeCompl V`. Establish `hb2` using `GlobalTheory.TopForm.isBaseChange_exteriorPower hb 2`.

Set `S` to `Localization.AtPrime p.asIdeal`. Set `M` to `LocalizedModule p.asIdeal.primeCompl V`. Set `q : PrimeSpectrum S` to `IsLocalRing.closedPoint S`. Establish `hq : PrimeSpectrum.comap (algebraMap R S) q = p` using `PrimeSpectrum.ext (Localization.AtPrime.comap_maximalIdeal (I := p.asIdeal))`. Establish `h1` using `Module.rankAtStalk_isBaseChange hb q`.

Establish `h2` using `Module.rankAtStalk_isBaseChange hb2 q`. Rewrite `h1`, `h2` using `[hq]`. Use `haveI : Module.Finite S M := Module.Finite.equiv hb.equiv`. Use `haveI : Module.Flat S M := Module.Flat.of_linearEquiv hb.equiv.symm`. Use `haveI : Module.Free S M := Module.free_of_flat_of_isLocalRing`.

Establish `h3 : Module.finrank S M = g`. Rewrite using `[← hr p, ← h1, Module.rankAtStalk_eq_finrank_of_free]`. Both sides reduce to the same expression. Rewrite using `[← h2, Module.rankAtStalk_eq_finrank_of_free]`. Express the relevant statement in the definitionally equal form `Module.finrank S (⋀[S]^2 M) = _`.

Rewrite using `[exteriorPower.finrank_eq, h3]`.
-/
theorem vb_exteriorPower_two : ∀ (R V : Type) [CommRing R] [AddCommGroup V] [Module R V] (g : ℕ),
    VB R V g → VB R (⋀[R]^2 V) (g.choose 2) := by
  intro R V _ _ _ g h
  obtain ⟨hf, hp, hr⟩ := h
  have hproj : Module.Projective R (⋀[R]^2 V) := by
    obtain ⟨s, hs⟩ := Module.projective_def'.1 hp
    haveI : Module.Free R (⋀[R]^2 (V →₀ R)) := exteriorPower.instFree R 2
    refine Module.Projective.of_split (exteriorPower.map 2 s)
      (exteriorPower.map 2 (Finsupp.linearCombination R id)) ?_
    rw [← exteriorPower.map_comp, hs, exteriorPower.map_id]
  refine ⟨inferInstance, hproj, fun p => ?_⟩
  have hb := LocalizedModule.isBaseChange p.asIdeal.primeCompl V
  have hb2 := GlobalTheory.TopForm.isBaseChange_exteriorPower hb 2
  let S := Localization.AtPrime p.asIdeal
  let M := LocalizedModule p.asIdeal.primeCompl V
  let q : PrimeSpectrum S := IsLocalRing.closedPoint S
  have hq : PrimeSpectrum.comap (algebraMap R S) q = p :=
    PrimeSpectrum.ext (Localization.AtPrime.comap_maximalIdeal (I := p.asIdeal))
  have h1 := Module.rankAtStalk_isBaseChange hb q
  have h2 := Module.rankAtStalk_isBaseChange hb2 q
  rw [hq] at h1 h2
  haveI : Module.Finite S M := Module.Finite.equiv hb.equiv
  haveI : Module.Flat S M := Module.Flat.of_linearEquiv hb.equiv.symm
  haveI : Module.Free S M := Module.free_of_flat_of_isLocalRing
  have h3 : Module.finrank S M = g := by
    rw [← hr p, ← h1, Module.rankAtStalk_eq_finrank_of_free]
    rfl
  rw [← h2, Module.rankAtStalk_eq_finrank_of_free]
  change Module.finrank S (⋀[S]^2 M) = _
  rw [exteriorPower.finrank_eq, h3]

end GlobalTheory.CompanionTheory.WedgeOf
