import Mathlib
import Development.AbelianVarietyTheory.Definitions.CMLattices.ExistsIsThetaDegOfIsLocalModel
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.CmCurveBaseChangeCompStatement
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.OneMulConjFracOneEqInvDifferent

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open scoped CategoryTheory.Obj
open GlobalTheory GlobalTheory.CM

namespace GlobalTheory.CM

/- English proof (translation)
Introduce `hbc E _ _ _ H M K _ _ _ _ j ω ω' C C' φ x hm hx`. Take `⟨n, hn, hmean⟩` from `hx`. Use `⟨fun s => n (s.comp j), fun s => ⟨(hn _).1, fun r => ?_⟩, ?_⟩` and prove the remaining obligations. Rewrite using `[(GlobalTheory.T.cmCurveBaseChange_comp E H _ ω C _ ω' C' _ φ hm).2.2 _ r hbc]`. Establish `e : (s.comp (algebraMap (𝓞 K) K)).comp (RingOfIntegers.mapRingHom j) = (s.comp j).comp (algebraMap (𝓞 M) M)`.

Use extensionality with `a`. Both sides reduce to the same expression. Rewrite using `[e]`. Conclude with `(hn _).2 r`. Rewrite using `[GlobalTheory.meanLog_comp]`.

Conclude with `hmean`.
-/
theorem hasPeriod_of_ellMap : Out.PolBaseChangeSt → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (M K : Type) [Field M] [NumberField M] [Field K] [NumberField K] (j : M →+* K) (ω : 𝓞 M) (ω' : 𝓞 K) (C : Ell H (𝓞 M) ω) (C' : Ell H (𝓞 K) ω') (φ : C'.P.A.left ⟶ C.P.A.left) (x : ℝ), EllMap C' C (RingOfIntegers.mapRingHom j) φ → C.HasPeriod x → C'.HasPeriod x := by
  intro hbc E _ _ _ H M K _ _ _ _ j ω ω' C C' φ x hm hx
  obtain ⟨n, hn, hmean⟩ := hx
  refine ⟨fun s => n (s.comp j), fun s => ⟨(hn _).1, fun r => ?_⟩, ?_⟩
  · rw [(GlobalTheory.T.cmCurveBaseChange_comp E H _ ω C _ ω' C' _ φ hm).2.2 _ r hbc]
    have e : (s.comp (algebraMap (𝓞 K) K)).comp (RingOfIntegers.mapRingHom j)
        = (s.comp j).comp (algebraMap (𝓞 M) M) := by
      ext a; rfl
    rw [e]
    exact (hn _).2 r
  · rw [GlobalTheory.meanLog_comp]; exact hmean

end GlobalTheory.CM
