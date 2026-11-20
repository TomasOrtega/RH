import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.SatakeLifts.PairOfLiftAlt
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.HeckeAdjoints.SatConj
open NumberField IsDedekindDomain ValuativeRel GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.ThetaGL UpperTheory.Gal.TP.Loc
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

/- English proof (translation)
Introduce `hCU K _ _ w n V _ _ ρ hs hi hu B hB`. Take `⟨-, C, hC⟩` from `hCU (w.adicCompletion K) n V ρ hs hi hu`. Take `⟨b, -, hp, hinv⟩` from `hu`. Use `UpperTheory.V.Af.Gk.satConj K n w V (smoothPart ρ.dual) ρ (contra ρ) b.flip C ?_ ?_ hC B hB` and prove the remaining obligations. Introduce `x hx`.

Assume the negation of the conclusion as `h0`. Establish `h1` using `hp x h0`. Establish `h2 : b x x = 0` using `hx`. Rewrite `h1` using `[h2]`. Simplify using `at h1`.

Introduce `g x y`. Conclude with `hinv g y x`.
-/
theorem UpperTheory.Gal.TP.Loc.satContra :
    UpperTheory.Gal.TP.Loc.ContraUnit → UpperTheory.Gal.TP.Loc.SatContra := by
  intro hCU K _ _ w n V _ _ ρ hs hi hu B hB
  obtain ⟨-, C, hC⟩ := hCU (w.adicCompletion K) n V ρ hs hi hu
  obtain ⟨b, -, hp, hinv⟩ := hu
  refine UpperTheory.V.Af.Gk.satConj K n w V (smoothPart ρ.dual) ρ (contra ρ) b.flip C ?_ ?_ hC B hB
  · intro x hx
    by_contra h0
    have h1 := hp x h0
    have h2 : b x x = 0 := hx
    rw [h2] at h1
    simp at h1
  · intro g x y
    exact hinv g y x
