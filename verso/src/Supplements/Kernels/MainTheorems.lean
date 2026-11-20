import Formalism.GammaFactorNonvanishing.CritLine
import Development.AutomorphicArithmetic.CharacterBoxes.ClaimStrip
import Development.AutomorphicArithmetic.CharacterBoxes.MainConclusion

open Complex DirichletCharacter

/- English proof (authored)
The conclusion is exactly the right half-plane nonvanishing theorem `UpperTheory.FinalTheorems.everyCharacter`. Use that result for the given character and point.
-/
theorem allChi : UpperTheory.EveryCharacter := UpperTheory.FinalTheorems.everyCharacter

/- English proof (authored)
The reduction `Formalism.VW.rh_of_every` derives the Riemann Hypothesis from right half-plane nonvanishing for all characters. Supply that nonvanishing result using `allChi`.
-/
theorem rhOfAll : RiemannHypothesis := Formalism.VW.rh_of_every allChi

/- English proof (authored)
Fix a primitive character χ and a zero s with 0 < Re(s) < 1. Apply the critical-line criterion `Formalism.VW.critLine` with the nonvanishing theorem `allChi`. The criterion gives Re(s) = 1/2.
-/
theorem critAll (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N) (hχ : χ.IsPrimitive) (s : ℂ)
    (h0 : 0 < s.re) (h1 : s.re < 1) (hz : LFunction χ s = 0) : s.re = 1 / 2 :=
  Formalism.VW.critLine allChi N χ hχ s h0 h1 hz

/- English proof (authored)
The right half-plane claim is `allChi`. Applying `Claim.strip` and `Claim.zeta` to this result gives the critical-strip conclusion for Dirichlet L-functions and the zeta-function conclusion. Combine the three claims.
-/
theorem claimAll : Claim.HalfPlane ∧ Claim.Strip ∧ Claim.Zeta :=
  ⟨allChi, Claim.strip allChi, Claim.zeta allChi⟩
