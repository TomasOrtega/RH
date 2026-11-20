import Formalism.GammaFactorNonvanishing.CritLine
import Development.AutomorphicArithmetic.CharacterBoxes.ClaimStrip
import Development.AutomorphicArithmetic.CharacterBoxes.MainConclusion

open Complex DirichletCharacter

/- English proof (authored)
Apply the right half-plane nonvanishing theorem for every Dirichlet character to the given character and point.
-/
theorem allChi : UpperTheory.EveryCharacter := UpperTheory.FinalTheorems.everyCharacter

/- English proof (authored)
The reduction to the Riemann Hypothesis requires right half-plane nonvanishing for all characters. Apply it using the preceding nonvanishing theorem.
-/
theorem rhOfAll : RiemannHypothesis := Formalism.VW.rh_of_every allChi

/- English proof (authored)
Fix a primitive character χ and a zero s with 0 < Re(s) < 1. Apply the primitive-character critical-line criterion with the right half-plane nonvanishing theorem. The criterion gives Re(s) = 1/2.
-/
theorem critAll (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N) (hχ : χ.IsPrimitive) (s : ℂ)
    (h0 : 0 < s.re) (h1 : s.re < 1) (hz : LFunction χ s = 0) : s.re = 1 / 2 :=
  Formalism.VW.critLine allChi N χ hχ s h0 h1 hz

/- English proof (authored)
Start with right half-plane nonvanishing for every character. The Dirichlet critical-strip reduction and the zeta-zero reduction give the other two conclusions from this same input. Combine the three claims.
-/
theorem claimAll : Claim.HalfPlane ∧ Claim.Strip ∧ Claim.Zeta :=
  ⟨allChi, Claim.strip allChi, Claim.zeta allChi⟩
