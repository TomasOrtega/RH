import Mathlib
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ZarhinDualPolarisation.FlatFiniteFibres.FlatOfFibresFinite

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry

namespace GlobalTheory.CompanionTheory.Dblock

/- English proof (translation)
Introduce `R _ A B A' l hf hs hq g₁ g₂ h`. Establish `: EffectiveEpi l.left` using `inferInstance`. Establish `: Epi l.left` using `inferInstance`. Apply `Over.OverMorphism.ext` to reduce the goal to its premises. Rewrite using `[← cancel_epi l.left]`.

Simplify using `using congrArg (fun k => k.left) h`.
-/
theorem epiOfFF : PositivityTheory.Tls2.Zar3.Ch1.EpiOfFF := by
  intro R _ A B A' l hf hs hq g₁ g₂ h
  have : EffectiveEpi l.left := inferInstance
  have : Epi l.left := inferInstance
  apply Over.OverMorphism.ext
  rw [← cancel_epi l.left]
  simpa using congrArg (fun k => k.left) h

end GlobalTheory.CompanionTheory.Dblock
