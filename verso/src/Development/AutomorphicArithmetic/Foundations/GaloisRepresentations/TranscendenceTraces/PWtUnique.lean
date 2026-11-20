import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TranscendenceTraces.IsolateSpec

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC UpperTheory.Gal.TranscendenceTraces

/- English proof (translation)
Introduce `hV hL Z S p _ w w' hw hw' D hD hagree`. Establish `hdiff : IsWt p (w.add (Wt.smul (-1) w'))` using `hL.1 p w _ hw (hL.2.1 p (-1) w' hw')`. Establish `h0` using `hV p _ hdiff D hD (by`. Introduce `Ω _ _ z hz`. Use `show w Ω z + (-1) * w' Ω z = 0`.

Rewrite using `[hagree Ω z hz]`. Use the proof step `ring)`. Use function extensionality and compare the values at `Ω _ _ z`. Establish `h` using `congrFun (congrFun (congrFun (congrFun h0 Ω) ‹_›) ‹_›) z`. Express the relevant statement in the definitionally equal form `w Ω z + (-1) * w' Ω z = 0 at h`.

Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem UpperTheory.Gal.TranscendenceTraces.wtUnique_of :
    WtVanish → WtLin → WtUnique := by
  intro hV hL Z S p _ w w' hw hw' D hD hagree
  have hdiff : IsWt p (w.add (Wt.smul (-1) w')) := hL.1 p w _ hw (hL.2.1 p (-1) w' hw')
  have h0 := hV p _ hdiff D hD (by
    intro Ω _ _ z hz
    show w Ω z + (-1) * w' Ω z = 0
    rw [hagree Ω z hz]
    ring)
  funext Ω _ _ z
  have h := congrFun (congrFun (congrFun (congrFun h0 Ω) ‹_›) ‹_›) z
  change w Ω z + (-1) * w' Ω z = 0 at h
  linarith
